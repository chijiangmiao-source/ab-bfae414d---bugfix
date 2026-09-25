'use strict';

/**
 * 单位（量纲）单项式：基本单位与单位变量的整数次幂乘积。
 *   bases: Map<string, number>  例如 { m: 1, s: -1 } 表示 m/s
 *   vars:  Map<object, number>  单位变量（可泛化、可合一）
 */

class UnifyError extends Error {
  constructor(kind, data) {
    super(kind);
    this.name = 'UnifyError';
    this.kind = kind;
    Object.assign(this, data);
  }
}

function monoUnit() {
  return { bases: new Map(), vars: new Map() };
}

function monoBase(name, exp = 1) {
  const m = monoUnit();
  if (exp !== 0) m.bases.set(name, exp);
  return m;
}

function monoVar(v, exp = 1) {
  const m = monoUnit();
  if (exp !== 0) m.vars.set(v, exp);
  return m;
}

function addBase(m, b, e) {
  const ne = (m.bases.get(b) || 0) + e;
  if (ne === 0) m.bases.delete(b);
  else m.bases.set(b, ne);
}

function addVar(m, v, e) {
  const ne = (m.vars.get(v) || 0) + e;
  if (ne === 0) m.vars.delete(v);
  else m.vars.set(v, ne);
}

function addInto(dst, src, k) {
  for (const [b, e] of src.bases) addBase(dst, b, k * e);
  for (const [v, e] of src.vars) addVar(dst, v, k * e);
}

function monoMul(a, b) {
  const r = monoUnit();
  addInto(r, a, 1);
  addInto(r, b, 1);
  return r;
}

function monoDiv(a, b) {
  const r = monoUnit();
  addInto(r, a, 1);
  addInto(r, b, -1);
  return r;
}

function monoPow(a, k) {
  const r = monoUnit();
  addInto(r, a, k);
  return r;
}

/** 归约（zonk）：递归展开已绑定的单位变量。 */
function resolveMono(m) {
  const r = monoUnit();
  addResolved(r, m, 1);
  return r;
}

function addResolved(dst, m, k) {
  for (const [b, e] of m.bases) addBase(dst, b, k * e);
  for (const [v, e] of m.vars) {
    if (v.instance) addResolved(dst, v.instance, k * e);
    else addVar(dst, v, k * e);
  }
}

function monoEqual(a, b) {
  if (a.bases.size !== b.bases.size || a.vars.size !== b.vars.size) return false;
  for (const [k, e] of a.bases) if (b.bases.get(k) !== e) return false;
  for (const [v, e] of a.vars) if (b.vars.get(v) !== e) return false;
  return true;
}

/** 若单项式仅为一个一次单位变量，返回该变量。 */
function bareVar(m) {
  if (m.bases.size === 0 && m.vars.size === 1) {
    const [[v, e]] = m.vars;
    if (e === 1) return v;
  }
  return null;
}

function occursUVar(v, m) {
  return resolveMono(m).vars.has(v);
}

/* 单位变量在整数指数自由阿贝尔群中取值：v 可被替换为任意单位单项式，
 * 因此「v = v^2 * m」一类方程经群消去仍可解（v = m^-1），并不构成无限类型。
 * 模块内兜底的新变量工厂（正常路径由推断上下文注入，保证编号连续）。 */
let moduleUSeq = 0;
const defaultFreshUVar = () => ({ id: ++moduleUSeq, instance: null });

/**
 * 对系数行 n（长度 c，均非零）做整数列初等变换，求幺模矩阵 Q，使
 *   n · Q = [g, 0, …, 0]，其中 g = gcd(|n_i|) > 0。
 * 列变换：交换两列、列 j 减去列 i 的整数倍（欧几里得算法），末尾把首列符号归一。
 */
function diophantineBasis(coeff) {
  const c = coeff.length;
  const n = coeff.slice();
  const Q = [];
  for (let i = 0; i < c; i++) {
    Q.push(new Array(c).fill(0));
    Q[i][i] = 1;
  }
  const swapCols = (p, q) => {
    const t = n[p];
    n[p] = n[q];
    n[q] = t;
    for (let i = 0; i < c; i++) {
      const t2 = Q[i][p];
      Q[i][p] = Q[i][q];
      Q[i][q] = t2;
    }
  };
  const subtractCols = (j, i, k) => {
    if (k === 0) return;
    n[j] -= k * n[i];
    for (let r = 0; r < c; r++) Q[r][j] -= k * Q[r][i];
  };
  for (;;) {
    // 取绝对值最小的非零系数到首列
    let p = -1;
    for (let j = 0; j < c; j++) {
      if (n[j] !== 0 && (p === -1 || Math.abs(n[j]) < Math.abs(n[p]))) p = j;
    }
    if (p === -1) break;
    if (p !== 0) swapCols(p, 0);
    for (let j = 1; j < c; j++) {
      if (n[j] !== 0) subtractCols(j, 0, Math.trunc(n[j] / n[0]));
    }
    let residual = false;
    for (let j = 1; j < c; j++) {
      if (n[j] !== 0) { residual = true; break; }
    }
    if (!residual) break; // 首列即 gcd，其余列已清零
  }
  if (n[0] < 0) {
    for (let r = 0; r < c; r++) Q[r][0] = -Q[r][0];
    n[0] = -n[0];
  }
  return { g: n[0], Q };
}

/**
 * 单位合一：在整数指数（自由阿贝尔）群上求解线性丢番图方程。
 * 方程 a = b 归并为 eq = a * b^-1 = 1：
 *   Σ n_i·v_i = -Σ m_j·b_j
 * 令 g = gcd(n_i)：当且仅当 g 整除每个 m_j 时有整数解；
 * 解的自由维（c-1 个）以新鲜单位变量表示，得到最一般合一子（MGSU）。
 * 无解（g 不整除基准指数）抛出 UnifyError('unit-mismatch')。
 */
function unifyMonos(u1, u2, freshUVar = defaultFreshUVar) {
  const a = resolveMono(u1);
  const b = resolveMono(u2);
  if (monoEqual(a, b)) return;
  // 快道：单侧恰为一次单位变量时直接绑定（另一侧不含该变量，避免成环）
  const av = bareVar(a);
  if (av && !occursUVar(av, b)) {
    av.instance = b;
    return;
  }
  const bv = bareVar(b);
  if (bv && !occursUVar(bv, a)) {
    bv.instance = a;
    return;
  }
  const eq = monoDiv(a, b);
  const vars = [...eq.vars.keys()];
  if (vars.length === 0) throw new UnifyError('unit-mismatch', { u1: a, u2: b });
  const coeff = vars.map((v) => eq.vars.get(v));
  const { g, Q } = diophantineBasis(coeff);
  // 右侧常量 d = -eq.bases；可解性：g 整除每个基准指数
  for (const [, be] of eq.bases) {
    if (be % g !== 0) throw new UnifyError('unit-mismatch', { u1: a, u2: b });
  }
  // y_0 = d/g（基准单项式），y_1…y_{c-1} 为自由维（新鲜单位变量）
  const c = vars.length;
  const free = [];
  for (let j = 1; j < c; j++) free.push(freshUVar());
  for (let i = 0; i < c; i++) {
    const sol = monoUnit();
    for (const [bn, be] of eq.bases) addBase(sol, bn, (-be / g) * Q[i][0]);
    for (let j = 1; j < c; j++) {
      if (Q[i][j] !== 0) addVar(sol, free[j - 1], Q[i][j]);
    }
    vars[i].instance = sol;
  }
}

/** 以 uMap 中的单项式替换量化单位变量（实例化用）。 */
function substMono(m, uMap) {
  const rm = resolveMono(m);
  const r = monoUnit();
  for (const [b, e] of rm.bases) addBase(r, b, e);
  for (const [v, e] of rm.vars) {
    const rep = uMap.get(v);
    if (rep) addInto(r, rep, e);
    else addVar(r, v, e);
  }
  return r;
}

function renderMono(m, nameU) {
  const r = resolveMono(m);
  const parts = [];
  const bases = [...r.bases.entries()].sort((x, y) => (x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0));
  for (const [b, e] of bases) parts.push(e === 1 ? b : `${b}^${e}`);
  for (const [v, e] of r.vars) {
    const n = nameU(v);
    parts.push(e === 1 ? n : `${n}^${e}`);
  }
  return parts.length ? parts.join('*') : '1';
}

module.exports = {
  UnifyError,
  monoUnit,
  monoBase,
  monoVar,
  monoMul,
  monoDiv,
  monoPow,
  resolveMono,
  monoEqual,
  unifyMonos,
  substMono,
  renderMono,
};
