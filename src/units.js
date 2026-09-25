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

/**
 * 扩展欧几里得：返回 { g, p, q }，其中 g = gcd(a, b) ≥ 0 且 p·a + q·b = g。
 */
function egcd(a, b) {
  let r0 = Math.abs(a);
  let r1 = Math.abs(b);
  let s0 = 1;
  let s1 = 0;
  let t0 = 0;
  let t1 = 1;
  while (r1 !== 0) {
    const q = Math.floor(r0 / r1);
    const r2 = r0 - q * r1;
    const s2 = s0 - q * s1;
    const t2 = t0 - q * t1;
    r0 = r1;
    r1 = r2;
    s0 = s1;
    s1 = s2;
    t0 = t1;
    t1 = t2;
  }
  return { g: r0, p: a < 0 ? -s0 : s0, q: b < 0 ? -t0 : t0 };
}

let fallbackUVarSeq = 0;

/** 未提供新鲜变量工厂时的内部回退（变量身份唯一即可，id 取负避免与推断上下文混淆）。 */
function freshUVarFallback() {
  return { id: -(++fallbackUVarSeq), instance: null };
}

/**
 * 单方程整数指数一般求解（MGU）。
 * 方程 eq = 1（即 ∏ v^e · ∏ b^c = 1）在整数指数阿贝尔群上求最一般合一子：
 * 对指数行向量做幺模列变换 e·U = [g, 0, …, 0]（g 为全部变量指数的最大公约数）。
 * 每个基本单位指数均须被 g 整除，否则方程无整数解（返回 null）。
 * 可解时返回绑定列表 [[变量, 单项式], …]：
 *   X_i = T0^U[i][0] · ∏_{k≥1} T_k^U[i][k]
 * 其中 T0 = ∏ b^(−c/g) 为特解方向，T_k 为新鲜单位变量（齐次解格的自由度，
 * 由 U 的幺模性保证不丢失任何解，即最一般性）。
 */
function solveUnitEquation(eq, freshUVar) {
  const vars = [...eq.vars.entries()];
  const n = vars.length;
  if (n === 0) return null;
  const U = vars.map((_, i) => vars.map((_, j) => (i === j ? 1 : 0)));
  const f = vars.map(([, e]) => e);
  for (let k = 1; k < n; k++) {
    if (f[k] === 0) continue;
    const { g, p, q } = egcd(f[0], f[k]);
    const c0 = U.map((row) => row[0]);
    const ck = U.map((row) => row[k]);
    const f0 = f[0];
    const fk = f[k];
    for (let i = 0; i < n; i++) {
      U[i][0] = p * c0[i] + q * ck[i];
      U[i][k] = (f0 / g) * ck[i] - (fk / g) * c0[i];
    }
    f[0] = g;
    f[k] = 0;
  }
  const g = f[0];
  for (const [, c] of eq.bases) {
    if (c % g !== 0) return null;
  }
  const t0 = monoUnit();
  for (const [b, c] of eq.bases) addBase(t0, b, -c / g);
  const tz = [];
  for (let k = 1; k < n; k++) tz.push(monoVar(freshUVar()));
  const binds = [];
  for (let i = 0; i < n; i++) {
    const m = monoUnit();
    addInto(m, t0, U[i][0]);
    for (let k = 1; k < n; k++) addInto(m, tz[k - 1], U[i][k]);
    binds.push([vars[i][0], m]);
  }
  return binds;
}

/**
 * 单位合一：在整数指数阿贝尔群上求解。
 * 失败抛出 UnifyError('unit-mismatch' | 'occurs-unit')。
 * freshUVar（可选）：一般求解引入齐次自由度时的新鲜单位变量工厂。
 */
function unifyMonos(u1, u2, freshUVar) {
  const a = resolveMono(u1);
  const b = resolveMono(u2);
  if (monoEqual(a, b)) return;
  const av = bareVar(a);
  if (av) {
    if (occursUVar(av, b)) throw new UnifyError('occurs-unit', { v: av, u: b });
    av.instance = b;
    return;
  }
  const bv = bareVar(b);
  if (bv) {
    if (occursUVar(bv, a)) throw new UnifyError('occurs-unit', { v: bv, u: a });
    bv.instance = a;
    return;
  }
  // 方程 a * b^-1 = 1：先尝试单变量求解 v^e = R^-1（要求 R 的指数均可被 e 整除），
  // 成功时得到最简绑定（其余变量保持自由，即最一般合一子）。
  const eq = monoDiv(a, b);
  let best = null;
  for (const [v, e] of eq.vars) {
    if (best === null || Math.abs(e) < Math.abs(best.e)) best = { v, e };
  }
  if (best) {
    const { v, e } = best;
    const r = monoUnit();
    let solvable = true;
    for (const [bn, be] of eq.bases) {
      if (be % e !== 0) { solvable = false; break; }
      addBase(r, bn, -be / e);
    }
    if (solvable) {
      for (const [v2, e2] of eq.vars) {
        if (v2 === v) continue;
        if (e2 % e !== 0) { solvable = false; break; }
        addVar(r, v2, -e2 / e);
      }
    }
    if (solvable) {
      v.instance = r;
      return;
    }
  }
  // 单变量可除性失败不代表不可解：如 ux^2·uy^3 = m（gcd(2,3)=1 整除 m 的指数，
  // 整数解存在，如 ux=m^-1、uy=m）。改用一般整数求解（MGU），
  // 仅当变量指数的最大公约数不整除某基本单位指数时才真正不可解。
  const binds = solveUnitEquation(eq, freshUVar || freshUVarFallback);
  if (!binds) throw new UnifyError('unit-mismatch', { u1: a, u2: b });
  for (const [v, m] of binds) v.instance = m;
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
