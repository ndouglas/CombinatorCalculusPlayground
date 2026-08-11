// The {S,C} calculus. Mirrors SCStep / scSucc in
// CombinatorCalculusPlayground/Universality/SCDecidability.lean.
// Terms are nested two-element arrays; atoms are the strings 'S' and 'C'.

export const isApp = (t) => Array.isArray(t);

/** All one-step successors, in Lean's order: root, then appL, then appR. */
export function step(t) {
  const out = [];
  if (isApp(t) && isApp(t[0]) && isApp(t[0][0])) {
    const h = t[0][0][0], f = t[0][0][1], g = t[0][1], x = t[1];
    if (h === 'S') out.push([[f, x], [g, x]]);
    else if (h === 'C') out.push([[f, x], g]);
  }
  if (isApp(t)) {
    for (const f2 of step(t[0])) out.push([f2, t[1]]);
    for (const x2 of step(t[1])) out.push([t[0], x2]);
  }
  return out;
}

export function leaves(t) {
  let n = 0;
  const stack = [t];
  while (stack.length) {
    const x = stack.pop();
    if (isApp(x)) { stack.push(x[0], x[1]); } else { n++; }
  }
  return n;
}

export function eq(a, b) {
  if (isApp(a)) return isApp(b) && eq(a[0], b[0]) && eq(a[1], b[1]);
  return a === b;
}

/** In-order leaf sequence with bracket depth — the spatial axis of the spacetime figure. */
export function leafSeq(t) {
  const out = [];
  const stack = [[t, 0]];
  while (stack.length) {
    const [x, d] = stack.pop();
    if (isApp(x)) { stack.push([x[1], d + 1], [x[0], d + 1]); }
    else out.push({ atom: x, depth: d });
  }
  return out;
}

/**
 * Leftmost march. Always takes the first successor, so it works on branching
 * terms too; `branched` records whether a choice was ever available.
 */
export function march(t, maxFires, opts = {}) {
  const leafCap = opts.leafCap ?? 20000;
  const states = [t];
  let cur = t;
  let branched = false;
  for (let i = 0; i < maxFires; i++) {
    const r = step(cur);
    if (r.length === 0) return { states, fate: 'halt', branched };
    if (r.length > 1) branched = true;
    cur = r[0];
    if (leaves(cur) > leafCap) return { states, fate: 'capped', branched };
    states.push(cur);
  }
  return { states, fate: 'running', branched };
}

// --- surface syntax: left-associative application over atoms S and C ---

export function parse(s) {
  let i = 0;
  const skip = () => { while (i < s.length && s[i] === ' ') i++; };

  function atomOrGroup() {
    skip();
    if (i >= s.length) throw new SyntaxError(`unexpected end of input at ${i}`);
    const ch = s[i];
    if (ch === '(') {
      i++;
      const t = expr();
      skip();
      if (s[i] !== ')') throw new SyntaxError(`expected ')' at ${i}`);
      i++;
      return t;
    }
    if (ch === 'S' || ch === 'C') { i++; return ch; }
    throw new SyntaxError(`unexpected ${JSON.stringify(ch)} at ${i}`);
  }

  function expr() {
    let t = atomOrGroup();
    for (;;) {
      skip();
      if (i >= s.length || s[i] === ')') return t;
      t = [t, atomOrGroup()];
    }
  }

  const t = expr();
  skip();
  if (i !== s.length) throw new SyntaxError(`trailing input at ${i}`);
  return t;
}

export function show(t) {
  if (!isApp(t)) return t;
  const r = isApp(t[1]) ? `(${show(t[1])})` : show(t[1]);
  return `${show(t[0])} ${r}`;
}

// --- the mill family, transcribed from SCDecidability.lean ---

/** The nine-leaf core at the bottom of every tower (scMillK). */
export const millK = parse('C (S C) (S (C S (C C)) C)');

/** One tower layer (scMillL). */
export const millL = (x) => [['C', 'C'], ['C', x]];

/** The tower: m layers over the core (scMillT). */
export function millT(m) {
  let t = millK;
  for (let i = 0; i < m; i++) t = millL(t);
  return t;
}

/** The junk block: the core, C-parked, holding the climber's original tail (scMillB2). */
export const millB2 = [['C', millK], parse('S (C S (C C)) C')];

/** The two-counter state (scMillG). */
export const millG = (a, m) => [[millT(a), ['C', millT(a)]], millT(m)];

/** The peak inside each revolution: after the turnover, before the descent (scMillPeak). */
export const millPeak = (m) => [millG(m, m + 1), millB2];
