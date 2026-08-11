# The Clockmaker's Shop Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build and deploy a public GitHub Pages essay on `{S,C}` reduction carrying two live, in-browser figures: a cellular-automaton-style spacetime diagram, and a phase atlas whose empty upper-right quadrant is the subject.

**Architecture:** Five plain ES modules under `site/`. All computation is pure and lives in modules with no DOM access (`sc.js`, `sample.js`, and the `*Raster`/`*Points` halves of the two panel modules), so the entire substance of the page is testable under `node --test`. Only thin `draw*` functions touch a canvas. No build step, no dependencies, no framework.

**Tech Stack:** Vanilla ES modules, `<canvas>`, `node --test` (Node 18.20.2 present). Zero runtime dependencies, matching the repo's existing zero-dependency posture.

## Global Constraints

- **No dependencies.** No npm packages, no CDN links, no build step. The repo is deliberately dependency-free (no Mathlib, no Batteries); the site matches that.
- **Term representation:** nested two-element JS arrays; atoms are the strings `'S'` and `'C'`. `[a, b]` means application. Never classes, never objects.
- **Step order must mirror Lean's `SCStep`:** root redex first, then `appL` successors, then `appR`. Verified output for `C S S (C S S S) C` is exactly `['S (C S S S) S C', 'C S S (S S S) C']` in that order.
- **Surface syntax:** left-associative application, atoms `S`/`C`, parentheses. `C (S C C) S` is the notebook's style and the parser/printer must round-trip it.
- **Honesty tiers.** Every claim rendered on the page is tagged proved / probed / open. C14 is **open**. The page must never state or imply that `{S,C}` has been shown non-universal.
- **Sampled figures must show their seed** and label constructed data as constructed.
- **Pages deployment is not enabled by the implementer.** Task 6 writes the workflow; a human enables Pages.

---

### Task 1: The calculus in JavaScript

**Files:**
- Create: `site/sc.js`
- Test: `site/sc.test.mjs`

**Interfaces:**
- Consumes: nothing.
- Produces: `step(t) -> Term[]`, `leaves(t) -> number`, `eq(a,b) -> boolean`, `leafSeq(t) -> {atom,depth}[]`, `march(t, maxFires, opts) -> {states, fate, branched}`, `parse(s) -> Term`, `show(t) -> string`, and the mill constructors `millK`, `millL(x)`, `millT(m)`, `millG(a,m)`. `fate` is one of `'halt' | 'capped' | 'running'`.

- [ ] **Step 1: Write the failing test**

Create `site/sc.test.mjs`:

```js
import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  step, leaves, eq, leafSeq, march, parse, show,
  millK, millL, millT, millG,
} from './sc.js';

const climber = parse('C S S (S S) C (S (C S (C C)) C)');

test('parse and show round-trip the notebook syntax', () => {
  for (const s of ['S', 'C', 'C S S', 'C (S C C) S', 'C S S (S S) C (S (C S (C C)) C)']) {
    assert.equal(show(parse(s)), s);
  }
});

test('parse rejects malformed input with a position', () => {
  assert.throws(() => parse('C ('), { name: 'SyntaxError' });
  assert.throws(() => parse('C K'), { name: 'SyntaxError' });
  assert.throws(() => parse('C S)'), { name: 'SyntaxError' });
});

test('S and C fire per the Lean rules', () => {
  assert.equal(show(step(parse('S C S C'))[0]), 'C C (S C)');
  assert.equal(show(step(parse('C C S C'))[0]), 'C C S');
  assert.equal(step(parse('S')).length, 0);
  assert.equal(step(parse('S C')).length, 0);
});

test('step order is root, then appL, then appR', () => {
  const succ = step(parse('C S S (C S S S) C')).map(show);
  assert.deepEqual(succ, ['S (C S S S) S C', 'C S S (S S S) C']);
});

test('the climber has twelve leaves and is forced for 400 fires', () => {
  assert.equal(leaves(climber), 12);
  const m = march(climber, 400);
  assert.equal(m.fate, 'running');
  assert.equal(m.branched, false);
  assert.equal(m.states.length, 401);
});

test('the climber stays forced far past the Lean guard', () => {
  const m = march(climber, 2000);
  assert.equal(m.branched, false);
  assert.equal(leaves(m.states[2000]), 624);
});

test('mill towers weigh 9 + 3m', () => {
  assert.equal(leaves(millK), 9);
  for (let m = 0; m < 5; m++) assert.equal(leaves(millT(m)), 9 + 3 * m);
});

test('sc_mill_descent: six fires strip one layer, any payloads', () => {
  for (const [x, y] of [[millT(2), millK], [millT(0), parse('S C')], [parse('C C'), millT(1)]]) {
    const lhs = [[millL(x), ['C', millL(x)]], y];
    const m = march(lhs, 6);
    assert.ok(eq(m.states[6], [[x, ['C', x]], y]));
  }
});

test('millG(a,m) reaches millG(0,m) in exactly 6a fires', () => {
  for (const [a, m] of [[1, 2], [2, 3], [3, 1], [4, 5]]) {
    const run = march(millG(a, m), 6 * a);
    assert.ok(eq(run.states[6 * a], millG(0, m)));
    assert.ok(!eq(run.states[6 * a - 1], millG(0, m)), 'must not arrive early');
  }
});

test('leafSeq reads leaves left to right with bracket depth', () => {
  assert.deepEqual(leafSeq(parse('C S')), [
    { atom: 'C', depth: 1 }, { atom: 'S', depth: 1 },
  ]);
  assert.deepEqual(leafSeq(parse('C (S C)')).map(l => l.atom), ['C', 'S', 'C']);
  assert.deepEqual(leafSeq(parse('C (S C)')).map(l => l.depth), [1, 2, 2]);
  assert.equal(leafSeq(climber).length, 12);
});

test('march halts on a normal form and caps on runaway growth', () => {
  assert.equal(march(parse('S C'), 10).fate, 'halt');
  assert.equal(march(climber, 2000, { leafCap: 100 }).fate, 'capped');
});
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `node --test site/sc.test.mjs`
Expected: FAIL — `Cannot find module './sc.js'`.

- [ ] **Step 3: Write the implementation**

Create `site/sc.js`:

```js
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
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `node --test site/sc.test.mjs`
Expected: PASS, 11 tests.

If `millK` fails the 9-leaf assertion, the transcription of `scMillK` is wrong — re-read `SCDecidability.lean:6160`. The Lean is `.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)`, which is `C (S C) (S (C S (C C)) C)` in surface syntax.

- [ ] **Step 5: Commit**

```bash
git add site/sc.js site/sc.test.mjs
git commit -m "feat(site): the {S,C} calculus in JavaScript, checked against Lean

Ports SCStep/scSucc and the mill family. The test suite re-checks
sc_mill_descent directly -- six fires, exact term equality, arbitrary
payloads -- so the page's engine is validated against the proofs rather
than being an unaudited parallel implementation."
```

---

### Task 2: The sampler, and the thesis as a test

**Files:**
- Create: `site/sample.js`
- Test: `site/sample.test.mjs`

**Interfaces:**
- Consumes: `step`, `leaves`, `march` from `./sc.js`.
- Produces: `mulberry32(seed) -> () => number`, `randomTerm(n, rnd) -> Term`, `screenKind(t, opts) -> 'halt'|'branch'|'corridor'`, `coords(t, opts) -> {width, drop, peak, kind}`, `sampleBatch(rnd, count, opts) -> Sample[]` where `Sample` is `{term, phase, width, drop, peak}`, and the constants `QUADRANT_WIDTH = 2`, `QUADRANT_DROP = 40`.

Two independent measurements per term, and they must not be conflated. `screenKind` asks *does this term ever branch* and reproduces the census (67/33/0.2). `coords` asks *what does a leftmost march look like* and gives the atlas position. Under a leftmost march ~96% of terms normalize, so `coords` does **not** reproduce the census split and must never be used for it.

- [ ] **Step 1: Write the failing test**

Create `site/sample.test.mjs`:

```js
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { leaves, parse } from './sc.js';
import {
  mulberry32, randomTerm, screenKind, coords, sampleBatch,
  QUADRANT_WIDTH, QUADRANT_DROP,
} from './sample.js';

test('mulberry32 is deterministic and in range', () => {
  const a = mulberry32(12345), b = mulberry32(12345);
  for (let i = 0; i < 100; i++) {
    const x = a();
    assert.equal(x, b());
    assert.ok(x >= 0 && x < 1);
  }
  assert.notEqual(mulberry32(1)(), mulberry32(2)());
});

test('randomTerm produces terms of exactly the requested size', () => {
  const rnd = mulberry32(7);
  for (let i = 0; i < 200; i++) assert.equal(leaves(randomTerm(10, rnd)), 10);
  assert.equal(leaves(randomTerm(1, rnd)), 1);
});

test('screenKind classifies the known specimens', () => {
  assert.equal(screenKind(parse('S C')), 'halt');
  assert.equal(screenKind(parse('C S S (S S) C (S (C S (C C)) C)')), 'corridor');
});

test('the sampler reproduces the Stage 241 census', () => {
  const rnd = mulberry32(20260810);
  const batch = sampleBatch(rnd, 2000, { size: 10 });
  const frac = (k) => batch.filter((s) => s.phase === k).length / batch.length;

  assert.ok(frac('halt') > 0.60 && frac('halt') < 0.73, `halt ${frac('halt')}`);
  assert.ok(frac('branch') > 0.27 && frac('branch') < 0.39, `branch ${frac('branch')}`);
  const corridors = batch.filter((s) => s.phase === 'corridor').length;
  assert.ok(corridors >= 1 && corridors <= 12, `corridors ${corridors}`);
});

test('THE THESIS: the branching-and-descending quadrant is empty', () => {
  const rnd = mulberry32(20260810);
  const batch = sampleBatch(rnd, 2000, { size: 10 });
  const inQuadrant = batch.filter(
    (s) => s.width >= QUADRANT_WIDTH && s.drop >= QUADRANT_DROP,
  );
  assert.deepEqual(inQuadrant, [],
    'A term that both branches and descends deeply would falsify the essay. ' +
    'If this fires, do not "fix" the test -- the page is now making a false ' +
    'claim and the prose must change.');
});

test('the two arms of the atlas are separated as the essay describes', () => {
  const rnd = mulberry32(20260810);
  const batch = sampleBatch(rnd, 2000, { size: 10 });
  const branchy = batch.filter((s) => s.width >= 2);
  const deep = batch.filter((s) => s.drop >= QUADRANT_DROP);
  assert.ok(branchy.length > 0, 'expected some branchy survivors');
  assert.ok(Math.max(...branchy.map((s) => s.width)) > 100, 'branchy arm should reach high width');
  assert.ok(Math.max(...branchy.map((s) => s.drop)) < QUADRANT_DROP, 'branchy arm must stay shallow');
  for (const s of deep) assert.equal(s.width, 1, 'deep descenders must be width 1');
});

test('coords caps runaway growth instead of chasing it', () => {
  const c = coords(parse('C S S (S S) C (S (C S (C C)) C)'), { leafCap: 60 });
  assert.equal(c.kind, 'big');
});
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `node --test site/sample.test.mjs`
Expected: FAIL — `Cannot find module './sample.js'`.

- [ ] **Step 3: Write the implementation**

Create `site/sample.js`:

```js
// Sampling and classification. Pure — no DOM, no canvas — so the atlas's
// entire claim is testable under `node --test`.

import { step, leaves } from './sc.js';

export const SCREEN_FIRES = 30;
export const DEEP_FIRES = 300;
export const LEAF_CAP = 20000;
export const LATE_WINDOW = 50;

/** The quadrant a universal computer would have to live in. */
export const QUADRANT_WIDTH = 2;
export const QUADRANT_DROP = 40;

export function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export function randomTerm(n, rnd) {
  if (n === 1) return rnd() < 0.5 ? 'S' : 'C';
  const k = 1 + Math.floor(rnd() * (n - 1));
  return [randomTerm(k, rnd), randomTerm(n - k, rnd)];
}

/**
 * The census measurement: does this term ever branch?
 * Cheap forcedness screen, then a deep march for survivors.
 */
export function screenKind(t, opts = {}) {
  const screen = opts.screen ?? SCREEN_FIRES;
  const deep = opts.deep ?? DEEP_FIRES;
  let cur = t;
  for (let i = 0; i < screen + deep; i++) {
    const r = step(cur);
    if (r.length === 0) return 'halt';
    if (r.length > 1) return 'branch';
    cur = r[0];
    if (leaves(cur) > (opts.leafCap ?? LEAF_CAP)) return 'corridor';
  }
  return 'corridor';
}

function medianLate(widths, k) {
  const tail = widths.slice(-k).sort((a, b) => a - b);
  return tail.length ? tail[Math.floor(tail.length / 2)] : 0;
}

/** The geometry measurement: what does a leftmost march look like? */
export function coords(t, opts = {}) {
  const horizon = opts.horizon ?? DEEP_FIRES;
  const leafCap = opts.leafCap ?? LEAF_CAP;
  let cur = t;
  let hi = leaves(cur);
  let maxDrop = 0;
  const widths = [];
  for (let i = 0; i < horizon; i++) {
    const r = step(cur);
    if (r.length === 0) return { width: 0, drop: maxDrop, peak: hi, kind: 'halt' };
    widths.push(r.length);
    cur = r[0];
    const n = leaves(cur);
    if (n > hi) hi = n;
    if (hi - n > maxDrop) maxDrop = hi - n;
    if (n > leafCap) {
      return { width: medianLate(widths, LATE_WINDOW), drop: maxDrop, peak: hi, kind: 'big' };
    }
  }
  const w = medianLate(widths, opts.lateWindow ?? LATE_WINDOW);
  return { width: w, drop: maxDrop, peak: hi, kind: w === 1 ? 'line' : 'tree' };
}

/** One sample carries both measurements: phase from the screen, position from the march. */
export function sampleBatch(rnd, count, opts = {}) {
  const size = opts.size ?? 10;
  const out = [];
  for (let i = 0; i < count; i++) {
    const term = randomTerm(size, rnd);
    const c = coords(term, opts);
    out.push({ term, phase: screenKind(term, opts), width: c.width, drop: c.drop, peak: c.peak });
  }
  return out;
}
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `node --test site/sample.test.mjs`
Expected: PASS, 7 tests.

The census test is the one that may need its tolerance widened — the reference Python run at 4,000 terms gave 67.2 / 32.6 / 0.20 against Stage 241's recorded 67 / 33 / 0.15, but a different PRNG will land somewhere nearby, not identically. **Widen the band only if the observed value is close to the recorded census.** If it is far off, the port is wrong, not the tolerance.

- [ ] **Step 5: Commit**

```bash
git add site/sample.js site/sample.test.mjs
git commit -m "feat(site): sampler, with the essay's thesis as an executable test

Two independent measurements per term: screenKind reproduces the Stage 241
census (67/33/0.2), coords gives the atlas geometry. Conflating them would
be wrong -- a leftmost march normalizes ~96% of terms and does not see the
census split.

The empty-quadrant test asserts the essay's central claim. If a term is
ever found that both branches and descends deeply, the suite fails loudly
rather than the page quietly continuing to claim otherwise."
```

---

### Task 3: The spacetime figure

**Files:**
- Create: `site/spacetime.js`
- Test: `site/spacetime.test.mjs`

**Interfaces:**
- Consumes: `march`, `leafSeq`, `leaves` from `./sc.js`.
- Produces: `spacetimeRaster(term, opts) -> {width, height, pixels}` where `pixels` is a `Uint8ClampedArray` of RGBA, and `drawSpacetime(canvas, raster)`. `opts` is `{fires, mode, leafCap, theme}` with `mode` in `'atom' | 'depth'`.

The raster function is pure and returns pixels, so the figure's geometry is tested without a DOM. Only `drawSpacetime` touches a canvas, and it is deliberately trivial.

- [ ] **Step 1: Write the failing test**

Create `site/spacetime.test.mjs`:

```js
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parse, leafSeq, march } from './sc.js';
import { spacetimeRaster } from './spacetime.js';

const climber = parse('C S S (S S) C (S (C S (C C)) C)');
const px = (r, x, y) => {
  const i = (y * r.width + x) * 4;
  return [r.pixels[i], r.pixels[i + 1], r.pixels[i + 2], r.pixels[i + 3]];
};

test('raster is one column per fire, as tall as the largest term', () => {
  const r = spacetimeRaster(climber, { fires: 100, mode: 'atom' });
  const run = march(climber, 100);
  assert.equal(r.width, run.states.length);
  assert.equal(r.height, Math.max(...run.states.map((s) => leafSeq(s).length)));
  assert.equal(r.pixels.length, r.width * r.height * 4);
});

test('rows are tail-anchored so emitted junk keeps its position', () => {
  const r = spacetimeRaster(climber, { fires: 100, mode: 'atom' });
  // The first state has 12 leaves, so in column 0 everything above
  // height-12 is background (alpha 0) and the last 12 rows are painted.
  assert.equal(px(r, 0, r.height - 1)[3], 255);
  assert.equal(px(r, 0, r.height - 13)[3], 0);
  assert.equal(px(r, 0, r.height - 12)[3], 255);
});

test('atom mode paints S and C in distinct colours', () => {
  const r = spacetimeRaster(parse('S C'), { fires: 0, mode: 'atom' });
  assert.equal(r.width, 1);
  assert.equal(r.height, 2);
  const s = px(r, 0, 0), c = px(r, 0, 1);
  assert.notDeepEqual(s, c);
  assert.equal(s[3], 255);
  assert.equal(c[3], 255);
});

test('depth mode is independent of the atom', () => {
  const a = spacetimeRaster(parse('S C'), { fires: 0, mode: 'depth' });
  const b = spacetimeRaster(parse('C S'), { fires: 0, mode: 'depth' });
  assert.deepEqual(Array.from(a.pixels), Array.from(b.pixels));
});

test('the leaf cap bounds the raster for a runaway term', () => {
  const r = spacetimeRaster(climber, { fires: 2000, mode: 'atom', leafCap: 200 });
  assert.ok(r.height <= 200);
});
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `node --test site/spacetime.test.mjs`
Expected: FAIL — `Cannot find module './spacetime.js'`.

- [ ] **Step 3: Write the implementation**

Create `site/spacetime.js`:

```js
// The spacetime figure: x = fire number, y = position in the leaf string,
// anchored to the tail so emitted junk keeps its place and reads as the
// frozen field that sc_swap_revolution proves it to be.

import { march, leafSeq } from './sc.js';

const S_COLOUR = [255, 196, 64];
const C_COLOUR = [72, 160, 255];

const VIRIDIS = [[68, 1, 84], [59, 82, 139], [33, 145, 140], [94, 201, 98], [253, 231, 37]];

function ramp(u) {
  const x = Math.max(0, Math.min(1, u)) * (VIRIDIS.length - 1);
  const i = Math.floor(x);
  if (i >= VIRIDIS.length - 1) return VIRIDIS[VIRIDIS.length - 1];
  const f = x - i, a = VIRIDIS[i], b = VIRIDIS[i + 1];
  return [0, 1, 2].map((k) => Math.round(a[k] + (b[k] - a[k]) * f));
}

export function spacetimeRaster(term, opts = {}) {
  const fires = opts.fires ?? 520;
  const mode = opts.mode ?? 'atom';
  const { states } = march(term, fires, { leafCap: opts.leafCap ?? 20000 });

  const rows = states.map(leafSeq);
  const width = rows.length;
  const height = rows.reduce((m, r) => Math.max(m, r.length), 0);
  const maxDepth = rows.reduce((m, r) => r.reduce((n, l) => Math.max(n, l.depth), m), 1);

  const pixels = new Uint8ClampedArray(width * height * 4);
  for (let x = 0; x < width; x++) {
    const row = rows[x];
    const offset = height - row.length; // tail-anchored
    for (let j = 0; j < row.length; j++) {
      const leaf = row[j];
      const [r, g, b] = mode === 'depth'
        ? ramp(leaf.depth / maxDepth)
        : (leaf.atom === 'S' ? S_COLOUR : C_COLOUR);
      const i = ((j + offset) * width + x) * 4;
      pixels[i] = r; pixels[i + 1] = g; pixels[i + 2] = b; pixels[i + 3] = 255;
    }
  }
  return { width, height, pixels };
}

/** The only part that touches a canvas. Nearest-neighbour, never smoothed. */
export function drawSpacetime(canvas, raster) {
  const src = document.createElement('canvas');
  src.width = raster.width;
  src.height = raster.height;
  src.getContext('2d').putImageData(
    new ImageData(raster.pixels, raster.width, raster.height), 0, 0,
  );

  const ctx = canvas.getContext('2d');
  ctx.imageSmoothingEnabled = false;
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.drawImage(src, 0, 0, canvas.width, canvas.height);
}
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `node --test site/spacetime.test.mjs`
Expected: PASS, 5 tests.

- [ ] **Step 5: Commit**

```bash
git add site/spacetime.js site/spacetime.test.mjs
git commit -m "feat(site): tail-anchored spacetime raster

Pure raster function returning RGBA, so the figure's geometry is tested
without a DOM; only drawSpacetime touches a canvas.

Tail-anchoring is the point: head-anchoring smears the static tail into
diagonals because every insertion shifts later positions, misrepresenting
what is actually frozen."
```

---

### Task 4: The phase atlas

**Files:**
- Create: `site/specimens.js`
- Create: `site/atlas.js`
- Test: `site/atlas.test.mjs`

**Interfaces:**
- Consumes: `parse` from `./sc.js`; `sampleBatch`, `mulberry32`, `coords`, `QUADRANT_WIDTH`, `QUADRANT_DROP` from `./sample.js`.
- Produces: from `specimens.js`, `FOUND_CORRIDORS` (array of `{drop, source}`), `CLIMBER` (string), `SPECIMENS` (array of `{label, source, fires}`); from `atlas.js`, `KNOWN_CORRIDORS` (array of `{name, source}`), `knownCorridorPoints(opts) -> Point[]`, `project(point, box) -> {x, y}`, `drawAtlas(canvas, points, opts)`, and `runAtlas(canvas, opts) -> {stop()}`. `Point` is `{width, drop, phase, constructed, name?}`.

**Why the corridors are hard-coded.** Every specimen here was verified before being
written down. The mill components (`millK`, `millT m`) are **normal forms on their
own** — they only run when assembled through `millG`, so they are useless as menu
entries. And the climber, `millPeak 1..3`, and the climber advanced 44 fires all
report the identical drop of 121, because they are all on the *same road*: the mill
is reached from the climber. Plotting them would put four markers in one spot. The
fourteen corridors below were found by search over ~37,000 random terms at 8–12
leaves, one per distinct maximum drop, and they give the arm a real vertical spread.

- [ ] **Step 1: Write the failing test**

Create `site/atlas.test.mjs`:

```js
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { KNOWN_CORRIDORS, knownCorridorPoints, project } from './atlas.js';
import { QUADRANT_WIDTH, QUADRANT_DROP, coords } from './sample.js';
import { FOUND_CORRIDORS, SPECIMENS, CLIMBER } from './specimens.js';
import { parse, leaves, march } from './sc.js';

test('the constructed corridors are all genuinely corridors', () => {
  assert.ok(KNOWN_CORRIDORS.length >= 3);
  for (const p of knownCorridorPoints()) {
    assert.equal(p.constructed, true);
    assert.equal(p.width, 1, `${p.name} should be forced`);
    assert.ok(p.name, 'constructed points must be named on the figure');
  }
});

test('every recorded corridor drop matches what the engine computes', () => {
  for (const c of FOUND_CORRIDORS) {
    assert.equal(coords(parse(c.source), { horizon: 1200 }).drop, c.drop, c.source);
  }
});

test('the corridor arm has real vertical spread, not one repeated point', () => {
  const drops = new Set(knownCorridorPoints().map((p) => p.drop));
  assert.ok(drops.size >= 10, `expected a spread of drops, got ${drops.size} distinct`);
});

test('the menu specimens do what their labels claim', () => {
  const byLabel = (s) => SPECIMENS.find((x) => x.label.includes(s));
  assert.equal(leaves(parse(CLIMBER)), 12);
  assert.equal(march(parse(byLabel('normalizer').source), 200).fate, 'halt');
  assert.equal(march(parse(byLabel('storm').source), 200, { leafCap: 1200 }).fate, 'capped');
  assert.equal(march(parse(CLIMBER), 900).fate, 'running');
});

test('constructed corridors reach the deep-descent arm', () => {
  const drops = knownCorridorPoints().map((p) => p.drop);
  assert.ok(Math.max(...drops) >= QUADRANT_DROP,
    'the corridor arm must actually be populated, else the figure has one axis');
});

test('constructed corridors are outside the quadrant, like everything else', () => {
  for (const p of knownCorridorPoints()) {
    assert.ok(!(p.width >= QUADRANT_WIDTH && p.drop >= QUADRANT_DROP));
  }
});

test('project maps log-width and linear-drop into the box', () => {
  const box = { x: 0, y: 0, w: 100, h: 100, maxWidth: 1000, maxDrop: 250 };
  const lo = project({ width: 1, drop: 0 }, box);
  const hi = project({ width: 1000, drop: 250 }, box);
  assert.equal(lo.x, 0);
  assert.equal(lo.y, 100);   // drop 0 at the bottom
  assert.equal(hi.x, 100);
  assert.equal(hi.y, 0);     // max drop at the top
  const mid = project({ width: 1000 ** 0.5, drop: 125 }, box);
  assert.ok(Math.abs(mid.x - 50) < 0.001, 'width axis must be logarithmic');
  assert.ok(Math.abs(mid.y - 50) < 0.001);
});

test('width 0 (normalizers) projects onto the left edge, not off it', () => {
  const box = { x: 0, y: 0, w: 100, h: 100, maxWidth: 1000, maxDrop: 250 };
  const p = project({ width: 0, drop: 0 }, box);
  assert.ok(p.x >= 0 && p.x <= 100);
});
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `node --test site/atlas.test.mjs`
Expected: FAIL — `Cannot find module './atlas.js'`.

- [ ] **Step 3: Write the specimens**

Create `site/specimens.js`. Every entry below was verified against the engine; the
recorded `drop` values are re-checked by the test above, so a bad transcription
fails the suite rather than quietly mislabelling the figure.

```js
// Verified specimens. The corridors were found by search over ~37,000 random
// terms at 8-12 leaves, one per distinct maximum drop, because uniform sampling
// inside the page would essentially never turn up a deep one.

/** The 12-leaf climber, scMt5T. */
export const CLIMBER = 'C S S (S S) C (S (C S (C C)) C)';

/** Corridors found by offline search. `drop` is measured at horizon 1200. */
export const FOUND_CORRIDORS = [
  { drop: 0,  source: 'S (S (S C)) (S (S C)) (S S)' },
  { drop: 1,  source: 'S (C S) (S S) S (C (S C))' },
  { drop: 3,  source: 'S (S S S) C (C S C) S' },
  { drop: 4,  source: 'C (S S S) (S (C S S) C (S C C))' },
  { drop: 6,  source: 'S (C S) (S C) S (C (C C (S (C C))))' },
  { drop: 7,  source: 'S (C C) C (C S (C C)) (S S C)' },
  { drop: 8,  source: 'C S (C S) (S (C S (C C))) C' },
  { drop: 9,  source: 'S S S (C S C) (C C) (S C (S C))' },
  { drop: 29, source: 'S (S C) (S C) (C (C (C C))) (S S C)' },
  { drop: 33, source: 'S C S C (S (C S)) (S (S C)) C' },
  { drop: 34, source: 'S S C (C S C) (S C C)' },
  { drop: 35, source: 'S (S (C (C (S S)) C)) (S C) C' },
  { drop: 64, source: 'S C C (S (S (C S C) C)) (S C)' },
  { drop: 66, source: 'S (S C C) C (S (S C C) (C (C C)))' },
];

/** The spacetime figure's menu. `fires` is tuned per specimen. */
export const SPECIMENS = [
  { label: 'the climber — 12 leaves, forced forever', source: CLIMBER, fires: 520 },
  { label: 'a deep corridor — drop 66', source: 'S (S C C) C (S (S C C) (C (C C)))', fires: 520 },
  { label: 'a storm — explodes, hits the render cap at fire 62', source: 'S (S (S C C) (S S)) (C S) S', fires: 120 },
  { label: 'a normalizer — halts at fire 111', source: 'C (S S S (S S S) (C C) C)', fires: 140 },
];
```

- [ ] **Step 4: Write the atlas**

Create `site/atlas.js`:

```js
// The phase atlas. Position from `coords` (leftmost-march geometry),
// colour from `screenKind` (census phase). The upper-right region is the
// subject of the figure, so it is drawn and labelled, not left as absence.

import { parse } from './sc.js';
import {
  sampleBatch, mulberry32, coords, QUADRANT_WIDTH, QUADRANT_DROP,
} from './sample.js';
import { FOUND_CORRIDORS, CLIMBER } from './specimens.js';

/**
 * Constructed, not sampled. Uniform sampling at n=10 yields ~2 corridors per
 * 1,000 terms and almost none with the deep drops that define the corridor
 * arm, so the arm is populated deliberately and labelled as such.
 */
export const KNOWN_CORRIDORS = [
  { name: 'the climber (scMt5T)', source: CLIMBER },
  ...FOUND_CORRIDORS.map((c) => ({ name: `found corridor, drop ${c.drop}`, source: c.source })),
];

export function knownCorridorPoints(opts = {}) {
  return KNOWN_CORRIDORS.map(({ name, source }) => {
    const c = coords(parse(source), { horizon: opts.horizon ?? 1200, ...opts });
    return { name, width: c.width, drop: c.drop, phase: 'corridor', constructed: true };
  });
}

export function project(p, box) {
  const w = Math.max(1, p.width);
  const lx = Math.log(w) / Math.log(box.maxWidth);
  const ly = p.drop / box.maxDrop;
  return {
    x: box.x + Math.max(0, Math.min(1, lx)) * box.w,
    y: box.y + box.h - Math.max(0, Math.min(1, ly)) * box.h,
  };
}

const PHASE_COLOUR = {
  halt: 'rgba(140,150,170,0.45)',
  branch: 'rgba(72,160,255,0.55)',
  corridor: 'rgba(255,196,64,0.95)',
};

export function drawAtlas(canvas, points, opts = {}) {
  const ctx = canvas.getContext('2d');
  const pad = 48;
  const box = {
    x: pad, y: pad,
    w: canvas.width - pad * 2,
    h: canvas.height - pad * 2,
    maxWidth: opts.maxWidth ?? 1000,
    maxDrop: opts.maxDrop ?? 250,
  };

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  // The empty quadrant, drawn because it is the subject.
  const q = project({ width: QUADRANT_WIDTH, drop: box.maxDrop }, box);
  const qb = project({ width: QUADRANT_WIDTH, drop: QUADRANT_DROP }, box);
  ctx.fillStyle = 'rgba(255,80,80,0.07)';
  ctx.fillRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.strokeStyle = 'rgba(255,80,80,0.45)';
  ctx.setLineDash([4, 4]);
  ctx.strokeRect(q.x, q.y, box.x + box.w - q.x, qb.y - q.y);
  ctx.setLineDash([]);

  for (const p of points) {
    const { x, y } = project(p, box);
    if (p.constructed) {
      ctx.strokeStyle = PHASE_COLOUR.corridor;
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      ctx.moveTo(x - 4, y); ctx.lineTo(x + 4, y);
      ctx.moveTo(x, y - 4); ctx.lineTo(x, y + 4);
      ctx.stroke();
    } else {
      ctx.fillStyle = PHASE_COLOUR[p.phase] ?? PHASE_COLOUR.halt;
      ctx.fillRect(x - 1, y - 1, 2, 2);
    }
  }
  return box;
}

/**
 * Progressive sampling under a frame budget, so the page stays responsive and
 * the reader watches the quadrant stay empty rather than being told it is.
 */
export function runAtlas(canvas, opts = {}) {
  const seed = opts.seed ?? 20260810;
  const total = opts.total ?? 4000;
  const budgetMs = opts.budgetMs ?? 12;
  const rnd = mulberry32(seed);
  const points = knownCorridorPoints();
  let done = 0;
  let stopped = false;

  function tick() {
    if (stopped || done >= total) return;
    const start = Date.now();
    while (Date.now() - start < budgetMs && done < total) {
      const batch = sampleBatch(rnd, 25, { size: opts.size ?? 10 });
      for (const s of batch) {
        points.push({ width: s.width, drop: s.drop, phase: s.phase, constructed: false });
      }
      done += batch.length;
    }
    drawAtlas(canvas, points, opts);
    opts.onProgress?.(done, total, points);
    requestAnimationFrame(tick);
  }

  requestAnimationFrame(tick);
  return { stop() { stopped = true; } };
}
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `node --test site/atlas.test.mjs`
Expected: PASS, 8 tests.

If "constructed corridors reach the deep-descent arm" fails, the horizon is too short. Measured maxima: the climber drops 121, and the deepest found corridor drops 66 — both clear the threshold of 40 at horizon 1200, but a short horizon will not reach them.

- [ ] **Step 6: Commit**

```bash
git add site/specimens.js site/atlas.js site/atlas.test.mjs
git commit -m "feat(site): the phase atlas, with the empty quadrant drawn

Position from leftmost-march geometry, colour from census phase. The
corridor arm is populated by fourteen corridors found by offline search,
one per distinct drop, because uniform sampling yields ~2 corridors per
1,000 terms and essentially no deep ones. They carry a distinct glyph and
are labelled constructed.

Not used: the mill components are normal forms on their own, and the
climber, millPeak 1-3 and the climber-at-44-fires all sit at drop 121
because they are all on the same road -- four markers in one spot."
```

---

### Task 5: The essay

**Files:**
- Create: `site/index.html`
- Create: `site/style.css`
- Create: `site/main.js`

**Interfaces:**
- Consumes: `parse`, `show`, `leaves` from `./sc.js`; `spacetimeRaster`, `drawSpacetime` from `./spacetime.js`; `runAtlas` from `./atlas.js`; `SPECIMENS` from `./specimens.js`.
- Produces: the page. Nothing imports it.

This task has no unit test — it is markup and wiring over modules already tested. It ends with a manual verification step instead.

- [ ] **Step 1: Write the stylesheet**

Create `site/style.css`:

```css
:root {
  --bg: #fbfaf8;
  --fg: #1a1c20;
  --muted: #5c626e;
  --rule: #dcd8d0;
  --panel: #ffffff;
  --accent: #b45309;
  --proved: #166534;
  --probed: #92400e;
  --open: #9f1239;
}

@media (prefers-color-scheme: dark) {
  :root {
    --bg: #0e1014;
    --fg: #e8e6e3;
    --muted: #9aa1ad;
    --rule: #262b33;
    --panel: #14171d;
    --accent: #fbbf24;
    --proved: #4ade80;
    --probed: #fbbf24;
    --open: #fb7185;
  }
}

* { box-sizing: border-box; }

body {
  margin: 0;
  background: var(--bg);
  color: var(--fg);
  font: 17px/1.65 Georgia, 'Iowan Old Style', 'Times New Roman', serif;
}

main { max-width: 44rem; margin: 0 auto; padding: 4rem 1.25rem 6rem; }

h1 { font-size: 2.1rem; line-height: 1.15; margin: 0 0 .4rem; letter-spacing: -.01em; }
h2 { font-size: 1.35rem; margin: 3rem 0 .75rem; letter-spacing: -.005em; }
.standfirst { color: var(--muted); font-size: 1.1rem; margin: 0 0 3rem; }

code, .mono {
  font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  font-size: .88em;
}

figure {
  margin: 2.5rem 0;
  padding: 1rem;
  background: var(--panel);
  border: 1px solid var(--rule);
  border-radius: 6px;
}
figure .scroll { overflow-x: auto; }
canvas { display: block; width: 100%; height: auto; image-rendering: pixelated; }
figcaption { color: var(--muted); font-size: .9rem; margin-top: .85rem; }

.controls {
  display: flex; flex-wrap: wrap; gap: .6rem; align-items: center;
  margin-bottom: .9rem; font-family: ui-monospace, Menlo, monospace; font-size: .82rem;
}
.controls select, .controls input, .controls button {
  font: inherit; padding: .3rem .5rem;
  background: var(--bg); color: var(--fg);
  border: 1px solid var(--rule); border-radius: 4px;
}
.controls input[type=text] { flex: 1 1 16rem; min-width: 0; }
.controls button { cursor: pointer; }
#parse-error { color: var(--open); font-size: .82rem; min-height: 1.2em; }

.tiers { border: 1px solid var(--rule); border-radius: 6px; padding: 1.25rem 1.5rem; margin: 3rem 0 0; }
.tiers dt { font-weight: bold; margin-top: .9rem; }
.tiers dt:first-child { margin-top: 0; }
.tiers dd { margin: .2rem 0 0; color: var(--muted); }
.tier-proved { color: var(--proved); }
.tier-probed { color: var(--probed); }
.tier-open { color: var(--open); }

.noscript { padding: 1rem; border: 1px dashed var(--rule); color: var(--muted); }
```

- [ ] **Step 2: Write the page**

Create `site/index.html`. The prose below is the deliverable — do not paraphrase it, and do not add claims to it.

```html
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>The Clockmaker's Shop — what {S,C} reduction actually looks like</title>
<link rel="stylesheet" href="./style.css">
</head>
<body>
<main>

<h1>The Clockmaker's Shop</h1>
<p class="standfirst">
  What <code>{S,C}</code> reduction actually looks like — and why the interesting
  question moved somewhere with nothing to look at.
</p>

<p>
  Take two combinators. <code>S f g x</code> reduces to <code>(f x) (g x)</code>;
  <code>C f g x</code> reduces to <code>(f x) g</code>. That is the whole system.
  Below is a single term of twelve leaves, reduced for several hundred steps. Each
  column is one reduction; the vertical axis is position in the term's leaf string,
  anchored at the tail so that anything the term emits keeps its place.
</p>

<figure>
  <div class="controls">
    <label>term <select id="term-pick"><!-- populated from specimens.js --></select></label>
    <label>colour
      <select id="mode-pick">
        <option value="atom">atom (S gold / C blue)</option>
        <option value="depth">bracket depth</option>
      </select>
    </label>
    <label>fires <input id="fires" type="range" min="40" max="900" value="520"></label>
    <input id="term-text" type="text" spellcheck="false" aria-label="your own term">
    <button id="term-go">run</button>
  </div>
  <div id="parse-error" role="status"></div>
  <div class="scroll"><canvas id="spacetime" width="1040" height="700"></canvas></div>
  <noscript><p class="noscript">This figure is computed in your browser and needs JavaScript.</p></noscript>
  <figcaption id="spacetime-caption"></figcaption>
</figure>

<p>
  It is hard not to read that as a cellular automaton. There are periodic engines,
  a travelling structure, and debris shed behind it. The comb of triangles is a
  real engine running a real cycle: the mill strips one tower layer every six
  fires, and each revolution is longer than the last, so the teeth widen as you go
  right. That much is not an impression — <code>sc_mill_descent</code> is a
  theorem, and the page you are reading re-checks it: six fires, exact term
  equality, arbitrary payloads.
</p>

<p>
  The solid band along the bottom is the interesting part. Those are emitted
  blocks, and they never change again. Not "appear not to" — the swapmill's full
  revolution has been certified under an arbitrary rider stack
  (<code>sc_swap_revolution</code>): the junk is emitted, the stack underneath is
  untouched, the engine walks on. One of those blocks turns out to be a parked copy
  of the machine's own driver.
</p>

<h2>Scenery is not physics</h2>

<p>
  So the calculus has particles, periodic structures, and emitted debris — the
  visual vocabulary of a Class 4 automaton. What it does not have is the thing that
  makes that vocabulary matter. In Rule 110, gliders <em>collide</em>: two
  structures meet, interact, and leave a third thing behind, and that is the entire
  mechanism by which a cellular automaton computes. Here nothing collides. The
  debris is provably inert and the engine is provably deterministic, so the
  structures pass each other and nothing happens. It is a shop full of clocks.
</p>

<p>
  Where could a computer be, then? It would need two things at once: it would have
  to <em>branch</em>, so that something in the term can act as a choice, and it
  would have to <em>descend</em>, so that a computation can consume what it built
  rather than merely accumulating. Those are the two axes below. Every dot is a
  random ten-leaf term. Horizontal is how many redexes the term offers late in its
  run; vertical is the deepest it ever falls back from its own peak.
</p>

<figure>
  <div class="controls">
    <span>seed <span id="seed-shown" class="mono"></span></span>
    <button id="reseed">reseed</button>
    <button id="atlas-stop">stop</button>
    <span id="atlas-progress" class="mono"></span>
  </div>
  <div class="scroll"><canvas id="atlas" width="1040" height="680"></canvas></div>
  <noscript><p class="noscript">This figure is computed in your browser and needs JavaScript.</p></noscript>
  <figcaption>
    Grey: terms that reach a normal form. Blue: terms that branch. Gold crosses:
    <strong>constructed</strong> corridor specimens, not sampled — uniform sampling
    at this size turns up roughly two corridors per thousand terms and almost none
    that descend deeply, so the deep arm is populated by hand and marked. The
    shaded region is the subject of the figure.
  </figcaption>
</figure>

<p>
  The branching terms run off to the right and stay flat. The deeply descending
  terms sit hard against the left edge, at width exactly one — no choices at all,
  ever. The region where a computer would have to live is empty, and it stays empty
  as the sample grows. You can reseed it and watch.
</p>

<p>
  This is measurement, not proof, and the distinction matters. What is proved is
  narrower and stranger: in the orderly phase, the structures provably do not
  interact. The corridor terms have been screened exhaustively at ten leaves — all
  7,311 of them, deep-marched, no crasher, maximum drop 211. The climber's
  reachable set is a single totally ordered road (<code>sc_mt5T_line</code>). These
  are the pretty objects, and they are closed.
</p>

<h2>The part with nothing to look at</h2>

<p>
  Which is why the open question is not here. It is in the storms — around 3.5% of
  term space, branchy exponential growers with no periodic structure, no emitted
  particles, and nothing that renders as anything but noise. They are not corridors
  in disguise; their late forced-fraction is flat zero. Whether reduction in that
  regime is decidable is <strong>open</strong>, and it is the whole question.
</p>

<p>
  What is known about storms is a floor, not a ceiling. No single fire loses more
  than one leaf (<code>sc_unit_drop</code>). C-fires never mint new C-redexes
  (<code>sc_cold_law</code>). Growth in inventory is paid for in leaves
  (<code>sc_minting_law</code>). Adversarial search digs at most 26 leaves out of
  storm peaks of 700 to 1,500 — so descent looks structurally unavailable, and the
  remaining gap is an integration step.
</p>

<p>
  The honest summary is that this calculus put all of its beauty in the phase that
  turned out to be tractable, and hid its difficulty in the phase that looks like
  static. The clocks are lovely and they are finished. The question is in the other
  room.
</p>

<dl class="tiers">
  <dt class="tier-proved">Proved (Lean, no <code>sorry</code>, no <code>native_decide</code>)</dt>
  <dd>
    <code>sc_mill_cycle</code>, <code>sc_mill_eternal</code>,
    <code>sc_corridor_unbounded</code>, <code>sc_mt5T_line</code>,
    <code>sc_swap_revolution</code>, <code>sc_unit_drop</code>,
    <code>sc_cold_law</code>, <code>sc_minting_law</code>, <code>sc_minting_run</code>.
  </dd>
  <dt class="tier-probed">Probed (measured, not proved)</dt>
  <dd>
    Storm digs ≤ 26 from peaks of 700–1,500. Median late forced-fraction 0.00 for
    storms. Dig budget tracking C-redex inventory, median 9. The phase census
    (≈67% halt, ≈33% branch, ≈0.15% corridor), which the figure above recomputes
    live in your browser.
  </dd>
  <dt class="tier-open">Open</dt>
  <dd>
    C14, the storm floor — and therefore whether <code>{S,C}</code> reduction is
    decidable at all. Nothing on this page shows that <code>{S,C}</code> is not
    universal. It shows where the question has been driven.
  </dd>
</dl>

<script type="module" src="./main.js"></script>
</main>
</body>
</html>
```

- [ ] **Step 3: Write the wiring**

Create `site/main.js`:

```js
import { parse, show, leaves } from './sc.js';
import { spacetimeRaster, drawSpacetime } from './spacetime.js';
import { runAtlas } from './atlas.js';
import { SPECIMENS } from './specimens.js';

const $ = (id) => document.getElementById(id);

/** The render cap. A storm reaches it at fire 62; that wedge is the point. */
const RENDER_LEAF_CAP = 1200;

for (const [i, s] of SPECIMENS.entries()) {
  const opt = document.createElement('option');
  opt.value = String(i);
  opt.textContent = s.label;
  $('term-pick').append(opt);
}

function renderSpacetime() {
  const text = $('term-text').value.trim();
  const chosen = SPECIMENS[Number($('term-pick').value)];
  let term;
  try {
    term = text ? parse(text) : parse(chosen.source);
    $('parse-error').textContent = '';
  } catch (e) {
    $('parse-error').textContent = e.message;
    return;
  }
  const fires = Number($('fires').value);
  const raster = spacetimeRaster(term, {
    fires, mode: $('mode-pick').value, leafCap: RENDER_LEAF_CAP,
  });
  const canvas = $('spacetime');
  canvas.width = raster.width;
  canvas.height = raster.height;
  drawSpacetime(canvas, raster);
  const capped = raster.height >= RENDER_LEAF_CAP;
  $('spacetime-caption').textContent =
    `${show(term)} — ${leaves(term)} leaves, ${raster.width - 1} fires, ` +
    `growing to ${raster.height} leaves` +
    (capped ? `, cut off at the ${RENDER_LEAF_CAP}-leaf render cap.` : '.');
}

$('term-pick').addEventListener('input', () => {
  $('term-text').value = '';
  $('fires').value = String(SPECIMENS[Number($('term-pick').value)].fires);
  renderSpacetime();
});
for (const id of ['mode-pick', 'fires']) {
  $(id).addEventListener('input', renderSpacetime);
}
$('term-go').addEventListener('click', renderSpacetime);
$('term-text').addEventListener('keydown', (e) => { if (e.key === 'Enter') renderSpacetime(); });
renderSpacetime();

let atlas = null;
function startAtlas(seed) {
  atlas?.stop();
  $('seed-shown').textContent = String(seed);
  const url = new URL(location.href);
  url.searchParams.set('seed', String(seed));
  history.replaceState(null, '', url);
  atlas = runAtlas($('atlas'), {
    seed,
    total: 4000,
    onProgress: (done, total) => { $('atlas-progress').textContent = `${done} / ${total} terms`; },
  });
}
$('reseed').addEventListener('click', () => startAtlas((Math.random() * 1e9) | 0));
$('atlas-stop').addEventListener('click', () => atlas?.stop());
startAtlas(Number(new URL(location.href).searchParams.get('seed')) || 20260810);
```

- [ ] **Step 4: Verify manually**

Run: `cd site && python3 -m http.server 8765`
Open `http://localhost:8765/`.

Confirm, and state each one explicitly when reporting:
1. The spacetime figure renders and shows the comb-with-frozen-band structure.
2. Switching colour to "bracket depth" changes the image. Switching to the storm gives a short, violently expanding wedge that stops at the render cap around fire 62 — visibly a different kind of object from the climber's long narrow comb. The normalizer terminates at fire 111.
3. Typing `C (S C C) S` in the text box and pressing run renders it; typing `C K` shows a parse error naming a position and does not blank the figure.
4. The atlas fills in progressively, the counter advances, `stop` halts it, `reseed` changes the seed shown and the URL.
5. The shaded quadrant contains no dots.
6. The page does not scroll horizontally at a 400px-wide viewport.

- [ ] **Step 5: Commit**

```bash
git add site/index.html site/style.css site/main.js
git commit -m "feat(site): the essay

Prose is tiered: every claim is marked proved, probed, or open, and the
status box states plainly that nothing here shows {S,C} is not universal.
Rule 110 appears as a named contrast in prose; no panel was built for it."
```

---

### Task 6: Deployment

**Files:**
- Create: `.github/workflows/pages.yml`
- Create: `site/.nojekyll`
- Modify: `README.md`

**Interfaces:**
- Consumes: the `site/` directory from Tasks 1–5.
- Produces: a deploy workflow. Nothing consumes it.

- [ ] **Step 1: Add the test runner to CI and write the workflow**

Create `.github/workflows/pages.yml`:

```yaml
name: Pages

on:
  push:
    branches: [main]
  workflow_dispatch:

permissions:
  contents: read
  pages: write
  id-token: write

concurrency:
  group: pages
  cancel-in-progress: false

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v5
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
      - name: Run the site test suite
        run: node --test site/

  deploy:
    needs: test
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - uses: actions/checkout@v5
      - uses: actions/configure-pages@v5
      - uses: actions/upload-pages-artifact@v3
        with:
          path: site
      - id: deployment
        uses: actions/deploy-pages@v4
```

Create an empty `site/.nojekyll` so GitHub Pages serves the directory verbatim.

- [ ] **Step 2: Verify the suite passes the way CI will run it**

Run: `node --test site/`
Expected: PASS — all four test files, 31 tests total (11 + 7 + 5 + 8).

- [ ] **Step 3: Add a pointer to the README**

In `README.md`, immediately after the `## Where to look` heading's bullet list, add:

```markdown
- **[The Clockmaker's Shop](https://ndouglas.github.io/CombinatorCalculusPlayground/)**
  — a visual essay on what `{S,C}` reduction looks like, with both figures computed
  live in the browser by an engine the test suite checks against the Lean.
```

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/pages.yml site/.nojekyll README.md
git commit -m "ci: deploy the visual essay to GitHub Pages

Gated on the site test suite -- a failing empty-quadrant assertion blocks
the deploy, so the page cannot publish a claim its own figures refute."
```

- [ ] **Step 5: Hand back for enabling Pages**

**Do not enable Pages.** Report to the user that the workflow is committed and that enabling requires either the repo's Settings → Pages → Source → "GitHub Actions", or:

```bash
gh api -X POST repos/ndouglas/CombinatorCalculusPlayground/pages -f build_type=workflow
```

The repo is public, so the essay becomes publicly readable the moment this runs. That is the user's call, not the implementer's.

---

## Self-Review

**Spec coverage.** Deployment → Task 6. `sc.js` → Task 1. `panels.js` → split into Tasks 3 and 4, which is a deliberate improvement: separating the pure raster/points functions from the two thin `draw*` functions is what makes the figures testable without a DOM. Sampling and the two-measurement distinction → Task 2. Essay structure, controls, status box → Task 5. Testing groups 1–3 → Tasks 1, 2. Error handling (parse failure, no-JS, interruptible sampling, leaf caps) → Tasks 1, 4, 5.

**Placeholders.** One stub (`globalThis.__scMarch` in `knownCorridorPoints`) was found and eliminated outright when the specimen list was rewritten — `knownCorridorPoints` no longer needs to advance a term, so the code is simply correct as written.

**Specimens were verified, not assumed.** The first draft of this plan named five specimens; four were wrong. `millK` and `millT 1` are normal forms on their own and reduce zero times. `S S S (S S S)` halts after one fire and is not a storm. `C C S (S C)` halts after one fire and shows nothing. Every specimen now in the plan was run before being written down, and the recorded drops are re-checked by a test so a transcription error fails the suite instead of mislabelling a figure.

**Type consistency.** `march` returns `{states, fate, branched}` everywhere. `coords` returns `{width, drop, peak, kind}`; `sampleBatch` flattens it to `{term, phase, width, drop, peak}` — `phase` comes from `screenKind`, `kind` from `coords`, and they are deliberately different names because they are different measurements. `Point` is `{width, drop, phase, constructed, name?}` in both `knownCorridorPoints` and `runAtlas`. `spacetimeRaster` returns `{width, height, pixels}`, consumed by `drawSpacetime` and the tests.

**Known risk carried forward.** The census tolerance in Task 2 may need widening for a different PRNG; the step says to widen only if the observed value is near the recorded census, and to treat a distant value as a porting bug.
