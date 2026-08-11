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
