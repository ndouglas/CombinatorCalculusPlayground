import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  KNOWN_CORRIDORS, knownCorridorPoints, project,
  DEFAULT_MAX_DROP, DEFAULT_MAX_WIDTH,
} from './atlas.js';
import { QUADRANT_WIDTH, QUADRANT_DROP, coords, mulberry32, sampleBatch } from './sample.js';
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

test('the default axes contain the data without wasting the frame', () => {
  const deepest = Math.max(...knownCorridorPoints().map((p) => p.drop));
  assert.ok(deepest <= DEFAULT_MAX_DROP,
    `deepest corridor drop ${deepest} must fit inside maxDrop ${DEFAULT_MAX_DROP}`);
  assert.ok(deepest > DEFAULT_MAX_DROP * 0.6,
    `maxDrop ${DEFAULT_MAX_DROP} wastes most of the frame against deepest ${deepest}`);

  const rnd = mulberry32(20260810);
  const widest = Math.max(...sampleBatch(rnd, 500, { size: 10 }).map((s) => s.width));
  assert.ok(widest <= DEFAULT_MAX_WIDTH,
    `widest sampled term ${widest} must fit inside maxWidth ${DEFAULT_MAX_WIDTH}`);
});

test('corridors descend deeper than any branchy term', () => {
  const deepestCorridor = Math.max(...knownCorridorPoints().map((p) => p.drop));
  // Branchy terms are bounded near 55 (see sample.test.mjs); corridors reach 109.
  assert.ok(deepestCorridor > 60,
    `deepest corridor ${deepestCorridor} must exceed the branchy ceiling`);
});
