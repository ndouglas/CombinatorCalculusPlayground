import { test } from 'node:test';
import assert from 'node:assert/strict';
import { leaves, parse } from './sc.js';
import {
  mulberry32, randomTerm, screenKind, coords, sampleBatch,
  QUADRANT_WIDTH, QUADRANT_DROP,
} from './sample.js';
import { ATLAS_TOTAL } from './atlas.js';

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

test('THE THESIS: branching and deep descent are near-exclusive', async () => {
  const rnd = mulberry32(20260810);
  const batch = sampleBatch(rnd, ATLAS_TOTAL, { size: 10 });
  const inQ = batch.filter(
    (s) => s.width >= QUADRANT_WIDTH && s.drop >= QUADRANT_DROP,
  );

  // Sparse, not empty. The essay states this count; if it climbs, the prose is stale.
  assert.ok(inQ.length <= 5,
    `${inQ.length} terms in the quadrant at ${ATLAS_TOTAL} samples -- the essay says a `
    + 'handful. If this has grown, the prose must be requantified, not the bound.');

  // And shallow: no branchy term descends as deep as the corridors do.
  const branchy = batch.filter((s) => s.width >= 2);
  const maxBranchyDrop = Math.max(...branchy.map((s) => s.drop));
  assert.ok(maxBranchyDrop <= 60,
    `branchy terms reached drop ${maxBranchyDrop}; the essay says they top out near 55`);
});

test('the two arms of the atlas are separated as the essay describes', () => {
  const rnd = mulberry32(20260810);
  const batch = sampleBatch(rnd, 2000, { size: 10 });
  const branchy = batch.filter((s) => s.width >= 2);
  const deep = batch.filter((s) => s.drop >= QUADRANT_DROP);
  assert.ok(branchy.length > 0, 'expected some branchy survivors');
  assert.ok(Math.max(...branchy.map((s) => s.width)) > 100, 'branchy arm should reach high width');
  assert.ok(Math.max(...branchy.map((s) => s.drop)) < QUADRANT_DROP, 'branchy arm must stay shallow');
  assert.equal(deep.length, 0,
    'Random sampling finds no deep descenders at this size. '
    + 'The deep arm of the atlas is reachable only via the '
    + 'constructed corridors in specimens.js -- which is why '
    + 'they are hard-coded there rather than sampled.');
});

test('coords caps runaway growth instead of chasing it', () => {
  const c = coords(parse('C S S (S S) C (S (C S (C C)) C)'), { leafCap: 60 });
  assert.equal(c.kind, 'big');
});
