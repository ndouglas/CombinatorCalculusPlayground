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

test('depth mode actually varies with depth, not just with atom', () => {
  // C (S C) has leaves at two distinct depths: [C@1, S@2, C@2]
  const r = spacetimeRaster(parse('C (S C)'), { fires: 0, mode: 'depth' });
  assert.equal(r.width, 1);
  assert.equal(r.height, 3);

  const shallow = px(r, 0, 0);   // depth 1
  const deep1 = px(r, 0, 1);     // depth 2
  const deep2 = px(r, 0, 2);     // depth 2

  // A constant-colour depth mode would fail this:
  assert.notDeepEqual(shallow, deep1,
    'leaves at different depths must get different colours');
  // Equal depths must agree:
  assert.deepEqual(deep1, deep2,
    'leaves at the same depth must get the same colour');
  // Pin the actual ramp values so a silent palette change is caught:
  assert.deepEqual(shallow, [33, 145, 140, 255]);
  assert.deepEqual(deep1, [253, 231, 37, 255]);
});

test('the leaf cap bounds the raster for a runaway term', () => {
  const r = spacetimeRaster(climber, { fires: 2000, mode: 'atom', leafCap: 200 });
  assert.ok(r.height <= 200);
});

test('the raster reports the march fate, so callers can see a capped run', () => {
  assert.equal(spacetimeRaster(climber, { fires: 100 }).fate, 'running');
  assert.equal(spacetimeRaster(climber, { fires: 2000, leafCap: 200 }).fate, 'capped');
  assert.equal(spacetimeRaster(parse('S C'), { fires: 10 }).fate, 'halt');
});
