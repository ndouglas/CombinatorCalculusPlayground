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
