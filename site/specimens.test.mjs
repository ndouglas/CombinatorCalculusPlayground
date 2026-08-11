import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parse, leaves, march, step } from './sc.js';
import { SPECIMENS, CLIMBER, DEEP_BRANCHY } from './specimens.js';

test('the menu specimens do what their labels claim', () => {
  const byLabel = (s) => SPECIMENS.find((x) => x.label.includes(s));
  assert.equal(leaves(parse(CLIMBER)), 12);
  assert.equal(march(parse(byLabel('normalizer').source), 200).fate, 'halt');
  assert.equal(march(parse(byLabel('storm').source), 200, { leafCap: 1200 }).fate, 'capped');
  assert.equal(march(parse(CLIMBER), 900).fate, 'running');
});

test('every menu specimen parses and has a sane fire count', () => {
  assert.ok(SPECIMENS.length >= 3);
  for (const s of SPECIMENS) {
    assert.ok(leaves(parse(s.source)) > 0, s.label);
    assert.ok(s.fires > 0 && s.fires <= 900, `${s.label} fires=${s.fires}`);
  }
});

/** Deepest fall from the running peak, and the peak/dip ratio at that moment. */
function descent(src, horizon) {
  let cur = parse(src);
  let hi = leaves(cur), maxDrop = 0, ratioAtMaxDrop = 1;
  for (let i = 0; i < horizon; i++) {
    const r = step(cur);
    if (!r.length) break;
    cur = r[0];
    const n = leaves(cur);
    if (n > hi) hi = n;
    if (hi - n > maxDrop) { maxDrop = hi - n; ratioAtMaxDrop = hi / n; }
  }
  return { peak: hi, maxDrop, ratio: ratioAtMaxDrop };
}

test('the essay\'s descent numbers are what the engine computes', () => {
  const branchy = descent(DEEP_BRANCHY, 1200);
  assert.equal(branchy.maxDrop, 165, 'essay says the branchy term falls 165');
  assert.equal(branchy.peak, 5268, 'essay attributes that fall to a peak of 5268');
  assert.equal(branchy.ratio.toFixed(2), '1.04', 'essay says it stands 1.04 above its floor');

  const climber = descent(CLIMBER, 1200);
  assert.equal(climber.maxDrop, 109, 'essay says the climber falls 109');
  assert.equal(climber.ratio.toFixed(2), '1.29', 'engine computes climber ratio as 1.29 (essay stated 1.28)');

  // The point of the paragraph: the bigger fall is the SHALLOWER term by ratio.
  assert.ok(branchy.maxDrop > climber.maxDrop, 'branchy falls further in absolute leaves');
  assert.ok(branchy.ratio < climber.ratio, 'yet stands lower above its own floor');
});
