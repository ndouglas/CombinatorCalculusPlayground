import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parse, leaves, march } from './sc.js';
import { SPECIMENS, CLIMBER } from './specimens.js';

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
