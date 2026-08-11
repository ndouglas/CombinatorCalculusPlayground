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
