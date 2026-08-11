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
