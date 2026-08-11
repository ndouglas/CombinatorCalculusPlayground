// Verified specimens. The corridors were found by search over ~37,000 random
// terms at 8-12 leaves, one per distinct maximum drop, because uniform sampling
// inside the page would essentially never turn up a deep one.

/** The 12-leaf climber, scMt5T. */
export const CLIMBER = 'C S S (S S) C (S (C S (C C)) C)';

/** The spacetime figure's menu. `fires` is tuned per specimen. */
export const SPECIMENS = [
  { label: 'the climber — 12 leaves, forced forever', source: CLIMBER, fires: 520 },
  { label: 'a deep corridor — drop 66', source: 'S (S C C) C (S (S C C) (C (C C)))', fires: 520 },
  { label: 'a storm — explodes, hits the render cap at fire 62', source: 'S (S (S C C) (S S)) (C S) S', fires: 120 },
  { label: 'a normalizer — halts at fire 111', source: 'C (S S S (S S S) (C C) C)', fires: 140 },
];
