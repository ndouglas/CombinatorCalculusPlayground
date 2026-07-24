# Stage 8: attack the `bwd` blocker, not the encoding

Goal 2 criterion (a) needs `Simulation (RS.Tag T) RS.SK`. Stage 6 identified
`bwd` as the blocker and Stage 7 proved it load-bearing (a positive claim
must be made in the demanding class). The instinct is to start building the
encoding; the leverage is to make `bwd` *derivable* first, so that when an
encoding is built the hard field comes for free from a standard obligation.

That is the classic adequacy technique: an abstraction function on ALL host
states, where each host step either stutters (leaves the abstraction fixed)
or advances it by exactly one source step. Supplying such a function is
mechanical for a given machine; deriving `bwd` from it should be a theorem
proved once.

## Stage 1: `bwd` from a stuttering abstraction
**Goal**: prove once, at the taxonomy level, that an abstraction function
with the stutter-or-advance property yields `bwd`.
**Success Criteria**:
- `RS.bwd_of_abstraction` — the reusable adequacy lemma.
- `Simulation.ofAbstraction` — a `Simulation` constructor taking enc, an
  abstraction function, the stutter-or-advance step property, and `fwd`.
- Non-vacuity: rebuild the existing `pureS_in_SK` through the new
  constructor, so the interface is shown to work on a real inhabitant.
- Honest scope: this does NOT make `bwd` easy. It makes it STANDARD —
  reducing an open-ended obligation to a per-machine mechanical one. Must be
  written that way, not as "blocker removed".
**Tests**: the `pureS_in_SK` rebuild is the test; plus `#print axioms`.
**Status**: Complete

## Stage 2: Scope Tag → SK as a multi-slice project
**Goal**: a written, ordered decomposition of what remains for criterion (a),
with each piece's difficulty named, so it can be picked up incrementally
instead of attempted opportunistically.
**Success Criteria**: recorded in the notebook; identifies which pieces are
mechanical, which need new infrastructure, and where the residual risk is.
**Status**: Complete

## Stage 3: Record
**Goal**: ledger + notebook entries; plan file removed.
**Status**: Complete
