# Stage 5, Slice 4: widening, fuel-testing, and ledger repair

Driven by the ideonomic progress review (2026-07-24). Four stages, in
dependency order. Stages 1–3 are cheap and certain; Stage 4 is the hard
open one and is scoped as a probe, not a resolution.

## Stage 1: Extract the weak encoding hypothesis
**Goal**: `PathEncoding` — injective + path-preserving, nothing else — as
the actual hypothesis of the acyclicity refutations, with both existing
refutations restated at that wider level and `Simulation.refute_of_acyclic`
recovered as a corollary (name preserved; CONJECTURES.md cites it).
**Success Criteria**:
- `PathEncoding` structure with exactly three fields (`enc`, `inj`, `path`).
- `Simulation.toPathEncoding` projection.
- `PathEncoding.refute_of_acyclic` proves the generic mechanism.
- `Simulation.refute_of_acyclic` re-derived from it, statement unchanged.
- `no_pathEncoding_SK_pureS` / `no_pathEncoding_SK_iota` as the widened
  headline results.
- Strictness witness: a `PathEncoding` whose encoder provably extends to
  no `Simulation`. Without this the generalization could be vacuous.
- Build green, no new axioms beyond the inherited `[propext, Quot.sound]`.
**Tests**: the strictness witness IS the test (a proof obligation that
fails if `PathEncoding` is secretly equivalent to `Simulation`).
**Status**: Complete

## Stage 2: Fuel-sensitivity of the C6 density table
**Goal**: determine whether the C6 divergence-density table measures
divergence or measures fuel=200.
**Success Criteria**: exhausted-count rows at a second fuel value for as
many n as runtime allows; CONJECTURES.md's C6 entry updated with whichever
answer comes back, including a negative.
**Tests**: n/a (census run). Record wall-clock and the fuel value.
**Status**: Complete

## Stage 3: Add a demotion state to the ledger
**Goal**: the status vocabulary distinguishes "never tested" from "tested
and weakened". Apply to C3.2, whose own Slice 3 probe disconfirmed it at
n=7..9 while it stayed filed as plain "open".
**Success Criteria**: status vocabulary documented at the top of
CONJECTURES.md; C3 re-filed; every other conjecture audited against the
new vocabulary and re-labelled where the evidence warrants.
**Tests**: n/a (documentation).
**Status**: Complete

## Stage 4: Non-size measures on the C1 trajectory
**Goal**: the review's finding is that C1 is trapped inside three census
properties and that every promoted result escaped one. Leaf count is the
only measure ever tried. Mine the c1 trajectory for candidate invariants
under other measures (spine length, depth, redex count).
**Success Criteria**: measures defined and computed along the trajectory;
report which are monotone/bounded/periodic and which are not. A negative
is a publishable result here — this is a probe, and C1 is NOT expected to
close.
**Tests**: `#guard`s pinning the observed values so the data is
build-enforced rather than a transcript claim.
**Status**: Complete
