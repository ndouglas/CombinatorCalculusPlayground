# Stage 6: finish the spec's goals

Re-reading the design spec showed the C-conjecture list is not the goal set.
Spec Goal 3 (is reachability between pure S-terms decidable?) is the stated
north star, and Slice 5's `enum_complete` supplies the finiteness ingredient
its last gap was missing. Spec Goal 2's remaining hole is the
calibration-sandwich criterion (a). Both are in reach; C1(a) is not, and may
not even be open. Order reflects that.

## Stage 1: Goal 3 — reachability is decidable
**Goal**: promote `reachable?` from a certified per-instance procedure to an
abstract decidability result for K-free sources.
**Success Criteria**:
- A finite universe of small terms (`smallTerms`) with membership proved
  from `enum_complete`.
- A strictly-decreasing measure (`deficit`) proving `boundedClosure`
  always saturates given enough fuel.
- `boundedClosure_isSome`, then `reachable_decide` / a `Decidable` result
  for `t ⟶* u` at K-free `t`.
- Honest framing: on paper this is folklore-adjacent (monotone size ⇒
  bounded search, two lines given Stage 2). The machine-checked version is
  the contribution, and the ledger must say so.
**Tests**: `#guard`s that the computed fuel bound actually works on the
existing `reachable?` examples; `#print axioms`.
**Status**: Complete

## Stage 2: Literature check on C1(a)
**Goal**: determine whether "some pure-S term has no normal form" is
already known, before any more work is spent on it.
**Success Criteria**: a documented answer with citations, recorded in
CONJECTURES.md's external register. Either outcome is a result: if known,
C1(a) is transcription like C5 and should be re-labelled; if not, the
project is doing research and must say so loudly.
**Status**: Complete

## Stage 3: Goal 2 — the calibration sandwich
**Goal**: a `Simulation` inhabitant certifying a KNOWN-universal system,
i.e. Tag → SK. This is the criterion `pureS_in_SK` does not discharge.
**Success Criteria**: assess feasibility first and report honestly. A
full Tag→SK encoding is a large formalization; if it does not land within
the 3-attempt budget, record precisely what blocks it rather than leaving
a half-built encoding in the tree.
**Status**: Complete — assessed, scoped, and deliberately NOT attempted;
blockers recorded. See notebook.

## Stage 4: Retire C3, record Stage 6
**Goal**: C3 closed as a census artifact (both halves weakened, never a
real conjecture); ledger and notebook updated; plan file removed.
**Status**: Complete
