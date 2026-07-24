# Stage 5, Slice 5: split C1, close its minimality half

Driven by the second ideonomic review (2026-07-24), which found that C1
bundles two independent claims and that the program has only ever attacked
the bundle. Re-ranked worklist: the `sTerms`-completeness chain moves from
priority 4 to priority 1, because it is the last obstacle to a kernel-level
proof of C1's minimality half — a fact nobody noticed while the halves were
fused. C5 stays valuable but drops in order (zero information gain).

## Stage 1: A verified enumerator (the blocked chain)
**Goal**: break the `sTermsTable` transparency blocker by adding a
structurally-recursive enumerator with BOTH directions proved, instead of
trying to make the imperative `Id.run do` version transparent.
**Success Criteria**:
- `enum : Nat → Nat → List Term`, structural in a depth budget.
- `enum_sound`: membership implies K-free with exactly n leaves.
- `enum_complete`: every K-free term with n leaves and budget ≥ n is a
  member. This is the lemma the chain was blocked on since Slice 1.
- Cross-validated against the existing census tooling by `#guard`, so the
  verified enumerator is tied to the one the census actually ran.
**Tests**: `#guard`s pinning `enum n n` against `sTerms n` for n ≤ 7
(lengths and set-equality); soundness/completeness are the theorems.
**Status**: Complete

## Stage 2: C1's minimality half, at the kernel
**Goal**: `∀ t, KFree t → leafCount t ≤ 6 → t normalizes` — kernel-checked.
**Success Criteria**: a named theorem, no `sorry`, no `native_decide`.
Route: `enum_complete` puts t in a finite list; a `decide`d `List.all` over
that list discharges it; `normalize_sound`/`normalize_normal` (Stage 1
certificates) turn a `normalize` success into a genuine normal form.
**Success Criteria (honest)**: this proves MINIMALITY only — that if a
diverging pure-S term exists, 7 leaves is the floor. It says nothing about
existence, which is C1's other half and stays open.
**Tests**: the theorem itself; plus `#print axioms`.
**Status**: Complete

## Stage 3: Split C1 in the ledger
**Goal**: C1(a) existence and C1(b) minimality as separately-tracked
claims, with (b) marked PROVED and (a) left open.
**Success Criteria**: CONJECTURES.md restructured; the status vocabulary
applied to each half; every stale "C1 is open" cross-reference audited.
**Status**: Complete

## Stage 4: Re-rank and record
**Goal**: notebook entry; next-target ranking revised (C5 demoted with the
reason stated; construct-don't-search framed as the high-variance route to
C1(a)); IMPLEMENTATION_PLAN.md removed.
**Status**: Complete
