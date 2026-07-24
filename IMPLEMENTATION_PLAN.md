# Stage 7: C4's semantic core, and a correction to the sandwich plan

The ideonomy pass recommended restating spec Goal 2 criterion (a) at
`PathEncoding` strength to bypass the `bwd` blocker. Working it showed that
recommendation is WRONG, and instructively so — see Stage 2 below. The
blocker is principled, not incidental, and the correction is itself a
formalizable taxonomy fact.

## Stage 1: C4's semantic core
**Goal**: resolve the mathematical content of C4 — that a host whose steps
strictly grow a measure cannot host SK — as a general theorem, and recover
the iota refutation from it.
**Success Criteria**:
- `RS.Acyclic.of_strict_measure`: strict measure growth implies acyclicity.
- `no_pathEncoding_SK_of_strict_measure`: such a host cannot path-encode SK.
  Stated at `PathEncoding` strength, which is correct for a NEGATIVE claim.
- `RS.Iota_acyclic` recovered as an instance, confirming the generalization
  is the right one.
- Honest scope: this is stronger than C4 semantically (any host, not just
  one-combinator ones) and weaker syntactically (it does not formalize
  "one-combinator single-rule first-order system"). C4 as WRITTEN needs a
  rule-schema formalism; that residue must be registered precisely, not
  glossed as "C4 proved".
**Status**: Complete

## Stage 2: The claim-asymmetry theorem (correcting the plan)
**Goal**: formalize why positive and negative claims want OPPOSITE encoding
classes, which is why criterion (a) cannot be weakened to `PathEncoding`.
**Success Criteria**:
- `UniversalReach.toPathEncoding` — the class inclusion at claim level.
- A documented statement of the asymmetry: negative claims strengthen as the
  class grows, positive claims strengthen as it shrinks. With
  `pathEncoding_strictly_weaker` the two levels provably differ, so the
  direction matters.
- Goal 2 criterion (a) re-registered as blocked on `bwd` for a PRINCIPLED
  reason, superseding the ideonomy pass's suggestion in the record.
**Status**: Complete

## Stage 3: Ledger primitives — materiality and prior art
**Goal**: add the two columns whose absence each cost nine stages.
**Success Criteria**: every live conjecture gets a materiality verdict (does
resolving it change a conclusion we care about?) and a prior-art line. C1 is
the worked example of both failing.
**Status**: Complete

## Stage 4: Record, fix the cycle, assess extraction
**Goal**: notebook entry including the self-correction; the working cycle
documented with its two missing phases; an honest verdict on extracting the
calibration suite as a standalone artifact.
**Status**: Complete
