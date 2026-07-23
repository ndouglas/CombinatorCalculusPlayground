# The S-Combinator Research Program — Design

**Date:** 2026-07-23
**Status:** Approved design, pre-implementation
**Context:** An attack on the Wolfram Combinator Prize question — *is the S
combinator alone computationally universal?* — using Lean 4 as a research lab.
The question is open research; this program is structured so that every stage
is a real, standalone deliverable even if the summit is never reached.

## Goals

1. Build a self-contained Lean 4 formalization of combinatory calculus deep
   enough to state and attack the prize question precisely.
2. Produce a machine-checked **taxonomy of computational-universality
   definitions** — the definitional groundwork the prize community lacks.
3. Drive toward the sharpest well-posed open question adjacent to the prize:
   **is reachability (t ⟶* u) between pure S-terms decidable?**
4. Meta-goal (explicit and first-class): measure how far Fable can push Lean
   on genuine research mathematics, recorded in a lab notebook.

## Non-goals

- Winning the prize is a hoped-for side effect, not the success criterion.
- No Mathlib/Batteries dependency (see Escape Hatches).
- No claim of universality under a bespoke definition that wouldn't survive
  external scrutiny — the calibration stage exists to prevent exactly this.

## Background facts that shaped the design

- **Waldmann 2000** (*The Combinator S*): normalization of pure S-terms is
  decidable. Consequence: any universality definition based on
  "encode halting as normalization" is dead for S. The definitional stage
  must offer definitions that survive this.
- **λI-calculus** (Church 1941, *The Calculi of Lambda Conversion*; Barendregt §9.5): the erasure-free calculus — combinator
  basis {S, B, C, I} — is computationally complete for total computable
  functions. Consequence: "S can't erase" is NOT an obstruction to
  universality by itself. Conservation-law results must be framed honestly.
- **One-combinator universal bases exist** (Barker's iota, Fokker's X).
  Consequence: "only one combinator" is not the obstruction either, and these
  are the correct apples-to-apples calibration targets.
- **The 2007 Wolfram 2,3 Turing machine prize dispute** (Smith's proof,
  Pratt's objection that the encoding did unbounded work): encoding fights
  are the historically recurring failure mode. Consequence: the encoding
  class must be pinned formally, as part of the definitions.
- **Quantifier asymmetry**: universality claims are ∃-encoding (exhibit one);
  non-universality claims are ∀-encoding (only meaningful over a pinned
  encoding class).

## Architecture

Self-contained Lean 4 (toolchain v4.28.0, zero dependencies). The current
single `Basic.lean` splits into focused modules as stages land:

```
CombinatorCalculusPlayground/
  Term.lean          -- Term, app2/app3, size/leaf-count measures
  Step.lean          -- Step, Steps, basic closure lemmas
  Confluence.lean    -- parallel reduction, diamond, Church-Rosser   (Stage 1)
  SFragment.lean     -- K-free predicate, conservation laws          (Stage 2)
  RS.lean            -- abstract rewriting-system interface          (Stage 3)
  Universality/
    Defs.lean        -- (system, encoder, decoder) definitions       (Stage 3)
    Taxonomy.lean    -- implications between definitions             (Stage 3)
    Calibration.lean -- iota/X certified; lambda-I stretch           (Stage 4)
  Census/
    Eval.lean        -- executable reducer (fuel-based)              (Stage 0)
    Enumerate.lean   -- S-terms by size, dynamics classifier         (Stage 0)
CONJECTURES.md       -- standing census-generated conjecture pipeline
LAB_NOTEBOOK.md      -- the Fable-vs-Lean meta-experiment record
```

Key interface decision: universality definitions are stated over an abstract
rewriting system (`RS`: a carrier type plus a step relation), never over
`Term` directly. SK, pure-S, iota, and reference machines (tag systems or
Turing machines) are instances. This is what makes the taxonomy comparative
rather than bespoke.

The stage dependency structure is a DAG, not a ladder — Stages 1, 2, 3 are
mutually independent and parallelizable:

```
Stage 0 (census) ----------------------------+--> feeds everything
Stage 1 (confluence) --+                     |
Stage 2 (conservation) +--> Stage 4 --> Stage 5
Stage 3 (taxonomy) ----+
```

## Stages

### Stage 0 — The census (starts immediately, never stops)

**Goal:** Empirical reconnaissance of pure-S dynamics.
**Deliverables:** fuel-based evaluator; enumerator of all S-terms up to
size n (Catalan growth caps n ≈ 15–20); classifier tagging each term
terminating / cyclic / growing; observables for spine shape and growth rate.
**First questions:** Does any pure S-term satisfy t ⟶⁺ t (a proper cycle)?
What is the smallest non-normalizing S-term? Growth-rate census.
**Success criteria:** `#eval`/`ccp` runs producing classified censuses;
`CONJECTURES.md` populated with machine-generated, later-checkable claims.
Every Stage-2+ lemma gets census-checked before proof effort is spent.

### Stage 1 — Confluence of SK reduction

**Goal:** Church–Rosser for `Steps`, via the parallel-reduction
(Tait–Martin-Löf) method, hand-rolled.
**Success criteria:** `theorem confluence : t ⟶* u → t ⟶* v → ∃ w, u ⟶* w ∧ v ⟶* w`
and corollary: uniqueness of normal forms. This gives convertibility
(and Stage 3's convertibility-based definitions) their meaning.

### Stage 2 — Conservation laws of the S-fragment

**Goal:** Formalize what S-reduction preserves.
**Deliverables:** `KFree` predicate closed under reduction; leaf count is
non-decreasing under S-steps (no erasure); spine-structure lemmas.
**Framing constraint (honest version):** these laws explain why *naive*
encodings fail; they are NOT an impossibility argument — λI is the standing
counterexample. The module docstring must say so.
**Success criteria:** the lemmas, plus census confirmation at small sizes.

### Stage 3 — The universality taxonomy (the intellectual center)

**Goal:** Machine-checked definitions of "computationally universal," stated
over `RS`, with proven implications between them.
**Deliverables:**
- `RS` interface; instances for SK, pure S, and a reference universal model.
- Definitions as properties of (system, encoder, decoder) triples, with the
  encoder/decoder class pinned (computable, with bounded preparatory work —
  the formal answer to the 2007 dispute).
- At minimum: normalization-based, reachability-based, and
  convertibility-based universality, plus the implication lattice among them.
**Design spec (the calibration sandwich):** a correct definition must
(a) certify known-universal systems including one-combinator bases,
(b) not be auto-killed for S by Waldmann's decidability alone, and
(c) identify precisely which definitions leave the prize question open.
**Success criteria:** the lattice compiles; each definition's status for
{S,K} and for pure S is either proven or explicitly registered as open.

### Stage 4 — Calibration

**Goal:** Prove the taxonomy certifies the systems it must certify.
**Deliverables:** combinatory completeness of {S,K} via bracket abstraction;
universality of a one-combinator basis (iota or X) under the taxonomy;
stretch: λI ({S,B,C,I}) completeness. Confirm formally that Waldmann's
result kills only the normalization-based definition for S.
**Success criteria:** `universal SK`, `universal iota` as theorems under at
least one taxonomy definition; the S-column of the status chart updated.

### Stage 5 — The attack (open-ended)

**North star:** decidability of reachability (and convertibility) between
pure S-terms — well-posed, encoding-free, and directly adjacent to the
prize: undecidability is computational richness; decidability is a major
obstruction.
**Bracketing program (the relaxation ladder):** classify universality of
bases between {S} and {S,K} — e.g., {S,I}, {S,B}, {S,C} — each rung a
publishable partial result that narrows where universality is lost.
**Method:** census conjectures → formalization attempts → notebook records
of what the prover resisted. No completion criterion; this is research.

## Standing artifacts

- **CONJECTURES.md** — every census observation worth proving, with status
  (open / proved / refuted, and by what).
- **LAB_NOTEBOOK.md** — dated entries: what was attempted, what Lean pushed
  back on, what automation could/couldn't do. If Stage 5 never terminates,
  the notebook is the result of the meta-experiment.

## Error handling & proof hygiene

- No `sorry` on main. Unproven census claims live in `CONJECTURES.md`, not
  as axioms.
- Executable code (census) is fuel-based and total; no `partial def` in
  proof-bearing modules.
- Every commit compiles (`lake build` clean) per global standards.

## Testing

- Proof-bearing modules: theorems ARE the tests; `#eval`/`example` blocks as
  executable sanity checks alongside.
- Census: golden tests on small hand-verified cases (e.g., I x ⟶* x, the
  known smallest divergent SK-terms), determinism of the classifier.
- Cross-validation: census classifier vs. proved lemmas wherever they overlap.

## Escape hatches (explicit triggers)

- **Mathlib trigger:** if hand-rolled infrastructure (not the research
  content) stalls for 3 documented attempts (per global 3-attempt rule),
  reconsider Batteries/Mathlib for infrastructure only.
- **Direction trigger:** if census + Stage 2 yield strong evidence in either
  direction on S-reachability, Stage 5 re-plans around that direction.

## Risks

- Stage 5 is an open problem and may never close: accepted; Stages 0–4 and
  both standing artifacts are unconditional deliverables.
- Hand-rolled infra debt if we later adopt Mathlib: accepted knowingly.
- Waldmann's paper details may complicate the Stage 4 "kills only
  normalization" claim: if the formalization gap is too large, downgrade to
  citing it in CONJECTURES.md as an external result rather than formalizing.
