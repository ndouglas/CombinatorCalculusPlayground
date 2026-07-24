# Status, by spec goal

The stage-by-stage record lives in `CONJECTURES.md` (the ledger) and
`LAB_NOTEBOOK.md` (the working notebook). Both are chronological and now run to
several thousand lines, which means neither answers the question "what is
actually settled?" This file does, organised by the four goals of
`docs/superpowers/specs/2026-07-23-s-combinator-research-program-design.md`.

Everything below is machine-checked in Lean 4 with **no dependencies** (no
Mathlib, no Batteries), **no `sorry`**, **no `native_decide`**, and **no
`Classical.choice`**. Axiom footprint is `[propext, Quot.sound]` or less
throughout — `Quot.sound` rides core tactic machinery (`omega`/`simp`), a trail
inherited since Stage 0.

At time of writing: 46 build targets, ~190 theorems, ~175 build-enforced
`#guard`s, ~4,400 lines of Lean.

---

## Goal 1 — a self-contained formalization deep enough to state the prize question precisely

**Status: DONE.**

| Result | Theorem | Where |
|---|---|---|
| SK reduction is confluent, with unique normal forms | `confluence`, `nf_unique` | `Confluence.lean` |
| `normalize` certified on both ends | `normalize_sound`, `normalize_normal` | `Census/Eval.lean` |
| K-freeness closed under reduction; no erasure | `KFree.of_step`, `leafCount_le_of_steps` | `SFragment.lean` |
| K-free normal forms are exactly the spine-≤2 shapes | `SNF_iff` | `SFragment.lean` |
| {S,K} combinatory completeness | `combinatory_completeness` | `Bracket.lean` |
| ...restated in the same language as the refutations | `combinatory_completeness_RS` | `Universality/Calibration.lean` |
| Abstract rewriting systems, with SK / pure S / tag instances | `RS`, `RS.SK`, `RS.PureS`, `RS.Tag` | `RS.lean` |

The prize question is stated precisely as a property of a pinned encoding class
over abstract rewriting systems — see Goal 2.

---

## Goal 2 — a machine-checked taxonomy of universality definitions

**Status: the taxonomy is built and calibrated. One instance remains open — see
"the open item" below.**

Three observation modes, all quantifying over a pinned encoding class:
`UniversalReach` / `UniversalNorm` / `UniversalConv` (`Universality/Defs.lean`).

**The encoding classes, and why there are two.** Negative claims strengthen as
the class grows; positive claims strengthen as it shrinks. So refutations are
stated for the weaker `PathEncoding` (injective + path-preserving, nothing else)
and certifications for the stronger `Simulation` (adds a decoder and backward
reflection). `Simulation.toPathEncoding` gives the inclusion;
`pathEncoding_strictly_weaker` proves it is proper, so the direction is
substantive rather than bookkeeping.

| Result | Theorem |
|---|---|
| One refutation mechanism for all acyclic hosts | `PathEncoding.refute_of_acyclic` |
| ...from a strictly-growing measure | `RS.Acyclic.of_strict_measure` |
| pure S cannot host SK | `no_pathEncoding_SK_pureS` |
| first-order ι cannot host SK | `no_pathEncoding_SK_iota` |
| **no one-combinator one-rule system of any arity can (C4)** | `no_pathEncoding_SK_poly` |
| `bwd` from a stuttering abstraction (adequacy) | `RS.bwd_of_abstraction`, `Simulation.ofAbstraction` |
| a `Simulation` whose source is known-universal | `universalReach_extend` |

**Negative controls** — what the definitions would collapse to if loosened:
`bareEncNorm_trivial` (an oracle encoder witnesses unpinned normalization-based
universality for *any* source) and `universalReach_self` / `universalNorm_self` /
`universalConv_self` (all three modes are trivially true on the diagonal, so a
ledger cell carries information only when reference ≠ host).

**Calibration criteria, from the spec.** (b) discharged in Stage 3. (c)
discharged by the definitions ledger plus the `PathEncoding` scoping. (a) — see
Stage 16 in the ledger — is **unsatisfiable as written**, because its
"including one-combinator bases" clause is refuted in first-order scope by C4;
in its satisfiable restatement (certify at least one known-universal system via
a `Simulation` inhabitant) it is **discharged**.

---

## Goal 3 — is reachability between pure S-terms decidable?

**Status: CLOSED. Yes, for K-free sources.**

`stepsDecidable` / `steps_decidable_of_kFree` (`Decidability.lean`). Stage 2
monotonicity confines every path inside a finite universe; `enum_complete`
(`Census/Completeness.lean`) proves that universe is exhaustively enumerable; a
`deficit` measure then bounds how long saturation can take, so the certified
per-instance procedure `reachable?` always returns a verdict.

Honest framing, also in the module header: on paper this is folklore-adjacent —
"monotone size ⇒ bounded search" is two lines given Stage 2. The machine-checked
version is the claim.

---

## Goal 4 — how far this setup pushes Lean on genuine research mathematics

**Status: ONGOING BY DESIGN — it is a deliverable, not a target.** The spec says
plainly: *"if Stage 5 never terminates, the notebook is the result."*
`LAB_NOTEBOOK.md` is that deliverable. Its most transferable content:

- **Four `Classical.choice` leaks**, all caught by a per-stage `#print axioms`
  audit and none by review, all originating in core's `BEq`/instance layer or in
  `omega` discharging a non-arithmetic goal. Three were fixed by rewriting; the
  fourth was resolved by *weakening a decorative claim* rather than paying the
  axiom.
- **A difficulty-estimate tally**: four under-estimates, one over-estimate,
  with the same cause in both directions — estimating from the first
  representation that came to mind rather than from the problem.
- **Four prototypes that found bad news**, each cheap, each preventing a larger
  rewrite. Naming the risky piece has been reliable; rating its difficulty has
  not.

---

## The conjectures

`C1`–`C6` were census output, not goals. Current standing:

| | Claim | Status |
|---|---|---|
| C1(a) | some pure-S term has no normal form | **external** (Wolfram; Waldmann) |
| C1(b) | none with ≤ 6 leaves does, so 7 is the floor | **PROVED** `no_small_divergence` |
| C2 | no proper cycles in pure-S reduction | **PROVED** `no_pure_S_cycle` (probably external too) |
| C3 | growth-pattern regularities | **RETIRED** as a census artifact |
| C4 | no one-rule first-order basis hosts SK | **PROVED** `no_pathEncoding_SK_poly` |
| C5 | conservation for pure S (WN ⇒ SN) | **external** (Church; Barendregt) |
| C6 | divergence density → 1 | **probed**, open, low materiality |

Every entry carries a **materiality** and a **prior-art** line in the ledger.
Those two fields were added in Stage 7 after nine stages went into C1, whose
materiality was low from the start and whose prior art was discoverable in an
hour.

---

## The open item

**Does SK certifiably host a known-universal system?** Concretely: is there a
`Simulation (RS.Tag T) RS.SK`?

This is the one substantive thing left, and it is **research-blocked**, not
merely unbuilt. The obstruction is `bwd`, and it is load-bearing: a positive
certification must be made in the demanding class (Stage 7's asymmetry), so it
cannot be weakened away. Stage 8 reduced `bwd` to supplying a stuttering
abstraction, which makes the obligation standard rather than open-ended — but
Stages 10 and 13 then showed the obvious abstraction fails, because `S f g x`
duplicates `x` and the copies drift, and transient duplicates are unavoidable in
SK (moving a value past another costs a copy). The abstraction must therefore be
insensitive to doomed subterms — up to `Joinable`, or reading only the live
spine. That is a research obligation.

Infrastructure already in place for it: pieces (i) and (ii) of the decomposition
(`ofTerm`/`toTerm` bridge, `abs2`/`abs2_beta`), plus `normalForm_bracket` (all
machine code is normal, so a fixpoint's self-application is safe).

## What this program does not claim

- It does not resolve the Wolfram prize question. What it establishes is where
  the question lives: **if S alone is universal, its encoding must be
  non-injective or must fail to preserve reduction paths.**
- It does not claim priority on C1, C2, or C5 — all are external or probably so.
- It does not claim `Simulation` is the right definition of universality. It
  claims the definition is *pinned*, *calibrated in both directions*, and that
  the unpinned alternatives provably measure nothing.
