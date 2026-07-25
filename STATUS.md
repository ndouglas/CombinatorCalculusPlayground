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

At time of writing: 48 build targets, ~200 theorems, ~177 build-enforced
`#guard`s, ~4,700 lines of Lean.

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

## The relaxation ladder — an ACYCLICITY ladder (spec Stage 5, second component)

The spec's Stage 5 has **two** components. The north star — reachability
decidability — is Goal 3 above and is closed. The other is the *bracketing
program*: "classify universality of bases between {S} and {S,K} — e.g., {S,I},
{S,B}, {S,C} — each rung a publishable partial result that narrows where
universality is lost." Sixteen stages engaged only with the first; the ladder was
opened in Stage 17.

**WHAT THIS LADDER ANSWERS, AND WHAT IT DOES NOT.** The spec says "classify
**universality** of bases." What this program can answer per rung is
**acyclicity** — and acyclicity only bounds *refutability*: an acyclic basis can
be refuted as a host of SK by the existing mechanism, a cyclic one cannot be
touched by it. **No rung below settles universality.** Rung one does *not* say
`{S,I}` is or is not universal; it says the program's refutation tool cannot
reach it. Stated here because rung one otherwise reads like a universality
result, which would be the same misreading the `Tag → Tag` result was scoped
against in Stage 16.

| rung | basis | acyclicity verdict |
|---|---|---|
| 0 | `{S}` | **acyclic** (`no_pure_S_cycle`); hence refuted as a host of SK |
| 1 | `{S,I}` | **cyclic** (`omegaSI_cycle`). NO monotone measure exists in either direction (`SI_no_strict_measure`, `SI_no_decreasing_measure`) — so the mechanism is not merely unhelpful here, it is provably inapplicable |
| 2 | `{S,B}` | **open, target narrowed to one condition.** No counting measure is monotone (`no_monotone_counting_measure`). No cycle under **any** strategy up to 8 leaves within a 30-leaf cap, cap-insensitive to 120 (`onCycleAny`); the cap is not liftable by brute force. **τ strictly drops on every B-reduction and every τ-light S-reduction, so the τ-light fragment is ACYCLIC** (`sbLight_acyclic`) — hence any cycle must fire an S-reduction duplicating a τ-**heavy** argument (`sbCycle_needs_heavy_S`) |
| 3 | `{S,C}` | **open, and structurally UNLIKE rung 2.** `C x y z → x z y` has the same `leafCount` delta as `B` (−1), so no counting measure separates them — but τ does: B always lowers τ, **C can raise it** (`tauSC_C_red`, delta `τ(z)−τ(y)−8`), because permuting moves a heavy argument into a lighter position. So the light fragment needs **two** conditions (`scLight_acyclic`). Censused: no cycle up to 6 leaves under any strategy within a 30-leaf cap |
| top | `{S,K}` | **cyclic** — by the Ω ↔ M cycle, and independently by inheritance from rung one (`SK_not_acyclic_via_rung1`) |

**A standing caveat on census evidence here.** Cycle hunts based on a single
reduction strategy are **leftmost-outermost only**. Stage 0 flagged that for pure S; Stage 21
gave it a concrete witness — rung one's cycle is *kernel-proved to exist* and
leftmost-outermost reduction provably never returns to it (`omegaSI` grows
6,8,7,10,9,8,12,… forever). So "no cycle found" at any rung bounds LO cycles only,
never the reduction relation. Pure S is unaffected because C2 *proved* acyclicity by
a measure, not by the census. **Stage 22 replaced the rung-two hunt with a
strategy-independent one** (`onCycleAny`, all one-step successors, validated by
finding rung one's cycle) — so rung two's evidence is no longer subject to this
caveat, only to a size cap.

**The rungs are not independent — the ladder is a hierarchy.** Cycles propagate
along path encodings (`not_acyclic_of_pathEncoding`, axiom-free), so a cyclic
basis makes every system it path-encodes into cyclic as well. Rung one is
therefore an **upward-closed family**, not a point: any basis with a definable
`I` inherits its cycle. `siInSK` witnesses this at the top of the ladder, and
`SK_not_acyclic_via_rung1` re-derives SK's non-acyclicity by that route —
independent of the Ω ↔ M cycle, so the two agree.

### What each rung has ESTABLISHED

The spec's purpose for a rung is *"a publishable partial result that narrows where
universality is lost"* — not a full acyclicity proof. Reporting rungs 2 and 3 only as
"open" understates them against that purpose, so here is what each has delivered.

- **Rung 0 `{S}`** — acyclicity PROVED (`no_pure_S_cycle`), and refuted as an SK host.
  Also a genuine decision procedure for reachability, because monotonicity confines
  every path.
- **Rung 1 `{S,I}`** — cyclic, PROVED, and **upward-closed**: any basis with a
  definable `I` inherits the cycle (`not_acyclic_of_pathEncoding`, `siInSK`). Also the
  witness that erasure-freeness does *not* explain rung 0's acyclicity, and that
  **arity** is the discriminator.
- **Rung 2 `{S,B}`** — four results, none of them the full proof: no counting measure
  is monotone (`no_monotone_counting_measure`); the τ-light fragment is ACYCLIC
  (`sbLight_acyclic`); any cycle must fire an S-reduction on a τ-heavy argument, with
  the threshold bootstrapped from τ ≥ 4 to an average of τ ≥ 14; and no I-like
  combinator exists up to 7 leaves, closing the transport route. Censused clean to 8
  leaves under *any* strategy, cap-insensitive.
- **Rung 3 `{S,C}`** — the τ-light fragment is acyclic with a two-clause condition
  (`scLight_acyclic`), and the structural finding that **τ separates B from C where no
  counting measure can**, since both rules have identical `leafCount` deltas.

### The rung procedure

Order is load-bearing. Rung one ran this before it was written down.

```
0. PRECONDITION: the basis {S, X} and X's rule as a rewrite schema.

1. Compute each rule's leafCount delta at minimal instantiation.
   -> know whether leafCount is monotone up, down, or neither.  [arithmetic]

2. IF every rule strictly increases: RS.Acyclic.of_strict_measure -> refuted.
   STOP. [one line -- where iota and all of C4 land]

3. ELSE hunt for a cycle. Canonical attempt: Omega = (S X X)(S X X).
   -> a cycle KILLS every monotone measure in both directions, so step 4
      becomes provably futile; or the attempt terminates, weak evidence
      toward acyclic. [small; absence of a cycle is not proof of none]

4. ONLY IF no cycle: hunt a combined measure -- lexicographic, since by
   step 1 no single component is monotone. [a full slice, as C2 was]

5. Record the rung, and say which question was answered (acyclicity,
   not universality).
```

**Step 3 must precede step 4**, because a cycle makes step 4 provably
impossible. At rung one that ordering saved the expensive step entirely — by
luck rather than design, which is why it is written down now. Steps 1 and 3 are
independent and can run together.

**What rung 1 establishes.** The program's entire negative apparatus routes
through one mechanism, `RS.Acyclic.of_strict_measure` — and that mechanism
**stops dead at the first rung**. It covers `{S}`, first-order ι, and every
one-combinator one-rule system (C4); it provably cannot touch `{S,I}`. Also:
erasure-freeness is *not* what keeps pure S acyclic, since `{S,I}` erases nothing
either and still cycles. Higher rungs need positive constructions or new
mechanisms.

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
