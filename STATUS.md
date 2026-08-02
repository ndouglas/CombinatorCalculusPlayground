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
inherited since Stage 0. As of Stage 76 this claim is **build-enforced**:
`Audit.lean` pins the headline theorems' exact footprints with `#guard_msgs`,
so any drift fails the build.

At time of writing (Stage 114 review): 32 modules, ~843 theorems, ~439
build-enforced `#guard`s plus 62 `#guard_msgs`-pinned axiom footprints, ~17,100
lines of Lean. Since the Stage 97 review: the 3-cycle CLASSIFICATION became a
theorem (Stage 101 — the program's first complete description of a cycle
space), and the HOSTING THREAD (Stages 98–113, its own section below) built a
machine-checked computation stack inside `{S,C}` — a calculus with no erasure,
no identity, and no selectors — culminating in `tailInSC` (the first positive
hosting certificate on any upper rung) and the ONE-TAG-STEP. The entire
hosting stack is axiom-free.

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

**Status: DONE — taxonomy built, calibrated in both directions, and the open
item CLOSED (Stages 75–79): a genuine tag system is hosted by a machine-checked
`Simulation`, generalised to EVERY finite-alphabet 2-tag system. See "the open
item" below for the route.**

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
| **a `Simulation` of a genuine multi-step machine INSIDE SK** | `countdownInSK` |
| **a `Simulation` of a genuine TAG SYSTEM inside SK — the open item, closed** | `tagABInSK`, `universalReach_tagAB_SK` |
| **...generalised: EVERY finite-alphabet 2-tag system is hosted** | `tagTInSK`, `finTagInSK`, `universalReach_finTag` |

**Negative controls** — what the definitions would collapse to if loosened:
`bareEncNorm_trivial` (an oracle encoder witnesses unpinned normalization-based
universality for *any* source) and `universalReach_self` / `universalNorm_self` /
`universalConv_self` (all three modes are trivially true on the diagonal, so a
ledger cell carries information only when reference ≠ host).

**Adequacy — the blocker, now cleared (Stages 45–48).** `bwd` was the risky
piece from Stage 8. Stage 10 found the failure (duplicated arguments drift),
Stage 13 refuted the first two fixes (constrain the encoding: impossible, since
transient duplicates are unavoidable; abstract up to joinability: too coarse,
`joinable_abs_not_functional`), Stage 45 found the third — read a term's
**K-normal form**, so doomed subterms and any drift inside them are invisible —
Stage 46 made that denote (`knf_unique`, `IsKNF.of_kstep`), and Stages 47–48
proved the S-step half via a commutation square (`sk_square`, `itower_sStep`).
The result is `countdownInSK`, a `Simulation` into `RS.SK` with a genuinely
multi-step encoding rather than an inclusion.

Stages 49–58 then produced a **second, independent** adequacy proof for the
same machine (`countdownInSK'`), via the *trajectory relation* rather than
K-normal forms, sharing nothing with the first but the encoding. Getting there
lifted four inherited pure-S restrictions from Goal 3's decidability layer
(`enumAt`, `smallTerms`, `deficit`, `boundedClosure_isSome`) and produced
`reachableWithin_correct` — **bounded-region reachability is decidable for full
SK** — plus `RS.bwd_of_abstraction_path`, which lets an abstraction advance by a
source *path* rather than a single step.

Its limit, stated plainly: the countdown is **not** universal, so this
discharges the *mechanism* criterion (a) was blocked on, not criterion (a).

**The tag-step driver — spec piece (v) — now exists and its forward half is
proved (Stages 59–64).** `STEPc` computes one step of a genuine two-symbol
m = 2 tag system (`a ↦ [b]`, `b ↦ [a,b]`) literally on fold-encoded words
(`STEPc_mkWord`), and `tagAB_fwd` gives `fwd` end to end: every source step is
simulated by actual SK reduction on the encoded word, via Stage 61's
fixpoint-free driver.

**Stage 65: the decoder is done (`decTag_encTag`), and the tag system
PATH-ENCODES into SK, machine-checked (`tagABPathEncoding`)** — the weaker
certificate class, but the one every refutation here is stated over, now
inhabited by a genuine dispatch machine. For the full `Simulation`, `bwd`
remains — and Stage 65 proved it is **false for the current encoding**
(`tagAB_bwd_false`): the tag step is partial, the compiled step function is
total, so the host keeps computing where the source has halted
(`encTag [b] ⟶* encTag [a,b]` with `[b]` a tag normal form). The driver needs
a length guard (Stage 66 design item). Both of the countdown's adequacy
templates are also provably inapplicable, for reasons that survive the guard:
the trajectory relation assumes a loop-free source and `tagAB` has a fixed
point (`onSegment_habs_fails_of_selfLoop`); the K-normal-form abstraction
demands intermediates that K-normalise to encodings, and the driver's first
self-application step already violates that (`tagDriver_knf_hstep_fails`).
A third abstraction, plus a characterisation of the guarded driver's
reachable set, is the remaining research obligation.

**Stage 66: the guarded driver is built and proved** (`STEPg`, 936 leaves):
stuck words are literally fixed (`STEPg_stuck`), `fwd` re-proved with the
Stage 64 lemmas untouched (`tagABg_fwd`), decoder and `PathEncoding`
retargeted (`tagABgPathEncoding`), and Stage 65's falsifier repaired
(`encTagG_stuck_returns`). `bwd` is now open rather than false; the
reachable-set characterisation is the whole of the remaining distance.

**Stages 67–68: the rigidity audit and the clean rebuild.** Shipped code was
NOT normal (Stage 11's `normalForm_bracket` does not cover `bracketOpt` over
bodies embedding applied constants); the audit accounted for every live
position and the rebuild (`TAILZn`/`TAILn`/`HASTWOn`/`STEPgn`, 870 leaves —
smaller than before) removed all non-word redexes, build-enforced. The final
encoding is `encTagN` / `tagABnPathEncoding`. Code drift now equals data
drift: ONE species, the reducts of `mkWord w`. That word-drift family, the
machine phases composed over it, and the third abstraction are what remain
for `bwd`.

**Stage 69: the word-drift family is DONE, by behaviour rather than
enumeration.** Every word reaches a canonical normal form
(`wordNF`/`mkWord_to_wordNF`), and every drifted copy still reaches it
(`mkWord_drift_complete` — confluence joins, normality pins), so drift can
always be completed and never conflates words (`mkWord_drift_functional`).
What remains for `bwd`: injectivity of `wordNF` (syntactic), and the phase
layer — where the checkpoints are not normal, so completion must come from
the driver's structure instead of `nf_unique`.

**Stages 70–73: the identity layer is done and the route is forced.**
Injectivity (`encWord_drift_pins`, Stage 70); drift-input step-correctness
with literal outputs — the fold restores literalness (`STEPgn_drift`,
`encTagN_drift_fwd`, Stage 71); the corrected frame — completion cannot see
order, so `bwd` needs a per-step tracking relation (Stage 72); and the
landscape closed by two more machine-checked refutations (Stage 73):
segment relations are inherently second proofs (`segRel_habs_iff`), and the
driver's region is UNBOUNDED (`driver_region_unbounded` — the shell
pre-unfolds future cycles, `selfRep_nests`), killing bounded-region
decidability. Four mechanisms refuted in total; the one remaining route is
a per-step tracking abstraction over the interior factorization: an
inductive family of shell contexts (closed under nesting) over data holes
(handled by the Stage 69–71 suite).

**Stage 74: the interior factorization EXISTS** (`DriverShell.lean`): a
12-kind inductive family, generic in the step function, proved closed under
reduction (`Sh.closed`), with `driver_interior_invariant` instantiating it
for the tag driver — every reduct of `encTagN w` is shell machinery over
data holes. The data layer is abstract behind two Step-closed predicates;
instantiating it, then reading the tracking abstraction off the factored
shape, is what remains for `bwd`.

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

- **Nine `Classical.choice` leaks** (the fifth in Stage 69 — Stage 9's `BEq`
  trap again, sixty stages later, in a file that quotes it; the SIXTH in
  Stage 76 was PRE-EXISTING — `occurs_bracket`'s `grind` had leaked since it
  was written, tainting `combinatory_completeness`, and was found only when
  new code imitated the old tactic). Five caught by a per-stage
  `#print axioms`; the sixth showed per-stage auditing certifies stages, not
  the tree — so the claim is now BUILD-ENFORCED (`Audit.lean` pins every
  headline theorem's exact footprint with `#guard_msgs`). The SEVENTH leak
  (Stage 79) was caught by that audit one stage after it was built, and came
  through a new door: `omega` aimed at a non-arithmetic goal routes through
  `Classical.choice`; the EIGHTH (Stage 93) was the same door again —
  the mechanism recurs because contradictory-hypothesis branches invite it; the
  NINTH (Stage 101) is a new variant of the same door: `omega` proving a
  CONJUNCTION-INSIDE-DISJUNCTION goal routes through choice even though plain
  disjunctions of equalities are clean (verified by experiment)
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
| C1(a) | some pure-S term has no normal form | **PROVED** `c1a` — `Recurrence.lean`, via a regular-tree-language certificate |
| C1(b) | none with ≤ 6 leaves does, so 7 is the floor | **PROVED** `no_small_divergence` |
| C2 | no proper cycles in pure-S reduction | **PROVED** `no_pure_S_cycle` (probably external too) |
| C3 | growth-pattern regularities | **RETIRED** as a census artifact |
| C4 | no one-rule first-order basis hosts SK | **PROVED** `no_pathEncoding_SK_poly` |
| C5 | conservation for pure S (WN ⇒ SN) | **PROVED** `conservation` — *not* an import; proved from Stages 1, 2, 6 and C2 |
| C6 | divergence density → 1 | **probed**, open, low materiality |

C1(a) is proved by a **recurrence set** (Endrullis–Zantema 2014): a
six-state deterministic tree automaton whose accepted language is non-empty,
closed under reduction, and contains no normal forms. Witness:
`S S S (S S S) (S S S (S S S))`, twelve leaves. C5 supplies the last step —
"admits an infinite reduction" ⟹ "has no normal form" is not automatic for
pure S, it *is* the conservation theorem.

The certificate is not tight: C1(b) proves the true divergence floor is **seven**
leaves, and the automaton rejects both seven-leaf candidates, so `c1` and `c2`
remain individually open.

C1(a)'s **loop route** (Stages 37–42) is closed off and was prior art —
Waldmann 2000 proved CL(S) admits no ground loops. What survives from those
stages is reusable machinery (`Subterm`, `Step.subterm_split'`,
`step_growth_eq`, `selfEmbed_imp_halfShape`) and one live pointer: the
**open-term** version, `t ⟶* C[tσ]`, is open in the literature. Everything
here is ground.

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

**THE LADDER IS COMPLETE** (Stage 96): every rung settled, the two two-combinator
bases split in opposite directions.

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
| 2 | `{S,B}` | **CLOSED — ACYCLIC (Stage 83: `SB_acyclic`), hence CANNOT HOST SK (`no_pathEncoding_SK_SB`).** The right-spine depth never decreases along any step and strictly increases at root steps; Stage 81's localization supplies the root step on every cycle. Subsumes all fragment results and census bounds. The route: 80 typechecked (termination dead), 81 localized (root steps forced), 82 dichotomized, 83 closed | No counting measure is monotone (`no_monotone_counting_measure`). No cycle under **any** strategy up to 8 leaves within a 30-leaf cap, cap-insensitive to 120 (`onCycleAny`); the cap is not liftable by brute force. **τ strictly drops on every B-reduction and every τ-light S-reduction, so the τ-light fragment is ACYCLIC** (`sbLight_acyclic`) — hence any cycle must fire an S-reduction duplicating a τ-**heavy** argument (`sbCycle_needs_heavy_S`) |
| 3 | `{S,C}` | **CLOSED — CYCLIC (Stage 96: `SC_cycle`, `SC_not_acyclic`, axiom-free witness).** With `h = C S C`: `S (C h) C h ⟶ C h h (C h) ⟶ h (C h) h ⟶ S (C h) C h` — a 3-cycle, 9 leaves, found by CHASING THE SURVIVING BRANCH of the impossibility hunt. Minimal cycle length is EXACTLY 3 (`sc_minimal_cycle_length`); the minimal cycle is NOT unique (Stage 99: the 13-leaf w-cycle, `C (w w) w w`, `w = S (C C)`); and the CLASSIFICATION is a theorem (Stage 101, `sc_root_three_cycle_classified`): every root 3-cycle is the h-cycle at basepoint A or B, or the w-cycle. `{S,C}` closes OPPOSITE to `{S,B}`; `PathEncoding.refute_of_acyclic` can never apply. The census stopped at 6 leaves; the witness sits at 9. Hosting: see THE HOSTING THREAD section below |
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
universality is lost"* — not a full acyclicity proof. Every rung is now SETTLED
(rungs 2 and 3 closed in opposite directions, Stages 83 and 96); here is what each
has delivered.

- **Rung 0 `{S}`** — acyclicity PROVED (`no_pure_S_cycle`), and refuted as an SK host.
  Also a genuine decision procedure for reachability, because monotonicity confines
  every path.
- **Rung 1 `{S,I}`** — cyclic, PROVED, and **upward-closed**: any basis with a
  definable `I` inherits the cycle (`not_acyclic_of_pathEncoding`, `siInSK`). Also the
  witness that erasure-freeness does *not* explain rung 0's acyclicity, and that
  **arity** is the discriminator.
- **Rung 2 `{S,B}`** — **CLOSED at Stage 83: ACYCLIC (`SB_acyclic`), hence not an SK
  host (`no_pathEncoding_SK_SB`)** — by right-spine-depth monotonicity composed with
  Stage 81's cycle localization. Everything below is subsumed, and kept as the record
  of the route (and of the six-stage miss the closure exposed — see the Stage 83
  notebook entry):
  - no counting measure is monotone (`no_monotone_counting_measure`);
  - the τ-light fragment is ACYCLIC (`sbLight_acyclic`), so a cycle must fire an
    S-reduction on a τ-**heavy** argument — threshold bootstrapped from τ ≥ 4 to an
    *average* of τ ≥ 14, with the argument family's cap recorded at τ ≈ 24;
  - the **S-only fragment is ACYCLIC** (`sbSOnly_acyclic`), so a cycle must contain a
    **B-reduction** (`sbCycle_needs_B`) — C2's squeeze transplanted, since S-only
    {S,B} is pure S over a two-symbol alphabet;
  - no I-like combinator AT ANY SIZE (`sb_no_I_like`, Stage 98 — upgraded from the
    7-leaf census: every step result is an application, so `t S ⟶* S` is a nonempty
    path ending at a leaf, impossible), closing the transport route unconditionally;
  - censused clean to 8 leaves under *any* strategy, cap-insensitive to 120.

  - the **no-B-duplication fragment is ACYCLIC** (`sbNoBDup_acyclic`) — a three-level
    squeeze on `#B`, then `leafCount`, then τ — so a cycle must contain an S-reduction
    whose duplicated argument **contains a `B`** (`sbCycle_needs_B_duplication`). This
    fragment strictly contains the S-only one, so it *subsumes* `sbSOnly_acyclic`.

  Composed, these give a **proved syntactic** necessary condition: a cycle requires an
  S-reduction whose third argument has ≥ 3 leaves, and an S-reduction whose third
  argument contains a `B`. (Measured: this does *not* prune a seed-filtered search —
  99.6% of 8-leaf terms survive — because it constrains a cycle's *steps*, not a
  search's *seeds*. Pruning during exploration is also unavailable: it would need a
  localizable unreachability certificate, and these constraints are global sums.)
- **Rung 3 `{S,C}`** — **CLOSED at Stage 96: CYCLIC (`SC_cycle`, `SC_not_acyclic` —
  axiom-free witness; minimal cycle length EXACTLY 3, `sc_minimal_cycle_length`).**
  With `h = C S C`, the 3-cycle is
  `S (C h) C h ⟶S C h h (C h) ⟶C h (C h) h ⟶C·appL S (C h) C h` — nine leaves,
  three above the census horizon, found by chasing the surviving branch of the
  impossibility hunt: Stage 95's budgets forced any S-rooted 3-cycle to carry two
  root fires, and the single consistent assignment through the injections is
  inhabited. The rung closes OPPOSITE to `{S,B}`; the acyclicity route to refuting
  `{S,C}` as an SK host (`PathEncoding.refute_of_acyclic`) is permanently closed.
  Everything below is the route that cornered the witness — six necessary
  conditions and two impossibility sweeps, every one satisfied by the cycle:
  two impossibility sweeps: the τ-light fragment is acyclic (`scLight_acyclic`); the
  S-only fragment is acyclic (`scSOnly_acyclic`); the no-C-duplication fragment is
  acyclic (`scNoCDup_acyclic`), so any cycle needs a C-duplicating S-reduction
  (`scCycle_needs_C_duplication`); any cycle passes through a root redex
  (`sc_acyclic_of_no_root_cycle`, Stage 81); any cycle fires a FLATTENING `C`
  (`scCycle_needs_flat_C`, Stage 84); and any root cycle's return path reaches a
  SECOND root redex, at the root or immediately left of it
  (`scCycle_second_redex`, Stage 88 — cycles cannot avoid the top-left spine). The
  collapse escape is narrowed (Stage 89): leaf-headed collapse is dead
  (`sc_no_leaf_collapse`) and every collapse fires a root redex from a right-nested
  subterm (`sc_collapse_needs_root`), and leaf-headed terms can never reach a root
  redex (`sc_leafLeft_no_root_reach`), giving the CYCLE ANATOMIES (Stage 90): a root
  S-cycle returns through a whole-term root step or `f` is an application and both
  projections carry root fires (`sc_root_S_anatomy`); a root C-cycle returns through
  a whole-term root step or `x` is an application with the left projection firing
  and `y ⟶* z` (`sc_root_C_anatomy`). Leaf-headed-argument root cycles must return
  through whole-term root steps. The frontier invariant is ROTATE OR DESCEND
  (`scCycle_rotate_or_descend`, Stage 91): every cycle carries a root cycle that
  either contains another root cycle on itself (through its return's whole-term
  root fire) or has an app-headed head argument whose `app head last` projection
  fires a root redex on a strictly smaller term. The well-foundedness scaffold is in
  place (Stage 92): length-indexed paths (`RS.StepsN`), a choice-free descent engine
  (`RS.acyclic_of_cycle_descent` — strictly-shortening cycle surgery proves
  acyclicity), and the conservation fact that rotation preserves total cycle length
  (`scRootCycle_rotate_same_length`) — rotation cannot escape a length descent.
  First purchase (Stage 93): the dichotomy and localization redone with lengths
  (`sc_stepsN_facts`, `sc_cycle_needs_root_length`), so MINIMAL CYCLES ARE ROOT
  CYCLES exactly (`sc_minimal_cycle_is_root`), no step is a self-loop
  (`scStep_irrefl`), and minimal cycles have length ≥ 2
  (`sc_cycle_length_ge_two`). Second purchase (Stage 94): a root fire is never
  undone in one step (`sc_no_root_two_cycle` — the live branch dies on the frozen
  left), so there are no 2-cycles and MINIMAL CYCLE LENGTH ≥ 3
  (`sc_cycle_length_ge_three`). Third purchase (Stage 95): collapse costs at least
  two steps (`sc_no_step_collapse`, `sc_collapse_length_ge_two`), and the return
  dichotomies carry exact budgets (`sc_root_S_return_length`,
  `sc_root_C_return_length`: sandwiches account for every step, projections split
  it, the S-side collapse costs ≥ 2) — so an S-rooted root cycle with a rootless
  return has cycle length ≥ 4 (`sc_root_S_projection_length`); short cycles must be
  C-rooted or carry second fires — and Stage 96's witness carries exactly the two
  fires the budget demanded. Termination routes were provably dead
  (`SC_not_normalizing`), positional measures provably insufficient (C permutes),
  the τ×ρ braid provably failed (Stage 85, witnessed), and the spine calculus
  (`scSpine_S_root`, `scSpine_C_root`, `sc_no_leaf_self_embed`) supplied the
  frozen-left theorem that closed the case analyses. The census stopped at 6 leaves;
  the witness sits at 9. The necessary conditions stand as theorems ABOUT the
  cycle space of `{S,C}` — no longer steps toward an acyclicity proof, but the
  sharpest published description of what its cycles must look like, verified against
  the one now known to exist.

**Shared machinery.** Every acyclic-fragment result above — and C2's original argument —
is an instance of one lemma, `RS.Acyclic.of_three_level`: three measures where each level
pins the next (`m1` never rises; when it holds still `m2` never falls; when that holds
still too `m3` strictly drops). Written by hand four times before being abstracted.

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

**Stage 96 postscript — step 3 has a second form.** The census (bounded cycle
hunt) is step 3's cheap form and it can miss: rung 3's cycle sits at 9 leaves,
three above where the census stopped. The expensive form is PROOF-GUIDED
SEARCH: run step 4's impossibility machinery with EXACT accounting (budgets,
not bounds), and when a branch refuses to die, its constraints are a
construction recipe -- unification either kills the branch or builds the
witness. Rung 3 fell to that form: sixteen stages of necessary conditions
specified the cycle up to one assignment. The procedure gains a step 4-prime:
if step 4 stalls with one surviving branch, instantiate it.

**What rung 1 establishes.** The program's entire negative apparatus routes
through one mechanism, `RS.Acyclic.of_strict_measure` — and that mechanism
**stops dead at the first rung**. It covers `{S}`, first-order ι, and every
one-combinator one-rule system (C4); it provably cannot touch `{S,I}`. Also:
erasure-freeness is *not* what keeps pure S acyclic, since `{S,I}` erases nothing
either and still cycles. Higher rungs need positive constructions or new
mechanisms.

## The hosting thread — SK ≤ `{S,C}`, the constructive half (Stages 98–113)

Rung 3's closure (cyclic) killed the refutation route and opened the opposite
question: can `{S,C}` — no erasure, no identity, no selectors — host
computation? Sixteen stages later the answer is a machine-checked stack, ALL OF
IT AXIOM-FREE (pure constructions, no `propext`, no `Quot.sound`):

| Capability | Theorem(s) | Stage |
|---|---|---|
| No I-like combinator, at any size (both `{S,B}` and `{S,C}`) | `sc_no_I_like`, `sb_no_I_like` | 98 |
| `{S,C}` path-encodes into SK (upward closure complete) | `scInSK` | 100 |
| Unbounded convergence (C-towers shred to `C C C`) — the naive erasure-impossibility is false | `sc_unbounded_convergence` | 102 |
| No one-application selector; the cyclic ROTATOR exists (`C C u v w ⟶* v w u`) | `scv_no_single_selector`, `scRot_beta` | 103 |
| Branching WITHOUT selectors: tags `C`/`C C` head-promote an arm under one uniform protocol, the untaken arm parked not erased | `scTagA_dispatch`, `scTagB_dispatch` | 104 |
| The word layer: normal, stable two-symbol words with per-symbol traversal (swap parity selects the arm) | `scWord_step_false/true`, `scWord_normal` | 105 |
| The re-launcher and the recycling arm: the parked arm is the next first arm | `scRelaunch_beta`, `scArm_step`, `scTraversal_step_*` | 106 |
| Payload regeneration: `scDup = S (C C) (C C)` (the w-cycle seed applied to a tag) duplicates the parked arm; UNBOUNDED TRAVERSAL; **the first machine hosted on any upper rung** | `scDup_step`, `scRun`, **`tailInSC : PathEncoding RS.TailB RS.SC`** | 107 |
| Production-carrying cells (differentiation is free at encoding time); the 3-arg driver protocol | `scPCell_step`, `scPCell_step_acc` | 108 |
| Runtime cons: the accumulator is writable, four fires, zero residue | `scCons_beta`, `scQCell_step` | 109 |
| **THE ONE-TAG-STEP**: read the cell, append its wrapper to the pile, advance, arms regenerated | `scTCell_step`, **`scTWord_step`** | 112 |
| Multi-symbol productions by cell layering | `scTCell2_step` | 113 |

**The method that carried it** — model, bound, edge, construct: Stage 110's
searches found mid-spine insertion census-dead across three protocols;
Stage 111 PROVED the bound in the searched model (opaque literals freeze the
spine at head — `scv_varHead2_step` — so at most one literal lands behind the
last atom) and located its edge (real cells are C-headed compounds, exempt);
Stage 112 constructed past it in two fires (`scTCell W rest = C (C rest scDup)
W` — the arms are CONSTANTS, so the cell supplies a fresh literal arm and
demotes a spare to accounted pile-junk).

**The member calculus** (the thread's working theory of `{S,C}` interrogation):
three moves — prefix-edit, passenger-step-back, z-nest — one terminator (an
atom reaching the head freezes the spine), one permanence (the last member is
immovable, so piles are LIFO by law; LIFO fold of LIFO pile restores FIFO).
Non-erasure forbids UNACCOUNTED waste, not waste: every surviving gadget gives
each forced passenger a job.

**What remains for a full tag `Simulation` into `{S,C}`**: the FOLD phase, and
its obstruction DEEPENED (Stage 115): elements are GENETICALLY CLOSED — data
flows elements → spine, one way — so the fold cannot re-create a NESTED next
word from pile members at all; the nested-word architecture ends at generation
one. The boustrophedon framing was itself corrected (Stage 116): front-push and
front-pop INTERLEAVE, so the induced dynamics are PREFIX REWRITING — a
deterministic stack process with a finite wrapper alphabet, pushdown-flavored,
and generational separation would need a mid-spine barrier that cannot exist.
THE FRONTIER QUESTION REFRAMED: is `{S,C}`-reachability DECIDABLE? Formal
transport (Stage 116, `Simulation.steps_iff` + `Simulation.transferDecidable`,
axiom-free): reachability is equivalent across a Simulation, so deciding the
host decides the source — a Simulation of SK into a reachability-decidable
host would decide SK-reachability (undecidable, external). Decidability of
`{S,C}` would therefore close the negative half at the Simulation class. The
C-FRAGMENT is settled (Stage 117, `scStepsC_conservation`, `SCC_acyclic`,
pinned): every C-fire loses exactly one leaf, so the fragment obeys EXACT
CONSERVATION (a length-`n` path loses exactly `n` leaves), terminates, is
acyclic (every full-system cycle fires an S — the dual of `scSOnly_acyclic`,
closing the fragment square), and has finite reachable sets (fragment
reachability decidable in principle). The dichotomy
(`scStep_leafCount_dichotomy`) pins the escape: the non-decreasing steps are
exactly the S-fires. Full-`{S,C}` decidability = whether S-fires can be
accounted — and the accounting now has its exact laws (Stage 118,
`scSteps_shrink_le`, `scSteps_growth_le`, pinned): the TWO-SIDED SPEED LIMIT —
no step loses more than one leaf (the anti-erasure law quantified; SK's K
erases mountains in one step, `{S,C}` pays retail) and no step more than
doubles. Every `{S,C}` path is metered on both sides. The member-sequence
abstraction collapses under S-compounding and non-erasing TRSs are
Turing-complete in general, so the question is genuinely about these rules;
SC-CONFLUENCE is now IN PLACE (Stage 119, `SC_confluence`, `sc_nf_unique`,
pinned at `[propext]` — matching SK's footprint): the Takahashi proof
transported arm for arm, with both redex inversions at depth three since
neither `{S,C}` rule erases. Normal forms are characterized (Stage 120, `SCNF_iff`, pinned — axiom-free):
exactly the spine-width-≤-2 shapes. BOUNDED REACHABILITY IS DECIDABLE
(Stage 121, `scReachFrom_iff`, `scReachWithin_decidable`, pinned): a verified
successor function and its n-step closure compute exactly the ≤-n-step cone.
The single remaining piece for full decidability is the BOUNDED-INTERMEDIATE
question — an intermediate bound plus the shrink limit would bound path
lengths, and `scReachWithin` would then decide `t ⟶* u` outright. Stage 115
also corrected Stage 111's prose invariant (atoms CAN sit at member heads via
S-fires, witnessed in-file; the freeze theorem and one-behind bound survive).
Negative standing results shaping any route: arm-level differentiation
homogenizes, arrival-order pairing conjectured impossible (≤ 9), opaque
mid-spine insertion impossible.

## The open item — CLOSED (Stage 75)

**Does SK certifiably host a genuine tag system?** Concretely: is there a
`Simulation (RS.Tag T) RS.SK`?

**YES — `tagABInSK : Simulation (RS.Tag tagAB) RS.SK`** (`DriverShell.lean`,
Stage 75): a genuine two-symbol, deletion-number-two tag system —
inspect, dispatch, append, guarded on its halting condition — hosted inside
SK in the demanding encoding class, encoder/decoder/`fwd`/`bwd` all
machine-checked, axioms `[propext, Quot.sound]`. The route, Stages 65–75:
`bwd` proved FALSE for the unguarded driver (65); the guard (66); the
rigidity audit and clean rebuild (67–68); the word-drift layer by
completion — canonical forms, injectivity, literalness restoration
(69–71); the frame corrections (72–73, four mechanisms refuted); the shell
factorization invariant (74); and the semantic data layer, under which
`bwd` is an INVERSION rather than a tracking argument (75) — the order was
in the slots, not the steps.

Honest scope, unchanged in kind since Stage 16: `tagAB` belongs to the
Cocke–Minsky universal CLASS (m = 2), but this two-symbol instance is not
itself proven universal and no such claim is made. Spec piece (v) — a
tag-step driver with a real `Simulation` — is discharged in full.

**Stages 76–79 completed the scaling**: `tagTInSK` (any m = 2 system, given
a four-hypothesis dispatch interface) and `finTagInSK` (the interface
discharged for every `Fin n` alphabet via selectors). Every concrete
known-universal 2-tag system in the literature is an instance of a
machine-checked theorem; universality of any particular table remains
EXTERNAL knowledge, cited not checked, as the repository has always
scoped it.

The original framing follows, for the record.

This is the one substantive thing left, and Stage 29 upgraded it from
"research-blocked" to a **stated structural obstruction**: the two candidate
abstractions fail for *opposite* reasons. The syntactic one is too **fine** — `S f g x`
duplicates `x`, the copies drift, and it loses track (`naiveAbs_not_stuttering`). The
joinability one is too **coarse** — it relates every trajectory state to every other, so
it is never functional on `enc`'s image (`RS.joinable_abs_not_functional`), which is
exactly the hypothesis the relational adequacy lemma needs. A workable abstraction must
sit strictly between, and neither obvious construction does.

Infrastructure in place for any future attempt: `RS.bwd_of_abstraction_rel` (adequacy
from a *relational* abstraction, with Stage 8's function version as a special case).

The older framing follows. The obstruction is `bwd`, and it is load-bearing: a positive
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
