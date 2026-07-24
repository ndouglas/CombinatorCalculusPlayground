# Conjectures

Census-generated claims, each with a status drawn from the vocabulary
below. Slice 4 added **probed** and **weakened**: the original three
labels could not distinguish a conjecture nothing had ever tested from one
whose own targeted probe had come back against it, and C3 had been sitting
in the latter position while labelled like the former.

- **open** — stated; no targeted test has been run beyond the census
  observation that generated it.
- **probed** — a targeted test was run and came back CONSISTENT with the
  conjecture. Still logically open; the label records that it has survived
  something.
- **weakened** — a targeted test came back AGAINST the conjecture, or
  against the specific reading that motivated it, without refuting it.
  Still logically open; the label records that the evidence now leans the
  other way. A weakened conjecture should not be quoted as support for
  anything.
- **external** — settled in the literature, NOT machine-checked here. Added
  in Stage 6, when a literature check found that C1 had been externally
  known all along (see the C1 entry). This is the same epistemic level the
  file already uses for Cocke–Minsky, Waldmann and Church/Barendregt; it had
  simply never been available as a *conjecture* status, so an
  externally-settled claim could sit indefinitely labelled "open".
  Formalizing an **external** claim is transcription, not research, and the
  distinction should be visible before effort is spent.
- **proved** (link the theorem) — kernel-checked.
- **refuted** (link the counterexample) — kernel-checked.

Note on what these labels are NOT: none of **open**/**probed**/**weakened**
carries any proof content. Only **proved** and **refuted** do. The three
soft labels track the state of the *evidence*, so that later readers can
tell tested-and-survived from tested-and-dented from untested.

## Two things every entry must carry (added Stage 7)

Status answers "how well established is this?" It does not answer "should
anyone work on it?", and nine stages went into a conjecture where the answer
to the second question was no. Two further fields, each of which would have
caught that on its own:

- **Materiality** — does resolving this change a conclusion we care about?
  Borrowed from audit standards, which pair scope-honesty with a materiality
  test; this file had the first and not the second. **C1 is the worked
  example of failure**: fully resolved in either direction it says nothing
  whatever about universality, which is the program's actual question, so its
  materiality was LOW from Stage 0 and nobody asked.
- **Prior art** — has this been settled elsewhere? A one-line answer, or an
  explicit "not checked". **C1 is the worked example here too**: both halves
  were externally known and the check that found it took under an hour, in
  Stage 6. The register was applied to every fact the program LEANED on
  (Cocke–Minsky, Waldmann, Church, Barker) and to none of the facts it was
  trying to establish.

Rule going forward: no conjecture gets attacked before both fields are
filled. "Not checked" is an acceptable value; a blank is not.
Census methodology: leftmost-outermost reduction (`stepOnce`), which is the
normalizing strategy; "exhausted" verdicts are fuel-outs, NOT divergence proofs.
As of Stage 1, SK reduction is proven confluent (`confluence`,
`Confluence.lean`) with unique normal forms (`nf_unique`), and
`normalize` is certified on both ends (`normalize_sound`,
`normalize_normal`): when `normalize` reports a normal form, that term IS
the unique normal form of its input. (The classifier's LOOP — its
step-counting and cycle bookkeeping alike — remains unverified census
tooling built over the verified `stepOnce`.)
As of Stage 2, the S-fragment's conservation laws are machine-checked
(`SFragment.lean`): K-freeness is closed under reduction
(`KFree.of_step`), leaf count never decreases (`leafCount_le_of_steps` —
no erasure), and K-free normal forms are exactly the spine-≤2 shapes
(`SNF_iff`). Honest framing per the spec: these explain why naive
erasure-based encodings fail; they are NOT an impossibility argument —
the erasure-free λI-calculus is complete (Church 1941; Barendregt §9.5).
As of Stage 3, the universality definitions themselves are formal objects
(`Universality/Defs.lean`) over abstract rewriting systems (`RS.lean`),
with a machine-checked implication lattice (`Universality/Taxonomy.lean`)
and instances for SK, pure S, and the tag-system reference. See the
Definitions ledger below.
As of Stage 4, the taxonomy is calibrated in both directions —
negatively at the taxonomy level (`no_sim_SK_iota`), positively at the
classical level (`combinatory_completeness`, a theorem about TermV, not
routed through `Simulation`). The spec's calibration-sandwich criterion
(a) — the definitions certifying a known-universal system via an actual
`Simulation` inhabitant — remains open for Stage 5; the `Simulation`
class currently has no machine-checked nontrivial inhabitant. Concretely:
{S,K} combinatory completeness is machine-checked (`Bracket.lean`), and
the first-order reading of the one-combinator iota basis is
machine-checked NOT to host SK (`Universality/Calibration.lean`) — with
Barker's λ-level iota universality explicitly registered as external and
out of first-order scope. Simulations compose (`Simulation.comp`), so
universality transports along hosts (`UniversalReach.of_sim`).
As of Stage 5 Slice 1, Stage 2's monotonicity gets a second life: bounded
reachability between pure S-terms is a CERTIFIED per-instance decision
procedure (`reachable?`, `reachable?_correct`, `Reachability.lean`), the
convertibility question narrows to its true open core (non-normalizing
pairs, `Joinable`/`conv_iff_joinable`), and `Simulation` gets its first
nontrivial inhabitant (`pureS_in_SK`, `Universality/Calibration.lean`).
See the Stage 5, Slice 1 section below for the honest-scope register.
As of Stage 5 Slice 2, the program has its first resolved conjecture —
`no_pure_S_cycle` (`Isometric.lean`) proves C2 outright via a
head-weight measure (`tau`) — and the same acyclicity powers a
precisely-scoped, prize-adjacent refutation, `no_sim_SK_pureS`
(`Universality/Calibration.lean`): pure S cannot host SK under the
pinned `Simulation` class. See the Stage 5, Slice 2 section below for
the full mechanism and its scope.
As of Stage 5 Slice 3, a reconnaissance pass — by design, and stated
plainly here: it was built to produce maps, not resolutions, and no
conjecture status changes as a result of it — finds that the two C1
candidates are one leftmost-outermost step apart on a single trajectory,
records an honest negative on the census's own plateau-nesting reading of
C3 at n=7..9, registers C5 (conservation) and C6 (divergence density),
and consolidates both existing universality refutations behind one
axiom-free mechanism (`Simulation.refute_of_acyclic`). See the Stage 5,
Slice 3 section below.
As of Stage 5 Slice 4, an audit-and-widen slice, resolving nothing but
strengthening two things and repairing one. (1) Both universality
refutations were UNDER-claimed: the mechanism needs only injectivity and
path-preservation, never `bwd` and never step-count faithfulness, so it is
now stated for `PathEncoding` (`no_pathEncoding_SK_pureS`,
`no_pathEncoding_SK_iota`), with `Simulation.refute_of_acyclic` kept
unchanged as a corollary and the widening proved non-vacuous
(`pathEncoding_strictly_weaker`). The prize-adjacent claim sharpens to: if
S alone is universal, its encoding must be non-injective or must fail to
preserve reduction paths. (2) The C1 trajectory has a proved FROZEN HEAD —
`S A B` with `A` normal admits only steps inside `B`, so C1 relocates onto
a payload (`frozen_normalizes_iff`, `Invariants.lean`, axiom-free) that is
BIGGER than `c1`; structure gained, search space not. (3) C6 survived a
4× fuel test unchanged, and the ledger gained `probed`/`weakened` status
labels. C1, C3, C4, C5, C6 all remain open. See the Stage 5, Slice 4
section below.
As of Stage 5 Slice 5, **C1 is SPLIT and half of it is PROVED**. The
conjecture bundled two independent claims — existence (some pure-S term
diverges) and minimality (none with ≤ 6 leaves does) — and nine stages had
only ever attacked the bundle. Minimality is finite: 65 terms, each
normalizing in ≤ 4 steps. Its one obstacle was the `sTerms`-completeness
chain, blocked since Slice 1 and ranked FOURTH because nobody had noticed
what it gated. Bypassing the imperative enumerator's opacity — a
structurally-recursive `enum` with both directions proved (`enum_sound`,
`enum_complete`, `Census/Completeness.lean`) rather than another attempt to
make `sTermsTable` transparent — closes it: `no_small_divergence` proves
every K-free term with ≤ 6 leaves reaches a normal form, and
`seven_is_the_floor` gives the contrapositive. **C1(b): PROVED. C1(a):
still open.** This is the program's first proved POSITIVE result about pure
S; everything settled before it was negative or structural. C3, C4, C5, C6
unchanged. See the Stage 5, Slice 5 section below.

Runs behind this file (all `lake exe ccp <maxLeaves> <fuel>`, pure-S terms only,
no `K` leaves ever appear — `sTerms` enumerates over `Term.S` alone):

- `ccp 12 200` — full census, n = 1..12, fuel 200. (0.48s through n=8, ~10s
  through n=10, ~50s through n=11, completed n=12 in well under 10 minutes.)
- `ccp 9 1000` — fuel raised to 1000 at small n, to probe fuel-sensitivity of
  the exhausted-term growth rate. Ran 5 minutes, reached n=7 fully and stalled
  partway through n=8 (killed at the 5-minute mark, no full n=8/n=9 line).
- `ccp 10 1000` — attempted per the task brief; killed at the 10-minute mark
  with **zero** flushed output (stdout is fully block-buffered when redirected
  to a file, not a tty; the process never got far enough for even n=1's line
  to reach the file before it was killed). Reducing fuel to 200 (above) is
  what actually completed n=10 (and beyond). See LAB_NOTEBOOK.md for the
  runtime/tooling story.
- `ccp 10 800` (Slice 4) — fuel-sensitivity test for C6. Line-buffered via
  `stdbuf -oL` so the buffering trap above could not repeat; it did not.
  Reached n=1..8 in ~9 minutes and was abandoned mid-n=9: at fuel 800 the
  extremal trajectories hit ~2.3e9 (n=7) and ~2.7e9 (n=8) logical leaves,
  and `classify` computes `leafCount` on them. Replaced by a targeted
  `exhaustedCount` probe that skips `maxFinalLeaves` entirely and reached
  n=10 at both fuel values — see the C6 entry for the result and the
  reproduction snippet.

## C1: Smallest non-normalizing pure-S term — SPLIT into C1(a) and C1(b)
- Materiality: **LOW, and it always was.** Resolved either way, C1 says
  nothing about universality — the program's actual question. A
  non-normalizing state does feed `bareEncNorm_trivial`'s hypothesis, but that
  theorem is a negative control showing the UNPINNED definition measures
  nothing, so C1 supports a result about a definition the program discarded.
  This entry is the reason the materiality field exists.
- Prior art: **settled externally, both halves** (Wolfram; Wolfram Data
  Repository; Waldmann). Found in Stage 6, in under an hour, after nine
  stages. This entry is also the reason the prior-art field exists.

**Slice 5 restructuring.** As originally written, C1 bundled two logically
independent claims, and for nine stages every attempt went after the bundle:

- **C1(a) EXISTENCE** — some pure-S term has no normal form (concretely:
  `c1` diverges). Status: **probed (open)**.
- **C1(b) MINIMALITY** — no pure-S term with ≤ 6 leaves diverges, so 7 is
  the floor. Status: **PROVED** (`no_small_divergence`,
  `Census/Completeness.lean`).

Separating them was the whole trick. (b) is a FINITE claim — 65 terms
(1+1+2+5+14+42), each normalizing in at most 4 leftmost-outermost steps —
and its only obstacle was the `sTerms`-completeness chain that had been
sitting in the queue since Slice 1 at priority 4. Nobody had noticed that
chain gated half of the program's flagship conjecture, because the halves
were fused and the fused claim looked uniformly hard.

### C1(b): minimality — PROVED

`no_small_divergence` (`Census/Completeness.lean`): for every K-free `t`
with `leafCount t ≤ 6`, there is a `u` with `t ⟶* u` and `NormalForm u`.
Contrapositive `seven_is_the_floor`: a diverging pure-S term has at least 7
leaves. Axioms `[propext, Quot.sound]`, matching the tree's inherited pair;
no `native_decide`.

Mechanism, and how the old blocker was bypassed: rather than making
`sTermsTable`'s `Id.run do`/`Array`/range-loop definition transparent —
three prior attempts died there, and even `sTerms 1 = [S]` will not close
by plain `rfl` — a structurally-recursive enumerator `enum` was added
alongside it and BOTH directions proved about that (`enum_sound`,
`enum_complete`, `mem_enumAt_iff`). `enum` recurses on a depth budget,
which is what makes it structural where a two-sided size recursion is not.
The imperative `sTerms` is unchanged and still runs the census; the two are
tied by `#guard` (equal lengths and containment both ways for n ≤ 7), so
the verified enumerator is not a parallel universe. `enum_complete` then
places any small term in a finite list, a `decide`d `List.all` over sizes
0..6 discharges it, and Stage 1's `normalize_sound`/`normalize_normal`
certificates turn the `normalize` success into a genuine normal form.

This is the program's **first proved positive result about pure S**.
Everything settled before it was negative (two hosting refutations) or
structural (acyclicity, the consolidation, the frozen head).

**Stage 6 correction to the novelty claim.** The FACT is external too:
Wolfram's "at size 7 and above" states the threshold, which is exactly this
half of C1 (see C1(a) above for citations). So `no_small_divergence` is a
machine-checked proof of an externally-known fact — precisely the standing of
`combinatory_completeness` (classical) and, very likely, `no_pure_S_cycle`
(see C2). That is a legitimate contribution and it is what this project is
FOR (spec Goal 1 and Goal 4), but "first proved positive result" is a claim
about this tree's internal history, NOT a discovery claim, and the earlier
wording invited the stronger reading. Corrected here rather than deleted, so
the overreach stays visible.

WHAT IT IS NOT: not evidence that any pure-S term diverges. If pure S turns
out to be strongly normalizing, C1(b) stays true and C1(a) is simply false.
The two halves are independent in both directions.

### C1(a): existence — EXTERNAL (known in the literature)

**Stage 6 literature check — the finding that should have come first.** Both
halves of C1 were already settled externally, and this file had presented
them as open conjectures for nine stages. The check cost under an hour and
was never performed, despite this file maintaining a careful
external/internal register for every OTHER background fact it relies on
(Cocke–Minsky, Waldmann, Church/Barendregt, Barker).

What the literature says:

- Wolfram, *Combinators: A Centennial View* / the S Combinator Challenge
  materials: **"At size 7 and above there are S combinator expressions that
  do not terminate."**
- The Wolfram Data Repository resource *Non-Terminating Combinator
  Expressions* ships, as data, **"S combinator expressions of leaf counts 1
  through 10 that do not halt"**, with its worked example at leaf count 7.

So non-normalizing pure-S terms are known to exist, the threshold is known
to be 7 leaves, and the underlying decision technology is Waldmann's
(normalization of S-terms is decidable — RTA 1998 / *Information and
Computation* 159(1–2):2–21, 2000, already cited in this file's Background,
using rational/regular tree languages).

HONEST SCOPE OF THIS CHECK: the two Wolfram sources agree and are enough to
register the fact at **external** level — the same standing as every other
cited result here. What was NOT done: the explicit leaf-7 expressions were
not extracted from the dataset and compared term-by-term with `c1`/`c2`, so
"their non-halting terms are exactly ours" is UNVERIFIED. The agreement
established is on the threshold (7) and on existence, not on the identity of
the witnesses. Extracting the dataset would settle it and is cheap.

**What this changes.** C1(a) is transcription, not research. Formalizing it
means importing an argument that exists — most plausibly Waldmann's
procedure, or a direct non-termination witness — not discovering one. The
census independently rediscovered a known threshold, which is a genuine
(if modest) validation of the census tooling, and that is the honest way to
describe what Stage 0 achieved.

**What this does NOT change.** The Wolfram prize question is UNIVERSALITY,
not non-termination, and it remains open. Non-terminating S-terms existing
is background for the prize, not progress on it. Related external work to
register alongside `no_sim_SK_pureS`: F. Vatan, *On Universality of the S
Combinator* (arXiv:2210.12893, 2022), which argues K is not expressible in
terms of S alone — an informal-level cousin of this tree's precisely-scoped
`no_pathEncoding_SK_pureS`, not a substitute for it and not machine-checked
here.

Prior internal status, retained as the record of what the census could see
on its own: probed and CONSISTENT — fuel-insensitivity checked at a second fuel value
(800, Slice 4 — the n=7 exhausted count is still exactly 2), and the
trajectory's structure is now partly proved rather than observed (the
frozen head, below). Nothing has come back against it. It remains open:
every probe is still fuel-bounded, and no divergence proof exists.

Census (fuel N=200) finds all S-terms with ≤6 leaves normalize — now a
theorem, C1(b) above; at 7 leaves, 2 of 132 terms exhaust fuel. Candidates
(rendered, standard combinator notation, left-associative application):

```
S S S (S S) S S
S (S S) S S S S
```

Conjecture: `S S S (S S) S S` (equivalently, by the same evidence,
`S (S S) S S S S`) has no normal form under leftmost-outermost reduction —
i.e. `stepOnce` never reaches `none` from it.

Supporting (not proving) evidence: raising fuel from 200 to 1000 at n=7 does
not let either candidate normalize — instead the final term size at cutoff
explodes from 120112 leaves (fuel 200) to 25740409924 leaves (fuel 1000), a
~5-order-of-magnitude increase for a 5x fuel increase. That is consistent
with genuine unbounded/explosive growth along the trajectory, not with a
near-normal-form plateau that a little more fuel would resolve — but it
remains fuel-exhaustion, not a divergence proof.

**Slice 3 discovery:** the two candidates are not independent — `c2`
reduces to `c1` in exactly one leftmost-outermost step (`stepOnce c2 =
some c1`, kernel-checked `rfl`, `Reachability.lean`; hand-traced by
review). C1 effectively collapses to a single candidate: any future
divergence proof for one transfers immediately to the other, since their
trajectories coincide from that point on. This is a discovery about
adjacency, not about divergence — it does not by itself show a loop or
show non-termination; no divergence proof was attempted this slice —
deliberately; the loop route needs C5.

**Slice 4 discovery — the frozen head (PROVED, and it does not close
C1):** from step 8 onward every reduct of `c1` has the form `S A B` for one
FIXED 9-leaf normal form `A = S (S S) (S (S (S S) S) S)`
(`frozenArg`, `Invariants.lean`), and the shell is provably inert: a term
`S A B` with `A` normal admits ONLY steps inside `B` — neither head rule
can fire (spine length 2 < the 3 an S-redex needs, and the head is `S` not
`K`) and `S A` is itself stuck (`step_frozen`, `steps_frozen`). Hence
`frozen_normalizes_iff`: for normal `A`, `S A B` normalizes iff `B` does.
All of these are AXIOM-FREE and hold for every term under EVERY strategy,
not just leftmost-outermost.

What this buys and what it does not. C1 for `c1` is now exactly the
question "does this 15-leaf term normalize?" — the payload
`S (S (S S) S) S (S (S S) (S (S (S S) S) S))`. That is BIGGER than `c1`'s
7 leaves, so the relocation is a gain in structure, not a smaller search
space, and it is not progress toward a divergence proof by itself. What it
does give: the first proved (as opposed to observed) invariant of this
trajectory, and a general shell-stripping lemma for any future pure-S
divergence argument.

**Slice 4 negative — τ has nothing to act on here.** `isoRedexCount`
(size-preserving S-redexes, the exact fragment `tau` governs in
`Isometric.lean`) is 0 from step 6 onward on this trajectory. So the
machinery that RESOLVED C2 is inapplicable to C1 by measurement, not by
guesswork — a concrete answer to the obvious "why not just reuse τ?".

**Slice 4 negative — no recurrence at the frozen granularity.** Slice 3
hunted for `c1` itself recurring inside its own trajectory. That hunt
could not have succeeded once the head freezes: `c1` has spine length 5
and every reduct from step 8 on has spine length 2, so `c1` cannot appear
as a later reduct at all. Re-run at the right granularity — does any
frozen reduct recur as a subterm of a later one, from 20 starting points —
all 20 negative (`Invariants.lean`). The loop route still has no witness in
the explored prefix, now checked at a granularity where one could have
existed.

**Slice 3 strategy note:** neither candidate self-embeds (nor
cross-embeds, beyond the one-step relation just noted) within 120
leftmost-outermost steps (`isSubterm` guards, `Reachability.lean` —
fuel-bounded census data, three honest negatives). The loop route to C1(a)
therefore has no cheap witness in the explored prefix; the two live
routes are (a) a leftmost-outermost reduction invariant (a decidable
predicate preserved by `stepOnce`, implying reducibility — none known
yet; candidate features should be mined from trajectory data), and (b) a
loop witness deeper in the trajectory or under a different strategy,
combined with C5 (registered below) to upgrade a self-embedding into an
actual divergence proof.

## C2: No proper cycles in pure-S reduction — status: PROVED

**Resolved (Stage 5, Slice 2):** `no_pure_S_cycle` (`Isometric.lean`) —
for every K-free t there is no v with t ⟶ v and v ⟶* t. The theorem is
STRONGER than the census conjecture on both axes: any strategy (not just
leftmost-outermost) and any size (not just ≤ 12 leaves). Mechanism: any
cycle must preserve leaf count at every step (Stage 2 monotonicity
squeezed around the loop); a size-preserving K-free step is an S-redex
with atomic third argument; the head-weight measure τ (τ(app a b) =
2·τ(a) + τ(b)) strictly drops by 6 at every such redex
(`tau_lt_of_isometric_step`) and cannot return. Axioms: `#print axioms`
against the built tree — `tau_pos`, `KFree.leafCount_eq_one`,
`tau_lt_of_isometric_step`, `tau_lt_of_steps_size_eq`, and
`no_pure_S_cycle` all report `[propext, Quot.sound]` (the `Quot.sound` rides
core tactic machinery — `omega`/`simp` alone pull it in this toolchain — the
same inherited trail present since Stage 0's completeness lemmas; nothing
new to this slice). The τ
technique is standard term-rewriting technology (polynomial
interpretation); its application here may be folklore — the
machine-checked resolution is the contribution claimed.

**Stage 6 sharpening of that hedge, from the literature check:** it is not
merely "may be" folklore. Secondary sources on Waldmann's work state that he
studied CL(S) and showed **it admits no ground loops** — which is C2, or
close enough that C2 should be assumed external until someone reads the
paper and confirms the exact statement. Registered at **external** level
with that caveat: the primary source was not obtained (the Springer chapter
is paywalled and the redirect could not be followed), so the precise
relationship between `no_pure_S_cycle` and Waldmann's loop result is
UNCONFIRMED. What is unaffected: the τ proof here is axiom-light,
strategy-independent and size-independent, and it is machine-checked, which
is the contribution this project claims. What should change is the framing —
C2 was described as "the program's first RESOLVED conjecture", and resolved
is right while first-to-know is not.

The Slice 1
evaluator sweep and kernel instances (`onCycle?`, `ssss_not_on_cycle`,
`sssss_not_on_cycle`) remain in the tree as independent evidence paths
that now agree with the general theorem.

### History (pre-resolution census and Slice 1 text, superseded above)

The three paragraphs below are kept verbatim as the historical record of
how C2 stood before Stage 5 Slice 2; where they say "remains open" that
was accurate at the time of writing and is superseded by the PROVED
resolution above.

No S-term with ≤12 leaves revisits a previous term (leftmost-outermost,
fuel 200). Confirmed at every n = 1..12 (`No cycles found at any size (within
fuel).` printed by every run in this file's data). Conjecture: pure-S
leftmost-outermost trajectories never cycle. (NOTE: cycle-freedom under ALL
strategies is a stronger, separate claim; this census only ever runs
leftmost-outermost.)

**Proven constraint (Stage 2):** any K-free reduction cycle is
leaf-count-constant (`cycle_leafCount_eq`, `SFragment.lean`). Hence —
an immediate corollary on paper, not formalized — a cycle hunt may
restrict to size-preserving steps, i.e. S-redexes whose third argument
is a single leaf. C2 itself remains open.

**Stage 5 Slice 1 upgrade, with the epistemic level stated precisely:**
every pure-S term with ≤ 6 leaves is checked cycle-free at COMPILE TIME
via `onCycle?` and a `#guard` (`Reachability.lean`) — this is an
EVALUATOR-checked fact (Lean's untrusted `#guard` evaluator, per its own
doc comment), NOT a kernel proof. `onCycle?` itself is unverified census
tooling: its cycle-freedom reading additionally rides the proven-on-paper,
unformalized skip-larger-successors corollary of Stage 2 monotonicity
(noted at its definition in Reachability.lean). Separately, two CONCRETE instances (the
4-leaf term `S S S S` and the 5-leaf term `S S S S S`) are proven
cycle-free at the kernel level (two theorems in `Reachability.lean`,
`ssss_not_on_cycle` and `sssss_not_on_cycle`, each via `succs_complete`
pinning the sole successor, a `by rfl`-evaluated
`reachable? ... = some false`, and `reachable?_correct` lifting that to a
genuine `¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t)` fact) — these ARE kernel-checked. The
general theorem form (`no_small_cycle : ∀ t, KFree t → leafCount t ≤ 5 →
¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t)` — stated at ≤ 5 rather than the sweep's ≤ 6
because the theorem attempt deliberately targeted a smaller universe
first; the blocker below is size-independent) was attempted and
escape-hatched after 3 tries: it is blocked on an `sTerms`-completeness theorem (`∀ t, KFree t →
t ∈ sTerms (leafCount t)`) that does not yet exist, which is itself
blocked on `sTermsTable`'s imperative `Id.run do`/`Array`/range-loop
definition not being `rfl`/`decide`/`simp`-transparent at the needed
generality — confirmed concretely: even `sTerms 1 = [S]` does not close
by plain `rfl`. Fixing this chain would likely mean reimplementing
`sTermsTable` in a structurally-recursive style (with a proven-equal
imperative version kept for performance) or proving a general unfold
lemma for the `for`-loop first. Registered as a blocked chain, queued
alongside the reachability pigeonhole item (see the Stage 5, Slice 1
section) — not claimed as a theorem. C2 in full remains open.

## C3: Growth-pattern regularities observed — RETIRED (closed as artifact)

**Stage 6: closed, not carried.** C3 was never a conjecture about pure S —
its own title says "regularities *observed*", and both regularities are
properties of the fuel-200 census cutoff rather than of S-reduction. Both
halves were probed, both probes came back against them (details retained
below), and continuing to carry an entry in this state invites re-probing
something the evidence already leans against. Retired with the data kept as
the record.

Anything genuinely at stake here was absorbed elsewhere: the "explosive
growth" content lives in C1(a) and C6; the argmax structural question is
answered negatively at n=7..9 and would need the n≥10 argmaxes recomputed
(runtime-prohibitive) to say more; and the spine-length observation was
superseded outright by Slice 4's frozen head, which shows spine length is a
property of the STARTING term that does not survive its own trajectory.

Re-labelled WEAKENED in Slice 4 before retirement here. Neither half is
refuted — these are observations whose motivating reading lost support, not
false claims.

- **C3.1 (head shape) — weakened by sample collapse, twice over.** Slice 3
  showed the two n=7 "samples" are adjacent points on ONE trajectory
  (`stepOnce c2 = some c1`), making this a sample of one. Slice 4 adds a
  second dent: `spineLength 5` is a property of the STARTING term only and
  does not survive its own trajectory — spine length locks at 2 from step 8
  onward (`Invariants.lean`). Whatever "head applied to 5 arguments" is
  tracking, it is not a persistent feature of divergent behavior.
- **C3.2 (maxFinalLeaves plateau) — weakened** by Slice 3's plateau-nesting
  probe: every structural check at n=7..9 came back false and the deltas
  explode instead of staying near +1. See the probe write-up below.

Two observations from the fuel=200, n=1..12 run:

1. **Head shape of the smallest exhausted terms.** Both n=7 candidates are a
   head `S` applied to exactly 5 arguments (`spineLength` 5) — two more than
   the 3 arguments an `S`-redex needs to fire. (`S S S (S S) S S` = `S`
   applied to `S, S, (S S), S, S`; `S (S S) S S S S` = `S` applied to
   `(S S), S, S, S, S`.) Sample size is only 2 terms, so this is a weak
   signal, not yet checked against the fuller n=8 exhausted set (41 terms;
   this census run does not print more than the first exhausted size's
   candidates, capped at 10 — see `Main.lean`'s `censusLine`). (Slice 3
   later showed these two "samples" are adjacent points on ONE
   trajectory — `stepOnce c2 = some c1` — so this is effectively a
   sample of one.)

2. **`maxFinalLeaves` plateaus once n ≥ 10 (fuel fixed at 200).** The largest
   final size any fuel-exhausted trajectory reaches, per n:

   | n  | maxFinalLeaves | maxSteps |
   |----|----------------|----------|
   | 7  | 120112         | 15       |
   | 8  | 390363         | 15       |
   | 9  | 2849113        | 86       |
   | 10 | 88163896       | 109      |
   | 11 | 88163897       | 173      |
   | 12 | 88163898       | 174      |

   From n=10 to n=12 `maxFinalLeaves` increases by exactly 1 leaf per unit of
   n, while at fixed fuel it had grown by roughly 30x from n=9 to n=10.
   Conjecture (tentative, unexplained): once n is large enough, the
   trajectory that saturates 200 fuel steps is essentially the same
   explosive expansion regardless of which (n-leaf) starting term achieves
   it, with the extra starting leaves surviving un-reduced off to the side —
   this is an observation about the fuel=200 cutoff, not a claim about
   unbounded fuel behavior, and it is not yet explained by any proved lemma.

**Slice 3 probe (fuel-bounded census data, fuel 200, n = 7..9):** the
max-final-size terms at consecutive sizes are **NOT** structurally
nested — no nesting relation was observed. The three argmax terms
(each found by scanning `sTerms n` and keeping the term whose 200-step
`trace` ends at the largest `leafCount`) are:

```
n=7: S S S (S S) S S              (final leafCount 120112)
n=8: S S S (S (S S S)) S          (final leafCount 390363)
n=9: S (S S) S (S (S S S) S)      (final leafCount 2849113)
```

The n=7 argmax is exactly `c1` (`Reachability.lean`'s named C1 candidate,
confirmed by `==`, not just matching render strings) — the smallest
fuel-exhausted term is also the term whose trajectory grows biggest by
step 200, at this size. But that is where the relation stops: `isSubterm`
(from Task 1) finds the n=7 argmax is NOT a subterm of the n=8 argmax,
and the n=8 argmax is NOT a subterm of the n=9 argmax (both directions
checked; also checked and false: the n=7 argmax is not a subterm of the
n=9 argmax either, ruling out a relation that skips a step). Neither
`app argmax(n) S` nor `app S argmax(n)` (the two "rider" shapes) equals
argmax(n+1) at either transition. A broader sweep also came back empty:
neither C1 candidate (`c1` nor `c2`) occurs as a subterm anywhere inside
the n=8 or n=9 argmax terms. So **(a)** argmax(n+1) is structurally
unrelated to argmax(n) at n = 7..9 — no app-with-rider shape, no subterm
nesting in either direction, and no recurrence of the C1 candidates
themselves inside the later argmaxes.

**(b)** the final-leaf-count deltas between consecutive n are emphatically
NOT small/constant here: +270251 (n=7→8) and +2458750 (n=8→9) — roughly
3x and then 7x multiplicative jumps, the opposite of the n=10..12 "+1"
pattern. This means the "+1" plateau behavior documented above is NOT
yet present at n = 7..9: whatever mechanism makes the n≥10 argmaxes
converge onto (what looks like) a single shared extremal trajectory has
not kicked in by n=9 — each of n=7, 8, 9 still finds a genuinely
different, unrelated extremal term, with final size still exploding
between them. The n=10..12 plateau reading — "a single extremal
trajectory family with rider leaves" — is **not corroborated** by this
probe; if anything it is weak evidence that the plateau is a threshold
phenomenon starting somewhere between n=9 and n=10, not a pattern visible
across the whole n≥7 range. The n=10..12 argmax terms themselves were not
recomputed (runtime cost, per the brief) so the actual n=9→10 transition
(nested or not) remains unobserved — this probe only establishes that
n=7,8,9 do not already exhibit it.

Reproduce with (argmax scan, repeated for `sTerms 7/8/9`; `getLastD t`
used in place of `getLast!` since `Term` has no `Inhabited` instance):

```lean
#eval (sTerms 9).foldl (fun (best : Term × Nat) t =>
  let fl := leafCount ((trace 200 t).getLastD t)
  if fl > best.2 then (t, fl) else best) (Term.S, 0)
```

and the relation checks:

```lean
#eval m7 == c1                  -- true
#eval isSubterm m7 m8           -- false
#eval isSubterm m8 m9           -- false
#eval isSubterm m7 m9           -- false
#eval m8 == Term.app m7 S       -- false
#eval m8 == Term.app S m7       -- false
#eval m9 == Term.app m8 S       -- false
#eval m9 == Term.app S m8       -- false
#eval isSubterm c1 m8 -- false; #eval isSubterm c2 m8 -- false
#eval isSubterm c1 m9 -- false; #eval isSubterm c2 m9 -- false
```

(where `m7`, `m8`, `m9` are the three argmax terms rendered above, built
the same way `c1`/`c2` are — `Term.app` nestings matching the rendered
strings.)

## Definitions ledger (Stage 3)

Universality is relative to a reference system R and an observation mode
(Universality/Defs.lean). Designated reference: deletion-number-2 tag
systems (`RS.Tag`, arbitrary symbol alphabet) — m = 2 tag systems over
finite alphabets are universal by Cocke–Minsky 1964, an EXTERNAL fact
cited, not machine-checked. All three Universal* definitions
(`UniversalReach`/`UniversalNorm`/`UniversalConv`) quantify over the
pinned `Simulation` class — uniform encoder, decoder-inversion,
`fwd`/`bwd` (note: `fwd` was always MANY-step, `A.step a a' → B.Steps
(enc a) (enc a')`, so "step-faithful" was never quite the right word for
it; Slice 4 replaced that wording throughout) — never over bare encoding
functions. The
bare-function variant is machine-checked to be trivial
(`bareEncNorm_trivial`, Universality/Defs.lean): a classical oracle
encoder witnesses it for ANY source system (given the host has one
normalizing and one non-normalizing state), so an unpinned definition
measures nothing. Computability of encoders is NOT internally pinned (no
computability theory in a zero-dependency setting) — an explicit,
registered limitation.

Proven lattice edges (Universality/Taxonomy.lean): simulations preserve
convertibility unconditionally (`Simulation.conv_preserve`); they reflect
it when the host is Church–Rosser and image-closed
(`Simulation.conv_reflect`); they preserve normalization under
normal-form correspondence (`Simulation.normalizes_preserve`); one such
simulation into a Church–Rosser, image-closed host already witnesses
Conv-universality (`Simulation.toUniversalConv`). SK is Church–Rosser in
RS-language (`RS.SK_churchRosser`, riding Stage 1).

Status of `UniversalReach (RS.Tag T) — / UniversalNorm — / UniversalConv —`
for each host:

| Host        | Reach (Simulation)    | Norm                  | Conv |
|-------------|-----------------------|-----------------------|------|
| `RS.SK`     | open (Stage 4 target) | open                  | open |
| `RS.PureS`  | open (prize-adjacent) | open, expected FALSE¹ | open |

¹ With the definitions now pinned (`UniversalNorm` ranges over
`Simulation`, not bare functions), the external expectation is that this
cell is FALSE for any reference R with undecidable halting: Waldmann 2000
shows pure-S normalization is decidable, so a COMPUTABLE encoder making
normalization agree would make R's halting decidable — killing every
computable step-faithful encoding. Both ingredients stay external:
Waldmann's decidability result is not machine-checked here, and encoder
computability is not internally pinned (see above), so the cell is
registered open-expected-false, not refuted. The BARE-function variant of
this cell is not worth a register entry at all: `bareEncNorm_trivial`
(Universality/Defs.lean) proves it holds for ANY source once the host has
one normalizing and one non-normalizing state (for pure S the latter's
existence is exactly **C1(a)** — so the unpinned cell tracks C1(a), not
universality, which is precisely why it was replaced. Note this is the
existence half specifically; C1(b), now proved, is no help here — a
non-normalizing state is exactly what minimality does not supply).

No cell of this table is a theorem yet; the table is the register the
spec's Stage 3 success criterion requires ("proven or explicitly open").

Updated table (Stage 4):

| Host        | Reach (Simulation)                          | Norm                  | Conv |
|-------------|----------------------------------------------|-----------------------|------|
| `RS.SK`     | combinatory completeness proven at TermV level (`combinatory_completeness`, `Bracket.lean`); Tag→SK still open | open | open |
| `RS.Iota`   | open in general² | open | open |
| `RS.PureS`  | REFUTED vs SK (`pureS_not_universalReach_for_SK`)³; open vs Tag (prize-adjacent) | REFUTED vs SK (`pureS_not_universalNorm_for_SK`)³; open vs Tag, expected FALSE¹ | REFUTED vs SK (`pureS_not_universalConv_for_SK`)³; open vs Tag |

² Against reference SK, ALL THREE observation modes fall for first-order
iota: `no_sim_SK_iota` refutes `UniversalReach RS.SK RS.Iota`, and since
`UniversalNorm`/`UniversalConv` also quantify over `Simulation`, `¬
UniversalNorm RS.SK RS.Iota` and `¬ UniversalConv RS.SK RS.Iota` are
immediate corollaries (one line each from `no_sim_SK_iota` — stated
here, not added to the tree; the same growth argument would refute
Tag→Iota for any tag system with a genuine reduction cycle, not
formalized). Against the table's own reference, `RS.Tag`, none of the
three cells is refuted — the Iota row is open in general against `RS.Tag`.

³ Against reference SK, ALL THREE observation modes fall for pure S too,
by the mirror-image mechanism (acyclicity instead of strict growth —
see the Stage 5, Slice 2 section below): `no_sim_SK_pureS`
(`Universality/Calibration.lean`) refutes `UniversalReach RS.SK
RS.PureS`, with `pureS_not_universalNorm_for_SK` and
`pureS_not_universalConv_for_SK` as immediate named corollaries (all
three quantify over `Simulation`). SCOPE — **widened in Slice 4, see the
Slice 4 section**: the refutation does not actually need step-faithfulness
or `bwd`. What is ruled out is any INJECTIVE, PATH-PRESERVING encoding
(`no_pathEncoding_SK_pureS`), a strictly larger class than `Simulation`.
It still does NOT resolve the Wolfram prize question — an informal
universal encoding could be non-injective (merging states) or
non-path-preserving — but those are now the only two escape hatches left,
rather than the vaguer "non-step-faithful". Against the table's own
reference, `RS.Tag`, this cell remains open — the same acyclicity
mechanism would refute Tag→PureS for any tag system with a genuine
reduction cycle, not formalized here.

### Stage 4 calibration results

- **Positive:** {S,K} is combinatorially complete
  (`combinatory_completeness`, `Bracket.lean`): every single-variable term
  over {S,K,·} is realized by a closed combinator, via naive bracket
  abstraction (`bracket_beta`). This is the classic sense in which S and K
  suffice; the Tag→SK Reach cell below remains open (encoding a reference
  machine is Stage 5-adjacent work).
- **Negative (machine-checked):** `UniversalReach RS.SK RS.Iota` — Reach
  with SK as the REFERENCE (not the ledger's designated `RS.Tag`
  reference) — is **REFUTED** (`no_sim_SK_iota`,
  `Universality/Calibration.lean`): every
  first-order iota step strictly grows leaf count (`iota_step_lt`), SK has
  an explicit 5-step reduction cycle (Ω = (SII)(SII)), and no injective
  encoding survives both. IMPORTANT SCOPE: this refutes the FIRST-ORDER
  reading of ι (`RS.Iota` as defined). Barker's one-combinator
  universality is a λ-calculus (higher-order, erasing) result — external,
  NOT contradicted, and not capturable by a first-order applicative rule
  like `RS.Iota`'s (the RS framework itself could express λβ with
  binder/substitution machinery — that formalization simply isn't in
  scope here). The taxonomy just drew that boundary precisely.
- **Deviation register (spec-sanctioned):** (1) the spec's "universality
  of iota under the taxonomy" deliverable became the refutation above —
  the finding forced it; (2) the spec's "confirm formally that Waldmann's
  result kills only the normalization-based definition" takes the spec's
  own Risks-section downgrade: Waldmann 2000 remains cited-not-formalized
  (a formal kill needs a computability theory; zero-dep constraint).
  The λI ({S,B,C,I}) stretch goal was not attempted this stage.

## C4: No single-rule first-order combinator basis hosts SK — REDUCED
**Status: semantic core PROVED; syntactic residue open.**
- Materiality: **HIGH** — it is a claim about a CLASS of encodings and hosts,
  so it lives at the taxonomy level, which is where this program's
  comparative advantage is. Resolving it changes what the taxonomy can say
  about systems nobody has examined individually.
- Prior art: **none found.** The Stage 6 literature check turned up external
  answers for C1 and probably C2; it found nothing for C4. As of Stage 7 this
  is the one conjecture on the list that is both open and unambiguously ours.

**Stage 7 — the semantic core, PROVED.** C4 bundles a semantic claim with a
syntactic class, exactly as C1 bundled existence with minimality, and the
semantic claim is the whole mathematical content:

`no_pathEncoding_SK_of_strict_measure` (`Universality/Calibration.lean`) — no
host whose every step strictly increases some Nat-valued measure can
path-encode SK, with `no_sim_SK_of_strict_measure` as the `Simulation`-level
corollary. Engine: `RS.Acyclic.of_strict_measure` (`Taxonomy.lean`) plus SK's
Ω ↔ M cycle. This is STRONGER than C4 in the semantic direction — it holds
for any host with such a measure, one-combinator or not — and it confirms the
generalization was the right one, since `RS.Iota_acyclic` and Stage 4's
refutation are both recovered as one-line instances. Strict growth was never
a property of ι; it was a property of ι's measure.

**The syntactic residue, stated precisely so this is not read as resolved.**
C4 as WRITTEN quantifies over "one-combinator, single-rule, first-order
systems whose rule is strictly size-increasing on every instance." Nothing in
this tree formalizes that class: there is no datatype of rewrite-rule
schemas, no matching, no substitution for rule variables. Closing C4 as
written needs (i) that formalism and (ii) a proof that every system in the
class has a strictly growing leaf-count measure — at which point (ii) feeds
the theorem above and C4 falls out. So C4 is **reduced to a formalization
task with the mathematics already done**, which is a different and better
position than "open", but it is not proved.

Original conjecture text follows. `no_sim_SK_iota` refutes iota specifically,
via strict growth. Conjecture:
the argument generalizes — any ONE-combinator, single-rule, first-order
system whose rule is strictly size-increasing on every instance (each
rule variable occurs at least once in the reduct AND the reduct is
strictly larger even at the minimal instantiation — true of ι, whose
smallest redex goes 2 → 10 leaves; false of S, whose redex is
size-preserving when the third argument is a single leaf) cannot host SK
under `Simulation`. (Compare pure S — non-erasing but size-PRESERVING
steps exist at the minimal instantiation, so this class excludes S by
construction and the argument does NOT apply to it; C2's cycle question
needed the separate τ-measure route — resolved by `no_pure_S_cycle`
(Stage 5, Slice 2).)

(C5 was reserved and had not yet been registered — closed below, Stage 5
Slice 3, per the reviewer note on Task 2.)

## C5: Conservation for pure S (WN ⇒ SN) — status: external (open here)
- Materiality: **LOW as leverage, MEDIUM as a deliverable.** Its stated
  purpose was to upgrade a C1 loop witness into a divergence proof — and C1(a)
  is now external, so that purpose is gone. What remains is its value as a
  formalization under spec Goals 1 and 4, plus the unbounded-trajectory
  corollary.
- Prior art: **settled externally** — the λI conservation theorem, Church
  1941 / Barendregt §9.5, cited in this file since Stage 2. Re-labelled
  **external** in Stage 7 for consistency: it was always a known classical
  theorem, and calling it "open" conflated "we haven't done it" with "nobody
  has." Formalizing it is transcription.

In erasure-free calculi, weak normalization implies strong normalization
(the λI conservation theorem — Church 1941 territory; Barendregt §9.5 has
the modern treatment). Pure S is erasure-free (Stage 2), so conservation
SHOULD hold — but it is not formalized here, and nothing in this tree
depends on it yet. WHY IT MATTERS: it is the missing link of the loop
route to **C1(a)** — a self-embedding t →⁺ C[t] yields an infinite reduction;
conservation would upgrade that to "no normal form." Without it, a loop
proves only the existence of one infinite trajectory. Registered as a
future-slice target; classical proof routes exist (external), none
machine-checked here.

**Corollary registered alongside (statement ready, dependency noted):**
every infinite pure-S trajectory has unbounded size — bounded size plus
`no_pure_S_cycle` plus the finiteness of each size class would force a
revisit. Blocked on the same finiteness lemma as the pigeonhole queue
(`sTerms`-completeness chain); registered, not claimed.

## C6: Divergence density grows with size — status: probed (open)
- Materiality: **LOW.** A density asymptotic over small n bears on nothing
  else in this tree; no theorem depends on it and it does not touch
  universality. It is cheap and it is genuinely ours, and Stage 7's ranking
  deliberately does NOT promote it on those grounds — cheapness is precisely
  what made C1 attractive for nine stages.
- Prior art: **not checked** for the density asymptotic specifically. Adjacent
  work certainly exists (Wolfram's dataset covers leaf counts 1–10 and would
  give the same counts); whether the monotone-to-1 conjecture is settled is
  unknown. Checking is cheap and should precede any further work here.


**Slice 4 fuel-sensitivity test — the table is NOT an artifact of fuel
200.** This was the cheapest open item on the board and the most exposed:
every row was measured at a single fuel value, so the whole table could
have been reporting "how many terms need more than 200 steps" rather than
anything about divergence. Re-measured at fuel **800** (a 4× increase), the
exhausted counts are *identical*:

| n  | exhausted @ fuel 200 | exhausted @ fuel 800 |
|----|----------------------|----------------------|
| 7  | 2                    | 2                    |
| 8  | 41                   | 41                   |
| 9  | 276                  | 276                  |
| 10 | 1484                 | 1484                 |

Not one term of the 6,853 at n = 7..10 moved from "exhausted" to
"terminating" between fuel 200 and fuel 800. That is real support for the
conjecture: the fraction is measuring a stable property of the terms, and
the fuel-200 rows below can be read as divergence density rather than as a
cutoff artifact. It remains support, not proof — every one of these is
still a fuel-out, and fuel-insensitivity at 4× says nothing about
unbounded fuel. This test also independently REPRODUCED both counts the
table below had been citing from LAB_NOTEBOOK.md without recomputation
(276 at n=9, 1484 at n=10); the caveat attached to those two rows is
discharged.

Reproduce (cheaper than the full census — it skips the `leafCount` of the
final term, which is what makes `classify` expensive at high fuel):

```lean
def exhaustedCount (fuel n : Nat) : Nat :=
  (sTerms n).foldl
    (fun acc t => if (normalize fuel t).isNone then acc + 1 else acc) 0
#eval exhaustedCount 800 9    -- 276,  same as fuel 200
#eval exhaustedCount 800 10   -- 1484, same as fuel 200
```

RUNTIME NOTE, since it shaped what got measured: the full
`lake exe ccp 10 800` was started first and abandoned after ~9 minutes,
having completed only n=1..8 — at fuel 800 the extremal trajectories reach
logical sizes of ~2.3e9 leaves (n=7) and ~2.7e9 leaves (n=8), and
`classify` computes `leafCount` on those. Terms are shared DAGs in memory,
so they FIT; counting their leaves is what costs. Dropping `maxFinalLeaves`
from the measurement is what made n=9 reachable at all.

Fraction of pure-S terms at exactly n leaves that exhaust fuel 200
(leftmost-outermost; fuel-outs are NOT divergence proofs — this is a
density of *fuel-exhaustion*, a proxy observable). Exhausted counts for
n=7,8,11,12 and totals for n=7,8,9,10,11,12 are as already recorded in
this file / LAB_NOTEBOOK.md. The n=9 and n=10 exhausted counts were
originally pulled from LAB_NOTEBOOK.md's census-headline entry rather than
recomputed; **Slice 4's `exhaustedCount` probe recomputed both (276, 1484)
and they agree**, so that caveat no longer applies to those two rows. The
n=11 and n=12 rows remain as-recorded — 16,796 and 58,786 terms, still the
"runtime-prohibitive" case, and untested for fuel-sensitivity.
Per-n totals are the Catalan numbers (binary trees with n leaves = C_(n-1);
documented at `Census/Enumerate.lean`'s `sTermsTable` comment) and were
cross-checked cheaply via `#eval (sTerms n).length` (no fuel/reduction
involved, so this is not the disallowed recomputation):

| n  | exhausted / total | fraction |
|----|--------------------|----------|
| 7  | 2 / 132            | 1.5%     |
| 8  | 41 / 429           | 9.6%     |
| 9  | 276 / 1430         | 19.3%    |
| 10 | 1484 / 4862        | 30.5%    |
| 11 | 6842 / 16796       | 40.7%    |
| 12 | 29337 / 58786      | 49.9%    |

Conjecture: the fraction is monotone non-decreasing in n and → 1. All six
rows above are monotone increasing, consistent with the conjecture, but
six points is a short run — nowhere near n large enough to see whether
growth keeps accelerating, levels off short of 1, or enters some different
regime at larger n. (The C3 addendum used to be cited here as a reason to
expect a regime change at n≥10, on the strength of the `maxFinalLeaves`
plateau; C3.2 is now **weakened**, so that expectation has lost its
support and should not be leaned on either way.)

The fuel-sensitivity worry that stood over this table is now DISCHARGED
for n = 7..10 — see the fuel-800 comparison at the top of this entry.
What remains genuinely untested: n = 11, 12 at a second fuel value, and
any n beyond 12 at all.

Reproduce the total-count cross-check with:

```lean
#eval (sTerms 9).length   -- 1430
#eval (sTerms 10).length  -- 4862
```

(the n=11 and n=12 exhausted counts come from the `lake exe ccp 12 200` run
already on record — see the "Runs behind this file" note above and
LAB_NOTEBOOK.md's census-headline entry — not from a scratch re-run. The
n=7..10 counts were recomputed in Slice 4 at two fuel values.)

### Stage 5, Slice 1: bounded reachability

- **The north-star question moves.** The spec's Goal 3 — is reachability
  t ⟶* u between pure S-terms decidable? — is now answered per-instance
  by a CERTIFIED decision procedure (`reachable?`, `reachable?_correct`,
  `Reachability.lean`): monotonicity (Stage 2's `leafCount_le_of_steps`)
  confines every path inside the finite universe of terms with at most
  `leafCount u` leaves, so a saturated `boundedClosure` (built from `succs`/
  `succs_sound`/`succs_complete`, saturation witnessed by
  `mem_closureStep`/`boundedClosure_sound`/`boundedClosure_subset`/
  `boundedClosure_saturated`/`mem_of_saturated`) decides. Every `some`
  answer is a theorem-backed verdict (for K-free `t`); `none` is fuel
  exhaustion and verdicts nothing. HONEST SCOPE: the abstract `Decidable (t ⟶* u)`
  instance needs one more ingredient — a finite-pigeonhole argument that
  sufficient fuel always saturates — queued as the next slice, not
  claimed here. FOLKLORE CAVEAT: the paper-level observation
  (monotone size ⇒ bounded search) is two lines given Stage 2 and may
  well be known in the rewriting literature; the machine-checked
  procedure and certificates are the contribution claimed.
- **Convertibility narrows to its true open core** (`Joinable`,
  `conv_iff_joinable`, `joinable_normalizes`, `joinable_iff_nf_eq`):
  convertibility of normalizing pairs reduces to normal-form equality;
  a normalizing term is never convertible with a non-normalizing one
  (contrapositive of `joinable_normalizes`); the open frontier is
  exactly: convertibility of two NON-normalizing S-terms.
- **C2 upgraded at small sizes, epistemic level stated precisely:**
  cycle-freedom for all pure-S terms with ≤ 6 leaves is EVALUATOR-checked
  at compile time (`onCycle?` + `#guard`, `Reachability.lean` — Lean's
  untrusted evaluator, NOT a kernel proof), upgrading the census's
  fuel-bounded observation. `onCycle?` itself is unverified census tooling:
  its cycle-freedom reading additionally rides the proven-on-paper,
  unformalized skip-larger-successors corollary of Stage 2 monotonicity
  (noted at its definition in Reachability.lean). Separately, two concrete instances (`S S S S`,
  `S S S S S`) are additionally proven cycle-free at the KERNEL level
  (see the C2 entry above for the exact theorem chain). The general
  theorem form (`no_small_cycle`) is blocked on `sTerms`-completeness,
  itself blocked on `sTermsTable`'s `Id.run do`/`Array`/range-loop
  definition not being `rfl`/`decide`/`simp`-transparent — registered as
  a blocked chain, queued for the next slice alongside the reachability
  pigeonhole item. C2 in full remains open — superseded: C2 PROVED in
  Slice 2, see the C2 entry.
- **`Simulation` is nontrivially inhabited** (`pureS_in_SK`): the pure-S
  fragment embeds in SK by inclusion, with the decoder re-checking
  K-freeness (decidable by Stage 2), and a concrete `RS.PureS.step`
  witness (`S S S S → (S S)(S S)`) confirms the embedding carries real
  dynamics, not a vacuous inclusion. The calibration-sandwich criterion
  (a) at last has a machine-checked instance — modest, but real; a
  known-universal-system certification remains open (Tag→SK).

**Next-slice queue (both items registered here, not attempted this
slice):** (1) the finite-pigeonhole saturation-existence argument needed
to promote `reachable?` from a per-instance certified procedure to the
abstract `Decidable (t ⟶* u)` instance; (2) the `no_small_cycle` blocked
chain above (`sTerms`-completeness, itself blocked on `sTermsTable`
transparency) — a separate gap, but one that also blocks any future
theorem-level (as opposed to per-instance/evaluator-level) generalization
of C2 — NOTE (Slice 2): `no_pure_S_cycle` resolved C2's generalization
WITHOUT this chain; the chain remains queued only for the
pigeonhole/`Decidable` item.

### Stage 5, Slice 2: the isometric fragment

- **C2 is the program's first resolved conjecture** (see C2 above).
- **Prize-adjacent refutation, precisely scoped:** `no_sim_SK_pureS`
  (`Universality/Calibration.lean`) — under this taxonomy's pinned
  Simulation class, pure S cannot host SK: SK's explicit Ω ↔ M reduction
  cycle cannot be carried by an injective encoding into a system that
  `no_pure_S_cycle` proves cycle-free. All three observation modes fall
  together as named theorems (`pureS_not_universalReach_for_SK`,
  `pureS_not_universalNorm_for_SK`, `pureS_not_universalConv_for_SK`),
  since all three quantify over `Simulation`. SCOPE — read before
  quoting: this does NOT resolve the Wolfram prize question, whose
  informal universality admits broader encodings than step-faithful
  simulation. What is now machine-checked: **if S alone is universal,
  its encoding must do non-step-faithful work.** The taxonomy has
  located the prize question in the gap between the pinned class and
  the informal one — which is exactly the definitional territory the
  program was built to map. (SUPERSEDED IN SLICE 4, and in the
  strengthening direction: the refutation never needed step-faithfulness.
  The correct reading of the italicized sentence is now **if S alone is
  universal, its encoding must be non-injective or must fail to preserve
  reduction paths.** See the Slice 4 section.)
- **The refutation mechanism, unified:** iota fell to strict growth
  (Stage 4); pure S falls to acyclicity (this slice). Both are instances
  of one pattern — a system whose reduction order admits no return trips
  cannot host a cyclic source under injective path-preserving encoding
  (Slice 4 corrected "step-faithful" to "path-preserving" here — the
  weaker and accurate hypothesis).
  C4's strictly-size-increasing class is one cause of no-return; τ-style
  termination of the isometric fragment is another. (C4's statement is
  unchanged; this remark widens the observed pattern, not the
  conjecture.)

### Stage 5, Slice 3: the invariant observatory

Reconnaissance slice — by design it produced maps and one consolidation
theorem, and resolved nothing (as planned; no conjecture status changes
this slice except the additions below):
- **Self-embedding hunt on the C1 candidates:** no self-embedding or
  cross-embedding loop witness within 120 leftmost-outermost steps
  (`isSubterm` guards, `Reachability.lean`) — three honest negatives.
  The one positive result found instead was a discovery, not a loop: `c2`
  reduces to `c1` in exactly one leftmost-outermost step (`stepOnce c2 =
  some c1`, kernel-checked), collapsing the two candidates onto a single
  trajectory. See the C1 entry above for the strategy note this drives.
- **C3 plateau-nesting probe:** NOT corroborated at n=7..9 — all
  structural checks (subterm nesting in either direction, both
  skip-a-step and rider-append shapes, recurrence of `c1`/`c2` as
  subterms) came back false, and the final-leaf-count deltas explode
  (+270251, then +2458750) rather than staying small. The n=7 argmax IS
  `c1` exactly, but that coincidence does not propagate to n=8 or n=9.
  n=10..12 remains agnostic (argmaxes not recomputed, runtime cost). See
  the C3 entry above for the full data.
- C6 registered (divergence density, 1.5% at n=7 rising monotonically to
  49.9% at n=12, six points, fuel-bounded — see the C6 entry above).
- **Consolidation theorem:** `Simulation.refute_of_acyclic`
  (`Universality/Taxonomy.lean`) — an injective path-preserving encoding
  cannot carry a two-point cycle into an acyclic host (stated for
  `Simulation` in this slice; Slice 4 restated it at its true strength for
  `PathEncoding` and kept this name as a corollary). `RS.PureS_acyclic`
  and `RS.Iota_acyclic` (`Universality/Calibration.lean`) instantiate it;
  both existing refutations (`no_sim_SK_pureS`, `no_sim_SK_iota`) are
  recovered as one-line `example`s, originals unchanged. Axioms:
  `Simulation.refute_of_acyclic` is AXIOM-FREE (the generic mechanism
  depends on nothing beyond the `Simulation`/`RS.Acyclic` definitions);
  the two instances, `RS.PureS_acyclic` and `RS.Iota_acyclic`, each carry
  `[propext, Quot.sound]` (inherited from `no_pure_S_cycle`/`iota_step_lt`
  respectively, not new to this consolidation).
- C5 (conservation, WN ⇒ SN for pure S) and the unbounded-trajectory
  corollary registered with dependencies (see the C5 entry above) —
  neither is formalized; both are future-slice targets the loop route to
  C1 will need.

**Maps, not resolutions:** this slice's five probes/registrations
(embedding hunt, plateau-nesting probe, C6, the consolidation theorem,
C5-plus-corollary) were scoped from the start to produce reconnaissance
data and one structural theorem, not to close C1, C3, or C6 — and none
of them did. C1 and C3 remain open, C6 is open from first registration
(status labels as of Slice 3; Slice 4 re-labelled C1 and C6 **probed** and
C3 **weakened** — all still logically open, see the vocabulary at the top);
the one THEOREM this slice adds (`Simulation.refute_of_acyclic`) is a
consolidation of already-proved results, not a new resolution.

### Stage 5, Slice 4: widening, fuel-testing, ledger repair

Driven by an ideonomic review of the program's own method rather than by
new census data. The review's operative finding: **every conjecture that
became a theorem did so by escaping one of the census's definitional
properties** (C2 escaped leftmost-outermost AND bounded size; τ escaped
fuel-boundedness; `refute_of_acyclic` escaped per-system-ness), and
everything still open is still trapped inside at least one. This slice
negates three more of those properties and repairs the ledger's status
vocabulary.

- **The refutations were under-claimed; widened to `PathEncoding`.** An
  audit of `Simulation.refute_of_acyclic` found it consumes only two
  consequences of the five-field `Simulation`: injectivity of `enc` (via
  `dec_enc`) and path-preservation (via `fwd`, which was ALREADY many-step).
  It never touches `bwd`, and no step-count condition is involved anywhere
  in the proof. `PathEncoding` (`Universality/Defs.lean`) names that weaker
  hypothesis; `PathEncoding.refute_of_acyclic` carries the mechanism;
  `Simulation.refute_of_acyclic` survives unchanged in name and statement
  as a corollary via `Simulation.toPathEncoding`, so nothing downstream
  moved. The widened headline results are `no_pathEncoding_SK_pureS` and
  `no_pathEncoding_SK_iota`. **Revised prize-adjacent claim: if S alone is
  universal, its encoding must be non-injective or must fail to preserve
  reduction paths** — two named escape hatches in place of the vaguer
  "non-step-faithful work". The widening is proved non-vacuous rather than
  asserted: `pathEncoding_strictly_weaker` exhibits a `PathEncoding` (a
  two-point step-free system mapped onto SK's Ω/M cycle) whose encoder
  extends to no `Simulation`, since `bwd` would reflect a genuine host path
  back into a source that has none. `Simulation.toPathEncoding` is
  therefore not surjective. Axioms: mechanism and strictness witness are
  AXIOM-FREE; the two instances carry the inherited `[propext, Quot.sound]`.
- **The frozen head (C1, PROVED structure — C1 itself still open).** See the
  C1 entry for the full statement. Negating "leafCount is the only measure"
  (Term.lean's own words) and mining the trajectory under spine length,
  depth, redex count and isometric-redex count found one regularity strong
  enough to prove for all terms and all strategies: `S A B` with `A` normal
  admits only steps inside `B`, so `frozen_normalizes_iff` relocates C1
  exactly onto the payload. Six axiom-free theorems (`Invariants.lean`).
  Two useful negatives came with it: τ governs nothing on this trajectory
  (`isoRedexCount = 0` from step 6), which explains by measurement why the
  C2 machinery does not transfer; and no frozen reduct recurs as a subterm
  of a later one from any of 20 starting points, so the loop route still has
  no witness — now checked at a granularity where one could have existed
  (Slice 3's hunt for `c1`, spine 5, could not have found one after the head
  freezes to spine 2).
- **C6 fuel-tested, and it PASSED.** The density table was the cheapest open
  item on the board and the most exposed: measured at one fuel value only,
  it could have been reporting "needs more than 200 steps" rather than
  anything about divergence. At fuel 800 the exhausted counts for n = 7..10
  are identical to fuel 200 (2, 41, 276, 1484) — not one of 6,853 terms
  changed verdict under a 4× fuel increase. C6 moves to **probed**. Two
  side benefits: the n=9 and n=10 rows, previously cited from
  LAB_NOTEBOOK.md without recomputation, are now independently reproduced;
  and the cheap `exhaustedCount` probe (which skips `maxFinalLeaves`, the
  actual cost centre at high fuel) is recorded for reuse. n=11 and n=12
  remain untested for fuel-sensitivity.
- **The ledger gained a demotion state.** `open` / `probed` / `weakened`
  now separate untested from tested-and-survived from tested-and-dented
  (vocabulary at the top of this file). C3 was the motivating case: its own
  Slice 3 probe had come back against it while it stayed filed as plain
  "open", indistinguishable from C5 which has never been tested at all.
  Both halves of C3 are now **weakened**; C1 and C6 are **probed**.

**What did NOT happen** (status labels as of Slice 4; SUPERSEDED for C1 by
Slice 5, which split it and proved the minimality half — see below):
C1, C3, C4, C5 and C6 all remain open. No
conjecture was resolved this slice. The theorems added are a
strengthening of existing refutations (`PathEncoding`) and a structural
reduction of C1 (`frozen_normalizes_iff`) that makes the target term
BIGGER, not smaller — 15 leaves against `c1`'s 7. Registered plainly so
the slice is not read as progress toward a divergence proof.

### Stage 5, Slice 5: C1 split, minimality proved

The first slice since Slice 2 to resolve anything, and it did so by
restructuring a conjecture rather than by attacking it harder.

- **C1 split into existence and minimality.** See the C1 entry above. The
  bundled statement had made both halves look uniformly hard; separated,
  minimality is a finite claim over 65 terms and existence is the genuinely
  open one. This is pure bookkeeping and it is what made the rest visible.
- **The `sTerms`-completeness chain is closed** (`enum_sound`,
  `enum_complete`, `mem_enumAt_iff`, `Census/Completeness.lean`). Blocked
  since Slice 1, attempted and escape-hatched three times, and ranked
  FOURTH in the standing queue — a ranking that was itself an artifact of
  the unsplit C1, since the chain's description ("blocks `no_small_cycle`
  and the abstract `Decidable` instance") never mentioned that it also
  gated half of C1. Route: stop trying to make the imperative
  `sTermsTable` transparent and prove both directions about a
  structurally-recursive twin instead, with `#guard`s tying the two
  together so they cannot drift.
- **C1(b) PROVED** — `no_small_divergence` / `seven_is_the_floor`. The
  program's first proved POSITIVE result about pure S. Everything settled
  before it was negative (`no_sim_SK_iota`, `no_sim_SK_pureS`) or
  structural (`no_pure_S_cycle`, `refute_of_acyclic`, the frozen head).
- **Still open, and unaffected:** C1(a), C3, C4, C5, C6. Minimality gives
  no leverage on existence — if pure S turns out to be strongly
  normalizing, C1(b) remains true and C1(a) is simply false.
- **Choice-freeness maintained.** A first version of `enum_complete` leaked
  `Classical.choice`, which would have been the tree's first use of it. It
  came from `omega` discharging a non-arithmetic goal (an existential) out
  of contradictory hypotheses; replaced with an explicit witness. The whole
  chain now reports `[propext, Quot.sound]`, and
  `smallAllNormalize_true` reports `[propext]` alone.

**Method note, since the last two slices raised it.** Slices 3 and 4 both
resolved nothing while writing more prose than Lean; a timeline of the
program showed the prose/Lean ratio inverting at Slice 3 and the
invention/discovery mix drifting toward invention. This slice's resolution
came from neither more invention nor a new probe, but from noticing that an
existing conjecture was two conjectures. The re-ranking that followed
(`sTerms`-completeness from 4th to 1st, C5 demoted for having zero
information gain) is recorded in LAB_NOTEBOOK.md.

### Stage 6: the spec's goals, and a literature check that reframes C1

Prompted by re-reading the design spec, which showed that the C-conjecture
list is not the goal set. The spec's Goal 3 is the north star and had never
been ranked first; C1, which had absorbed most of Stage 5, is Stage 0 census
output.

- **Spec Goal 3 CLOSED — reachability between pure S-terms is decidable**
  (`stepsDecidable`, `steps_decidable_of_kFree`, `Decidability.lean`).
  Slice 1 had a certified per-instance procedure and one gap: nothing proved
  that enough fuel always saturates the closure. That gap needed exactly the
  finiteness of the bounded term universe, which Slice 5's `enum_complete`
  supplies. Pigeonhole with an explicit measure: `smallTerms bound` is the
  finite universe, `deficit` counts what is uncollected, `deficit_lt` shows a
  non-empty frontier strictly reduces it, `boundedClosure_isSome` concludes.
  All four of Slice 1's hand-tuned examples re-verdict at the PROVED fuel
  (`reachFuel`), so the bound is usable and not merely finite. Axioms
  `[propext, Quot.sound]`.
  HONEST FRAMING: on paper this is folklore-adjacent — "monotone size ⇒
  bounded search" is two lines given Stage 2 — and the rewriting literature
  may have it. The machine-checked version is the claim.
- **C1 reframed by literature check — both halves were EXTERNAL all along.**
  See the C1 entry. Non-terminating pure-S terms are known to exist and the
  7-leaf threshold is known (Wolfram; Wolfram Data Repository dataset for
  leaf counts 1–10; Waldmann's decidability result as the underlying
  technology). C1(a) is therefore transcription, not research. C1(b), proved
  in Slice 5, is a machine-checked proof of a known fact — a legitimate
  contribution under spec Goals 1 and 4, but not a discovery, and the
  "first proved positive result" wording has been corrected in place.
  C2 is very likely external too (secondary sources credit Waldmann with
  showing CL(S) admits no ground loops); registered with the caveat that the
  primary source was not obtained.
- **Spec Goal 2 criterion (a) — assessed, still open, blocker stated.** The
  criterion wants a `Simulation` inhabitant certifying a KNOWN-universal
  system, i.e. Tag → SK; `pureS_in_SK` does not discharge it because pure S
  is not known-universal. Deliberately NOT attempted this stage. What it
  needs: a concrete finite-alphabet tag system (the current `TagSystem.Sym`
  is an arbitrary `Type`, so it cannot be encoded as-is), Church-style list
  and symbol encodings, a fixpoint combinator, multi-variable bracket
  abstraction (`Bracket.lean` has the single-variable case only), and then
  `fwd` — all substantial but mechanical. The actual blocker is **`bwd`**:
  `RS.SK.Steps (enc w) (enc w') → RS.Tag.Steps w w'` is a full adequacy
  theorem, asserting no spurious SK path connects two encoded words. `bwd`
  was free for `pureS_in_SK` only because that encoder is inclusion. For a
  real encoding it is research-grade and is the hard part of the whole
  criterion. Recorded rather than half-built.
- **Negative control added to the taxonomy** (`universalReach_self`,
  `universalNorm_self`, `universalConv_self`, `Universality/Taxonomy.lean`):
  `Simulation.id` makes all three Universal* predicates trivially true on
  the diagonal, so a ledger cell carries information only when R ≠ B. Every
  row of the actual table has R = `RS.Tag` ≠ B, so nothing in it is
  affected — this exists so nobody discharges criterion (a) by exhibiting a
  diagonal instance, which would be the reflexive analogue of the
  oracle-encoder cheat `bareEncNorm_trivial` already rules out.
- **C3 RETIRED** as a census artifact — see the C3 entry.

**Standing status after Stage 6.** Proved here: C1(b), C2, Goal 3
decidability, both hosting refutations (at `PathEncoding` strength), the
frozen head, combinatory completeness, confluence, the Stage 2 conservation
laws. External and unformalized: C1(a), C5, and probably C2's priority.
Open and genuinely unsettled: C4, C6, spec Goal 2's criterion (a), and the
Wolfram prize question itself — which is about UNIVERSALITY and is untouched
by anything in the C1 literature.

### Stage 7: C4 reduced, and a plan corrected mid-execution

- **C4's semantic core PROVED, syntactic residue registered.** See the C4
  entry. `no_pathEncoding_SK_of_strict_measure` covers any host with a
  strictly step-increasing measure, and `RS.Iota_acyclic` plus Stage 4's
  refutation both fall out as one-line instances — strict growth was a
  property of ι's MEASURE, never of ι. C4 as written still needs a
  rule-schema formalism (variables, matching, substitution) that does not
  exist here, so it is reduced-to-a-formalization-task, not resolved.
- **The plan that produced this stage was wrong, and the correction is now a
  theorem.** The prompting analysis recommended restating spec Goal 2
  criterion (a) at `PathEncoding` strength to bypass the `bwd` blocker.
  Working it showed that inverts the correct move: negative claims strengthen
  as the encoding class GROWS (so refutations belong at `PathEncoding`, as
  Slice 4 established), while positive claims strengthen as it SHRINKS (so
  certifications belong at `Simulation`). Criterion (a) is a positive claim
  whose whole purpose is to show the DEMANDING definition is satisfiable.
  `UniversalReach.toPathEncoding` records the inclusion; with
  `pathEncoding_strictly_weaker` the levels provably differ, so the direction
  is substantive. **`bwd` is load-bearing and the Goal 2 blocker is
  principled, not incidental.** This supersedes the suggestion; recorded
  rather than quietly dropped.
- **Two ledger fields added — materiality and prior art** (documented after
  the status vocabulary). Status says how well established a claim is; it
  never said whether anyone should work on it, and that is the question nine
  stages got wrong. C1 is the worked failure of both fields: materiality LOW
  from Stage 0, prior art settled externally and discoverable in an hour.
  Every entry now carries both, "not checked" permitted, blank not.
- **C5 re-labelled external** for consistency with C1(a): the λI conservation
  theorem has been cited in this file since Stage 2, so calling it "open"
  conflated "we haven't done it" with "nobody has." Its stated purpose —
  upgrading a C1 loop witness — is also gone now that C1(a) is external.

**Where the program stands, by level rather than by conjecture.** The bottom
of the tree (facts about specific small S-terms: C1, C2, C6) is done or
external — it is the level enumeration reaches, hence the level where prior
art was always densest. The top (what faithful encoding MEANS: `Simulation`,
`PathEncoding`, the three observation modes, the refutation mechanism, the
negative controls) is where this tree's theorem mass actually sits and where
the literature check found nothing. C4 and spec Goal 2 criterion (a) are both
at the top, and they are the two live items that matter.
