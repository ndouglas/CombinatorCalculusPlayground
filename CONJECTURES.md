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
  `c1` diverges). Status: **PROVED** (Stage 43, `c1a`, pinned — this header
  was stale from Stage 43 to Stage 138; caught by the ledger audit).
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

### C1(a): existence — EXTERNAL (known in the literature); internal route now one gap

**Stage 32 status of the internal route.** C5 is proved (Stage 31), so the loop route no
longer waits on external work: `no_normalForm_of_infiniteRed` means an infinite reduction
sequence suffices. What remains is a reducibility invariant, and it is now down to one
arithmetic gap:

- `reducible_of_head_spine` — for K-free terms, **head spine ≥ 3 ⇒ reducible** (the only
  leaf is `S`, so the head of any chain is `S`). The reducibility criterion.
- `spineLength_S_red` — firing `S f g x` leaves head spine `spineLength f + 2`; with `k`
  trailing arguments, `spineLength f + 2 + k`. The preservation arithmetic.
- **Stage 33 correction — that gap was an artefact.** `reducible_of_head_spine` is
  *sufficient* for reducibility but not *necessary*: a term of head spine 2 such as
  `(S x)(g x)` can still reduce inside. So demanding head spine ≥ 3 as an **invariant**
  asks for strictly more than reducibility needs, and the `k = 0` case was a consequence of
  that over-strong demand rather than a real obstacle.
- **The replacement needs no invariant.** `no_normalForm_of_unbounded`
  (`Conservation.lean`): a K-free term whose reducts have **unbounded size** has no normal
  form. Via `leafCount_le_of_normalizes` — confluence sends every reduct to the normal form
  and monotonicity caps it. Contrapositive `bounded_of_normalizes`: a normalizing K-free
  term has a size bound on its *whole reduction graph*, so **any bound on the census's
  exploding sizes would have been a normalization proof**.
- **Why this target is better matched.** It needs only a family of reducts, one above each
  bound — no preserved predicate. It is what the census actually measured (`c1`: 120112
  leaves by step 200, 25740409924 by fuel 1000), so evidence and goal finally agree. And it
  is monotone in the evidence: every larger reduct found is progress, whereas invariant
  hunting produced nothing cumulative across Slices 3, 4 and 32.
- **What is still missing:** a proof of unboundedness, which needs a growth step — from any
  reduct, reach a strictly larger one. Open.
- Self-embedding remains witness-free, now including **the literature's own term**: the
  classic 14-leaf `S A A (S A A)` with `A = S S S` does not self-embed within 40 steps
  (sizes 14, 20, 26, 35, 44, 53, 65, …).

The external record follows.

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

## C4: No single-rule first-order combinator basis hosts SK — **PROVED**
**Status: PROVED at every arity.** Semantic core Stage 7
(`no_pathEncoding_SK_of_strict_measure`); syntactic class arity 1 Stage 14
(`no_pathEncoding_SK_mono1`); general arity Stage 15
(`no_pathEncoding_SK_poly`, `Universality/OneRule.lean`). C4 was the last
conjecture on this list that was both open and unambiguously ours.
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

## C5: Conservation for pure S (WN ⇒ SN) — **PROVED** (Stage 31)
`conservation` (`Conservation.lean`): a K-free term that reaches a normal form admits no
infinite reduction. **Not an import.** Proved from Stage 1 confluence, Stage 2
monotonicity, Stage 6 `enum_complete`, a constructive pigeonhole, and C2's
`no_pure_S_cycle`. Axioms `[propext, Quot.sound]`. See the Stage 31 section for why the
"external" label was wrong.

Historical status line follows.
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

## C6: Divergence density grows with size — status: RETIRED (Stage 138, out of scope)
- Materiality: **LOW.** A density asymptotic over small n bears on nothing
  else in this tree; no theorem depends on it and it does not touch
  universality. It is cheap and it is genuinely ours, and Stage 7's ranking
  deliberately does NOT promote it on those grounds — cheapness is precisely
  what made C1 attractive for nine stages.
- Prior art: **not checked** for the density asymptotic specifically. Adjacent
  work certainly exists (Wolfram's dataset covers leaf counts 1–10 and would
  give the same counts); whether the monotone-to-1 conjecture is settled is
  unknown. Checking is cheap and should precede any further work here.
- Retirement (Stage 138): declined by one hundred and twenty-four consecutive
  rankings, always on the materiality already recorded above. Nothing in the
  four goals consumes a density asymptotic, and the divergence content it
  gestured at is now covered by strictly stronger, materially-connected
  theorems (`c1a`; the `{S,C}` glider with certified determinism and
  normal-form-freeness). Retirement is a scope decision, not a resolution:
  the conjecture remains open mathematics, recorded here for whoever wants
  it, and reopening requires only a ranking that places it first.


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

### Stage 8: the `bwd` blocker made standard

Work on spec Goal 2 criterion (a), attacking the blocker rather than starting
the encoding.

- **`bwd` is now derivable from a stuttering abstraction**
  (`RS.abstraction_tracks`, `RS.bwd_of_abstraction`,
  `Simulation.ofAbstraction`, `Universality/Defs.lean`; all AXIOM-FREE). Give
  an abstraction function on ALL host states such that every host step either
  stutters (abstraction unchanged) or advances it by exactly one source step,
  and `bwd` follows; the abstraction doubles as the decoder, so `dec_enc` goes
  with it and `fwd` is left as the only obligation.
  SCOPE: this does not make `bwd` easy, it makes it STANDARD — a per-machine
  mechanical check instead of an open-ended characterisation of every path
  between encoded states. Exercised on `pureS_in_SK`, rebuilt through the
  constructor; that instance is degenerate in a useful way (no step ever
  stutters, since every SK step out of a K-free term advances the source
  exactly one PureS step), so it checks the interface, not the hard case.
- **A structural fact about the tree, previously unregistered.** There is no
  bridge from `TermV` (Bracket.lean's terms-with-variables) to `Term`, and no
  transfer from `StepsV` to `Steps`. So `combinatory_completeness` — the
  program's Stage 4 "positive" calibration result — lives in a universe
  disconnected from the `RS`/`Term` layer where every NEGATIVE result lives.
  CONJECTURES.md already noted it is "a theorem about TermV, not routed
  through `Simulation`"; what was not noted is that the gap is structural, not
  stylistic. **The positive and negative sides of this program's calibration
  have never been in the same universe.** That is a second, independent reason
  criterion (a) is the item that matters: it is the only thing that would put
  a positive result in the same language as the refutations.
- **Criterion (a), decomposed.** Remaining work, in order, with difficulty
  named: (i) a closed-`TermV` → `Term` bridge with `StepsV` → `Steps`
  transfer — infrastructure, mechanical; (ii) multi-variable bracket
  abstraction by iterating `bracket` — mechanical, needs one iteration lemma;
  (iii) Church-style data: a codable finite alphabet, lists, booleans,
  conditionals — mechanical but bulky; (iv) a fixpoint combinator with its
  unfolding lemma — small, standard; (v) the tag step as a combinator (length
  test, head, drop m, append rule output) and `fwd` proving the driver takes
  `enc w` to `enc w'` — bulky, the largest single piece; (vi) the abstraction
  function and its stutter-or-advance proof — now mechanical thanks to this
  stage, but voluminous, and where the residual RISK sits: `abs` must be
  total on SK terms including garbage, and tracking must survive every
  intermediate state the driver passes through.

### Stage 9: the TermV/Term bridge — one language at last

Piece (i) of the criterion (a) decomposition, and the repair for Stage 8's
structural finding.

- **Bracket.lean imported nothing.** Not "was stylistically separate" —
  imported nothing at all, so `combinatory_completeness` had no connection to
  `Term`, `Step` or `RS`. The program's POSITIVE calibration result had never
  been stated about the same system as any of its NEGATIVE results.
- **The bridge** (`ofTerm`, `toTerm`, `toTerm_ofTerm`, `ofTerm_injective`,
  `closedV_ofTerm`, `step_toTerm`, `steps_toTerm`; Bracket.lean). Step
  transfer needs no closedness hypothesis — `StepV`'s rules are `Step`'s,
  `toTerm` is an application homomorphism, variables are inert on both sides —
  and both transfer lemmas are AXIOM-FREE.
- **`combinatory_completeness_RS`** (`Universality/Calibration.lean`, placed
  deliberately beside the refutations): an actual SK `Term` `F` with
  `RS.SK.Steps (app F u) …` for every `Term u`. That is literally the relation
  `no_sim_SK_pureS` and `no_sim_SK_iota` are stated about, so the calibration
  now reads as one sandwich in one language:
  - POSITIVE: `combinatory_completeness_RS`
  - NEGATIVE: `no_pathEncoding_SK_pureS`, `no_pathEncoding_SK_iota`,
    `no_pathEncoding_SK_of_strict_measure`
- **What this does NOT close.** The positive side is about SK realizing
  λ-style BODIES; criterion (a) wants SK hosting a known-universal MACHINE via
  a `Simulation`. Putting both sides in one language makes the gap legible; it
  does not close it. Stated in the file so the sandwich is not misread.
- **A claim deliberately weakened rather than an axiom paid.** The stronger
  faithfulness lemma `ClosedV v → ofTerm (toTerm v) = v` needs
  `(n == n) = true`, and every route to that in this toolchain pulls
  `Classical.choice` through the `BEq`/`LawfulBEq` instances — which would be
  this tree's first use of it. Four attempts failed. The lemma is decorative
  and the bridge only ever transfers FROM `Term`s, so the claim was reduced to
  `ofTerm_injective`. Recorded at the lemma and in the notebook; the whole
  bridge reports `[propext]` or less.

### Stage 10: piece (vi) prototyped — it fails, and the failure is useful

Stage 8 called the stutter-or-advance obligation "mechanical" and flagged
piece (vi) as the one that could fail IN KIND, to be prototyped before the
machine it tracks gets built. Done, and it failed.

- **Scoping correction to piece (ii).** It is not "one iteration lemma".
  Iterating `bracket` needs substitution to commute with bracketing, and that
  holds only UP TO REDUCTION: `subst x u (bracket y (var x))` is `K u` while
  `bracket y (subst x u (var x))` is `bracket y u` — reduction-equivalent, not
  equal. Since (ii) is investment (vi) could invalidate, (vi) was done first.
- **`naiveAbs_not_stuttering`** (`AdequacyProbe.lean`) — machine-checked: the
  obvious structural abstraction over a genuinely nondeterministic test
  machine does NOT satisfy `RS.bwd_of_abstraction`'s hypothesis. There is a
  step out of an abstracted state whose target abstracts to `none`.
- **Cause.** `S f g x → (f x)(g x)` duplicates `x`; the copies then reduce
  independently; an abstraction that reads a duplicated subterm syntactically
  must handle them drifting apart, and the drifted state space is
  combinatorial in the live redexes inside the duplicated part. So piece (vi)
  is not "check each rule" — the naive abstraction is simply wrong.
- **The design constraint this buys, which is the point of prototyping.**
  Either define the abstraction up to `Joinable` (correct, but drags SK
  confluence through every case), or — better — **constrain the encoding so
  duplication only ever hits NORMAL FORMS.** If `x` is normal when `S f g x`
  fires, the copies cannot drift and desynchronisation is impossible by
  construction. That is a restriction on how piece (v)'s tag-step driver must
  be written: every argument it duplicates must already be in normal form at
  the moment of duplication. Achievable — encoded words and symbols are data,
  and data can be kept normal — but it constrains the machine's construction
  and cannot be patched in afterwards. `sync_step` confirms the diagnosis: the
  same shape over a normal payload advances exactly as required.
- **Revised difficulty for criterion (a).** Stage 8 rated (vi) mechanical.
  It is mechanical only CONDITIONAL on the piece (v) design obeying the
  normal-forms-only discipline. That coupling between (v) and (vi) did not
  appear in Stage 8's decomposition and is the main thing this stage adds.

### Stage 11: Stage 10's constraint is satisfiable for code

Stage 10 ended with a design constraint (duplication must only hit normal
forms) and Stage 10's own methodological note said to trust risk flags over
difficulty ratings. The flag here: is that constraint satisfiable at all? If
not, pieces (ii)–(v) are wasted.

- **Half the answer is YES, and proved.** `normalForm_bracket` (Bracket.lean):
  every bracket-abstraction output is a normal form, because `bracket` only
  ever emits `K` applied to ONE argument and `S` applied to TWO, neither of
  which is a redex. Since all of this program's code comes from `bracket`, a
  machine's code is safe to duplicate — and the self-application inside any
  fixpoint combinator duplicates exactly that. **Stage 10's failure cannot
  touch code, only data.** Four reusable shape lemmas come with it
  (`normalForm_S`/`_K`, `normalForm_app_K`, `normalForm_app_S_one`/`_two`),
  which piece (v) will need regardless.
- **The diagnosis is now a theorem, not an observation.** `step_app_K_pair`
  (`AdequacyProbe.lean`): over a NORMAL payload the half-consumed shape has
  exactly ONE successor. Stage 10 checked this on a single instance; this is
  the general form, and it is the precise sense in which the constraint fixes
  the failure.
- **The other half is NOT settled, and this is the live risk.** A fixpoint's
  reduct `f (x x f)` hands the step function a PENDING RECURSIVE CALL, which
  is not normal. If the driver duplicates that argument, drift returns. Piece
  (v) therefore needs a strict discipline — force the recursive call before
  duplicating it. That is an obligation on how the driver is written, not a
  consequence of anything proved here, and it is now the sharpest known
  requirement on criterion (a)'s remaining work.

### Stage 12: piece (ii) — two-variable abstraction

- **The commutation lemma, and why one suffices.** Stage 10 found that
  iterating `bracket` needs substitution to commute with bracketing, which
  holds only UP TO REDUCTION. Two design choices reduce that to a single
  lemma: (1) n-variable abstraction is not needed, because a driver takes a
  fixpoint self-reference and a state and its data can be TUPLED, so two
  nested abstractions suffice — and two is exactly the case the lemma handles
  in one application; (2) the substituted argument is always encoded DATA
  (image of `ofTerm`), which removes the `var` case.
- **`bracket_subst_applied`** (Bracket.lean): substituting encoded data into
  `[y]t` and applying gives the same result as both substitutions directly.
  The two combinators are not equal; applied to any argument they reach the
  same term, and applied is the only way they are ever used.
- **`abs2` / `abs2_beta` / `normalForm_abs2`**: two-variable abstraction, its
  beta law, and the fact that its combinator is a normal form — hence safe to
  duplicate per Stage 11. All `[propext]`.
- **The Stage 9 leak paid a dividend.** Choosing `ofTerm p` over an abstract
  `ClosedV u` was motivated by Stage 9's `Classical.choice` trap, which lives
  exactly in deriving a contradiction from `ClosedV (var n)`. Avoiding that
  shape produced a cleaner lemma than the general one would have been.
- **Vestigial hypothesis flagged:** `combinatory_completeness_Term`'s
  single-variable condition is unused — the `Term`-level statement does not
  assert closedness, and `toTerm` erases variables regardless. Renamed `_h`
  rather than dropped, for parity with the `TermV` version where it IS needed.

**Criterion (a) status after Stage 12.** Pieces (i) and (ii) done; (vi)
prototyped with its design constraint known and half-discharged (code is
normal, `normalForm_bracket`); (iii)–(v) remain, under the
force-before-duplicate discipline. The residual risk is unchanged and specific:
a fixpoint's reduct hands the step function a pending recursive call, which is
not normal.

### Stage 13: the pending-call risk — Stage 10's preferred route is insufficient

Prototyping the residual risk Stage 11 left, before building pieces (iii)–(v)
on top of it. It broke, and it breaks Stage 10's preferred fix with it.

- **`naive_bracket_duplicates` / `naive_bracket_drifts`** (`AdequacyProbe.lean`,
  both axiom-free). `bracket` is the naive algorithm — no occurs-check — so
  `[x](a b) = S ([x]a) ([x]b)` distributes the argument to BOTH branches even
  when `x` occurs in one, and `S A B u → (A u)(B u)` duplicates `u` at every
  application node of the body. Demonstrated on a body that uses its variable
  **exactly once** and still duplicates; the doomed copy then drifts.
- **What this corrects.** Stage 10 preferred route (2) — constrain the encoding
  so duplication only hits normal forms — over route (1), an abstraction up to
  `Joinable`. Route (2) implicitly assumed duplication is under the driver
  author's control. It is not:
  - occurrence-counting does not help (single-occurrence bodies duplicate);
  - the duplicate is DOOMED (`(K S) u` discards `u`) but exists for at least one
    step, and a syntactic abstraction must still assign a source state to the
    drifted intermediate;
  - transient duplicates are not an artefact of the naive algorithm. In SK every
    `S`-redex duplicates its third argument, so moving a value past another
    costs a transient copy. An occurs-check-optimized abstraction reduces how
    MANY copies appear; it cannot reduce them to zero.
- **Revised difficulty for piece (vi), third revision.** Stage 8: mechanical.
  Stage 10: mechanical conditional on (v)'s design. Stage 13: **not mechanical.**
  The abstraction must be insensitive to doomed subterms — defined up to
  `Joinable` (using SK confluence, which this tree has) or reading only the live
  spine. Route (1) is back and probably unavoidable.
- **What survives unchanged.** Stage 11's `normalForm_bracket`: machine CODE is
  normal, so a fixpoint's self-application is safe. The problem is specifically
  the pending recursive call, which is data-shaped and not normal. Pieces (i)
  and (ii) are unaffected and still needed.

### Stage 14: C4's syntactic residue closed for arity 1

Switched off criterion (a) deliberately, on Stage 13's own evidence: the piece
(vi) estimate had been revised upward three times monotonically, which is
evidence it would move again, while C4's residue was assessed as bulk work with
no hidden research problem. Acted on that rather than walking down (a) one
revision at a time.

- **The class, formalized** (`Universality/OneRule.lean`): `Mono` (one
  combinator plus application), `Pat1` (reduct patterns with one rule variable),
  `Pat1.inst`, `countC`, `countVar`, `MonoStep`, `RS.Mono1`.
- **C4's condition becomes arithmetic.** C4 said "each rule variable occurs at
  least once in the reduct AND the reduct is strictly larger even at the minimal
  instantiation". That is now exactly `1 ≤ countVar rhs` and `2 ≤ countC rhs` —
  two decidable counts on the reduct pattern. The bridge is
  `Pat1.leafCount_inst`: instantiation is LINEAR in the argument's size.
- **`no_pathEncoding_SK_mono1`** (with `no_sim_SK_mono1` as corollary): no
  arity-1 one-combinator one-rule system passing that check can path-encode SK.
  `[propext, Quot.sound]`.
- **Why arity 1 is not an arbitrary cut.** It is exactly ι's arity, so this
  generalizes the instance C4 was abstracted FROM — from "ι specifically" to
  "every arity-1 one-rule system passing a decidable check". ι's rule is written
  as a `Pat1` with both clauses discharged by `decide` (`countVar = 1`,
  `countC = 9`).
  SCOPE, stated in the file: `RS.Mono1 iotaRhs` is ι's RULE SHAPE over the
  abstract carrier `Mono`, not the `RS.Iota` instance (carrier `IotaTerm`).
  Nothing re-derives `no_pathEncoding_SK_iota`; the example shows C4's condition
  is satisfiable by a rule the program already cares about.
- **What remains, precisely delimited.** General arity. The size formula
  generalizes to `countC R + Σ_{i<n} (countVar i R)·|σ i|` against a left-hand
  side of `1 + Σ_{i<n} |σ i|`, with the same condition shape and the same proof
  idea — but establishing it needs sums over `i < n` and their algebra
  (additivity over `app`, an indicator-sum lemma for the `var` case, a partition
  lemma to split the variable list at an application node). None exist in core
  4.28 in usable form, and this tree has no Mathlib. **So the obstacle is
  list-sum algebra, not anything about combinators** — bulk work, exactly as
  Stage 13 assessed.

### Stage 15: C4 closed at every arity

- **`no_pathEncoding_SK_poly`** (with `no_sim_SK_poly`): no one-combinator,
  single-rule, first-order system of ANY arity whose reduct uses every rule
  variable and contains at least two combinators can path-encode SK. This is C4
  as written. `[propext, Quot.sound]`.
- **C4's informal condition, fully arithmetized.** "Each rule variable occurs at
  least once in the reduct" is `∀ i < n, 1 ≤ countVar i rhs`; "strictly larger
  even at the minimal instantiation" is `2 ≤ countC rhs`. The bridge is
  `Pat.leafCount_inst`: `|inst σ p| = countC p + Σ_{i<n} (countVar i p)·|σ i|`.
- **Stage 14's obstacle was mis-framed, in two ways** (both recorded in the file
  rather than quietly fixed):
  - the "list-sum algebra" was an artefact of assuming the rule's arguments
    arrive as a LIST, which forces `getD` bookkeeping and a cons/append mismatch
    against range-based sums. Taking the assignment as a FUNCTION `Nat → Mono`
    with recursion on the arity removes lists entirely;
  - the "partition lemma to split the variable list across an application node"
    was never needed. It is only needed if one avoids the exact size formula;
    proving the formula makes the `app` case decompose by plain additivity.
  What was actually required: seven small facts about `Σ_{i<n}`.
- **Non-vacuity at general arity:** ι's rule as a `Pat`, plus a genuine arity-3
  example (`c x y z → x (y z) c c`) with all three hypotheses discharged.

**Standing status after Stage 15.** Proved here: C1(b), **C4 (in full)**, C2,
spec Goal 3 decidability, both hosting refutations at `PathEncoding` strength,
the frozen head, combinatory completeness (now in `RS` language), confluence,
the Stage 2 conservation laws. External and unformalized: C1(a), C5, probably
C2's priority. Open and genuinely unsettled: **C6** (ours, low materiality),
**spec Goal 2 criterion (a)** (blocked on the adequacy abstraction — see Stages
10–13), and the Wolfram prize question itself.

### Stage 16: criterion (a) resolved — as written it is unsatisfiable in scope

The ambiguity flagged in the fourth review is resolved, and the resolution is
sharper than the review's own framing. The review called it "letter vs spirit";
the spec's wording NAMES its targets, and one of them is refuted here.

**The spec, verbatim:** "a correct definition must (a) certify known-universal
systems **including one-combinator bases**, (b) not be auto-killed for S by
Waldmann's decidability alone, and (c) identify precisely which definitions
leave the prize question open."

- **The one-combinator clause is REFUTED in first-order scope.** That is
  `no_pathEncoding_SK_iota`, and generally C4 at every arity
  (`no_pathEncoding_SK_poly`). No first-order one-combinator basis meeting C4's
  growth condition can host SK. So criterion (a) **as written cannot be
  satisfied by this program**, and the reason was already in the spec's own
  Background: Barker's ι universality is a λ-level, erasing phenomenon, out of
  first-order scope. Stage 4 registered that as a spec deviation; what nobody
  had done is connect it to criterion (a)'s satisfiability. **This is a finding
  about the criterion, not a failure against it.**
- **The general clause is now DISCHARGED** — `universalReach_extend` /
  `tagInExtend` (`Universality/TagEmbed.lean`): a tag system is
  `Simulation`-simulated by a tag system over a larger alphabet, and m = 2 tag
  systems over finite alphabets are universal (Cocke–Minsky 1964 — EXTERNAL,
  cited). Two things this does that `pureS_in_SK` could not: the source is
  KNOWN-UNIVERSAL (pure S is not), and `bwd` is earned rather than free
  (`pureS_in_SK`'s encoder is an inclusion). It is also the first
  non-degenerate use of Stage 8's `Simulation.ofAbstraction`.
- **What remains open, stated without hedging:** that **SK** certifiably hosts a
  known-universal system — Tag → SK — is open and research-blocked on the
  adequacy abstraction (Stages 10–13). That is the interesting instance and
  nothing here touches it.
- **Criterion (b)** was discharged in Stage 3 (the definitions are pinned over
  `Simulation`, and `bareEncNorm_trivial` shows why the unpinned variant
  measures nothing). **Criterion (c)** — identify precisely which definitions
  leave the prize question open — is discharged by the definitions ledger plus
  Stage 4's `PathEncoding` scoping: the prize question survives exactly in the
  gap between injective path-preserving encodings and the informal notion.

**Restated criterion (a′), the satisfiable form, for the record:** *the
definitions must certify at least one known-universal system via an actual
`Simulation` inhabitant.* Under (a′), criterion (a) is **DISCHARGED**. Under the
spec's literal (a), it is unsatisfiable in first-order scope for the reason
above. Both statements are recorded so neither can be quoted alone.

### The Mathlib decision, made once and recorded (Stage 16)

The spec lists zero-dependency as a non-goal with an explicit escape hatch, and
the hatch has never been considered. The tax is now countable: four
`Classical.choice` traps (all originating in core's `BEq`/`LawfulBEq` instance
layer, not in the proofs), two Mathlib tactics hand-replaced (`by_contra`,
`interval_cases`), one direction of `eraseDups` membership, two list-filter
length lemmas, and a seven-lemma `sumTo` battery standing in for
`Finset`/`BigOperators`.

**Decision: keep zero dependencies.** Nothing currently open is blocked on
Mathlib — the remaining items are Tag → SK adequacy (a research problem, not a
library problem), transcription work, and C6. The tax has been paid and the
resulting lemmas are in the tree. Revisit only if a future target is blocked
specifically by absent library algebra. Recorded here so that "we never decided"
stops being the state.

### Stage 17: the relaxation ladder opened — rung one, {S,I}

The fifth review asked a cardinality question — how many things are left? — and
the answer was "one research problem, no portfolio". The substitution test on
that ("what would the swarm form be?") turned up a workstream sitting in the
spec's own Stage 5, one paragraph below the north star, unmentioned in sixteen
stages and five reviews:

> "Bracketing program (the relaxation ladder): classify universality of bases
> between {S} and {S,K} — e.g., {S,I}, {S,B}, {S,C} — each rung a publishable
> partial result that narrows where universality is lost."

- **Rung one is `{S,I}`, and it is where the program's only negative mechanism
  dies.** `omegaSI_cycle` (`Universality/Ladder.lean`, axiom-free): `(S I I)(S I I)`
  cycles in three steps. Hence `SI_not_acyclic`, and — stronger —
  `SI_no_strict_measure` / `SI_no_decreasing_measure`: NO monotone measure exists
  in either direction. Not "none found": none exists.
- **The boundary is sharp, and that is the rung's content.** Pure S is acyclic
  (`no_pure_S_cycle`, C2, via τ, all terms and all strategies). Adding `I` —
  which erases nothing and duplicates nothing — destroys it. So:
  - **erasure-freeness is not what keeps pure S acyclic.** `{S,I}` is erasure-free
    too. Whatever τ measures is specific to S-only reduction, not a consequence
    of non-erasure. This corrects a natural reading of the Stage 2 conservation
    laws that the ledger has never explicitly ruled out.
  - **the acyclicity boundary is exactly rung one.** The program's whole negative
    apparatus — `no_pathEncoding_SK_pureS`, `no_pathEncoding_SK_iota`, C4 at every
    arity — covers `{S}`, ι, and every one-combinator one-rule system, and reaches
    no further. Higher rungs need positive constructions or new mechanisms.
- **Rungs two and three scoped, not attempted.** `{S,B}` and `{S,C}` each pair a
  strictly leaf-count-DECREASING rule (−1) with S's rule (+|x|−1 ≥ 0), so
  `leafCount` is non-monotone in both directions and a combined τ-style measure
  would be needed — the shape of work that took a full slice for C2. One concrete
  data point recorded: the obvious Ω attempt for `{S,B}` **terminates**
  (`S B B (SBB)` reduces to a normal form, since `B` with fewer than three
  arguments is stuck), which is weak evidence `{S,B}` may be acyclic and therefore
  refutable by the *existing* mechanism — the opposite verdict from rung one, and
  the reason rung two is the next thing worth doing.

### Stage 18: the ladder is a hierarchy, and it answers acyclicity not universality

Two corrections to Stage 17, both from the sixth review, and the second matters
more than the first.

- **The rungs are not independent.** `not_acyclic_of_pathEncoding`
  (`Universality/Taxonomy.lean`, AXIOM-FREE) is the contrapositive of
  `PathEncoding.refute_of_acyclic` and is five lines: cycles propagate along path
  encodings, so a cyclic basis makes every system it path-encodes into cyclic
  too. **Rung one is an upward-closed family, not a point** — any basis with a
  definable `I` inherits its cycle and is beyond the acyclicity mechanism.
  Concrete witness: `siInSK` sends the primitive `I` to `S K K`, and
  `SK_not_acyclic_via_rung1` re-derives SK's non-acyclicity from rung one, by a
  route independent of the Ω ↔ M cycle in `Calibration.lean`. Two independent
  routes to the same fact, which is a check on the generic theorem as much as a
  result.
- **HONESTY CORRECTION — the ladder answers ACYCLICITY, not universality.** The
  spec says "classify universality of bases between {S} and {S,K}." What this
  program can answer per rung is acyclicity, which only bounds *refutability*:
  an acyclic basis is refutable as an SK-host by the existing mechanism, a cyclic
  one is not touchable by it. **Rung one does NOT say `{S,I}` is or is not
  universal.** It says the refutation tool cannot reach it. Stage 17's write-up
  did not state this and rung one reads like a universality result without it —
  the same misreading the `Tag → Tag` result in Stage 16 was explicitly scoped
  against, recurring one stage later in a different place. STATUS.md now names
  the ladder an *acyclicity ladder* and states the gap to the spec's wording.
- **The rung procedure is written down** (STATUS.md), with the ordering rationale:
  step 3 (hunt a cycle) must precede step 4 (hunt a combined measure), because a
  cycle makes step 4 provably futile. Rung one got that order right by luck.
  Rung 2's step-4 tool is now named concretely: a **lexicographic** measure, since
  step 1 shows no single component is monotone on `{S,B}` or `{S,C}`.

### Stage 19: rung two censused — {S,B} looks like pure S

Step 3 of the rung procedure, done properly. Stage 17 had one hand-traced Ω
attempt; the procedure calls that weak evidence, so this runs Stage 0's census
methodology on rung two. Tooling (`sbStepOnce`, `sbTerms`, `sbOnCycle`,
`Universality/Ladder.lean`) is UNVERIFIED census tooling and labelled as such.

- **Up to 6 leaves (3238 terms):** every term normalizes within fuel 100, no
  cycles.
- **At 7 leaves:** of 16896 terms, exactly **6 exhaust fuel 200 — and still 6 at
  fuel 1000**, so not a cutoff artifact. None is on a detectable cycle within 400
  steps. All six grow explosively (final sizes 20698–132443 leaves).
- **So `{S,B}` looks structurally like PURE S:** plausibly acyclic *and* plausibly
  non-normalizing — the C1 + C2 combination. **Correction to Stage 17:** it read
  the terminating Ω attempt as "evidence toward acyclic, hence refutable". The
  first half survives; the second was too quick, since acyclicity does not require
  termination and pure S is the proof of that. Direction unchanged, basis now
  16896 terms rather than one trace.
- **Cross-validation, free.** Pure-S terms ARE {S,B}-terms, so the rung-2 census
  CONTAINS the rung-0 census. Two of the six exhausted terms are exactly C1's
  candidates, and `S S S (S S) S S` reproduces the **120112**-leaf figure recorded
  for `c1` — computed by an independently written reducer. A check on both
  censuses. The other four contain a `B` and are new to this rung.
- **Why the Ω pattern fails here, and what a cycle would need.** `B` takes THREE
  arguments and self-application supplies too few: `S B B x → (B x)(B x)` leaves
  `B` applied to one argument on each side, and the whole to two — still short.
  Rung one worked because `I` takes ONE. **Neither erasure nor duplication is the
  discriminator; arity is.** That refines Stage 17's finding, which had ruled out
  erasure-freeness without saying what replaced it.
- **Step 4's target, sharpened:** not a termination measure but a τ-style
  ACYCLICITY measure, lexicographic (neither `leafCount` nor B-count is monotone
  alone — `B_red` removes a `B` while `S_red` duplicates its third argument). A
  C2-sized slice, not attempted.

### Stage 20: rung two step 4 — both obvious routes closed

Stage 19 specified step 4's target as "a τ-style acyclicity measure,
lexicographic". Working the arithmetic showed that specification is wrong, and the
correction is a theorem rather than a note.

- **How C2 actually worked, restated because it is the thing that fails to port.**
  C2 did not exhibit a decreasing measure — pure S is not terminating. It ran a
  SQUEEZE: (a) `leafCount` is monotone on pure S, so a cycle must be
  leafCount-CONSTANT; (b) size-preserving K-free steps are exactly S-redexes with
  atomic third argument; (c) τ strictly drops on those. **Step (a) is
  load-bearing** — with no monotone quantity there is no squeeze, and (b) has
  nothing to characterise.
- **`no_monotone_counting_measure`** (`Universality/Ladder.lean`): for any weights
  `a, b` with `0 < a ∨ 0 < b`, the quantity `a·#S + b·#B` **both rises and falls**
  along `{S,B}` reduction. So no counting measure is monotone in either direction,
  and Stage 19's "lexicographic" is ruled out by the same fact — a lexicographic
  order needs its first component monotone, and none is. Supporting: `SBStep` as a
  relation, `countS`/`countB` with `count_add`, four rule-level arithmetic lemmas,
  and four witness terms (one per direction of each count).
- **The other route is closed independently.** A globally decreasing Nat-measure
  would force termination, and the Stage 19 census found 7-leaf terms that do not
  normalize at fuel 1000.
- **So rung two is open, with the remaining possibilities named:** a non-counting
  STRUCTURAL measure (τ was positional, not a count — `τ(app a b) = 2τ(a) + τ(b)`
  weights by position); an interpretation argument; or the census is simply wrong
  about there being no cycle. **That last deserves real weight** — the hunt reached
  7 leaves and 400 steps, which is small, and rung one's cycle lives at 6 leaves.
  Recorded as open, not as nearly-done.
- **Runtime datapoint:** extending the hunt to 8 leaves (109824 terms) was
  abandoned after 10 minutes. The bottleneck is `sbOnCycle`'s seen-list, which is
  quadratic per term; a faster detector would be needed to go further.

### Stage 21: a faster detector, and validating it invalidated the hunt's scope

- **The detector.** `floydFind` (`Universality/Ladder.lean`) — Floyd
  tortoise-and-hare with a size cap, O(1) memory, generic over the term type since
  `sbStepOnce` is a function and the trajectory is a functional graph. Stage 20's
  quadratic `sbOnCycle` was abandoned at n=8 after ten minutes; this reaches
  **n=8 in 6 seconds (109824 terms) and n=9 in 38 seconds (732160 terms)**, with
  0 cycles found and 259 / 4496 no-verdict at size cap 1000, fuel 300.
- **The validation, which is the actual result.** An untested cycle detector
  reporting "no cycles found" is worthless, so the true-positive path was checked
  against a cycle known to exist: rung one's `omegaSI_cycle`, kernel-proved. **The
  detector did not find it** — and that is not a bug. The proved cycle closes with
  `appR (I_red)`, an INNER redex; leftmost-outermost fires the head S-redex instead
  and never returns. Both facts are build-enforced: the LO trajectory from `omegaSI`
  has sizes 6,8,7,10,9,8,12,11,10,9,14,… and never revisits it in 60 steps.
- **Correction to Stages 19–20.** Every cycle-hunt figure in this module is
  **leftmost-outermost only**, and Stages 19–20 read the `{S,B}` data as stronger
  evidence for acyclicity than it is. It rules out LO cycles and says nothing about
  the reduction relation. Rung one is now the concrete witness for why that gap
  matters.
- **The uncomfortable part.** Stage 0's census carried exactly this caveat for pure
  S — *"cycle-freedom under ALL strategies is a stronger, separate claim; this
  census only ever runs leftmost-outermost"* — and it is still in the C2 entry
  above. I rebuilt Stage 0's methodology on a new rung and reproduced its caveat
  without noticing. What Stage 21 adds is that the caveat now has a witness rather
  than being theoretical. Pure S itself is unaffected: C2 proved acyclicity by a
  measure, not by the census.

### Stage 22: rung two re-hunted, strategy-independently

Stage 21 showed a leftmost-outermost hunt is blind to exactly the phenomenon rung
one exhibits, so more LO data was the wrong thing to want. Acyclicity is a property
of the **relation**, so the search has to range over all one-step successors — the
shape `Reachability.lean` already uses for pure S.

- **The tooling** (`siSuccs`, `sbSuccs`, `closureG`, `onCycleAny`,
  `Universality/Ladder.lean`; unverified census tooling, as `onCycle?` is).
  `some true` = a return path was found. `some false` = the closure SATURATED, so no
  cycle through `t` stays within the size cap. `none` = fuel out, no verdict.
- **Validated before use**, which is the lesson Stage 21 taught at some cost:
  `onCycleAny … omegaSI = some true` — it finds the kernel-proved cycle that the
  leftmost-outermost detector provably misses. Plus two true negatives so it is not
  crying wolf.
- **Rung two's evidence, upgraded.** Guarded: every `{S,B}`-term up to **7 leaves**
  gets a verdict and none is on a cycle within a 30-leaf cap, **under any
  strategy**. Measured: n=8 at cap 30 (109824 terms, 0 cycles, all verdicted, ~15 s);
  n=7 at cap 60 and cap 120 (identical verdicts). So the result is **cap-insensitive
  across a 4× range** and nothing ran out of fuel at any size up to 8.
- **Honest scope, a real limit.** `some false` means no cycle whose terms *all* stay
  within the cap. A cycle that swells past the cap and returns is not excluded — and
  since `{S,B}`'s `leafCount` is non-monotone in both directions
  (`no_monotone_counting_measure`), such a cycle is not obviously impossible. The cap
  matters here in a way it would not for pure S, where monotonicity confines every
  path. This is the first place in the program where the *absence* of a monotone
  quantity degrades the census as well as the proof.

### Stage 23: τ on {S,B} — the τ-light fragment is acyclic

Stage 22 left one hole: a cycle swelling past the census size cap. It is not
closable by brute force — the closure at cap 200 on the explosive 7-leaf terms did
not finish in ten minutes — so it had to be attacked analytically. Stage 20 had
already named the tool: τ is not a *count*, it weights by **position**
(`τ(app a b) = 2τ(a) + τ(b)`), so Stage 20's no-counting-measure theorem does not
apply to it.

- **`tauSB_S_red`**: on an S-reduction τ moves by exactly `2τ(x) − 8` — down when the
  duplicated argument is light, up when heavy. The same shape as pure S, where C2
  used the `τ(x) = 1` case to get its drop of 6.
- **`tauSB_B_red`**: on a B-reduction τ **strictly decreases**, always, by
  `2τ(x) + 8 ≥ 10`. `B` duplicates nothing, so nothing compensates.
- **`sbLight_acyclic`**: the τ-light fragment (B-reductions plus S-reductions with
  `τ(x) ≤ 3`) is **ACYCLIC**. This is the direct analogue of C2's isometric fragment
  for pure S — isolate the steps a measure controls, and no cycle can live inside
  them.
- **`sbCycle_needs_heavy_S`**: therefore any `{S,B}` cycle must fire an S-reduction
  duplicating a τ-**heavy** argument (`τ(x) ≥ 4`). Rung two remains open, but the
  target is a single named condition rather than an unbounded search. The boundary
  sits at small terms: `S S` has τ = 3 (light), `S (S S)` has τ = 5 (heavy).
- Also added **`RS.Acyclic.of_decreasing_measure`** (Taxonomy) — the dual of
  `of_strict_measure`, which covers growing hosts while terminating-style fragments
  need the other direction. Stage 17 had an ad-hoc copy inside
  `SI_no_decreasing_measure`.

### Stage 24: rung three {S,C} — τ separates what leafCount cannot

- **The τ family, recorded as arithmetic.** With `τ_k(app a b) = k·τ_k(a) + τ_k(b)`
  the S-reduction delta is `k(τ_k(x) − k²)`, so the τ-light fragment **grows with
  k**: `S (S S)` is τ₂-heavy (5 ≥ 4) but τ₃-light (7 < 9). The general-`k` lemmas
  need `ring`, which this zero-dependency tree does not have, so the family is not
  formalised; the k = 2 instance is `tauSB` (Stage 23).
- **The stage's finding.** `C x y z → x z y` has the *same* `leafCount` delta as
  `B x y z → x (y z)` — both remove exactly one leaf — so **no counting measure can
  separate rungs two and three.** τ separates them sharply:
  - `tauSB_B_red`: delta `−(2τ(x) + 8)`, always negative;
  - `tauSC_C_red`: delta `τ(z) − τ(y) − 8`, which **can be positive**, because
    permuting moves a heavy argument into a lighter position.
  Witnessed by two C-reductions with identical `leafCount` deltas (−1) and opposite
  τ deltas (29→35 and 43→21).
- **Consequences.** `SCLightStep` needs **two** clauses where rung two needed one, so
  `scLight_acyclic` is a weaker foothold than `sbLight_acyclic`; rung three is
  correspondingly further from a full acyclicity proof. `scSuccs` plus Stage 22's
  generic `onCycleAny` transferred for free: no cycle through any `{S,C}`-term of ≤ 6
  leaves within a 30-leaf cap, under any strategy, every term verdicted.
- **Rung three is open like rung two, but for a structurally different reason** — and
  that difference is invisible to every measure this program used before Stage 23.

### Stage 25: the literature does not apply, and the threshold bootstraps

The seventh review ranked "read the tree-automata papers" first, on the grounds that
Stage 6 had registered them and never used them. Read properly, **neither applies** —
and establishing that is the stage's most useful outcome.

- **Endrullis & Zantema, *Proving non-termination by finite automata* (RTA 2015).**
  General term rewriting, so it *does* cover `{S,B}` and `{S,C}`. Method: find a
  non-empty **regular** language of terms closed under rewriting containing no normal
  forms; certificate is a tree automaton; automated by SAT. Succeeds on "the S-rule
  from combinatory logic".
- **arXiv:2406.14305, *Disproving Termination of Non-Erasing Sole Combinatory
  Calculus with Tree Automata* (2024).** Applies **exclusively to sole
  (single-combinator) systems** — it cannot handle `{S,B}` or any multi-combinator
  basis. Settled 8 previously-open combinators (P, P₃, D₁, D₂, Φ, Φ₂, S₁, S₂); S, B,
  C, I are not among them, and S's non-termination is noted as already known.
- **Why neither helps: they prove NON-TERMINATION, and the open rung questions are
  about ACYCLICITY.** Those are different properties, and this program contains the
  proof that they differ — pure S is acyclic (C2) *and* non-terminating (external,
  Stage 6). Non-termination is about infinite paths; acyclicity is about *returning*
  ones. The automata certificate (a closed language with no normal forms) does not
  dualize to a no-return statement; ranking/measure arguments are the right tool for
  that, which is what the program has been using.
- What they *would* buy, registered as available: an automata certificate would
  upgrade Stage 19's census evidence that `{S,B}` is non-terminating into a theorem.
  Not the property needed, and it requires a SAT solver, which the Stage 16
  zero-dependency decision rules out for now.
- **The bootstrap** (`leafCount_S_red_heavy` and friends): chaining τ against
  `leafCount` raises Stage 23's threshold from τ(x) ≥ 4 to an *average* of τ ≥ 14 over
  a cycle's heavy S-reductions. Per-step facts proved; the summation is recorded as
  arithmetic. **And the limit is recorded too:** iterating gives `T' = 5·f(T) − 1` with
  `f` logarithmic (max τ on n leaves is `2ⁿ − 1`), so the iteration fixes around
  τ ≥ 24 and stops. τ grows exponentially in size while the constraint grows linearly.
- **No I-like combinator in `{S,B}`** up to 7 leaves, against four structurally
  distinct probes. That closes the transport route into rung two — the emptiest
  informative cell of the evidence chart — and is consistent with `{S,B}` being
  acyclic.

### Stage 26: the S-only fragment of {S,B} is acyclic

The ranked task was formalising Stage 25's τ ≥ 14 summation. Doing the arithmetic first
showed that is per-class path accounting — one accumulator per step kind — for a
*tightening* of a bound whose argument family Stage 25 already proved caps near τ ≈ 24.
Redirected to a new structural fact, per the standing lesson about doing the cheap
arithmetic before committing.

- **The observation:** the S-only fragment of `{S,B}` is pure S over a two-symbol
  alphabet, so **C2's squeeze transplants verbatim** — `leafCount` is monotone there
  (no B-reduction to shrink it), a cycle forces it constant, constancy forces every
  duplicated argument atomic, and τ drops by 6 on those.
- **`sbSOnly_acyclic`** (`Universality/Ladder.lean`), via `sbSStep_squeeze` and
  `sbSSteps_squeeze`. The per-step lemma states both halves — leafCount never shrinks,
  and when it is unchanged τ strictly drops — in **one** conjunction, because the path
  induction has to recover the strict τ drop from the first step once leafCount is
  pinned.
- **`sbCycle_needs_B`**: therefore **any `{S,B}` cycle must contain a B-reduction.**
- **The three constraints on rung two now compose**, and they were obtained
  independently: a cycle needs a B-reduction (Stage 26), needs a τ-heavy S-reduction
  (Stage 23), and needs at least two of the former per one of the latter (Stage 25).
  That is a joint necessary condition, not three restatements.

### Stage 27: rung three's S-only fragment, and an honest negative on pruning

- **`scSOnly_acyclic` / `scCycle_needs_C`.** `C x y z → x z y` has `leafCount` delta −1
  exactly like `B`, so C is `{S,C}`'s only shrinking rule and its S-only fragment again
  has monotone `leafCount`. Stage 26's argument transplants verbatim, giving rung three
  a **second** constraint: any `{S,C}` cycle must contain a C-reduction.
- **Duplication flagged rather than hidden.** The two S-only fragments are the same
  system — pure S over a two-symbol alphabet — so Stage 27 is a near-copy of Stage 26.
  Abstracting it would need a term type parameterised by its atom set plus transport
  lemmas: more work than the copy, and indirection for two instances. The judgment is
  recorded in the file so a reader knows it was a choice.
- **Rung two's constraints composed.** From `sbCycle_needs_B` a cycle has ≥ 1
  B-reduction, and Stage 20's `#B` arithmetic equates that count with the sum over
  S-reductions of `#B(third argument)`. So some S-reduction must duplicate an argument
  **containing a `B`**; with the τ-heavy condition and `leafCount_ge_three_of_heavy`:
  **a `{S,B}` cycle requires an S-reduction whose third argument has ≥ 3 leaves, and
  some S-reduction whose third argument contains a `B`.** Syntactic and checkable,
  unlike a τ threshold.
- **And it does NOT prune a seed search — measured, not assumed.** Filtering `{S,B}`
  seeds to those containing a `B` with ≥ 5 leaves leaves 434/448 at n=5 and
  109395/109824 at n=8 (99.6%). The condition constrains the **steps** a cycle must
  contain, not the **seeds** a search starts from. It could guide pruning *during*
  closure exploration — a different algorithm from `onCycleAny` — but it buys nothing
  for the hunt as written. Recorded so the condition is not credited with a speedup it
  does not provide.

### Stage 28: the composed condition, proved

- **Pruning-during-exploration is unavailable, checked before building.** Sound pruning
  needs a *localizable* certificate that the seed is unreachable from a given state.
  Every constraint rung two has is a **global sum** over a cycle, and global sums do not
  localize into per-state tests. So the one remaining use Stage 27 credited the composed
  condition with does not exist either.
- **But the condition itself is now a theorem.** Stage 27 stated it as arithmetic
  depending on an unformalised summation. Contrapositively it admits Stage 26's pattern:
  if no S-reduction duplicates a `B`, then `#B` never rises and strictly falls on every
  B-reduction, so a cycle can contain no B-reduction — and what remains is the S-only
  fragment, already acyclic.
- **`sbNoBDup_acyclic`** (`Universality/Ladder.lean`), via a **three-level squeeze**:
  `#B` never rises; when it holds still, `leafCount` never falls; when that holds still
  too, τ strictly drops. The three levels must travel in a single invariant because each
  one pins the next — the same lesson as Stage 26, one level deeper.
- **`sbCycle_needs_B_duplication`**: any `{S,B}` cycle contains an S-reduction whose
  duplicated argument contains a `B`. **The unformalised summation is no longer needed —
  the squeeze replaces the accounting entirely.**
- The fragment is strictly larger than the S-only one (it contains every B-reduction), so
  `sbNoBDup_acyclic` **subsumes** `sbSOnly_acyclic`, and Stage 26's result is now a
  corollary rather than an independent fact.

### Stage 29: the Tag → SK blocker, restated as a structural obstruction

The joinability-insensitive abstraction lifter had been the standing proposal for spec
Goal 2's blocker since Stage 10, carried in the ranking as "route 1". Checked before
building, and it yields one construction and one obstruction.

- **The generalisation, which any future attempt needs** (`Universality/Defs.lean`, all
  AXIOM-FREE): `RS.Joinable`; `RS.abstraction_tracks_rel` and
  `RS.bwd_of_abstraction_rel` — adequacy with the abstraction as a **relation** rather
  than a function; and `RS.bwd_of_abstraction_rel_generalises`, showing Stage 8's
  function version is the special case `absR b a := (abs b = some a)`. Relaxing to a
  relation is precisely what a joinability-style abstraction requires, since "decodes to"
  becomes semantic rather than computed. **The price is a new hypothesis: the relation
  must be functional on `enc`'s image.**
- **The obstruction sits exactly at that price.**
  `RS.joinable_abs_not_functional`: `Joinable · (enc ·)` relates an encoded state to
  *every* source state it came from, so it is never functional on the image once the
  source has a single nontrivial step. The proposal *does* fix drift — drifted copies
  remain joinable in a confluent host — but by being far too coarse: everything on a
  machine's trajectory is joinable with everything else, so joinability cannot tell
  machine states apart at all.
- **The resulting picture, which is the stage's content.** The two candidate routes to
  `bwd` fail for **opposite** reasons:
  - the **syntactic** abstraction is too **fine** — duplicated copies drift and it loses
    track (Stages 10, 13);
  - the **joinability** abstraction is too **coarse** — it collapses the trajectory.

  A workable abstraction must sit strictly between, and neither obvious construction
  does. Criterion (a) is therefore a **structural obstruction**, not unbuilt work — a
  more honest and more useful description than ten stages of "research-blocked".

### Stage 30: the nested squeeze, abstracted; rung three at parity

- **The abstraction, and the threshold I had set wrong.** Stage 27 said the duplication
  threshold was "a fourth rung". The right threshold was a fourth **instance** — SB
  S-only (26), SC S-only (27), SB no-B-dup (28), SC no-C-dup (30). Two rungs, four
  instances. `RS.Acyclic.of_three_level` (`Universality/Taxonomy.lean`) now carries the
  pattern once: three measures where each level pins the next — `m1` never rises; when it
  holds still `m2` never falls; when that holds still too `m3` strictly drops. A
  two-level squeeze is the case `m1 := fun _ => 0`.
- **What was actually duplicated** was the path lemma and the final contradiction — never
  the interesting part. All three existing instances refactored onto the generic lemma;
  each is now a one-liner given its per-step lemma. **This is the pattern behind C2's
  original argument too**, so the ladder's fragments and the program's first resolved
  conjecture are now visibly the same move.
- **Rung three reaches parity with rung two.** `scNoCDup_acyclic` and
  `scCycle_needs_C_duplication`: any `{S,C}` cycle contains an S-reduction whose
  duplicated argument contains a `C`. `#C` behaves exactly as `#B` — falls by 1 on a
  C-reduction, rises by `#C(x)` on an S-reduction — because C permutes without
  duplicating. And as at rung two the no-C-dup fragment strictly contains the S-only one,
  so it subsumes `scSOnly_acyclic`.
- Both rungs now have the same three constraints, and both have their S-only result
  subsumed by their no-X-duplication result.

### Stage 31: C5 proved — the "external" label was wrong

C5 had been labelled **external** since Stage 5 Slice 3, on the reasoning that it is the
λI conservation theorem (Church 1941; Barendregt §9.5) and that formalizing it means
importing classical λI machinery. Stage 30 ranked it as *transcription* on that basis.
Checking before building showed the label was wrong: **for pure S this tree can prove it
directly**, and the argument is five lines of English.

- **The proof** (`conservation`, `Conservation.lean`). Suppose `t` reaches a normal form
  `n` and also admits an infinite reduction. Then: **confluence** (Stage 1) makes every
  `tᵢ` reach `n`, since `n` is normal; **monotonicity** (Stage 2) bounds
  `leafCount tᵢ ≤ leafCount n`; **`enum_complete`** (Stage 6) puts every `tᵢ` in one
  *finite* list; **pigeonhole** forces `tᵢ = tⱼ` for some `i < j`; and
  **`no_pure_S_cycle`** (C2) forbids that. Every ingredient was already here — only the
  pigeonhole was missing.
- **`no_normalForm_of_infiniteRed`**: the contrapositive. **Exhibiting an infinite
  reduction sequence is now sufficient to prove non-normalization for pure S**, with no
  external dependency. That is exactly what C1(a)'s loop route was waiting on, and it is
  no longer waiting.
- **Fifth `Classical.choice` near-miss, same trap as Stage 9.** The natural proof uses
  `List.erase`, and *both* `List.length_erase_of_mem` and `List.mem_erase_of_ne` report
  `Classical.choice` — synthesising `LawfulBEq` from `DecidableEq` goes through it.
  Found by bisection, then rebuilt on `List.filter` with `decide`, which avoids `BEq`
  entirely, plus one length lemma of our own (`length_filter_lt`). The pigeonhole is also
  stated **negatively** (`not_injective_into_list`) so no classical step is needed to
  produce an existential.
- **What this changes about the ledger's discipline.** The `external` status was added in
  Stage 6 precisely to stop untested claims sitting as "open". It worked — but C5 shows
  the label can be wrong in the *other* direction: a claim marked external because a
  famous theorem covers it, when a cheaper route existed inside the development. **An
  `external` label should record where the claim is known, not close the question of
  whether this tree can prove it.**

### Stage 33: C1(a)'s target replaced — the size criterion

- **Stage 32's gap was an artefact of an over-strong demand.** `reducible_of_head_spine` is
  sufficient but not necessary for reducibility (head spine 2 can still reduce inside), so
  requiring it as a preserved invariant asked for more than the problem needs.
- **`no_normalForm_of_unbounded`**: a K-free term with reducts of unbounded size has no
  normal form. Proof: `leafCount_le_of_normalizes` — confluence sends every reduct to the
  normal form, monotonicity caps its size — so unbounded reducts contradict normalization.
- **`bounded_of_normalizes`**: the contrapositive. A normalizing K-free term has a size
  bound on its entire reduction graph. This changes how the census reads: the exploding
  sizes are not merely suggestive, because **any bound on them would have been a
  normalization proof**.
- **The target is now better matched to the evidence** in three ways: no preserved
  predicate is needed; it is the quantity the census measured; and progress toward it is
  cumulative, unlike three slices of invariant hunting.
- Remaining: a growth step. Open.

### Stage 34: growth is necessary — and a classical result declined

- **`normalizes_of_no_growth`** (`Conservation.lean`): a K-free term whose reducts never
  grow must normalize. Strong induction on τ — each step on a size plateau strictly drops τ
  (`tau_lt_of_isometric_step`), and a Nat cannot drop forever. **So growth is necessary for
  non-termination in pure S.** The recursion is on `stepOnce`, not a classical case split
  over `NormalForm`, which is what keeps it constructive: `stepOnce` is computable and
  certified on both ends, so "normal or reducible" is *decided* rather than assumed.
- **Together with Stage 33** this is most of the equivalence between *"no normal form"* and
  *"unbounded reducts"* — the two currencies the census and the conjecture were using.
- **A classical result built, measured, and declined.** The remaining direction (no normal
  form ⇒ unbounded) is three short proofs away, but going from a **negative** hypothesis to
  a **positive** conclusion needs `¬∀ → ∃`, which is not constructive. Written the obvious
  way, all three reported `Classical.choice` — the sixth occurrence in this tree and **the
  first that was intrinsic rather than an instance-layer accident**. Removed rather than
  shipped: the tree has advertised no `Classical.choice` since Stage 0, the equivalence is a
  nice-to-have, and the direction that is a *tool* was already choice-free.
- **The constructive route is recorded rather than left as a gap.** Replace the negative
  hypothesis with "every reduct is reducible"; build the trajectory from `stepOnce`
  (computable, hence choice-free); prove `leafCount (f k) = leafCount t → tau (f k) + k ≤
  tau t` by induction on `k`; instantiate at `k = tau t + 1`, where the bound is
  contradictory. The refuted proposition is **decidable**, so monotonicity upgrades it to
  strict growth with no classical step. The equivalence is constructively true; this
  development just does not yet contain it.

### Stage 35: the equivalence, constructively — and Stage 34's obstruction was avoidable

- **`no_normalForm_iff_unbounded`** (`Conservation.lean`, `[propext, Quot.sound]`): for a
  K-free term, **having no normal form is the same thing as having reducts of unbounded
  size.** This settles the framing question Stages 32–34 circled — the census measured
  sizes, the conjecture asked about normalization, and for pure S they are one question.
- **Stage 34 called the negative-to-positive step intrinsic. It was not.** Stage 34's
  `by_cases` was on `∃ u, t ⟶* u ∧ leafCount t < leafCount u` — a statement about *all*
  reducts, genuinely undecidable. But `∃ v, u ⟶ v` for a **fixed** `u` is decided by
  `stepOnce`. Routing through "every reduct is reducible"
  (`all_reducible_of_no_normalForm`, which cases on the computable `stepOnce` rather than on
  the proposition) needs no classical step anywhere.
- **The machinery**: `iter` (the trajectory as a total function, stalling at a normal form),
  `iter_reduct`, `iter_step`, then `tau_budget` — if the trajectory has not grown by step
  `k`, τ has paid `k` units, since every plateau step drops τ. The growth step is then found
  at index `tau t + 1`, where the budget is exhausted, and iterating gives unboundedness.
- **The lesson, narrow and reusable:** *"this needs `¬∀ → ∃`"* depends on **which** `∀`. A
  quantifier over a fixed term's successors is decidable; one over all reducts is not.
  Stage 34's removal was right to preserve the tree's choice-freeness and wrong about the
  obstruction.

### Stage 36: the reformulations of C1(a) are all the same problem

- **`c1a_formulations`** (`Conservation.lean`, constructive): four statements proved
  equivalent —
  1. `t` has no normal form (the conjecture as stated);
  2. every reduct of `t` is reducible (Stage 35's "better target");
  3. there is a reducibility invariant with an explicit successor function (the route hunted
     in Slices 3, 4 and Stage 32);
  4. `t`'s reducts have unbounded size (Stage 33's criterion).
- **What that says about the last four stages.** Stages 32, 33 and 35 each replaced C1(a)'s
  statement with a provably equivalent one, and each time I read the replacement as progress.
  It was not. `(2) → (3)` is the sharpest illustration: `fun u => t ⟶* u` is *itself* an
  invariant whenever every reduct is reducible, so the invariant route and the positive route
  were never different problems.
- **Consequently the cycle cannot repeat.** Any further reformulation along these lines is a
  restatement. **Closing C1(a) requires a new fact about pure-S reduction** — something that
  produces, for one concrete term, an infinite reduction, an unbounded family of reducts, or a
  preserved reducibility predicate. The tree now supplies every *bridge* between those and
  none of the *sources*.
- **What the program has contributed to C1(a)**, recorded so the above is not mistaken for the
  whole story: C1(b) proved (nothing below 7 leaves diverges); C5 proved (an infinite
  reduction suffices); the frozen head proved (`c1`'s trajectory is `S A B` with `A` a fixed
  normal form, reducing the question to the payload); this equivalence, so the target is
  unambiguous; and three honest negatives — no self-embedding for `c1` within 120 steps, none
  for the literature's 14-leaf term within 40, and no I-like combinator in `{S,B}`.

### Stage 37: construct-don't-search, attempted

Stage 36 named the one route with genuinely new content: build a self-embedding `t ⟶⁺ C[t]`
by design. Such a `t` gives an infinite reduction directly (`C[t] ⟶⁺ C[C[t]]` by congruence)
and hence, via C5, no normal form — proving C1(a). Note **C2 forces `C` to be non-trivial**,
since `t ⟶⁺ t` is a cycle and pure S has none, so the target is *strict* self-embedding.

Attempting it meant first searching the design space systematically — which Slices 3 and 4
never did, having checked `c1` and `c2` only. **Result: nothing.**

```
leftmost-outermost, 60 steps, cap 3000,  every pure-S term up to 8 leaves:  0
leftmost-outermost, 200 steps, cap 20000, every term up to 8 leaves:        0
ALL STRATEGIES (bounded closure, cap 40, fuel 200), every term up to 6:     0
```

- **The all-strategies row is the one that counts.** Stage 21 showed a leftmost-outermost hunt
  provably misses cycles that exist in the relation — rung one's `omegaSI` is the witness — so
  an LO-only negative would have been weak evidence. The closure search is
  strategy-independent.
- Shipped as `selfEmbeds` with build-enforced guards at an affordable size; deeper runs
  recorded. Slice 3's 120-step result on `c1`/`c2` extended to 200 steps under a size cap.
- **What changes:** the route is no longer *unexplored* but *searched and empty where
  searchable* — a materially stronger negative than the ledger held.
- **What is not settled:** whether self-embedding is **impossible** in pure S. No obstruction
  is proved and none is apparent; C2 rules out only the trivial context. Proving impossibility
  would close the loop route for good; a witness at larger size would prove C1(a). The search
  cannot decide between them.

### Stage 38: the one-step obstruction, proved

Stage 37 ranked "prove self-embedding impossible in pure S" first and recorded that **no
obstruction was proved and none was apparent.** One is apparent after all — at depth one.

```
Step.not_sub_self : (t ⟶ u) → ¬ Subterm t u
```

Every SK term, no size bound. This is a different KIND of statement from Stage 37's search:
not "no witness below 8 leaves" but "no witness, ever, at depth one".

- **It has to be structural.** A measure falling on every pure-S step would prove strong
  normalization and hence *refute* C1(a). So no measure can close this.
- **What works:** the reduct of a redex never contains that redex. `S f g x ⟶ f x (g x)`,
  whose subterms are exactly `f x`, `g x`, the reduct, and the subterms of `f`, `g`, `x`. The
  last group is too small to hold the redex. Each of the first three forces an equation no
  term satisfies — `x = g x`, or `f = S f g` — since a term is never a proper subterm of
  itself. Congruence lifts it to a redex anywhere, and **transitivity of the subterm relation**
  is what makes the lifting work: if `app f u` sits inside `f'`, so does `f`, which is the
  induction hypothesis.

Also proved:

| | |
|---|---|
| `selfEmbed_leafCount_lt` | any self-embedding must **strictly grow** — equal leaf counts force equality, hence a cycle, which C2 forbids. The kernel form of Stage 37's prose claim that `C` cannot be trivial. |
| `selfEmbed_needs_two_steps` | the first step cannot be the whole path. |
| `isSubterm_iff_Subterm` | the Bool census predicate agrees with the kernel relation, so Stage 37's guards and Slice 3's are about `Subterm`, not about a search routine. |

**What does not lift, and exactly why.** The natural argument inducts on path length: given a
shortest self-embedding `t ⟶⁺ w` with last step `v ⟶ w`, split `t`'s occurrence in `w` by its
position relative to the redex. Off the redex, `t ⊴ v`, so `t ⟶⁺ v` is a shorter
self-embedding and minimality closes it. The residual cases are where the occurrence meets the
redex `S f g x`, and there `t` is one of: **a term containing the reduct `f x (g x)`**, **`f x`**,
or **`g x`**. None is contradictory on its face — size does not kill them (a self-embedding is
*allowed* to grow, which is what `selfEmbed_leafCount_lt` says) and neither does acyclicity
(these `t` need not recur). So the depth-one proof is a genuine base case with no inductive step.

Standing: the loop route now carries two proved constraints — **≥ 2 steps** and **strict
growth** — where Stage 37 left it carrying only search evidence.

### Stage 39: the trichotomy proved, and two of three shapes measured empty

Stage 38 left the three residual shapes as prose. They are theorems now.

| | |
|---|---|
| `Step.subterm_split` | **the positional trichotomy.** A step fires ONE root redex `r ⟶ r'` sitting inside `v`, so every subterm of `w` either already occurred in `v`, or contains `r'`, or is contained in `r'` — the three positions available relative to a single rewritten site. |
| `selfEmbed_residual_shapes` | the trichotomy applied. In a shortest self-embedding, the last step's redex is some `S f g x` inside `v` and `t` is one of exactly three shapes: **(A)** contains the reduct `f x (g x)`, **(B)** `t = f x`, **(C)** `t = g x`. |

Supporting: `RootRedex` (`Step` minus congruence — what a step's *witness* is), `KFree.of_subterm`,
`subterm_S_reduct_cases`, the three arg-subterm lemmas. All **axiom-free**, not even `propext`.

**Then measured — and Stage 38's ranking is inverted.** Stage 38 ranked shapes B and C first,
calling them "the constrained ones". They are constrained past the point of usefulness:

```
shapes B and C:  0 hits at every size up to 8 leaves
shape A:         1 at six leaves, 4 at seven, 19 at eight
```

B and C are empty *without* the `t ⋬ v` side condition, so the emptiness is theirs and not the
filter's. Proving them impossible would narrow the residue from three shapes to one and **would
not touch the obstruction** — shape A is where the difficulty lives, and it grows with size.

*The right question to measure.* The full residual **configuration** cannot occur: it is a case
analysis *of* the self-embedding hypothesis, so an instance would **be** a self-embedding and
Stage 37 found none. What is measurable is whether each shape's own structural demand is
satisfiable among a term's reducts — and the three shapes answer that differently.

**Loop route, honest standing:**

- depth one — **closed**, every SK term (`Step.not_sub_self`)
- any depth — reduced to **one shape** by the trichotomy: a self-embedding's last step must put
  `t` strictly *above* the reduct it fires; the other two shapes empty by measurement
- that one shape — **open**, inhabited, growing with term size

### Stage 40: shape A closed — the loop route now rests on the shape measured empty

Stage 39 ranked shape A first and recorded no argument. There is one, and it comes from noticing
what the trichotomy **threw away**.

`Step.subterm_split` records that a subterm of `w` above the redex "contains the reduct". That is
weaker than the truth. If `t` sits at a position above the redex, then the subterm of `v` at that
**same position** — call it `u` — satisfies `u ⟶ t`, by firing the very same redex. So shape A
does not say `t` contains something. It says:

> `t` is a one-step reduct of a subterm of `v`.

And that is fatal. `u ⊴ v` together with `u ⟶ t ⟶⁺ v` makes `u` a self-embedding term in its own
right, **one step earlier** than `t`. Walking backwards cannot go on forever: a pure-S step never
adds leaves, and a leaf-preserving step strictly lowers τ (`tau_lt_of_isometric_step` — the engine
of C2), so each backward step drops a rank built from the finite universe `smallTerms`.

| | |
|---|---|
| `Step.subterm_split'` | the strengthened trichotomy — "above the redex" recorded as *one-step reduct of a subterm* |
| `nuBelow`, `nuBelow_lt_of_step` | the rank, and the fact that stepping *backwards* lowers it |
| `selfEmbed_imp_halfShape` | **if any pure-S term self-embeds, some pure-S term has `HalfShape`** |
| `no_selfEmbed_of_no_halfShape` | contrapositive — the form the loop route now takes |
| `halfShape_target_ne` | the reduction is not vacuous: the redex outweighs both halves of its reduct, so `HalfShape` cannot be met by standing still |

`HalfShape` is **exactly** what Stage 39's census probe measured, and measured empty for every
pure-S term up to eight leaves. So the shape that was inhabited and growing is now impossible, and
the single remaining route is the one with no known instance at any size searched.

**C1(a), loop route:**

- depth one — closed, every SK term
- shape A (above the redex) — **closed**, every pure-S term, no size bound
- shapes B/C (`HalfShape`) — open, **no instance up to 8 leaves**

*Seventh Classical.choice encounter*, two new variants, both from `omega`: case-splitting a
**disjunctive hypothesis** costs the axiom, and so does a **disjunctive goal with a conjunction
nested inside it**. Both fixed by splitting by hand and supplying witnesses as terms.

### Stage 41: the ceiling raised, and two of three backward cases pinned

**A correction first.** Stage 39's guards read stronger than they were. `closureStep` keeps only
reducts with `leafCount ≤ bound`, so a size-capped closure **saturates having silently dropped
everything larger**. "No `HalfShape` witness in the closure at cap 24" means "none among reducts
reachable *through* terms of at most 24 leaves" — not "none at all". A witness needs `1 + |g|` more
leaves than `t` has, so a low ceiling is exactly where one would hide.

Raising the ceiling does not produce one:

```
strategy-independent, cap 40, every pure-S term up to 8 leaves:   0
strategy-independent, cap 60, every pure-S term up to 7 leaves:   0
leftmost-outermost, cap 4000, 300 steps, up to 8 leaves:          0
```

The LO trajectories really do run away — the largest reduct visited carries **3994 leaves** — so
they cover a size range the closure search cannot, along one strategy instead of all.

**Toward a proof.** Backward induction along the path is the right frame: every trichotomy case
steps back exactly one reduction, the path is finite, and at its start the requirement must be a
subterm of `t`, which size forbids (`S f g x` outweighs `t = f x` by `1 + |g|`). So it needs an
invariant surviving every case, and `|requirement| > |t|` survives **three of four** sub-cases:

| sub-case | status |
|---|---|
| inherited | invariant unchanged |
| one half of a bigger redex | `app3_S_reduct_half_grows` — requirement grows by ≥ 2, and `app3_S_reduct_half_forces` pins the bigger redex: third argument is `x` itself, `(S f) g` is one of the first two |
| produced by a **root** redex | `app3_S_as_root_reduct` — redex forced to `S (S f) b g` with `x = b g`, so the third argument strictly **shrinks** and the size is exactly `|t| + 2` |
| produced by a step **inside** it | **OPEN.** `u = p x` with `p ⟶⁺ (S f) g`, or `u = ((S f) g) q` with `q ⟶⁺ x`. The invariant can fail here: pure-S reduction grows, so `p` may be far lighter than `(S f) g`, and nothing yet stops `|u|` dropping to `|t|` or below. |

That last sub-case is the whole remaining gap. It is smaller than "prove `HalfShape` uninhabited"
was — it asks only whether a term at or below `t`'s size can reduce, at its own root, into
`S f g x`'s left spine. **Three controlled cases are not most of a proof**: the uncontrolled one is
where reduction's growth lives, which is where every hard case in this development has lived.

### Stage 42: pure-S growth accounted exactly; the gap is one size condition

Working Stage 41's arithmetic out properly made both halves of it sharper — and one was needlessly
specific.

| | |
|---|---|
| `reduct_half_lt` | a reduct half is **always** lighter than its redex, whatever its own shape. `app3_S_reduct_half_grows` was a special case of two lines of arithmetic; that branch of the backward induction needs nothing about S-shapes. |
| `step_growth_eq` | **a pure-S step grows a term by exactly `leafCount c - 1`**, where `c` is the third argument of the S-redex that fired, and `c` occurs in the source. The quantitative form of Stage 2's monotonicity: not "size does not fall" but "size rises by the weight of what got duplicated, less one". |
| `backward_invariant_or_big_duplication` | one step back, the requirement still outweighs `t` and stays **linked** to what it replaces — unless it was produced by a step duplicating an argument of at least `\|s\| + 1 - \|t\|` leaves. |

So Stage 41's "fourth sub-case" is not a case of a case analysis. It is a **size condition on a
single subterm**.

**The linkage clause is the content, and I nearly shipped without it.** Unlinked, the first disjunct
is almost vacuous: every reduct of `t` already outweighs `t`, so `s' = v'` satisfies it at every
point of the path but the start. Tracking the requirement is what makes this an induction step —
at the path's start it must be a subterm of `t`, and no subterm of `t` outweighs `t`.

**A second route, now enabled.** `selfEmbed_imp_halfShape` is strengthened to bound its witness by
the size of the term that self-embedded. The bound comes free — every source the descent produces is
a one-step predecessor, and pure-S steps never shrink — and it makes an **induction on term size**
available: chasing the requirement's *shape* rather than its size yields, at the path's start, a
self-embedding of a term strictly smaller than `t`. Two of that route's three start-cases work out;
the third (the requirement hiding inside `x`) does not yet.

### Stage 43: the literature hour — and C1(a) PROVED

The hour that STATUS.md said was owed since Stage 7 finally happened, and it paid in both
directions.

**The bad direction.** Endrullis & Zantema, *Non-termination using Regular Languages* (IWT 2014),
Example 2: *"For the S-rule it is known that there are no reductions `t →* C[t]` for ground terms
`t`, see [15]"* — [15] = Waldmann, *The Combinator S*, Inf. Comput. 159 (2000). **Stages 37–42
were re-deriving Waldmann's ground-loop theorem**, and reached one size condition short of it.
What survives: `Subterm`, `Step.subterm_split'`, `step_growth_eq`, `selfEmbed_imp_halfShape` —
reusable machinery. And one live pointer: the same Example 2 notes the **open-term** version,
`t →* C[tσ]`, is **open**. Everything in this development is ground.

**The good direction — C1(a) is now a theorem.** The same paper hands over the technique.

*Method (their Theorem 4).* A system is non-terminating **iff** there is a non-empty **recurrence
set**: every member has a redex, and every member steps to a member. No infinite object required —
the *set* is the certificate, and for the S-rule it can be taken **regular**.

Their automaton (Example 7) is nondeterministic with five states. Determinizing by hand gives six
reachable state sets (`Dst`). That trade — one extra state — removes all the infrastructure:

| | |
|---|---|
| `dstep_rule` | the quasi-model condition for the S-rule — the whole mathematical content, 216 cases by `decide` |
| `st_le_of_step` | closure under rewriting (their Thm 17). No `KFree` hypothesis needed: a `K` forces `bot`, and `bot` is below everything |
| `has_redex_of_s34` | every accepted term has a redex. They use a product-automaton inclusion; here the transition table gives it directly — the accepting state forces left spine ≥ 3, and a K-free term with spine ≥ 3 cannot be normal |
| `infiniteRed_of_s34` | iterate the certified evaluator; closure means it never runs out |
| **`c1a`** | **C1(a).** C5 supplies the last step — for pure S, "admits an infinite reduction" ⟹ "has no normal form" is *not* automatic; it **is** conservation |

**Witness:** `S S S (S S S) (S S S (S S S))` — twelve leaves, K-free.

Cross-checked against the census evaluator (a separate mechanism): leaf count climbs monotonically
**12 → 776** over 40 steps and never normalises. Guarded, not remarked.

**Not tight, and recorded as such.** C1(b) proves the true divergence floor is **seven** leaves,
and the automaton rejects both seven-leaf candidates — so `c1` and `c2` remain individually open.
Twelve is this certificate's floor, five above the real one.

**The ledger is now:** C1(a) proved, C1(b) proved, C2 proved, C3 retired, C4 proved, C5 proved,
C6 open and low-materiality. No entry is `external` any more.

### Stage 44: the finite-state route to rung acyclicity — measured, then ruled out

Stage 43 ranked rungs 2/3 first and named the missing tool: after counts (killed by
`no_monotone_counting_measure`) and positional measures (τ, which rises on S with heavy arguments),
the third category was to be **finite-state invariants** — what settled C1(a). I searched before
building.

**The search** (scratch tooling). Exhaustive over every automaton invariant with ≤ 3 states:
`φ(leaf)` per combinator, `φ(app a b) = f(φ a, φ b)`, `f` **monotone** in each argument,
`φ(reduct) ≤ φ(redex)` for all reachable argument states. Searching linear orders is free — an
invariant non-increasing in a partial order is non-increasing in every linear extension.

```
{S,B} 3 states: 608 monotone non-increasing, 154 with a strictly dropping step
{S,C} 3 states: 499                          121
```

The first run omitted monotonicity and reported hundreds that were not invariants at all — without
it the rule inequality does not survive being placed in a context.

They exist, and they are **not** all facts the tree already has. I guessed they would factor
through "is B-free" and "spine capped at two"; only **58 of 154** do.

**And it does not matter, because the ceiling is now a theorem.**

| | |
|---|---|
| `RS.no_decreasing_measure_of_infinite` | a strictly-decreasing measure proves **termination**, so no system with an infinite reduction has one — and C1(a) supplies that for anything containing `S` |
| `RS.no_return_of_strict_drop` | what a non-increasing measure *does* buy: nothing climbs back, so its strict steps cannot lie on a cycle |
| `RS.const_on_cycle` | equivalently: constant on cycles |
| `RS.PureS_hasInfinite` | C1(a) transported to the K-free subtype the ladder's refutations quantify over |
| `no_decreasing_measure_pureS` | hence **C2's three-level squeeze was forced, not chosen** |

A bounded invariant **partitions** the cycle space; it cannot **empty** it. Finite-state invariants
can therefore add constraints of the same kind as `sbCycle_needs_heavy_S` indefinitely and never
close a rung. Acyclicity must come from the unbounded well-founded level — and both candidates
there are shut.

**The ranking error.** I treated "tree automata" as one tool; the literature has two, doing
opposite jobs. Endrullis–Zantema certify **non-**termination, where a bounded certificate is fine
because one is *exhibiting* an infinite path rather than ruling one out — which is why Stage 43
transferred so cleanly. The termination direction (Geser–Hofbauer–Waldmann–Zantema 2007;
match-bounds) draws well-foundedness from a **height annotation** bounded over the reachable set:
a different mechanism, and a much larger build. Rungs 2/3 need the second, and it is not a
corollary of the first.

### Stage 45: the adequacy blocker has a mechanism (Goal 2)

Goal 2's remaining gap is a `Simulation` from a known-universal machine into SK, and its hard
obligation is `bwd`. Stage 13 left it with two routes dead and a third named but untried:

| route | status |
|---|---|
| abstraction up to `Joinable` | too **coarse** — `RS.joinable_abs_not_functional` |
| constrain the encoding so duplication only hits normal forms | refuted by Stage 13: transient duplicates are unavoidable in SK, and occurrence-counting does not help |
| *"read only the live spine, ignore subterms destined for a K-discard"* | **untried** |

The third has a small mechanism. A doomed subterm is doomed because some `K` will discard it — so
**contract the K-redexes first and read the result.** A doomed copy `(K a) u` collapses to `a` no
matter what `u` drifted into, so drift becomes **invisible** rather than prevented or tolerated.
`leafCount` is enough fuel, since each K-contraction discards both the `K` and an argument.

```
naiveAbs desync' = none      -- Stage 10's failure: drift lost the count
absK     desync' = some 0    -- restored
absK (Itower n)  = some n    -- still inverts the encoder, which is habs
stutter-or-advance: 0 failures over EVERY SK term up to 7 leaves (20386 terms, K included)
non-vacuous:       absK is defined on 813 of the 16896 seven-leaf terms
```

The test enumerates **all** SK terms rather than the reachable ones, because
`RS.bwd_of_abstraction` quantifies `hstep` over every pair of host terms.

`kStepOnce`/`kNorm`/`absK` ship as **unverified census tooling** and say so. Three attempts at
certifying soundness and the `leafCount` bound ran into the overlapping-pattern equation lemmas and
were abandoned per the three-attempt rule. Guards verified to bite by negative control.

**Not settled, and both are real.** *The general proof:* a K-step leaves the K-normal form alone
(modulo confluence of K-reduction, unproved here), but an S-step creates and destroys K-redexes, so
`absK` tracking one is exactly what needs an argument — agreement over 20386 terms is evidence, not
a theorem. *The source system:* the countdown is a genuine multi-step machine but is not universal,
so piece (v), the tag-step driver, is still unwritten. What changed is that its hardest obligation
now has a mechanism instead of two dead ends.

### Stage 46: confluence of K-reduction, and unique K-normal forms

Stage 45's mechanism reads a host term only after its doomed subterms are discarded, which makes
*"the K-normal form of `t`"* load-bearing — and the abstraction is well defined only if that phrase
denotes. This is the lemma Stage 45's ranking named.

Architecture mirrors `Confluence.lean` restricted to the K rule, because that file already
establishes the pattern in this development: `KStep`/`KSteps`, parallel `KPar` in between, complete
development `kdev`, Takahashi's triangle, then diamond → strip → confluence. The K-only version is
**strictly simpler** — no `S_red` case anywhere, and `kdev` has one redex arm instead of two.

| | |
|---|---|
| `KStep` / `KSteps` | the K rule and congruence, S-redexes deliberately excluded — contracting one is what *advances* an encoded machine |
| `KStep.toStep` | everything here sits inside the ambient SK system |
| `KPar`, `kdev`, `KPar.triangle` | Takahashi |
| `kconfluence` | **K-reduction is confluent** |
| `knf_unique` | **"the" K-normal form is well defined** |
| `IsKNF`, `IsKNF.unique` | the relational form, which is what `RS.bwd_of_abstraction_rel` needs |
| `IsKNF.of_kstep` | **a K-step does not move the K-normal form** |

That last one is exactly the **K-step case** of Stage 45's stutter-or-advance obligation, and it
needs no case analysis on the encoding: a host step that merely discards a doomed subterm leaves the
abstraction alone. Half the crux, certified.

Anchored against vacuity: `S` and `I` are K-normal — the second matters, since an S-redex being
K-normal is what keeps the machine's own steps out of the abstraction's reach — and `K S S` has
K-normal form `S`.

Deliberately **not** claimed: nothing here concerns the fuel-based `kNorm` in `AdequacyProbe.lean`,
which remains unverified census tooling. These are results about the *relation*.

Axioms: `[propext]` or none.

### Stage 47: adequacy reduced to one case, and the cheap route to it refuted

Assembling Stages 45/46 for the probe's own test machine. The abstraction is relational — `b` stands
for countdown state `n` when `b`'s **K-normal form** is `Itower n`.

**Discharged:**

| | |
|---|---|
| `Step.kOrS` | every SK step is a K-step or an S-step — the split is a theorem, not an assumption |
| `kNormalForm_Itower` | `habs`: the encoding is K-normal, so the abstraction reads it unchanged. Rests on `kNormalForm_I` — if the abstraction could K-reduce an `I` layer it would **advance the machine while claiming to observe it** |
| `Itower_injective` | via `leafCount (Itower n) = 3n + 1` |
| `absKNF_enc` / `absKNF_functional` | `habs` and `hfun`. `hfun` is the obligation that killed the joinability abstraction; reading the K-normal form passes it |
| `itower_fwd` | `fwd`: one countdown step is two host steps |

So of `bwd_of_abstraction_rel`'s three obligations, two are done and `hstep` splits by `Step.kOrS`:

- **K-step: done** via `IsKNF.of_kstep`, with nothing encoding-specific in it. The case Stage 45's
  mechanism existed for — now a theorem rather than 20386 measurements.
- **S-step: open**, and it is the half genuinely about the machine.

**The cheap route to it is refuted.** The tempting one-layer statement

```
SStep b b' → SStep (kdev b) (kdev b') ∨ kdev b = kdev b'
```

is **false** — `naive_kdev_commutation_fails`, on `S K S S`. When the fired redex is `S K g x` its
reduct `(K x)(g x)` is *itself* a K-redex, so `kdev` fires that too and lands further along than one
S-step from `kdev b` can reach. The true shape is a **commutation square** — S-step *then*
K-reduction — which is worth knowing before the next attempt spends a stage on the equation.

Two narrowings recorded but **not** proved: `Itower n`'s only redexes are its `I` layers' S-redexes,
so the square's right side is constrained; and an S-step in a doomed subterm cannot move the
K-normal form at all, while K-reduction never duplicates, so a live S-redex has exactly one
downstream image.

### Stage 48: adequacy CLEARED — a `Simulation` of a multi-step machine inside SK

The blocker Stage 8 flagged as *the piece that could fail in kind rather than in volume* is closed.

| | |
|---|---|
| `sk_local_square` | an S-step and a K-step out of the same term close up |
| `sk_square` | ...lifted to whole K-reductions |
| `itower_sStep` | an S-step out of the encoding advances it by **exactly one** |
| `naiveAbs_Itower` | `dec_enc` |
| `countdown_hstep` | **`hstep`, complete**, by `Step.kOrS` |
| **`countdownInSK`** | **`Simulation RS.Countdown RS.SK`** |

Both weakenings in the square turned out to be **forced**, and by different cases: *zero* S-steps on
the K-side when the S-redex sits in the argument a `K` discards, and *two* K-steps on the S-side when
the S-step duplicated a K-redex. Stage 47 was right that the equation is unavailable; the square
replaced it.

The S-step case closes because an S-step out of `Itower n` is completely determined — its only
redexes are the `I` layers, and firing one leaves `(K u)(K u)`, which K-collapses to `u`. So the
square's S-side output is `Itower n` itself (stutter) or one layer further along (advance).

**The full arc:** Stage 10 found the failure (duplicated arguments drift). Stage 13 refuted the first
two fixes — *constrain the encoding* is impossible, since transient duplicates are unavoidable in SK,
and *abstract up to joinability* is too coarse (`joinable_abs_not_functional`). Stage 45 found the
third: read the **K-normal form**, so drift is *invisible* rather than prevented or tolerated. Stage
46 made that denote. Stages 47–48 proved it.

`sk_local_square` and `sk_square` need **no axioms at all**.

**The limit, stated plainly.** The countdown is **not** universal, so this discharges the *mechanism*
criterion (a) was blocked on — not criterion (a). A tag-step driver, spec piece (v), is still
unwritten. What changed is that its hardest obligation is now a solved problem with a worked example
rather than a research risk.

### Stage 49: what the K-normal-form abstraction actually demands — a correction to Stage 48

Stage 48's ranking said piece (v) could follow the countdown's pattern *"provided the driver keeps its
data K-normal"*. That is too optimistic, and the tree already contained the theorem that says so.

`knf_abstraction_forces_encodings` — `RS.abstraction_tracks_rel` forces the abstraction to be defined
at **every reachable host term**, not just at encodings. So if the K-normal-form abstraction
discharges `hstep`, then every term reachable from an encoded state K-normalises to an encoding, of a
source state reachable from the original. **The constraint is on intermediates, not on data.**
(Axiom-free.)

Verified on the countdown, and the measurement shows how strong the property is:

```
183 terms reachable from Itower 3
every one K-normalises to an encoding
and to nothing but the four states reachable from 3 — leaf counts 10, 7, 4, 1 = 3n+1
```

The whole reachable set collapses onto the encodings.

**Why this changes the remaining work.** The countdown's driver does its entire step in **one** S-step
followed by K-reduction, which is exactly why every intermediate K-normalises to the after-state. A
tag-step driver must inspect a symbol and dispatch, and each of those S-steps produces an intermediate
that must *also* K-normalise to an encoding — before-state for the early ones, after-state for the
later ones, **flipping exactly once**. Not obviously satisfiable; not obviously unsatisfiable either,
since combinator programming can hide work inside K-discards. What is clear is that it is the thing to
**prototype** before writing a driver — the lesson Stage 8 learned about piece (vi), arriving one piece
later.

**Two honest consequences:**

- *"Adequacy has a template"* is right about the machinery and wrong if read as *"the rest is
  construction"*. The template comes with a side condition the countdown satisfies for a reason the
  countdown alone explains.
- A driver could use a **different** abstraction. `RS.bwd_of_abstraction_rel` takes any relation, so
  this says what the K-normal-form one costs — not that it is the only option.

### Stage 50: prototyping the intermediate condition — dispatch passes, recursion does not

Stage 49 said to prototype the K-normal-form abstraction's demand before writing a driver. The
diagnostic is a **ratio**: along one source step's trajectory the abstraction tolerates at most **two**
distinct K-normal forms — before-state and after-state — so a construct producing more than that per
step cannot be tracked.

```
dispatch, true branch    K (S S) (K K)      reachable   2    K-normal forms   1
dispatch, false branch   S K (S S) (K K)    reachable   3    K-normal forms   2
countdown                Itower 3           reachable 183    K-normal forms   4
self-application         omegaSK            reachable 107    K-normal forms  17
```

**Dispatch passes, and exactly.** `S K a b` shows precisely two K-normal forms — itself and the
selected branch — because selecting is one S-step whose reduct is a K-redex, so it commits immediately
and the doomed branch vanishes with it. That is the flip-once behaviour the abstraction wants, arising
natively from the idiom. Dispatch was the part I expected to fight; it comes for free.

**Self-application does not.** `omegaSK`'s reachable set is *smaller* than the countdown's and its
K-normal forms are four times as many, sprawling into nested `S K K (…)` shapes instead of collapsing.

So the blocker for piece (v) is **recursion, not dispatch** — corroborating with numbers what Stages 11
and 13 flagged in prose about the pending recursive call.

**Honest limit.** `omegaSK` is not a driver and has no source machine, so seventeen K-normal forms is
not a refutation: a real driver's seventeen could all be encodings of reachable source states, since
the abstraction may stutter across many host terms. What the ratio shows is a **trend** in the wrong
direction — the countdown's set collapses as the closure grows, `omegaSK`'s does not.

Two routes for piece (v), and this stage says which is which:

- keep this abstraction and find a recursion scheme that **commits each unfolding through a K-discard**
  — a real design constraint, not obviously achievable;
- or use a different abstraction. `RS.bwd_of_abstraction_rel` takes an arbitrary relation, so the
  countdown's choice is not binding.

### Stage 51: committing steps cannot compute; and a conflation corrected

Stage 50 ranked *"find a recursion scheme that commits each unfolding through a K-discard"* first. That
phrasing is **impossible**, and the reason is two lines of injectivity.

| | |
|---|---|
| `committing_S_red_iff` | an S-step's reduct is a K-redex **only** when the first argument is literally `K` |
| `committing_S_red_projects` | and then `S K g x` reduces to `x`, discarding `g` — and the duplicate the S-step made sits *inside* that discarded argument, so it does no work either |

So committing steps cannot compute, and no driver can be built from them alone. What survives is the
weaker demand: **non-committing** S-steps whose intermediates K-normalise to encodings by some other
route.

**A conflation corrected.** Stage 50 treated "recursion" and "non-termination" as the same thing and
tested `omegaSK`. They are not — **the countdown terminates.** Its 183 reachable terms come from the many
orders its `I` layers may fire in, not from unbounded computation. What a driver needs is
**self-reproduction** — the driver reappearing alongside advanced data — with each segment finite.

And collapse is not rare: self-applications `A A` with `|A| ≤ 5` yielded four that collapse, the best at
**47 reachable / 3 K-normal forms** — and it terminates in four steps. Collapse coexists with bounded
work.

**Why the searches could not settle it** — worth more than the searches. Both failures were about
**controls**:

- the all-terms sweep is affordable to six leaves; its positive control `Itower 3` has **ten**. So "no
  collapsing term up to six leaves" says nothing — and collapsing terms do turn up at ten. Caught by
  running the control at the search's own setting before believing the zero.
- the self-reproduction sweep used `onCycle?`, which is leftmost-outermost — and **Stage 21 proved an LO
  hunt is blind to cycles that exist in the relation**. `onCycle? omegaSK 40` returns `false` even though
  `omega_to_M`/`M_to_omega` are theorems putting it on a cycle. The probe was blind to its own control,
  and the smallest cycle is fourteen leaves, beyond exhaustive reach anyway.

The transferable lesson is Stage 41's, which I failed to apply: **when a probe has a parameter, the
finding is about the parameter — and a probe with a known blind spot must be run against a control that
exercises it.** I used a detector this tree had already proved unreliable for exactly this purpose. Both
facts are now guards.

### Stage 52: the diagnostic needs a source machine — correcting Stage 50

Stage 50 concluded *"dispatch passes, recursion does not"* from K-normal-form counts. **Half of that was
an unfounded inference**, and trying to construct Stage 51's self-reproducing prototype is what exposed it.

The diagnostic says: along one **source** step the abstraction tolerates at most two K-normal forms.
Applying it requires knowing how many source steps a host trajectory covers — and `omegaSK` **encodes
nothing**, so its seventeen K-normal forms cannot be compared to anything. Seventeen is fine for a machine
with seventeen reachable states.

- Stage 50's **dispatch** verdict stands: `S K a b` selects between two branches, the source is a two-state
  selection, and two K-normal forms is exactly right.
- Stage 50's **recursion** verdict does not follow from its measurement.

What the numbers do show is a difference in *kind* — suggestive, not decisive, and now guarded:

```
countdown   K-normal form leaf counts shrink monotonically:  10, 7, 4, 1
omegaSK     they oscillate and revisit:  14, 20, 17, 17, 26, 23, 23, 20, 20, 32, …
```

The first is the signature of a source that only moves forward; the second would force a source cycle.
Neither refutes anything, because neither term encodes anything.

**The methodological finding, which is the real output.** *"Prototype the obligation before building the
artifact"* has been the winning habit for six stages. This is the first time it does not apply, and the
precondition is now explicit: **the diagnostic must be interpretable without the artifact.** Here it is
not — "how many K-normal forms is too many" is a question about the source machine. Route one can only be
tested by building a driver, which is the work the prototype was meant to de-risk.

So the pivot is **route two**, which Stage 49 flagged and nothing since has touched:
`RS.bwd_of_abstraction_rel` takes an **arbitrary** relation, and the trajectory relation — *"`b` lies on
the host segment for source state `w`"* — can be designed and checked without first building the driver.

### Stage 53: route two — the trajectory relation survives `hfun`

Stage 52 pivoted here because route two can be designed and checked *before* any driver exists. It can, and
the two obligations that matter are now proved for the countdown.

`OnSegment enc b w` — *`b` is reachable from `enc w`, and not yet from the encoding of any successor of
`w`.*

| | |
|---|---|
| `onSegment_enc` | **`habs`** |
| `onSegment_functional` | **`hfun`** — the obligation that killed joinability |
| `itower_steps_le` | reachability between encodings recovers the source order, via the Stage 48 `Simulation`'s own `bwd` |

`hfun` is the one that mattered: it killed joinability (`RS.joinable_abs_not_functional`) and it is what any
coarse relation must survive. The trajectory relation survives, and the **"not yet past `w`"** clause is
precisely what makes it — bare reachability supplies `a ≤ a'`, the clause supplies `a' ≤ a`. Plain
reachability in *either* direction fails immediately, since the countdown's encodings are linearly ordered
by reachability.

**`hstep` remains**, and unwinding it gives a condition of a completely different character from route one's:

> no single host step may reach past **two** source states — i.e. consecutive encodings are at least two
> host steps apart.

For the countdown that is exactly true (`Itower (n+1)` reaches `Itower n` in two steps), and for a driver it
is a **design property one can arrange and check**, not a structural coincidence to hope for.

**Why this is the promising route.** The trajectory relation says nothing about the *shape* of intermediates,
only about reachability. So Stage 49's constraint — every intermediate must K-normalise to an encoding —
**does not apply to it at all.** That constraint is what made route one look hard and left Stages 50–52
unable to test it.

**The cost**, stated so it is not discovered later: the relation quantifies over reachability, so it is not a
computation. Fine for `bwd`, which takes an arbitrary relation — but a `Simulation` also needs a decoder
**function**, and the trajectory relation supplies none. The countdown got its decoder from `naiveAbs`
independently; a driver must do the same. **Decode syntactically, track relationally** — two obligations, and
route two discharges only the second.

### Stage 54: adequacy may advance by a path — the restriction that broke route two

Measured `hstep` for the trajectory relation **before** attempting the proof.

```
single-step advance:   36 failures out of the 183 terms reachable from Itower 3
path advance:           0
```

Stable at closure bounds 26, 30 and 36 with identical saturated closures — so the 36 is real, not a bound
artefact.

**The diagnosis is one example**, kept as a guard so the next attempt does not rediscover it.
`skipWitness = K (Itower 1) (K (Itower 2))` sits on segment 3 and is *itself a K-redex* whose contraction is
`Itower 1`. One host step, two source states — **segment 2 skipped.** Nothing to do with the spacing
condition hypothesised in Stage 53: the cause is that a K-step can **discard a pending computation and
arrive early.**

So the trajectory relation was never the problem — `bwd_of_abstraction_rel`'s single-step restriction was.
The tracking proof never needed it (it composes paths either way), so `trans` instead of `tail` removes it:

| | |
|---|---|
| `RS.abstraction_tracks_path` | tracking with multi-step advance |
| `RS.bwd_of_abstraction_path` | adequacy from a relation that may advance by a path |
| `RS.bwd_of_abstraction_path_generalises` | the single-step form is the special case |

All three **axiom-free**.

**Note the symmetry.** The K rule's erasure is what makes the K-normal-form abstraction well behaved —
drift inside discarded arguments becomes invisible — and it is the *very same* erasure that makes the
trajectory relation skip states. One mechanism, helping one abstraction and hurting the other.

Route two's obligation is now stated in the form the generalised interface asks for
(`OnSegmentHStepPath`), measured clean over one machine at one size, and unproved.

### Stage 55: route two reduces to one fact — strong normalisation of the encoding

Attempting `OnSegmentHStepPath` turned out not to need a case analysis on the step at all.

| | |
|---|---|
| `countdown_steps_of_le` | `m ≤ w` gives a source path |
| `onSegmentHStepPath_of_least` | given a **least** segment index, `hstep` is four lines |

The stutter case is *subsumed* rather than handled: if the least index happens to be `w`, the "advance" is
the empty path. The proof also never uses the **"not yet past `w`"** clause of its hypothesis — only the
reachability half — which says that clause earns its keep in `hfun` and nowhere else.

**What `hleast` needs.** Extracting a least element of `{m | Itower m ⟶* b}` needs that predicate to be
**decidable**. The set is non-empty (it contains `w`) and bounded, so decidability is the only missing
ingredient — and this development refuses `Classical.choice`.

Reachability from `Itower m` is decidable if its reachable set is finite, which follows from strong
normalisation (finitely branching + terminating ⟹ finite reachable set). So route two reduces to:

> **`Itower m` is strongly normalising.**

And that is not available here. C5 (`conservation`) gives WN ⇒ SN — but only for **K-free** terms, and
`Itower` is built from `I = S K K`. With `K` in play the implication is false in general: `K S omegaSK` has
a normal form *and* an infinite reduction. **So the one theorem in this tree that would supply SN is blocked
from reaching the countdown's own encoding** — by exactly the erasure Stage 54 showed cuts both ways.

That is a sharper statement of where piece (v) stands than "route two looks promising": it is reduced to a
single standard fact about one family of terms.

### Stage 56: the reachable set of `Itower m` has bounded size — `3·2^m − 2`, tight

Stage 55 reduced route two to strong normalisation of the encoding and found C5 blocked from supplying it
(C5 needs K-freeness; `Itower` is built from `I = S K K`). **Finite size is weaker, enough, and provable
directly.**

Measured first: the largest reduct of `Itower m` has **1, 4, 10, 22** leaves for m = 0…3 — which is
`3·2^m − 2`. The proved bound is exactly that, and the `half` case attains it.

| | |
|---|---|
| `Tower` | states of an m-layer tower: intact, half-consumed, collapsed. **The two copies of a half-consumed layer may drift independently** — the Stage 10 phenomenon, finally given a type, and what makes the family closed under reduction |
| `tower_Itower` | the encoding is one |
| `Tower.of_step` / `of_steps` | closed under reduction. An intact layer's only step is its own root redex, because `I` is a full-SK normal form |
| `Tower.leafCount_bound` | `leafCount t + 2 ≤ 3 · 2^m` |
| `itower_reduct_bound` | hence every reduct of the encoding is small |

No measure works for all of SK — `S` duplicates, so growth is unbounded — so the proof needs the reachable
set *characterised*, and three layer states suffice.

**What it gives.** The reachable set is finite: it sits inside the SK terms of at most `3·2^m − 2` leaves.
That is Stage 55's missing ingredient, obtained *without* strong normalisation.

**What it does not.** Turning "finite reachable set" into "decidable reachability" needs a **certified finite
universe of bounded-size SK terms** — and this tree's universe, `smallTerms`, is built from `enumAt`, which
enumerates **K-free** terms only. Goal 3's decidability machinery is K-free by construction, for the good
reason that it was built for pure S.

The chain now reads:

> route two's `hstep` ⟸ `hleast` ⟸ decidable reachability from `Itower m` ⟸ **a K-inclusive bounded
> enumeration** + the size bound above.

The last item is the only gap, it is **infrastructure rather than research**, and `skTerms`
(`AdequacyProbe.lean`) is already the uncertified version of exactly it.

### Stage 57: a certified finite universe of SK terms

Stage 56 left route two's chain needing exactly this. The reachable set of the countdown's encoding is known
finite (`itower_reduct_bound`, `3·2^m − 2`), but *finite* only becomes *decidable* against a certified
enumeration of the bounded universe — and this tree's universe, `smallTerms`, is K-free because `enumAt` is.

| | |
|---|---|
| `skEnum` / `skEnumAt` | SK terms with exactly `n` leaves, budget-indexed for structural recursion |
| `skEnum_sound` | nothing spurious |
| `skEnum_complete` | every SK term appears at its own leaf count — **no `KFree` hypothesis**, the whole difference from `enum_complete` |
| `mem_skEnumAt_iff` | the characterisation |
| `skSmallTerms`, `mem_skSmallTerms`, `skSmallTerms_sound` | the finite universe up to a size bound |

This is `Completeness.lean`'s enumerator with **one line changed** — the leaf case lists `K` as well as `S` —
and the K-freeness clause dropped from soundness. Everything else is the same argument, which is the point:
**the restriction was never structural, only inherited from what the census needed.** Goal 3's decidability
layer can now be widened past pure S whenever something wants it.

Counts guarded: `Catalan(n−1) · 2^n` = 2, 4, 16, 80, 448, 2688. And the reason the file exists is guarded
too — `I = S K K` has three leaves, sits in `skEnumAt 3`, and does **not** sit in `enumAt 3`.

### Stage 58: route two's chain closes — a second, independent adequacy proof

Stage 56 bounded the region, Stage 57 certified the universe, and the saturation argument shed its
K-freeness. That was everything `hleast` waited on.

| | |
|---|---|
| `skDeficit`, `skBoundedClosure_isSome` | `Decidability.lean`'s saturation argument with the `KFree` hypotheses **gone** — they existed only to place a frontier element in `smallTerms`, and `mem_skSmallTerms` wants a size bound and nothing else |
| `mem_of_saturated_region` | here the `KFree` hypothesis **was** load-bearing (it bounds an *intermediate* by leaf-count monotonicity, and with `K` present leaf count rises and falls). Replaced by what is actually needed: a bound on the whole **region**, which travels along the path because a reduct of a reduct is a reduct |
| `reachableWithin_correct` | **bounded-region reachability is decidable for full SK** |
| `exists_least` | least witness for a decidable predicate on `Nat`, by hand — `Nat.find` is Mathlib's, not core's |
| `hleast_itower` | the step that needed `Classical.choice` in Stage 55, now constructive |
| **`onSegmentHStepPath_countdown`** | **route two's `hstep`, proved** |
| **`countdownInSK'`** | a second `Simulation`, sharing nothing with Stage 48's but the encoding |

**Two abstractions, two independent proofs of the same `bwd`.** Stage 48 went through K-normal forms and a
commutation square; this goes through trajectory segments and a path-advancing interface.

Goal 3's decidability layer was pure-S-only in **five** places: `enumAt`, `smallTerms`, `deficit`,
`boundedClosure_isSome`, `mem_of_saturated`. Four of the five restrictions were **inherited rather than
structural** and are now lifted; the fifth was real, and got replaced by the right hypothesis.

Decidability of bounded-region SK reachability is not in tension with anything: SK reachability is
undecidable precisely because the region cannot be bounded in advance.

### Stage 59: a `TagSystem` hosted in SK, end to end

Before building a driver for a universal tag system, run the pipeline on the simplest genuine one and find
out whether the plumbing composes.

**The choice of system is the trick.** Deletion number `m = 1`, one symbol, rule appending nothing: words are
determined by their length, and the system halts exactly when empty. That **is** `RS.Countdown`, with
`List.length` as the isomorphism.

| | |
|---|---|
| `unaryTag` | the `TagSystem` |
| `unaryTagInCountdown` | the isomorphism, as a `Simulation` |
| `unaryTagInSK` | composed with Stage 48's `countdownInSK` |
| `unaryTagInSK'` | and with Stage 58's `countdownInSK'`, so the tag system inherits **both** independent adequacy proofs — composition does not care which `bwd` it is handed |
| `universalReach_unaryTag_SK` | |

**Settled:** the pipeline composes. `Simulation.comp` was written in Stage 8 and never used on anything but
toys; it now carries a `TagSystem` into SK through two layers with **no new SK-side work at all**.

**Not settled, and it is the whole of criterion (a):** `unaryTag` is **not universal**. Deletion number one
with an empty rule cannot compute — it is a countdown wearing a tag system's clothes, which is exactly why
the composition was free. A universal tag system (Cocke–Minsky: `m = 2` over a finite alphabet) needs the
driver to **inspect** a symbol and **append** its rule, and neither happens here.

What it does buy: the shape is fixed. Encode the word, simulate one deletion per source step, reuse the
countdown's adequacy template — the driver's extra work being symbol dispatch (Stage 50 measured this
compatible with the K-normal-form abstraction) and the rule append (untested).

### Stage 60: the rule append is not a component — it is a constant

Stage 59 ranked *"test the rule append"* first, calling it the last unmeasured piece of a driver. **The
measurement says it is not a piece at all.**

Encode a word as its **right fold**: `[x₁…xₙ]` is `λc.λn. c x₁ (c x₂ (… (c xₙ n)))`. Then appending at the
*end* is substituting for `n`, which is a fixed wrapper:

```
APPEND = λL.λy.λc.λn. L c (c y n)
```

No recursion, no traversal, no dependence on the list. Deletion at the *front* is equally cheap for a fold —
which is why this encoding suits tag systems: they consume at one end and produce at the other.

Compiled by the tree's own bracket abstraction and guarded: `APPEND` is **414 leaves** from the naive
algorithm (no occurs check; an optimised abstraction would be far smaller) and **the same 414 whatever it is
applied to**. Appending agrees with direct encoding on four checks, using **two different observers** `(c, n)`
so the agreement is not by collapse — `(K, S)` keeps only the head, `(I, K)` keeps the structure. Guards
verified to bite by negative control, since the build finished in 1.3 s and that felt too fast.

**What this does to the remaining work.** Stage 59's premise was wrong in the useful direction. With a fold
encoding, *both* halves of a tag step are fixed combinators, so a driver needs **no recursion for its list
operations at all**.

What it still needs recursion for is **self-reproduction**: `enc w` must reduce to `enc w'`, the encoding
contains the driver, so the driver must rebuild itself. That is self-application — exactly what Stages 50–52
isolated and could not settle without building the thing.

Piece (v) now has **one** unresolved ingredient rather than three:

| ingredient | status |
|---|---|
| symbol dispatch | measured compatible (Stage 50) |
| rule append | **constant** (here) |
| self-reproduction | **open** |

### Stage 61: self-reproduction, without a fixpoint combinator

Stage 60 left exactly one ingredient of piece (v) open. I had been assuming it meant a fixpoint combinator and
the sprawl Stage 50 measured. **It does not.**

```
W = λx.λd. x x (F d)        and then        W W d  ⟶*  W W (F d)
```

for an **arbitrary** step function `F`. The data advances, the driver reappears, and nothing recurses — the
self-application is a single `S`-redex, not an unfolding.

| | |
|---|---|
| `selfRepW` / `selfRep` | bracket-abstracted **by hand**: `λd. x x (F d)` is `S (K (x x)) F`, and abstracting `x` gives `S (S (K S) (S (K K) (S I I))) (K F)` |
| `selfRepW_unfold` | the self-application exposes `S (K (W W)) F` |
| **`selfRep_advances`** | **`W W d ⟶* W W (F d)`** |

Both theorems need **no axioms at all** — explicit reduction chains, nothing but congruence and the two rules.

**Size: `15 + |F|` leaves**, so the wrapper costs fifteen leaves regardless of what it drives. Contrast the
**414** leaves naive bracket abstraction produced for `APPEND` in Stage 60: doing this one by hand was worth
it, and the hand version is also what made the proof a short explicit chain rather than a normalisation.

**Piece (v)'s three ingredients are now all settled:**

| ingredient | |
|---|---|
| symbol dispatch | measured compatible (Stage 50) |
| rule append | a constant (Stage 60) |
| **self-reproduction** | **proved here**, and cheaper than expected |

Stage 50's measurement of `omegaSK` is not contradicted: `omegaSK` is self-application *without* a step
function, so it has nothing to advance and no reason for its K-normal forms to collapse. A driver's
self-application carries `F`, and `F` is where the encoding's discipline lives.

What remains is assembling the step function itself — head extraction, dispatch, append, and the `m = 2`
double deletion — from parts that are individually understood.

### Stage 62: the occurs check, added when it finally paid

Assembling the tag step needs `head`, `tail`, `cons`, `nil` and pairs on fold-encoded words. All are fixed
combinators — the traversal in `tail` is performed **by the data's own fold**, not by driver recursion.

Compiled with the tree's naive `bracket` they are **unusable**: `TAIL` came out at **14,100 leaves** and
`normalize` **aborted** on it (SIGABRT, not a timeout). That is the concrete cost of a decision
`Bracket.lean` documents honestly — *"no occurs-check optimization… for calibration the proofs win (YAGNI)."*
Right for calibration, fatal for a driver.

| | |
|---|---|
| `TermV.subst_of_not_occurs` | `subst` is the identity when the variable is absent |
| `TermV.bracketOpt` | bracket abstraction **with** the occurs check |
| `TermV.bracketOpt_beta` | same beta property as `bracket`; the extra branch needs the lemma above |
| `NILf CONSf HEADf PAIRf FSTf SNDf TAILf` | the toolkit, recompiled |

```
CONS      414 →  66
TAILSTEP 4593 → 139
TAIL    14100 → 192      a 73× reduction
```

The difference between a term the evaluator aborts on and one it handles in a third of a second. The
optimisation is negligible on toys (15 vs 9 leaves for a three-abstraction constant function) and decisive on
real code, because it **compounds with nesting**.

Verified, not merely measured: `head [S,K] = S`, and `tail [S,K]` agrees with `[K]` under **two different
observers**, so the agreement is not by collapse.

**Where the driver stands.** Every component now exists and runs — `head`/`tail` here, `APPEND` (Stage 60),
dispatch free (Stage 50), self-reproduction (Stage 61). What remains is writing the `m = 2` step function as
one term and proving `fwd`: assembly rather than design, and a long proof, because `fwd` must be a reduction
chain over a term in the hundreds of leaves.

### Stage 63: the m = 2 tag step function, assembled and validated

A genuine **two-symbol, deletion-number-two** tag system: `a ↦ [b]`, `b ↦ [a,b]`. Every piece is
constant-size, including the rule append — concatenating two folds is `λL M c n. L c (M c n)`, cheaper than
Stage 60's single-element append and it handles rules of any length.

| | |
|---|---|
| `symA` / `symB` | symbols as booleans, so dispatch is application (Stage 50) |
| `CONCATf` | 68 leaves |
| `RULEf` | 218 leaves, the two-way dispatch |
| **`STEPf`** | **696 leaves** — `λL. CONCAT (TAIL (TAIL L)) (RULE (HEAD L))` |
| `tagFwd_of_step` | **`fwd` follows from step-correctness alone**, since the driver half is already proved for any `F` by `selfRep_advances` |

Validated on four steps of the system, each under **two observers** so agreement cannot be by collapse, plus
a negative control that must and does fail.

**A correction to Stage 62's outlook.** I said proving `fwd` would be *"a reduction chain over a term in the
hundreds of leaves"* and called it a proof-engineering problem. Assembling the thing shows a better route
that was available all along.

`tagFwd_of_step` reduces `fwd` to `STEPf (mkWord w) ⟶* mkWord w'`, and that does **not** need chasing the
compiled 696-leaf term. `TermV.bracketOpt_beta` says an abstraction applied to an argument reduces to the
substituted body, so the compiled pieces can be reasoned about at the **lambda level** and composed:

```
HEADf   (mkWord (x :: xs))       ⟶*  x
TAILf   (mkWord (x :: xs))       ⟶*  mkWord xs
CONCATf (mkWord u) (mkWord v)    ⟶*  mkWord (u ++ v)
        plus the two-case dispatch
```

Each is an induction over a list, not a walk through a large term. The remaining work is four compositional
lemmas and their assembly — real work, but ordinary.

### Stage 64: the four lemmas, step-correctness, and `fwd` — and one of the four was false

**`fwd` for a genuine two-symbol, m = 2 tag system is PROVED** (`tagAB_fwd`, `tagAB_fwd_SK`): for every
step `w → w'` of the system `a ↦ [b]`, `b ↦ [a,b]`, the encoded word actually reduces —
`selfRep STEPc (encWord w) ⟶* selfRep STEPc (encWord w')`, genuine SK reduction, axiom footprint
`[propext, Quot.sound]`. This is the forward half of piece (v), end to end, on a machine that is not a
countdown in disguise.

| | |
|---|---|
| `bracketOpt_subst_ofTerm` | substituting closed data under an optimised abstraction commutes **as an equality** — the naive algorithm's version (Stage 12) held only up to reduction |
| `bracketOpt_beta*_Term` | the β-ladder to arity 4: compiled combinators reasoned about at the lambda level |
| `HEADf_mkWord` | `head (mkWord (x::xs)) ⟶* x` — **no induction at all**: one β and a `K`-firing |
| `TAILf_mkWord` | one list induction (`mkWord_tailPair`: the fold computes `⟨word, tail⟩` cons-built) |
| `CATf_mkWord` | one list induction (`mkWord_fold_cons`) — on the **corrected** concatenation |
| `RULEf_encSym` | dispatch: two firings per symbol |
| **`STEPc_mkWord`** | **step-correctness, literally**: `STEPc (encWord (s::y::rest)) ⟶* encWord (rest ++ ruleAB s)` |
| **`tagAB_fwd`** | their composition with Stage 61's driver |

**The finding: Stage 63's concat lemma was FALSE as stated.** `CONCATf (mkWord u) (mkWord v)` can never
reduce to `mkWord (u ++ v)`. The left side β-reduces to a compiled abstraction whose top spine is `S`
applied to TWO arguments — and no reduction ever fires a top-level redex there again, while a nonempty
`mkWord` has `S` applied to FOUR at its spine. The two are observationally equal, which is exactly what
Stage 63's two-observer guards certified; but SK has no extensionality, and `fwd` needs REACHABILITY. The
fix is the classic cons-directed concatenation `CAT = λL M. L CONS M` (82 leaves — 14 more than `CONCATf`,
the price of carrying `CONSf` as a constant), under which every intermediate stays cons-built. `STEPc`
(710 leaves) is `STEPf` with that one substitution.

The validated-but-wrong combinator is the instructive part: the two-observer discipline, adopted in Stage 50
precisely to avoid vacuous agreement, certifies observational equality — and observational equality is not
the property `fwd` consumes. Validation can only vouch for the equivalence it tests.

New anchors are literal-normal-form guards — `nf (STEPc (encWord w)) = nf (encWord w')` — stronger than
two-observer agreement, available now because the output is reachable rather than merely equal-under-tests.

**What remains for `Simulation (RS.Tag tagAB) RS.SK`:** `dec`/`dec_enc` (mechanical) and `bwd` — adequacy,
the demanding half, as it was for the countdown (Stages 45–48, 49–58). One structural difference to face:
`enc`'s image contains the driver, which duplicates ITSELF at every step, so Stage 11's `normalForm_bracket`
(machine code is safe to duplicate) becomes load-bearing rather than reassuring.

### Stage 65: the decoder, a `PathEncoding` — and `bwd` is FALSE for this encoding

Proceeding to `dec` and `bwd`. The decoder is done, and checking `bwd` produced the stage's real
output: three refutation theorems, one fatal and two that survive any fix to it.

| | |
|---|---|
| `decTag` / `decTag_encTag` | the decoder, syntactic, with `dec_enc` proved — `[propext]` only |
| `encTag_injective` | injectivity, free from `dec_enc` |
| **`tagABPathEncoding`** | **the m = 2 tag system PATH-ENCODES into SK** — the class every refutation is stated over, now inhabited by a genuine inspect-dispatch-append machine |
| **`tagAB_bwd_false`** | **`bwd` is false outright for `encTag`** — not hard: false |
| `onSegment_habs_fails_of_selfLoop` | route two's hidden acyclicity assumption, exposed (axiom-free, any source, any encoder) |
| `tagDriver_knf_hstep_fails` | route one's `hstep`, refuted at the driver's very first host step |
| `isKRedex` / `hasKRedex` / `kNormalForm_of_no_kredex` | K-normality DECIDED — every K-normality obligation on machine code is now `by decide` |

**The central finding.** A tag step is PARTIAL — it requires `m ≤ |w|` — but `STEPc` is TOTAL. On the
stuck word `[b]` (a tag normal form): `tail (tail [b]) = []`, `head [b] = b`, append `[a,b]` — so the
host walks `encTag [b] ⟶* encTag [a,b]` where the source has no step at all (`STEPc_stuck`,
`encTag_outruns`). `bwd` is therefore false, and since the adequacy machinery PROVES `bwd` from its
hypotheses, no abstraction whatsoever can be instantiated for this encoding. The driver must change:
dispatch on "has at least two symbols" (a constant-size fold observer, same idiom as `HEADf`) and
return stuck words unchanged, so they SELF-LOOP in the host. That is a Stage 66 design item.

Stage 63's validation could not have caught this: every test word was long enough to step. Second
stage in a row where the gap between "validated" and "true" was found only by attempting the proof —
Stage 64's version was "a test only vouches for the equivalence it tests"; this stage's is "a test
only vouches for the inputs it exercises."

**The two templates, refuted for reasons that survive the guard fix.** Route two (trajectory
relation): `OnSegment`'s "not yet past `w`" clause is an assumption about the SOURCE — no state may
recur on its own trajectory — and `tagAB` has a fixed point, `[b,a,b] ↦ [b,a,b]` (`tagAB_selfLoop`).
`habs` fails for every encoder before any host behaviour is consulted. The countdown never noticed
the assumption because it only ever counts down. Route one (K-normal form): the first host step out
of ANY encoded state fires the driver's self-application, and its K-normal form `(X W) STEPc d` is a
mid-step term, provably not an encoding (head `≠` driver, one `decide`). Stage 49 predicted route
one's constraint; this is its concrete bite, and it applies to any `selfRep`-driven encoding.

**What remains, correctly targeted now.** Stage 66: the guarded driver, re-proving `fwd` (the four
Stage 64 lemmas are reusable) plus "stuck words self-loop". After that, `bwd` needs a THIRD
abstraction — mid-step-aware and loop-tolerant — and the genuine obstacle is characterising the
driver's reachable set, the analogue of Stage 56's `Tower` for a 1450-leaf machine. Attempting that
on the unguarded driver would have been effort spent proving the unprovable, which is what makes the
refutation-first order this stage followed the right one.

### Stage 66: the guarded driver — the step function learns that tag steps are partial

The repair Stage 65 called for, built and proved in one sitting because every ingredient already
existed. The guard is the same constant-size fold-observer idiom as the rest of the toolkit:
`NONNIL = λL. L (λx a. T) F` reads emptiness off the fold (12 leaves), `HASTWO = NONNIL ∘ TAIL`
shifts it by one (211), and `STEPg = λL. HASTWO L (STEPc L) L` dispatches (936, vs `STEPc`'s 710 —
226 leaves is what respecting partiality costs).

| | |
|---|---|
| `NONNILf_nil` / `NONNILf_cons` | the observer's verdicts — one β each, NO induction |
| `HASTWOf_nil` / `HASTWOf_one` / `HASTWOf_long` | the guard's three verdicts, riding `TAILf_mkWord` |
| **`STEPg_mkWord`** | step-correctness where a tag step exists — guard passes, `STEPc_mkWord` finishes |
| **`STEPg_stuck`** | **stuck words are FIXED, literally**: `F = S K` exposes a `K` that discards the doomed `STEPc L` branch UNREDUCED |
| `tagABg_fwd` / `tagABg_fwd_SK` | `fwd`, re-proved — the Stage 64 lemmas carried over untouched |
| `encTagG_stuck_returns` | Stage 65's falsifier repaired: the stuck-word trajectory returns to its own encoding |
| `decTagG_encTagG` / **`tagABgPathEncoding`** | decoder and `PathEncoding`, retargeted at the guarded driver |

New permanent regression guards include exactly the input class Stage 63's suite missed: a stuck word
normalises to ITSELF, and provably NOT to what the unguarded driver produced.

**What the guard does and does not buy.** `bwd` is now OPEN rather than false — the one known
falsifier is repaired, and the dispatch shape means the driver shell never adopts the doomed branch as
data: on stuck words the `K` discards it whole. NOT bought: a smaller reachable set. The host remains
free to reduce INSIDE the doomed `STEPc L` argument before the dispatch discards it, so the reachable
set still contains the unguarded computation's states — as subterms of doomed positions. The future
abstraction must be blind to them (which is exactly what both Stage 65 refutations, still standing,
already demanded: mid-step-aware, loop-tolerant, doomed-blind). The remaining distance to
`Simulation (RS.Tag tagAB) RS.SK` is unchanged in kind: characterise the guarded driver's reachable
set — Stage 56's `Tower`, for a machine three orders larger.

### Stage 67: the rigidity audit — shipped code is not normal, and its drift is one species

The ranking said to start the reachable-set characterisation with `HEADf`. The audit of that plan's
central prerequisite — code is rigid when duplicated — came first, and it FAILS: Stage 11's
`normalForm_bracket` covered the naive algorithm on pure bodies, and the real toolkit is `bracketOpt`
over bodies embedding APPLIED constants, which ship as K-protected chunks with their redexes live.

| | |
|---|---|
| `*_normal` (11 theorems) | every pure-body compilation IS normal: `NILf CONSf HEADf PAIRf FSTf SNDf TAILSTEPf CATf constTf NONNILf selfRepX` — one line each via `stepOnce_none_normal` |
| `*_not_normal` (6) | everything embedding an applied constant is NOT: `TAILf RULEf HASTWOf STEPc STEPg`, and `selfRepW STEPg` — **the term the driver duplicates every cycle** |
| build-enforced counts | live redex positions compose additively: 1 (TAILf) + 3 (RULEf) → 5 (STEPc) → 6 (STEPg); drift distance 168 LO-steps for STEPg; words carry one live redex PER CONS CELL and quiesce to compact code-forms (2-symbol word: 72 steps, 63 leaves) |

**The accounting is the finding.** Of `STEPg`'s six live positions: three are the rule outputs — but
those are WORDS, and words are non-normal BY DESIGN (`mkWord` is a chain of `CONSf`-applications;
that is what made Stage 64's literal reachability work), so their drift is word drift, owed anyway
for every word in flight. The other three are copies of ONE internal constant, `TAILf`'s accumulator
`PAIRf NILf NILf` — not data, and fixable: ship the compiled pair `λs. s [] []` instead (normal,
β-identical). After that one rebuild, **code drift and data drift collapse into one species**, and
the reachable-set characterisation owes exactly one drift family: the reducts of `mkWord w`.

**The census ceiling, recorded plainly.** `boundedClosure` on bare `TAILf` — one live chunk — did not
saturate in twenty-five minutes where the countdown's entire reachable set (183 states) saturates
inside a `#guard`. Enumerative invariants at this scale are not merely unwritable; they are not even
measurable. The drift families must be parameterized (Tower's `half` constructor generalised), which
the per-combinator plan already intended — and the useful number is not the state count but the
species count, which is one.

### Stage 68: the accumulator rebuild — every live position in the shipped driver is a word

Stage 67's fix, built and proved. `TAILZn = λs. s [] []` compiled directly (15 leaves, NORMAL) replaces
the applied pair `PAIRf NILf NILf` (37 leaves, live redex), and the stack rebuilds on it: `TAILn`
(170), `HASTWOn` (189), `STEPcn`, `STEPgn` (870 — smaller than `STEPg`'s 936; rigidity turned out to
be a discount, not a cost).

| | |
|---|---|
| `TAILZn_normal` / `TAILn_normal` / `HASTWOn_normal` | the rebuilt tail chain is NORMAL — Stage 67's three accumulator copies are gone |
| build-enforced | `STEPcn`, `STEPgn`, `selfRepW STEPgn` each carry exactly **3** live positions — the rule-output words, nothing else |
| `mkWord_tailPairN` | the tail fold's invariant, EXISTENTIAL: the fold reaches something that *projects* like `⟨word, tail⟩` |
| **`TAILn_mkWord`** | `tail` uniformly over ALL words — the nil case stops being special, because `TAILZn` projects like `⟨[],[]⟩` by β |
| `STEPgn_mkWord` / `STEPgn_stuck` | step-correctness and stuck-fixity, re-proved on the clean stack |
| `tagABn_fwd` / `decTagN_encTagN` / **`tagABnPathEncoding`** | the driver, final form — the encoding all `bwd` work targets from here |

The existential restatement of the fold invariant is the small methodological catch of the stage: the
old invariant demanded the accumulator literally BE a `PAIRf`-application, which is why replacing the
accumulator looked like it would ripple. Stated as "reaches something that projects correctly", the
base case is two β-lemmas and the ripple vanishes — and `TAILn_mkWord` comes out UNIFORM over all
words, subsuming what used to be two lemmas.

**Where `bwd` stands**: `enc`/`dec`/`dec_enc`/`fwd` proved, stuck words idle, code drift = word drift,
one species. The remaining obligation is the word-drift family (reducts of `mkWord w`, parameterized
over independent copy drift), the machine phases composed over it, and the third abstraction.

### Stage 69: the word-drift family, characterised by behaviour — no enumeration

The ranking asked for an inductive drift family over the reducts of `mkWord w`. Attempting the single
cell showed even it is an interleaved two-layer distribution machine, and Stage 67 had already shown
such state spaces are beyond measuring. Stage 68's lesson — behaviour, not shape — applied one level
up DISSOLVES the enumeration:

| | |
|---|---|
| `wordCode x M` | the code-form of a cons cell, `λc n. c x (M c n)` compiled; `wordCode_explicit` writes it out |
| `wordNF w` | **the canonical normal form of a word** — code-forms all the way down; `wordNF_normal` |
| `mkWord_to_wordNF` | every word reaches its canonical form (partial-application β + `steps_toTerm_subst`, the new generic congruence-under-substitution lemma) |
| **`mkWord_drift_complete`** | **THE DRIFT-COMPLETION THEOREM**: every reduct of a word, however far its copies have drifted, still reduces to `wordNF w` — confluence supplies the join, normality of `wordNF` pins it |
| `mkWord_drift_functional` | drift cannot conflate words: common reducts force equal canonical forms |
| `encWord_drift_complete` | the instantiation on encoded tag words |

The family "reducts of `mkWord w`" is exactly the terms between `mkWord w` and `wordNF w`, and the
second endpoint is canonical BECAUSE it is normal. Membership is closed under reduction by
construction, and never needs to be described — only completed. Sizes: `wordNF` of a 2-symbol word is
63 leaves, matching what the evaluator computes (`nfW` anchors).

**The fifth `Classical.choice` leak**, caught by the per-stage audit like the first four:
`wordCode_explicit`'s original `simp` closed the goal and dragged choice in through the `BEq` layer —
Stage 9's exact trap, eleven weeks later. Fix: supply the decidable literals by hand (`rfl` and
`decide` facts) and let `simp only` do assembly; the audit lands on `[propext]` for the lemma and
`[propext, Quot.sound]` for the chain.

**What is still owed for `bwd`**: (i) injectivity of `wordNF` on encoded words — syntactic, next;
(ii) the same completion treatment for the machine's PHASES, where the checkpoints (`encTagN w`) are
NOT normal, so the completion argument needs the driver's structure rather than bare `nf_unique`.
That asymmetry — words have normal canonical forms, machine states never do — is the precise shape of
the remaining problem.

### Stage 70: drift pins the word — the identity layer is complete

The small stage the ranking promised. Injectivity of the canonical form, then the corollary chain
down to the tag alphabet:

| | |
|---|---|
| `wordNF_injective` | equal canonical forms are equal words — injection chains through the fixed skeleton, `[propext]` only |
| **`mkWord_drift_pins`** | two words whose arbitrarily-drifted copies share a reduct are THE SAME word — `hfun` at the data level, with no shape analysis anywhere |
| `encSym_injective` / `map_encSym_injective` | the alphabet does not collide |
| **`encWord_drift_pins`** | an encoded tag word in flight — duplicated, drifted, reduced on any schedule — determines its source word uniquely |

**The phase layer, scoped while the identity layer is fresh.** The word layer's recipe was canonical
form + confluence + injectivity. The phase layer has canonical checkpoints (the encodings) and
injectivity (`encTagN_injective`) but NOT normality — `encTagN w` always carries its driver redex —
so join points cannot be pinned by `nf_unique`, and completion can only be FORWARD. The candidate
statement, recorded for the next attempt:

    every reduct of `encTagN w` reaches `encTagN w'` for some `w'` with `Tag.Steps w w'`

— forward drift-completion through the driver's phases, with `encWord_drift_pins` handling the data
slots. That single statement, once proved, IS `bwd`'s tracking argument; proving it is the remaining
research content.

### Stage 71: the fold restores literalness — forward completion for the driver's data slot

The ranked segment ("driver applied to a drifted word") looked FALSE on first analysis: word drift is
irreversible, so a drifted state can seemingly never reach a literal encoding. The analysis was wrong
for a structural reason now on record: **the machine never passes the word-term through — it folds
it.** Drift lives in cell machinery; application consumes machinery; symbols and code are normal; so
every fold REBUILDS its output as literal cons-cells. Drift is erased at each fold and does not
compound across cycles.

The recipe: complete the drifted input to `wordNF` (Stage 69), then prove the machine suite on
CANONICAL input — outputs come out literally `mkWord`-shaped:

| | |
|---|---|
| `wordCode_beta` | the canonical form COMPUTES: `wordCode x M c n ⟶* c x (M c n)` |
| `HEADf_wordNF` / `wordNF_tailPair` / `TAILn_wordNF` / `wordNF_fold_cons` / `CATf_wordNF` | the Stage 64 suite replayed on `wordNF`-input — literal `mkWord` outputs, the same inductions |
| `STEPcn_wordNF` / `STEPgn_wordNF` / `STEPgn_wordNF_stuck` | the step function on canonical input: literal encoded output; stuck canonical words are fixed |
| **`STEPgn_drift`** | drift-input step-correctness: ANY reduct of `encWord w` in the data slot still computes the tag step, literally |
| **`encTagN_drift_fwd`** | **the one-segment forward-completion theorem** — every "driver + drifted word" state reaches the LITERAL `encTagN w'`; Stage 70's candidate statement, proved for this phase family |

Axioms `[propext, Quot.sound]`, zero warnings, and the anchors show the evaluator agrees.

**What remains of `bwd`**: the segment INTERIOR — reducts where the DRIVER has partially unfolded
(mid-`selfRep`, mid-dispatch, mid-fold) rather than only the data having drifted. The endpoints
re-anchor themselves (this stage); the interior is the remaining case analysis.

### Stage 72: what completion cannot see — a correction, and the interior's true shape

**The correction, before anything else.** Stage 70 called forward drift-completion "bwd's tracking
argument" and Stage 71 repeated the frame. It is WRONG: completion sees where states FLOW, and `bwd`
is a statement about the ORDER in which encodings can be VISITED. Full forward completion is
consistent with a foreign encoding sitting inside the cone as a confluent tributary that rejoins the
trajectory downstream — completion would never notice it. The countdown's two adequacy proofs both
knew this implicitly: stutter-or-advance and least-segment-index are per-step and order-aware;
neither is an endpoint completion. The remaining target is therefore the `hstep` of a genuine
segment relation, with Stage 71's completion lemmas as ingredients rather than as the argument.

| | |
|---|---|
| `interior_joins_trajectory` | the cone lemma: every interior state joins with EVERY future encoding — confluence ∘ `fwd`, one line; the honest generic content of completion |
| `selfRep_layer_shed` | the shell's self-similarity, tamed: a pre-unfolded driver layer, applied, advances the data by exactly one step-function application — `S (K X) F d ⟶* X (F d)`, generic in the continuation, AXIOM-FREE |
| `decWord_wordCode` | recognizability: the decoder is blind to canonical-form cells, so interior states and literal encodings cannot be confused |

**The design, recorded.** The candidate segment relation, loop-tolerant per Stage 65:

    absR t u := (encTagN u ⟶* t) ∧ ∀ v, Tag.step u v → (encTagN v ⟶* t) → Tag.Steps v u

`habs` immediate; `hfun` and `hstep` reduce to encoding-to-encoding reachability facts — which is
where the order lives, and which need the interior factorization: shell contexts (drift-free, finite
family — the code is normal) over data holes (completed by Stages 69/71), with hand-off to the data
layer exactly where holes are consumed in function position. The shell's nesting corresponds to
multi-step source advances, which `RS.bwd_of_abstraction_path` already permits — that interface,
built in Stage 54 for the countdown's K-discards, turns out to be shaped for this driver too.

Stage 65's question was asked again, as it now must be: is `bwd` false once more? No falsifier
found — literal `mkWord` output arises only from the fold rebuild, the rebuild produces only
`tail² ++ rule` words, and doomed branches are discarded whole. The question stays open until
`hstep` closes it.

### Stage 73: the cheap test, and two more mechanisms off the table

The ranked test — `habs`/`hfun` for the segment relation before its engine — FAILED the relation as
a first proof, and caught another Stage 72 error ("habs immediate": it is not). The obligations ARE
encoding-order facts, formally (`segRel_habs_iff`): the relation holds honestly only at stuck words
(clause vacuous) and the fixed point (return by `refl`); everywhere else it presupposes the order
under proof. The countdown's trajectory relation had this same shape and survived by leaning on the
FIRST proof's completed `bwd` — segment relations are inherently SECOND proofs.

And the second finding closes the landscape: **the driver's reachable region is unbounded**
(`driver_region_unbounded`). The shell pre-unfolds future cycles to any depth — `selfRep_nests`,
AXIOM-FREE: `selfRep F ⟶* shellNest F k` with `leafCount` growing linearly in `k` — so no size bound
covers `Reach(encTagN w)` and `stepsDecidableWithin`, the engine of the countdown's second adequacy
proof, provably cannot apply. The self-reproduction that makes the machine run is exactly what makes
its region unbounded.

| | |
|---|---|
| `SegRel` / `segRel_enc_stuck` / `segRel_enc_fixedPoint` | the candidate relation and its two honest `habs` instances |
| **`segRel_habs_iff`** | everything else IS the order — nothing cheaper hides in the relation |
| `shellNest` / **`selfRep_nests`** | the driver runs arbitrarily far ahead of its data (axiom-free) |
| **`driver_region_unbounded`** | no bound covers the reachable set — bounded-region decidability refuted |

**Four mechanisms, four machine-checked refutations**: KNF `hstep` (65), `OnSegment` `habs` (65),
segment-relation bootstrapping (73), bounded regions (73). One route remains, forced rather than
preferred: a per-step tracking abstraction over the interior factorization — shell contexts as an
INDUCTIVE family (the unbounded nesting rules out enumeration) over data holes (Stages 69–71). The
factorization is the theorem `bwd` has been waiting for since Stage 65, and every alternative now
ends in a refutation with a name.

### Stage 74: the shell invariant — the interior factorization exists

The theorem four stages of refutations forced, built in one sitting: `DriverShell.lean` defines a
12-kind, 24-constructor inductive family `Sh F D DA k t` describing every term reachable from
`app (selfRep F) d` — the driver applied to data — as SHELL MACHINERY over abstract data holes, and
proves it CLOSED UNDER REDUCTION (`Sh.closed`), generic in the step function `F`.

| | |
|---|---|
| kinds | `wcopy iw kf ks kk zw yw xw eng kfd ydat drv` — one per machinery stage of the engine `W W` |
| `Sh.closed` | one host step never leaves the family, kind by kind — a single induction, every impossible root discharged by index unification |
| `Sh.start` | the driver's start state is in the family (AXIOM-FREE) |
| **`driver_interior_invariant`** | **every reduct of `encTagN w` factors as shell machinery over data holes** — instantiated with `D := reducts of encWord w`, `DA := True` (the data layer stays abstract, as ranked) |

Design facts found by tracing and now encoded: finished `I`-towers reassemble into NESTED engines
(Stage 73's unbounded pre-unfolding — one constructor, `eng_pair`, not infinitely many); a half-built
layer `S y f` can consume data EARLY, so the premature-application states (`ydat`) are real and the
family is false without them; the mid-flight data discard (`ydat`'s `K`-fire) is where a duplicated
data copy dies.

Why this was writable when Stage 67 said such families were not: five stages of preparation deleted
the drift species before enumeration began. Normal code (Stage 68) removed every code-drift kind;
the word layer (Stages 69–71) let data hide behind two Step-closed predicates; layer-shedding
(Stage 72) predicted the premature states. Twelve kinds against Tower's four — a factor of six, not
the two orders of magnitude the raw machine suggested.

**What remains**: instantiate `D`/`DA` with the actual data layer (the word and step-function
expressions of Stages 69–71, as a family), then read the tracking abstraction off the factored
shape — the shed-layer count is the source-steps-ahead, the data slot decodes the word — then
`hstep`. The order argument finally has a floor to stand on: the shell alone can never produce a
literal encoding, because encodings live in the data slots.

### Stage 75: the data layer instantiated — and `bwd` falls. THE SIMULATION EXISTS.

**`tagABInSK : Simulation (RS.Tag tagAB) RS.SK`** — a genuine two-symbol, deletion-number-two tag
system, inspect-dispatch-append, guarded on its halting condition, certifiably hosted inside SK in
the demanding encoding class: encoder, decoder, `fwd`, and `bwd`, all machine-checked, axioms
`[propext, Quot.sound]`, no `sorry`, no `Classical.choice`. The open item standing since Stage 8 —
"is there a `Simulation (RS.Tag T) RS.SK`?" — is CLOSED, ten stages after Stage 65 proved the first
attempt's `bwd` false.

The stage's discovery: the data layer's right instantiation is SEMANTIC, and once chosen, `bwd` is
an inversion rather than a tracking argument.

| | |
|---|---|
| `DataW w t` | the semantic data layer: `t` denotes a source-reachable word — `∃ u, Tag.Steps w u ∧ t ⟶* wordNF u` |
| `DataW_step` | Step-closed FOR FREE: confluence joins, normality of `wordNF` pins — no shape analysis |
| `STEPgn_wordNF_all` / `DataW_app` | the hand-off discharged: applying any step-function reduct to a data term yields a data term denoting the NEXT word — Stage 71's suite behind one confluence square |
| `Sh.kfd_data` | machinery-wrapped slots denote too, by induction over the `kfd` fragment |
| **`driver_interior_invariant_data`** | the interior invariant with NOTHING abstract: every reduct of `encTagN w` is shell machinery whose every data slot denotes a source-reachable word |
| `DataW_pins` | a denoting slot that IS a literal encoded word pins its source word — `nf_unique` + `wordNF_injective` |
| **`tagABn_bwd`** | **`bwd`**: the endpoint's data slot is `encWord w'`, the invariant says it denotes, denotation pins |
| **`tagABInSK`** / `universalReach_tagAB_SK` | the `Simulation`, and the taxonomy's certificate |

**Where the order was hiding.** Stage 72 established that completion cannot see order and predicted
a per-step tracking relation with stutter-or-advance bookkeeping. That prediction was WRONG in an
instructive direction: the order was never in the steps — it was in the SLOTS. The shell invariant
separates machinery from data; the semantic layer makes every slot carry its source-reachability
witness; and a literal endpoint forces its slot's witness to be its own word. No segment relation,
no `hstep`, no stutter-or-advance — the four refuted mechanisms were all attempts to recover from
host steps what the factorization carries in its holes.

**Honest scope, as always**: `tagAB` is a genuine m = 2 tag system and m = 2 tag systems are the
Cocke–Minsky universal CLASS, but this particular two-symbol instance is not itself proven
universal — that claim was never made and is not made now. What is discharged is spec piece (v) in
full: a real tag-step driver, hosted by a real `Simulation`. Scaling the alphabet is construction,
not mechanism.

### Stage 76: the N-ary abstraction, a pre-existing leak, and the audit made build-enforced

Toward the any-alphabet tag theorem, whose only alphabet-dependent piece is dispatch. The β-ladder
stopped at arity 4; now it is list-indexed and total:

| | |
|---|---|
| `appArgs` / `absArgs` / `substArgs` | application to, abstraction over, substitution of an argument LIST |
| **`absArgs_beta`** | β at every arity in one theorem — `bracketOpt_beta2/3/4_Term` retired as special cases |
| `selArgs` / **`selArgs_correct`** | the selectors `λx₁…xₖ. xᵢ` and their β, stated pre/post-style with no index arithmetic |
| `bracketOpt_not_occurs` / `absArgs_var_ge` | closed forms: a selector is `K`-wraps around an `S (K K)`-chain |
| **`selArgs_normal`** | selectors are NORMAL, generically in `k` and `i` — safe to ship as symbols for any alphabet size |

**The sixth `Classical.choice` leak — and this one was PRE-EXISTING.** The new `occurs_bracketOpt`
imitated `occurs_bracket`'s `grind`, the per-stage audit fired on the imitation, and the trail led
back: `occurs_bracket` had been leaking since it was written, with `bracket_closed` and the Goal 1
headline **`combinatory_completeness`** downstream. The global "no `Classical.choice`" claim was
false for an unknown span — the per-stage audit never re-checks old theorems. Both lemmas are now
explicit (`beqSelf` supplies `(n == n) = true` by a provably clean route), the headline is back to
`[propext, Quot.sound]`, and:

**`Audit.lean` makes the claim BUILD-ENFORCED**: every headline theorem's exact axiom footprint is
pinned with `#guard_msgs in #print axioms`, so any future leak — in new code or old — fails the
build. Twelve theorems pinned, `confluence` and `nf_unique` at `[propext]` alone.

### Stage 77: the any-alphabet dispatch

The dispatcher `λs. s out₀ … out_{n-1}`, compiled generically in the output table, with its β and
its correctness — and the pre/post idiom from Stage 76 made the headline theorem ONE LINE:

| | |
|---|---|
| `appArgsV` / `toTerm_appArgsV` / `subst_appArgsV` / `map_subst_toTerm` | the three little list lemmas β needs |
| `dispatchT` / `dispatchT_beta` | the compiled dispatcher and its β |
| **`dispatchT_correct`** | the dispatcher applied to the selector at position `p` returns the output at position `p` — `dispatchT_beta` ∘ `selArgs_correct`, no index arithmetic anywhere |
| `selArgs_succ_lt` / `selArgs_top_S` | the closed-form dichotomy: below the top index a layer is a `K`-wrap; the top selector is `S`-headed |
| **`selArgs_injective`** | distinct symbols stay distinct — what the decoder and canonical-form pinning consume at the tag layer |

With Stage 76's `selArgs_normal`, the symbol layer for ANY alphabet is complete: selectors are
normal (safe to ship and duplicate), injective (decodable), and dispatchable (one β away from their
rule outputs). What remains for the any-alphabet `Simulation` is assembly: the general step function
over `Fin n`, its `wordNF`-suite, and the Stage 74–75 machinery re-instantiated — which is generic
in everything but the dispatch this stage just supplied.

### Stage 78: the general tag machine — any m = 2 system, given a dispatch

**`tagTInSK : Simulation (RS.Tag T) RS.SK`** for ANY tag system `T` with deletion number 2, given a
symbol encoding and dispatcher satisfying a four-hypothesis interface:

    hNorm : symbols normal      hInj  : symbols injective
    hRULE : dispatch correct    hdecS : symbols decodable

The whole Stages 63–75 pipeline, re-built once, parametrically (`TagGeneral.lean`): step function
over the abstract dispatch, canonical-input suite, drift versions, driver, decoder, semantic data
layer, shell-invariant instantiation, `bwd`, and the assembled `Simulation` plus
`universalReach_tagT`. Two structural notes:

- `fwd` routes through drift-completion (Stage 71), so the literal-input step suite never needed
  restating — the general file is SHORTER per theorem than the two-symbol original;
- the two-symbol `tagAB` is re-derived as an instance in one `example`, every hypothesis discharged
  by a lemma that already existed — the calibration that the interface is the right one.

**Every concrete known-universal 2-tag system is now an instance away.** What remains is the
`Fin n` discharge of the interface via Stage 76–77's selectors (`selArgs_normal` ✓,
`selArgs_injective` ✓, `dispatchT_correct` ✓ — plus the rule-table bookkeeping), and then citing any
universal table from the literature is construction, not mechanism.

### Stage 79: the `Fin n` discharge — every finite-alphabet 2-tag system, hosted

**`finTagInSK (n) (rule) : Simulation (RS.Tag ⟨Fin n, 2, rule⟩) RS.SK`** — every deletion-number-2
tag system over a finite alphabet is certifiably hosted inside SK, with `universalReach_finTag` the
taxonomy certificate. Each concrete known-universal 2-tag system from the literature is now an
instance of a machine-checked theorem; citing one is bibliography, not mathematics.

| | |
|---|---|
| `finEncS` / `finEncS_normal` / `finEncS_injective` | symbols as selectors, table-ordered — Stage 76–77's lemmas discharge normality and injectivity |
| `kDepth` / `kDepth_selArgs` / `finDecS` | the decoder COUNTS `K`-WRAPS: a selector's wrap-depth is its symbol index, and off-image garbage is harmless because `dec_enc` is the whole spec |
| `table_decomp` / `finRULE` | the take/drop bookkeeping, done once: any table position splits into pre/post of the right lengths, and `dispatchT_correct` does the rest |

**The SEVENTH `Classical.choice` leak — caught by the build-enforced audit, one stage after the
audit was built.** And it came through a NEW door: `omega` closing a NON-ARITHMETIC goal (the
existential, from contradictory hypotheses) routes through `Classical.choice` — six leaks came via
`BEq`/`simp`, this one via `omega`'s exfalso path. Fix: `absurd hs (Nat.not_lt_zero s)`. The audit
file paid for itself before its first birthday.

### Stage 80: the ranked route, typechecked at last

"Rungs 2/3 via match-bounds" sat in the ranking for THIRTY-FIVE STAGES and was never typechecked.
Match-bounds are TERMINATION certificates; termination implies acyclicity; but the full rung systems
have divergent terms — C1(a)'s witness is K-free, embeds B-freely (resp. C-freely), and diverges in
`{S,B}` and `{S,C}` exactly as it does in pure S. Machine-checked:

| | |
|---|---|
| `RS.SB` / `RS.SC` | the FULL rung systems as rewriting systems — the fragments each had one; the wholes, oddly, did not |
| `sbOfTerm` / `scOfTerm` | pure S embedded with an injective junk-map (`K ↦ B`/`K ↦ C`, never exercised on K-free terms) |
| `sbOfTerm_step` / `_step_back` / `sb_steps_back` | a full bisimulation on the K-free image — the backward path lemma is AXIOM-FREE |
| **`SB_not_normalizing`** / **`SC_not_normalizing`** | both rungs' full systems are not even weakly normalizing |

**So acyclicity-via-termination is CLOSED for both rungs**: no termination proof — by match-bounds,
by any measure, by any method — exists to imply it. The route as recorded was not hard; it was
type-incorrect, and the error survived thirty-five rankings because it was never written as a claim
(Stage 61's lesson, at the level of the ranking itself). The corrected open problem, impossibility
half machine-checked: certify LOOP-FREENESS of a non-terminating system — a relative/transformed
match-bound whose termination is EQUIVALENT to cycle-absence (the transformation is the research
content), or the unbounded well-founded measure Stage 44 named. The ledger's necessary conditions
(a cycle needs a B-duplicating S-step on a τ-heavy, ≥3-leaf argument) are inputs any such
certificate may consume.

### Stage 81: cycle localization — a minimal cycle passes through a ROOT redex

The design probe's survivor, and a necessary condition of a NEW SPECIES: every prior rung constraint
came from measures; this one comes from projection. A cycle whose steps all happen inside arguments
projects to a strictly smaller cycle on one argument, so a minimal cycle must fire a redex at the
root — and therefore, to prove the rungs acyclic, it SUFFICES to rule out cycles through root
redexes.

| | |
|---|---|
| `SBRootStep` / `SCRootStep` | root reduction, no congruence |
| `sbStep_cases` | every step is a root step or a one-sided projection |
| `sb_path_facts` / `sb_plus_facts` | the path dichotomy: contains a root step, or projects into the two sides with one projection nonempty |
| **`sb_cycle_needs_root`** / **`sc_cycle_needs_root`** | any cycle yields a cycle through a root redex — strong induction on size |
| **`sb_acyclic_of_no_root_cycle`** / **`sc_...`** | **the reduction**: `{S,B}` (resp. `{S,C}`) is acyclic iff no term of shape `S f g x` / `B x y z` / `C x y z` reduces back to itself |

The rungs' open problem shrinks to a shape question: can `(f x)(g x)` rebuild `S f g x`? Can
`x (y z)` rebuild `B x y z`? The ledger's measure-based conditions now apply AT the root redex —
the root S-step's duplicated argument must contain a `B` and be τ-heavy — so the two condition
families finally compose at a single, maximally constrained site.

### Stage 82: what a root cycle's return path must do

Stage 81's dichotomy, applied to the root cycles it isolated. Each root cycle's return path either
carries a root step OF ITS OWN, or projects into the redex's two sides — and the projections are
exotic:

| | |
|---|---|
| **`sb_root_S_return`** | a root S-cycle's return: another root step, or `f x ⟶* S f g` AND `g x ⟶* x` |
| **`sb_root_B_return`** | a root B-cycle's return: another root step, or `x ⟶* B x y` AND `y z ⟶* z` |
| `sc_root_S_return` / `sc_root_C_return` | rung three at parity — the C-case projects to `x z ⟶* C x y` and `y ⟶* z`, its degenerate branch dying on `x = C x` |

The degenerate branches all die on size; the projections name two phenomena:

- **COLLAPSE TO ARGUMENT** (`u v ⟶* v`) — in BOTH rules' branches. The rung systems are non-erasing
  except for the fired combinator leaf itself, so a collapse must destroy all of `u` one
  combinator-fire at a time while rebuilding `v` exactly. Ruling it out is the new named sub-target,
  and it is a plausible theorem.
- **SELF-EMBEDDING UNDER APPLICATION** (`f x ⟶* S f g`, `x ⟶* B x y`) — the open-term cousin of
  Stages 39–42's ground self-embedding machinery.

If collapse falls, every root cycle's return path must contain an inner root step, and whether THAT
regress terminates becomes the whole of the rungs — a single well-shaped question where thirty
stages ago there was fog.

### Stage 83: RUNG 2 IS CLOSED — {S,B} is acyclic, and cannot host SK

The no-collapse probe found something stronger than no-collapse: **the right-spine depth
`ρ(app a b) = ρ(b) + 1` never decreases along any `{S,B}` step** — both rules bury the last argument
one application deeper right — **and strictly increases at every root step**. Composed with Stage
81's localization (every cycle yields a cycle through a root step): contradiction in two lines.

| | |
|---|---|
| `rightDepth` / `sbStep_rightDepth_le` | ρ is weakly monotone along ALL steps — an induction of four two-line cases |
| `sbRoot_rightDepth_lt` | root steps strictly raise it |
| **`SB_acyclic`** | **RUNG 2: `{S,B}` is acyclic** — subsuming `sbLight_acyclic`, `sbSOnly_acyclic`, `sbNoBDup_acyclic`, and every census bound at once |
| **`no_pathEncoding_SK_SB`** | **the rung's purpose: `{S,B}` cannot host SK** — the ladder's one refutation mechanism, now applicable |
| `sb_no_collapse` | the question that started the stage, now a corollary |

**Why every measure hunt since Stage 20 missed it**: ρ is not a counting measure — the ledger's
impossibility results (`no_monotone_counting_measure`) do not cover positional measures — and bare ρ
proves NOTHING without strictness on some step of every cycle, which only Stage 81's localization
supplies. The proof needed both halves, and the halves were built twenty months of stages apart in
the wrong order to notice. Six stages of fragment results (τ-machinery, three-level squeezes,
census hunts to eight leaves) are all subsumed by a measure a first-year student could check.

**Why rung 3 does not fall the same way**, exactly as the ledger's "structurally UNLIKE" predicted:
`C x y z → x z y` moves `z` OFF the right spine (Δρ = ρ(y) − ρ(z), either sign). Inherited free:
any `{S,C}` cycle must contain a right-spine C-reduction whose `y` is right-shallower than its `z`.

### Stage 84: rung 3 through the ρ-lens — the tame fragment is acyclic

Rung 3 does not fall to Stage 83's argument — `C` moves `z` off the right spine, and the paper hunt
confirmed the breakage is thorough: sums, maxima, and exponential weightings of right-depths each
fail on one rule or the other. The ledger's "structurally unlike" verdict from Stage 27 holds from
every direction tried. What survives:

| | |
|---|---|
| `SCTameStep` / `RS.SCTame` | the strictly-tame fragment: `C` fires only when it strictly DEEPENS the right spine (`ρ(z) < ρ(y)`) — a LOCAL condition, which is what lets localization survive projection (whole-term-Δρ fragments do not localize) |
| `scTameStep_rightDepth_le` / `scTameRoot_rightDepth_lt` | in the fragment, ρ is weakly monotone and BOTH root rules are strict |
| **`scTame_acyclic`** | the fragment is acyclic — Stage 83's two-piece argument, verbatim |
| **`scCycle_needs_flat_C`** | **any `{S,C}` cycle must fire a FLATTENING `C`** (`ρ(y) ≤ ρ(z)`) — rung three's fourth necessary condition, and its first positional one |

Rung 3's cycle conditions now read: a C-reduction; an S-reduction duplicating a `C`-containing
argument; a two-clause τ-heavy condition; and a flattening `C`. The τ-family and the ρ-family
measure DIFFERENT things (exponential subtree weight vs right-spine position), so the next hunt is
for their joint behavior — what does a flattening `C` do to τ, and can the two families be braided
into a lexicographic argument where each covers the other's blind steps?

### Stage 85: the braid fails, and what lies under both measures

The ranked τ×ρ braid does not exist, and the obstruction is now WITNESSED rather than suspected:
the flat C-steps every cycle must contain (`scCycle_needs_flat_C`) are τ-unconstrained — the
ledger's own `scHeavy` is flat AND τ-raising, build-enforced — and S-fires, the τ-family's bad
steps, always RAISE ρ. Each family's blind spot is invisible to the other; no lexicographic
composite of the two closes rung 3.

| | |
|---|---|
| `scSpine` / `rightDepthC_eq_spine_length` | the right-spine sequence; ρ is its length, τ weights its elements |
| **`scSpine_S_root`** | S refines the spine head into two elements and PRESERVES the tail — `rfl` |
| **`scSpine_C_root`** | C REPLACES the entire spine tail: `σ(z)` out, `σ(y)` in — `rfl` |
| guards | the independence witnesses, build-enforced |

The failure exposes the structure beneath both measures: rung 3's dynamics is a WORD REWRITING
SYSTEM over term-valued letters — the spine sequence — where S is tail-preserving and C is
tail-replacing. Any closing argument must handle the tail replacement, which no positional measure
(Stage 84's sweep) and no τ-composite (this stage) can. The spine calculus is the recorded route,
and it is genuine research: rung 3 remains open, now with five necessary conditions and two
machine-checked impossibility sweeps around it.

### Stage 86: the program review — the settled state, re-accounted

A documentation stage, ranked first because STATUS's header was forty stages stale and every goal
had moved. The refreshed accounting:

- **Scale**: 32 modules, ~700 theorems, ~377 build-enforced `#guard`s plus 16 pinned axiom
  footprints, ~14,100 lines — roughly double the last accounting, all of it from the
  tag-Simulation arc (59–79) and the ladder arc (80–85).
- **Goal 1** (foundations): DONE, unchanged.
- **Goal 2** (the taxonomy): now marked **DONE** — the open item closed at Stage 75 (`tagABInSK`),
  generalised at 78–79 (`tagTInSK`, `finTagInSK`): every finite-alphabet 2-tag system is
  certifiably hosted inside SK. The calibration is complete in both directions.
- **Goal 3** (pure-S reachability): CLOSED, unchanged.
- **Goal 4** (the methodology deliverable): richer by seven `Classical.choice` leaks with seven
  distinct mechanisms, the build-enforced audit, and the estimate-vs-structure catalogue.
- **The ladder**: rung 0 acyclic, rung 1 cyclic, **rung 2 CLOSED (acyclic, not an SK host)**,
  rung 3 open with five necessary conditions, two impossibility sweeps, and a recorded route.

What remains live in the original spec: rung 3 (genuine open research, honestly parked with its
route recorded) and C6 (declined seventy-three times on materiality). The program's headline
sentence is unchanged and now rests on a fully calibrated instrument: **if S alone is universal,
its encoding must be non-injective or must fail to preserve reduction paths.**

### Stage 87: the frozen left — the spine calculus's first theorem

The spine calculus opened with an invariant both measure families overlooked, because it is not a
measure: every `{S,C}` step RESULT is an application, and both root rules produce an APP-HEADED
LEFT component — S yields `(f x)(g x)`, C yields `(x z) y`. This is `{S,C}`-specific structure:
`{S,B}`'s `B x y z ⟶ x (y z)` can expose a leaf left, so the invariant marks a real dividing line
between the two rungs rather than a generic fact about applicative rewriting. Once the left is an
application it stays one (`appL` steps land on apps; `appR` steps don't touch it), so any path
containing a root step can never end at a term of shape `ℓ x` with `ℓ` a leaf. The path dichotomy
then leaves only the rootless spine branch, which forces `x = ℓ x₁` with `x₁ ⟶* ℓ x₁` — a strict
descent in `leafCount`. Hence, unconditionally:

| | |
|---|---|
| `scStep_result_isApp` | every step lands on an application — axiom-free |
| `sc_steps_to_leaf` | leaves are unreachable: a path ending at a non-application is empty — axiom-free |
| `scRootStep_left_app` | both root rules make the left component an application — axiom-free |
| `scStep_leftApp` / `scSteps_leftApp` | app-headedness of the left is invariant ever after — axiom-free |
| **`sc_no_leaf_self_embed`** | **no `{S,C}` term reduces to itself under a leaf: `¬(x ⟶* ℓ x)`** — `[propext, Quot.sound]`, pinned in Audit.lean |

This is exactly the target shape the second-level root-cycle analysis produces: a root-C cycle's
return path forces self-embeddings `x = C x₁`-style where a leaf sits over the recurring term, and
those are now closed off wholesale. The theorem is not itself a cycle condition — it kills a
FAMILY of return paths rather than constraining every cycle — which is why it is filed as the
spine calculus's first result rather than a sixth necessary condition. The next connection to make:
drive the root-cycle case analysis (`sc_cycle_needs_root`) one level deeper and count how many of
its branches terminate in a leaf-self-embedding.

### Stage 88: the second fire — rung 3's sixth necessary condition

The frozen-left theorem was cashed in one stage after it was proved. Stage 82's dichotomies left
each root cycle two escapes: the return path carries a root step of its own, or it projects into
the redex's two sides — and the LEFT projection is a self-embedding, `f x ⟶* (S f) g` for the
S-rule and `x z ⟶* (C x) y` for the C-rule, both instances of one shape: `f x ⟶* (ℓ f) g` with
`ℓ` a leaf. Running the path dichotomy on that path closes it: the trivial branch dies on size
(`f = ℓ f` inflates leaf count), and the projection branch is literally `f ⟶* ℓ f` — the frozen
left. So the self-embedding needs a root step of its own, and lifting through left congruence:

| | |
|---|---|
| `sc_left_self_embed_needs_root` | `f x ⟶* (ℓ f) g` carries a root sandwich — generic in the leaf `ℓ`, covering both rules at once |
| `sc_root_S_return2` / `sc_root_C_return2` | the second-level dichotomies: a root step in the return path, or one inside its left projection |
| `scSteps_appL` | left congruence lifted to paths — axiom-free |
| **`scRootCycle_second_redex`** | **every root cycle's return path reaches a second root redex — at the root, or immediately left of it** |
| **`scCycle_second_redex`** | composed with localization: every `{S,C}` cycle produces a root cycle whose return reaches a second root fire — `[propext, Quot.sound]`, pinned |

This is the sixth necessary condition, and the first positional one in TREE terms (Stage 84's
flat-C was positional in redex-argument terms): a cycle's activity cannot avoid the top-left
spine. The Stage 82 comment asked whether the root-step regress terminates, calling it "the whole
of the rungs" — the regress is now one level deep and machine-checked. What the second level did
NOT close: the surviving branches still carry the exotic reductions — `g x ⟶* x` (collapse to
argument, S-side) and `y ⟶* z` (C-side) — and the second root redex reached is not itself known
to cycle, so the regress does not yet iterate. Collapse-to-argument remains the named sub-target:
killing it would force every root cycle's return to carry a WHOLE-TERM root step, and the shape
lens (ask what is forced, not what is counted) has not yet been pointed at it.

### Stage 89: collapse cannot be rootless

Stage 82 named collapse-to-argument (`u v ⟶* v`) the load-bearing escape, and predicted it was "a
plausible theorem" to kill outright. The shape lens got two pieces of it — not the whole kill, but
enough to change the regress picture. First bite: every step SOURCE is an application, so leaves
are normal, so a leaf-headed term `ℓ v` is LEFT-RIGID — everything it reaches has shape `ℓ w` with
`v ⟶* w` — and leaf-headed collapse dies unconditionally by size descent through the rigidity.
Second bite: the path dichotomy on an arbitrary collapse has its trivial branch dead on size and
its projection branch forcing `v = F' X'` with `v ⟶* X'` — the *same collapse shape one level down
`v`'s right spine* — so the descent bottoms out only in the root branch:

| | |
|---|---|
| `scStep_source_isApp` / `scRootStep_source` | leaves are normal; root sources are app-app-headed — axiom-free |
| `scSteps_from_leafLeft` | left-leaf rigidity: from `ℓ v`, only the right side can ever move — axiom-free |
| **`sc_no_leaf_collapse`** | **leaf-headed collapse is dead: `ℓ v` never reduces to `v`** — pinned |
| `SCRightNested` | the right-nesting subterm relation |
| **`sc_collapse_needs_root`** | **every collapse fires a root redex, launched from a right-nested subterm of the collapsing term** — pinned |
| `sc_root_S_return3` | plugged into Stage 88: a root S-cycle either returns through a whole-term root step, or BOTH its projections carry root fires |

The regress picture after three stages of the shape lens: a root S-cycle's return path carries a
root fire at the top, or root fires in *both* projections; a root C-cycle's return carries one at
the top, or one in its left projection plus the unconstrained datum `y ⟶* z`. Root activity is
inescapable and increasingly localized — what is still missing is a *descent*: none of the fires
reached is yet known to cycle, so the regress does not iterate. The next lever is already visible
in this stage's own lemmas: root sources are app-app-headed while leaf-headed terms are left-rigid,
so when a redex's head argument is a leaf (`f` in `S f g x`, `x` in `C x y z`), the left projection
can never reach a root redex at all — Stage 88's second-level sandwich becomes absurd, and the
projection escape closes entirely for leaf-headed-argument root cycles.

### Stage 90: the leaf-argument kill — cycle anatomy

Stages 88 and 89 had already proved the two halves of a contradiction without composing them: root
sources are app-app-headed (`scRootStep_source`), and leaf-headed terms are left-rigid
(`scSteps_from_leafLeft`). Together: **a leaf-headed term can never reach a root redex**
(`sc_leafLeft_no_root_reach`, axiom-free). Stage 88's second-level sandwich lives inside the left
projections `f x ⟶* (S f) g` and `x z ⟶* (C x) y`, whose sources are leaf-headed exactly when the
fired redex's HEAD ARGUMENT is a leaf — so for those root cycles the projection escape is absurd,
and the return must carry a whole-term root step. Folding in Stage 89's collapse fire gives each
rule its sharpest cycle statement yet:

| | |
|---|---|
| `sc_leaf_or_app` / `sc_leafLeft_no_root_reach` | the dichotomy and the composition — axiom-free |
| `sc_root_S_return_leaf` / `sc_root_C_return_leaf` | leaf-headed-argument root cycles must return through a whole-term root step |
| **`sc_root_S_anatomy`** | **a root S-cycle returns through a whole-term root step, or `f` is an application AND both projections carry root fires** — pinned |
| **`sc_root_C_anatomy`** | **a root C-cycle returns through a whole-term root step, or `x` is an application, the left projection fires, and `y ⟶* z`** — pinned |

The anatomies are the current frontier statement of rung 3: any `{S,C}` cycle localizes to a root
cycle (Stage 81), and that root cycle's return path either fires a whole-term root redex — in
which case the cycle passes through ANOTHER root redex, since `b ⟶* t → u ⟶* a` closes a cycle
through `a` — or the redex's head argument is an application and the projections carry root fires
on strictly smaller terms. The first branch is a rotation, not a descent; the second branch
descends but lands on fires not yet known to cycle. Making the rotation formal (every root cycle
yields a root cycle at each of its return's root fires) is cheap and would close the branch tree
into a genuine dichotomy: rotate at the same size, or descend into projections.

### Stage 91: rotate or descend — one invariant for the frontier

Stage 90's per-rule anatomies close into a single dichotomy on root cycles. The rotation half is
three combinators of glue once stated: a whole-term root fire on the return path has `b ⟶* t` and
`u ⟶* a` around it, and root steps are steps, so `b ⟶* t → u ⟶* a` closes a root cycle THROUGH
the return's fire — on the same cycle, at the same size. The descent half turned out to be uniform
across the two rules, which the per-rule anatomies had obscured: for both `S f g x` and `C x y z`,
the left projection runs from `app h r` — the HEAD argument applied to the LAST argument — to the
fired term's left component. One statement, no case split in the conclusion:

| | |
|---|---|
| `scRootStep_step` / `scRootCycle_of_return_fire` | root steps are steps; the rotation — axiom-free |
| **`scRootCycle_rotate_or_descend`** | a root cycle contains another root cycle on itself, or its head argument is an application and `app head last` fires a root redex on a strictly smaller term |
| **`scCycle_rotate_or_descend`** | composed with localization: every `{S,C}` cycle carries a root cycle that rotates or descends — pinned |

Why this is the right frontier statement: rotation is movement among the finitely many root fires
ON a single cycle; descent leaves the cycle for a strictly smaller term, but lands on a fire not
known to cycle. Neither branch self-destructs, so rung 3 stays open — but the invariant now has
the shape of a well-foundedness argument missing exactly one ingredient: a reason rotation cannot
be taken forever. On a FINITE cycle it cannot (finitely many fires), but `RS.Steps` is Prop-level
and carries no length, so "finitely many rotations" is not yet a theorem. Length-indexed paths —
`StepsN n`, minimal-length cycles, rotation preserving total length while shifting basepoint —
are the missing infrastructure, and the first genuinely new machinery the spine-calculus thread
has needed since it opened.

### Stage 92: the scaffold — lengths, rotation conservation, and the descent engine

Stage 91 ended on a sentence that could not be formalized: "on a finite cycle, rotation can only
visit finitely many fires." `Steps` is Prop-level and lengthless — the program's rewriting
infrastructure, sufficient for eleven acyclicity results, simply cannot say "finitely many" about
a path. This stage builds the missing layer, generically in RS.lean:

| | |
|---|---|
| `RS.StepsN` | length-indexed paths; `toSteps`/`toStepsN` equivalence, `trans` (adds lengths), `rotate` (basepoint shift preserves length) — all axiom-free |
| **`RS.no_cycle_of_descent`** | **the descent engine: if every nonempty cycle yields a strictly shorter one, there are no nonempty cycles** — bounded strong induction, no minimum chosen, hence no choice axiom and no decidability demand |
| `RS.acyclic_of_cycle_descent` | the bridge: strictly-shortening cycle surgery proves `Acyclic` outright — pinned |
| `sc_cycle_stepsN` | every `{S,C}` cycle yields a length-indexed nonempty cycle |
| **`scRootCycle_rotate_same_length`** | **rotation preserves length**: `t → u ⟶ᵏ a → b ⟶ˡ t` and its rotation at the return's fire are both cycles of total length `k + l + 2` — pinned |

The design point worth recording: the engine never *finds* a minimal cycle. Extracting a minimum
from "some cycle exists" needs either decidability (unavailable — the carrier is infinite) or
choice (banned). Bounded induction sidesteps both: descend from any given cycle's own length, and
the hypothesis does the rest. The rung-3 reading: rotate-or-descend now has its measure. Rotation
provably spends no length, so it cannot escape a length-descent argument — if the DESCEND branch
(or any future surgery on the rotate branch) can be shown to strictly shorten some cycle, rung 3
closes through `acyclic_of_cycle_descent`. What descent currently lacks is a cycle at the smaller
size: the projection fires are on smaller terms but not known to recur. The gap between "fires"
and "cycles" is now the whole of rung 3.

### Stage 93: minimal cycles are root cycles — localization spends no length

The scaffold's first purchase. Stage 81's localization finds a root cycle inside any cycle but
forgets how long the found cycle is; against the descent engine, that discards the asset the
engine spends. Redoing the dichotomy and the localization in `StepsN` form recovers it, and the
accounting is exact: the root sandwich accounts for every step (`k₁ + 1 + k₂ = n`) and the
projection branch's component lengths SUM to the whole (`nf + nx = n`), so localization can only
shed length, never add it — and on a minimal cycle it can shed none:

| | |
|---|---|
| `scStep_irrefl` / `sc_no_one_cycle` / **`sc_cycle_length_ge_two`** | no step is a self-loop (the root cases die on occurs-check); minimal cycle length ≥ 2 — pinned |
| `RS.stepsN_zero_eq` / `RS.stepsN_one_step` | index-literal inversions, generic |
| `sc_stepsN_facts` | the path dichotomy with lengths |
| `sc_cycle_needs_root_length` | a cycle of length `n` yields a root cycle of total length ≤ `n` |
| **`sc_minimal_cycle_is_root`** | **on a minimal-length cycle the inequality is equality: some root cycle has EXACTLY the minimal length** — pinned |

The strategic consequence: any future descent argument may assume its minimal cycle fires at the
root, with the rotate-or-descend dichotomy and both anatomies available at full strength on a
cycle that cannot shrink. Every tool of Stages 81–92 now composes on a single object — the minimal
root cycle — and the rung closes if that object can be shown to yield any strictly shorter cycle.

The audit also caught the EIGHTH `Classical.choice` leak, and it is the seventh's mechanism
recurring: `omega` aimed at a non-arithmetic goal (an existential in a contradictory branch)
routes through choice. The lesson sharpens from "give omega arithmetic goals only" to a pattern:
contradictory-hypothesis branches INVITE the leak, because the goal there is whatever the theorem
concludes, and omega will happily close it. `subst` + `absurd` + a targeted `Nat` lemma is the
clean form.

### Stage 94: no two-cycles — the first kill

Stage 93's exact-length localization makes short cycles concrete enough to attack directly: a
2-cycle yields a root cycle of length ≤ 2, which is a root fire followed by AT MOST ONE step
straight back. The zero-step return dies on `scStep_irrefl`; the one-step return is the theorem
**a root fire is never undone in one step** (`sc_no_root_two_cycle`), by exhausting what that one
step can be against the fired shape. Eleven branches: nine die on absorption (a term equalling
itself under an application — the recurring size kill, now named `sc_ne_absorb_left/right`), one
on bookkeeping, and the single live-looking branch — an `appL` return over a root C-fire, which
forces `y = z` and the step `x z ⟶ (C x) z` — dies because its own projection demands the step
`x ⟶ C x`, forbidden by the frozen left. Stage 87's theorem, proved for the multi-step relation,
earns its keep at length one.

| | |
|---|---|
| `scRootStep_inv` | root steps as equations — axiom-free, and the method note below |
| `sc_ne_absorb_left` / `sc_ne_absorb_right` | absorption is impossible: `s ≠ s r`, `s ≠ r s` |
| **`sc_no_root_two_cycle`** | **a root fire is never undone in one step** — pinned |
| `sc_no_two_cycle` | no `{S,C}` cycle has length 2 |
| **`sc_cycle_length_ge_three`** | **minimal cycle length ≥ 3** — pinned |

Method note, earned across three build failures avoided: every hypothesis was converted to an
equation BEFORE analysis (`scRootStep_inv`, `scStep_cases`) rather than case-split in place. Cases
on a hypothesis whose indices are concrete terms risks dependent-elimination failures; equations
never do, and the whole proof is injections, two named absorption lemmas, and one frozen-left
call. The numeric ladder (no 1-cycles, no 2-cycles) is not the road to the rung — each length
costs multiplicatively more — but the 2-cycle proof surfaced the reusable pattern: the return's
FIRST step is already heavily constrained by the fired shape. The general form of that constraint
is the next thing worth stating.

### Stage 95: budgets — and collapse costs two

The general form of Stage 94's observation, plus an unconditional fact found on the way. **No
single step collapses `u v` to `v`** (`sc_no_step_collapse`): the root cases die on absorption
(the fired result contains `v` twice, or once plus a leaf), the `appL` case on absorption, and the
`appR` case demands the same collapse one size smaller — size induction closes it. With the
zero-step case dead on absorption too: **collapse costs at least two steps**
(`sc_collapse_length_ge_two`, pinned). Stage 82 called collapse "exotic"; it now has a price tag.

The return dichotomies then go length-indexed (`sc_root_S_return_length` pinned,
`sc_root_C_return_length`): the root sandwich accounts for every step (`k₁ + 1 + k₂ = n`), the
projection splits the budget (`kL + kR = n`), and the shapes force side conditions — both left
self-embeddings are nonempty (`kL ≥ 1`, absorption), and the S-side's right projection IS a
collapse, so `kR ≥ 2`. The C-side's right projection (`y ⟶* z`) may be free: the S/C asymmetry
that Stage 89 refused to force away persists at the budget level, and it now has consequences:

- `sc_root_S_projection_length`: an S-rooted root cycle with a rootless return has return length
  ≥ 3, cycle length ≥ 4. Combined with `sc_cycle_length_ge_three`: a 3-cycle, if one exists, is
  either S-rooted with TWO root fires among its three steps, or C-rooted.
- Any k-cycle question on the S side is now arithmetic over branch budgets. The C side, where the
  right projection is free, is where short cycles must live — the next case analysis knows its
  address.

### Stage 96: RUNG 3 IS CYCLIC — the three-cycle that was hiding in the last branch

The 3-cycle question did not get a kill; it got a WITNESS. Stage 95's budgets had cornered any
S-rooted 3-cycle into carrying two root fires among its three steps (`k₁ + 1 + k₂ = 2`), and
working that branch through the injections — fire one S, fire two C, an `appL` C-fire closing —
leaves a single consistent assignment. It is inhabited. With `h = C S C`:

    S (C h) C h  ⟶S  C h h (C h)  ⟶C  h (C h) h  ⟶C·appL  S (C h) C h

Nine leaves, verified computationally before formalizing, then proved by three constructor
applications — the whole cycle is AXIOM-FREE (`SC_cycle`, `SC_not_acyclic`, pinned).

| | |
|---|---|
| `scCycH` / `scCycA` / `scCycB` / `scCycC` | the witness: `h = C S C` and the three cycle terms |
| **`SC_cycle`** | **`StepsN 3 scCycA scCycA` — {S,C} has a reduction cycle** — axiom-free, pinned |
| **`SC_not_acyclic`** | **rung 3 closes: CYCLIC** — axiom-free, pinned |
| **`sc_minimal_cycle_length`** | **the minimal cycle length is EXACTLY 3** — Stages 93–94's kills were complete — pinned |

What this settles, and how it reads back through the arc:

- **The ladder is finished.** Rung 0 acyclic, rung 1 cyclic, rung 2 acyclic, rung 3 CYCLIC — the
  two two-combinator bases `{S,B}` and `{S,C}` split in opposite directions, exactly the
  "structurally unlike" the ledger called at Stage 27. `PathEncoding.refute_of_acyclic` can never
  apply to `{S,C}`: the acyclicity route to refuting SK-hosting there is permanently closed.
- **The impossibility hunt was a search procedure.** Every failed measure, every fragment
  acyclicity, every necessary condition narrowed where a cycle could live; Stage 95's budget said
  "an S-rooted 3-cycle must look like THIS," and the only shape satisfying the constraints is the
  cycle. The frozen left, the anatomies, the budgets — none of them was wasted; they were the
  successive refinements of the witness's address. The 6-leaf census missed it by three leaves.
- **Every necessary condition is validated against the witness**: both C-fires are flat (guarded
  in-file), the cycle passes through root redexes, carries a second fire, and its S-rooted return
  holds exactly two fires. Six conditions, all consistent — the theory was correct; only its
  conjectured conclusion (acyclicity) was wrong.
- **What survives as open**: whether `{S,C}` HOSTS SK is untouched — the refutation mechanism is
  gone, but no Simulation of SK into `{S,C}` exists either. Like rung 1, cyclicity makes `{S,C}` a
  candidate host rather than a refuted one.

### Stage 97: the program review — the settled state after the ladder closed

A documentation stage, triggered by the rule Stage 86 set: the review is rankable and lands
whenever a goal-level result does. Stage 96 was one. The refreshed accounting:

- **Scale**: 32 modules, ~770 theorems, ~412 build-enforced `#guard`s plus 35 pinned axiom
  footprints, ~15,200 lines — the growth since Stage 86 is the shape-lens arc (87–96), eleven
  stages from "no term reduces to itself under a leaf" to the rung-3 cycle.
- **Goals 1–3**: unchanged (DONE / DONE / CLOSED).
- **Goal 4** (methodology): richer by an eighth `Classical.choice` leak (mechanism seven
  recurring — contradictory-hypothesis branches invite `omega` onto non-arithmetic goals), the
  equations-before-analysis discipline for indexed case blasts, and the review's new procedural
  entry: **step 4′ of the rung procedure** — when the impossibility machinery stalls with one
  surviving branch under exact accounting, instantiate the branch; unification either kills it or
  builds the witness. Rung 3 fell to step 4′.
- **The ladder**: COMPLETE. Rung 0 acyclic, rung 1 cyclic, rung 2 acyclic (not an SK host),
  rung 3 CYCLIC (acyclicity-refutation permanently inapplicable). The two two-combinator bases
  split in opposite directions. Six necessary conditions on `{S,C}` cycles survive as the
  sharpest description of its cycle space, verified against the witness.
- **STATUS header, ladder table, rung-3 bullet, and rung procedure** all rewritten to the settled
  state; the census caveat now carries its sharpest example (missed the 9-leaf cycle by three).

What remains live in the original spec: C6 (declined eighty-four times), and the questions the
ladder's completion OPENS rather than closes — `{S,C}` and `{S,I}` as candidate SK hosts, where
the refutation mechanism cannot reach and no Simulation exists either. The headline sentence is
unchanged and now rests on a finished instrument: **if S alone is universal, its encoding must be
non-injective or must fail to preserve reduction paths.**

### Stage 98: no I-like combinator — the census bound becomes a theorem, without a search

The ranked probe was "bounded search for `t` with `t x ⟶* x`"; the shape lens answered before any
search started. Both `{S,B}` and `{S,C}` rules drop exactly their own fired combinator leaf and
never PROJECT an argument — so every step result is an application (Stage 87's
`scStep_result_isApp`, now mirrored as `sbStep_result_isApp`). An I-like combinator must in
particular satisfy `t S ⟶* S`: the path cannot be empty (`t S = S` is absorption) and cannot be
nonempty (it would end at a leaf, and leaves are unreachable — `sc_steps_to_leaf` /
`sb_steps_to_leaf`). Dead, at every size:

| | |
|---|---|
| `sbStep_result_isApp` / `sb_steps_to_leaf` | the `{S,B}` mirrors of Stage 87's lemmas — axiom-free |
| `sc_no_I_on_S` / `sb_no_I_on_S` | even the single instance `t S ⟶* S` fails |
| **`sc_no_I_like`** / **`sb_no_I_like`** | **no I-like combinator at any size** — both pinned |

Two readings. Methodological: `{S,B}`'s "no I-like up to 7 leaves" was a Stage-era census result;
the unconditional theorem was always one composition away from "every step result is an app," and
nobody asked until the transport question came up — bounded evidence has a way of looking like
the best available long after it stops being so. Structural: the contrast with `{S,K}` and
`{S,I}` is exactly PROJECTION — `K x y ⟶ x` and `I x ⟶ x` can return a bare argument, which is
how those bases host leaves-from-apps and why the ladder's cyclic-by-inheritance argument worked
there. `{S,B}` and `{S,C}` are projection-free, so the define-I transport is closed
unconditionally for both, and any SK-hosting certificate for them must survive without it: SK's
erasing steps must land on encoded terms (applications), which the leaf argument does not forbid.
The hosting question stays open in both directions, now with one fewer route on each side.

### Stage 99: the second three-cycle — uniqueness refuted, classification conjectured

The ranked question — is Stage 96's witness THE minimal cycle? — has answer no. The full paper
classification runs both budget branches of both root shapes through the injections (~40 leaf
cases). The consecutive-fires branch (two root fires then a step) survives only as the h-cycle,
exactly as Stage 96 found. But the C-rooted projection branch with `y = z` and a two-step left
path has its own surviving assignment: `x = w w`, `y = z = w`, `w = S (C C)`:

    C (w w) w w  ⟶C  (w w w) w  ⟶S·appL  (C C w (w w)) w  ⟶C·appL  C (w w) w w

Thirteen leaves, disjoint from the h-cycle (leaf counts 13/12/14 vs 9/11/10), and C-rooted with
ONE root fire — the budgets' other consistent answer, inhabited too. Both cycles axiom-free.

| | |
|---|---|
| `scWCycW/A/B/B2` + steps | the witness, by constructor — axiom-free |
| **`SC_second_cycle`** | **a second 3-cycle** — axiom-free, pinned |
| **`sc_min_cycle_not_unique`** | **minimal-cycle uniqueness REFUTED** — axiom-free, pinned |
| `scRightNested_size/trans/inv` | the right-nesting toolkit |
| **`sc_no_step_right_embed`** | **no single step right-embeds its source** — the case tree's recurring kill, packaged; subsumes single-step frozen-left and every wrap kill — pinned |

**CONJECTURE (3-cycle classification).** Every root 3-cycle of `{S,C}` is a rotation of the
h-cycle or the w-cycle — equivalently, `(a, b)` with `SCRootStep a b ∧ StepsN 2 b a` forces
`(a, b) ∈ {(scCycA, scCycB), (scCycB, scCycC′), (scWCycA, scWCycB)}`-shaped instances. Status:
the case tree is fully worked on paper (this stage); every branch dies on absorption, collapse,
right-embedding, or app-vs-leaf EXCEPT the two inhabited ones. Formalizing is a Stage-94-style
equations-first blast at roughly 4× scale — mechanical, bounded, and now specified. Materiality:
it would be the program's first complete classification of a cycle space; the two witnesses
already suffice for every downstream claim made so far.

A pattern note: this is the third consecutive stage where precise formulation dissolved or
inverted the ranked question (96: kill became witness; 98: search became one-liner; 99:
uniqueness became a second witness plus a two-point classification). Exact accounting keeps
outperforming intuition about which side of a question is true.

### Stage 100: the hosting question, scoped — and rung 3 embeds in the top

The ranked deliverable was the obstruction analysis for SK ≤ `{S,C}`, and it comes with a formal
core: the DIRECTION ASYMMETRY is now a theorem. `{S,C} ≤ SK` in the weak certificate class
(`scInSK : PathEncoding RS.SC RS.SK`, pinned): `C` is implemented by the Stage 76 bracket toolkit
(`cImpl x y z ⟶* x z y` is one application of `bracketOpt_beta3_Term`), and injectivity reuses
`siInSK`'s technique with a one-level cascade — `cImpl`'s right component is `K`-headed
(`cImpl_shape`, by `rfl`), no image is `K` or `K`-headed, done. Every rung of the ladder now
path-encodes into SK: the taxonomy's upward closure is complete.

The obstruction analysis for the hard direction, recorded honestly — every candidate fails:

1. **Acyclicity refutation**: inapplicable. Stage 96 made `{S,C}` cyclic, which is exactly the
   necessary condition `not_acyclic_of_pathEncoding` imposes on a host of cyclic SK. The one
   refutation mechanism the program owns cannot touch the question.
2. **Leaf reachability**: SK reaches leaves (`K K y ⟶ K`), `{S,C}` cannot — but path encodings
   land leaves on app-shaped images, so the mismatch does not transport.
3. **Conservation**: `{S,C}` is non-erasing (morally WN ⇒ SN), SK is not (`K x Ω`) — but
   normality does not pull back along `path`, so the mismatch does not transport either.
4. **Cycle-space cardinality**: killed formally this stage — cycles pump through congruence
   (`sc_cycle_pump`, axiom-free): `app scCycA u` cycles for EVERY `u`, so both systems have
   infinitely many cycle terms and no counting refutation exists.
5. **Cycle lengths**: source cycles stretch freely along host paths; `{S,C}`'s missing 2-cycles
   force nothing.

Conclusion: SK ≤ `{S,C}` is open with NO applicable tool in either direction. A refutation needs
a genuinely new transportable invariant — something preserved by injective step-to-path maps that
SK has and `{S,C}` lacks; nothing in the program's inventory qualifies. A certificate needs K's
erasure encoded inside app-shaped `{S,C}` terms, where the tag pipeline's Simulation machinery is
the template but the non-erasing host must simulate erasure by parking garbage — the exact
inverse of the problem `bwd` solved for the tag driver (there the host computed too much; here it
cannot forget at all). That inversion is the sharpest statement of why the question is hard.

### Stage 101: the classification — the conjecture discharged at scale

Stage 99's conjecture is now a theorem, and it is the program's first complete classification of
a cycle space: **every root 3-cycle of `{S,C}` is exactly the h-cycle at basepoint A, the h-cycle
at basepoint B, or the w-cycle** (`sc_root_three_cycle_classified`, pinned), and composed with
localization, **every 3-cycle passes through a known cycle** (`sc_three_cycles_are_known`,
pinned). The proof is the Stage-94 method at ~45 leaf branches: an S-rooted return cannot project
(the budget 1 + 2 exceeds 2), so it carries consecutive fires, and only S-then-C survives — into
the h-cycle at basepoint A; a C-rooted return's sandwich survives only as step-then-fire into
basepoint B, and its projection survives only as the w-cycle, found through either placement of
its double fire.

What made ~45 branches tractable, recorded as method: (1) EQUATIONS FIRST — every hypothesis
injected to atoms before any analysis; (2) LINEAR ARITHMETIC AS THE UNIVERSAL KILL — each
injected equation becomes a linear fact over leaf counts via a defeq-ascribed `congrArg`, and
`absurd _ (by omega)` combines them, so dead branches need no rewrite-direction judgment at all;
(3) the three step-shaped kills (`sc_no_step_collapse`, `sc_no_step_right_embed`,
`scStep_result_isApp`) for what counting cannot see. The three live branches pin every variable
by unification and close by `rfl` — the same collapse-to-one-assignment that FOUND both cycles.

The audit caught the NINTH `Classical.choice` leak, and it is a new variant of the omega door:
`omega` proving a CONJUNCTION-INSIDE-DISJUNCTION goal (`k₁ = 0 ∧ k₂ = 1 ∨ k₁ = 1 ∧ k₂ = 0`)
routes through choice, while plain disjunctions of equalities are clean — verified by a minimal
experiment before fixing. The budget-splitting idiom the length arc introduced at Stage 93 is
exactly where such goals arise, so the clean form (plain-disjunction omega, per-branch arithmetic
`have`s) is now the recorded idiom.

### Stage 102: garbage parking — the design analysis, and the shredder

The design probe for hosting SK inside `{S,C}`, worked to the point where every piece is either a
theorem, a named open question, or a stated tension. The problem: `enc (K x y) ⟶* enc x` for
EVERY `y`, with `enc` injective — unboundedly many distinct host terms converging on one, in a
host where every step preserves all material except its own fired combinator leaf.

**The enabling fact, now a theorem** (`sc_unbounded_convergence`, axiom-free, pinned): unbounded
convergence EXISTS in `{S,C}`. A left-nested C-tower is a chain of C-redexes, each fire consuming
exactly one leaf, and every tower collapses to the fixed residue `C C C` (`cTower_shreds`). So
the naive impossibility argument — "a non-erasing host cannot lose arbitrary material" — is
false: it can, one leaf per step, provided the material is TOWER-SHAPED. Any refutation of
SK ≤ `{S,C}` must find a subtler invariant than erasure-counting.

**The design tensions, stated honestly:**

1. **Good garbage is bad data.** Towers self-shred — they are volatile, decaying toward `C C C`
   under any strategy that reaches them. That makes them ideal garbage (drop the `y`-material as
   towers and let reduction consume it) and useless storage (a tower-coded datum can lose its
   value to a stray `appL`). Stable data needs normal forms — partial applications, the tag
   pipeline's `mkWord` discipline — and those are precisely the shapes that CANNOT be consumed.
   A hosting construction must convert stable code into volatile garbage at exactly the K-fire,
   and nowhere else.
2. **The no-I weakness bites the interpreter route.** Stage 98 proved `{S,C}` defines no I-like
   combinator even on single leaves; the same head-variable poverty makes it UNCLEAR whether
   `λs. s a` (application-to-a-fixed-argument, the heart of fold-style data) is definable at all.
   The tag pipeline's entire data discipline (fold-coded words, selector dispatch) presumes
   pairing; `{S,C}`'s definable-operations fragment may be too weak for it. NAMED OPEN QUESTION:
   is pairing (`pair a b s ⟶* s a b` for some closed `pair`) definable in `{S,C}`? A negative
   would kill the interpreter route outright and be the sharpest λI-fragment separation the
   program has; a positive unlocks the tag-pipeline template.
3. **Convergence is necessary, not sufficient.** The shredder converges tower families; K-erasure
   needs convergence of `enc (K x y)` over ALL `y` — the encoding must ROUTE arbitrary
   `y`-structure into tower shape before shredding. That routing is itself a computation the host
   must perform without erasure, on data it cannot pair-project. This circularity — you need the
   machine to build the garbage the machine needs to discard — is the precise residue of the
   hosting problem, sharper than Stage 100's "the host cannot forget."

Standing: SK ≤ `{S,C}` remains open in both directions, now with the failure modes of both naive
routes (impossibility-by-erasure, construction-by-interpreter) mapped. The pairing question is
the next decidable-feeling probe.

### Stage 103: the pairing probe — rotation yes, selection no

Stage 102's named question, answered in three parts. The probe needed a new carrier — `SCV`,
`{S,C}` terms over opaque variables, because closed terms are not inert enough to state
"definable on arbitrary arguments" — and the shape lens then did what it has done all arc:

- **Selection is impossible** (`scv_no_single_selector`, axiom-free, pinned): no machine `T`, at
  ANY size, reduces `T a s` to `s a`. Every fire result carries two spine arguments, so `s a` is
  never the result of a step; congruence would need a step landing on a bare variable; the path
  must be empty, and it is not. Three lemmas, no induction on the machine.
- **Rotation is definable** (`scRot_beta`, axiom-free, pinned): `C C u v w ⟶* v w u`. So pairing
  exists UP TO CYCLIC ROTATION of the argument order — a consumer arriving in the MIDDLE slot is
  applied to both fields.
- **Arrival-order pairing is open**: no machine `P` with `P a b s ⟶* s a b` up to 9 machine
  leaves (census). The paper genealogy forces the last two fires (`C s b a`, reached via
  `C C b s a` or `C (C s) a b`) but the ancestor tree branches beyond; CONJECTURED impossible.

The design consequence for hosting: `{S,C}` data protocols cannot use SK-style selectors, but
rotation-convention protocols — where the handler is passed in a fixed middle position — survive
the impossibility. The interpreter route is neither dead nor open as previously stated: it is
CONSTRAINED to rotation discipline, a design regime with no precedent in the tag pipeline. The
sharpest formal separation so far between `{S,C}` and every basis the program has hosted
machines in: SK and {S,K}-fragments select; `{S,C}` only rotates.

### Stage 104: branching without selectors — the design skeleton stands

The rotation-discipline design's crux was branching: a selector-free calculus cannot erase the
untaken arm, and every data protocol needs a two-way choice. Solved, by HEAD PROMOTION under a
uniform protocol (`tag β₁ β₂ x`, both tags consuming exactly three arguments):

| | |
|---|---|
| `scTagA := C` | dispatches FIRST arm: `a β₁ β₂ x ⟶ β₁ x β₂` — one C-fire |
| `scTagB := C C` | dispatches SECOND arm: `b β₁ β₂ x ⟶* β₂ x β₁` — Stage 103's rotator re-read |
| `scTag_normal` | both tags NORMAL — inert as stored data; distinguishable |

The chosen arm becomes the head, receives the continuation `x`, and receives the UNTAKEN arm as
an ordinary argument — parked, not erased. All axiom-free, dispatches pinned.

**The design skeleton for a `{S,C}` data layer, as it now stands:**

1. **Symbols**: the two-cell tag alphabet above; n-symbol alphabets via longer C-powers (each
   C-power dispatches with a distinct promotion pattern — unverified beyond n = 2).
2. **Branching**: this stage — uniform, inert, head-promoting, garbage-parking.
3. **Words**: chained cells where each cell's tag dispatches the driver's per-symbol arms and the
   continuation carries the rest of the word — the mkWord discipline with the handler in the
   protocol's third slot instead of SK's selector position. UNVERIFIED: the chaining plumbing.
4. **Driver recursion**: self-application via S-duplication (the cycle witnesses prove the
   pattern lives); fixpoint-free selfRep needs re-derivation without K. UNVERIFIED.
5. **The garbage-slot invariant**: each simulated step parks exactly one untaken arm — a FIXED
   closed term per branch — so `enc` can carry one designated slot whose contents must reduce
   back to a constant after each step. The finitely many obligations `Jᵢ⟨G₀⟩ ⟶* G₀` are concrete
   reduction checks once the arms are fixed. UNVERIFIED, and the likeliest failure point: the
   parked arm must land in a position where those reductions can actually fire.

Standing: no piece of the skeleton is known impossible; three pieces are proved (symbols,
branching, shredding); two are engineering with named obligations. This is the first time the
hosting question has had a constructive attack with no identified obstruction — the honest odds
moved. The next stage of this thread is the word-chaining plumbing, which will either produce
`{S,C}`-encoded two-symbol words with a working traversal step, or name the obstruction.

### Stage 105: the word layer — mkWord survives translation to rotation-land

Word chaining, closed — and the failure of the obvious route is as informative as the success of
the real one. The obvious protocol (cell = gadget applied to tag and rest, arms supplied at
interrogation) requires the 4-ary permuter `M t r x y ⟶* t x y r`; the census found no such
machine up to 9 leaves, matching the pairing pattern: `{S,C}` resists gadgets that hold a stored
argument BEHIND later arrivals under a fixed head. The working protocol dissolves the gadget:
store `rest` inside the tag application, and let the tags' own fire patterns do the chaining:

| | |
|---|---|
| `scCellA_step` | `(C rest) β₁ β₂ ⟶ rest β₂ β₁` — recurse into the word, arms SWAPPED |
| `scCellB_step` | `(C C rest) β₁ β₂ ⟶* β₁ β₂ rest` — dispatch the first arm |
| `scWord` | σ₁ := b-cell, σ₂ := a-cell over b-cell, over an end-marker parameter |
| **`scWord_step_false` / `scWord_step_true`** | **the traversal theorems: per-symbol arm dispatch under one calling convention** — the arm heads, receives the parked other arm, then the remaining word |
| `scWord_normal` | words over a normal end marker are NORMAL — stable data |

All axiom-free, all pinned. The design content: swap PARITY is the selection mechanism — a-cells
rotate which arm is "first," b-cells fire whichever arm currently is — so a two-symbol alphabet
encodes as `b` and `ab`, and every symbol block ends in a dispatch that lands on the right arm.
This is the tag pipeline's `mkWord`/`STEPc` discipline reborn without selectors.

The hosting skeleton stands at FOUR of five pieces proved: symbols (104), branching (104),
shredding (102), words (105). The remaining piece is the driver: (a) the arms must re-invoke the
traversal on `rest` — recursion, without K-based `selfRep`; S-duplication is the mechanism and
the cycle witnesses prove the pattern lives, but a driver that duplicates ITSELF into the arm
position is unbuilt; (b) the garbage-slot obligations — each dispatch parks one arm, a fixed
closed term, and the machine must reduce it back to a constant slot. Both are engineering with
named shapes; neither has an identified obstruction.

### Stage 106: the re-launcher and the recycling arm — one gap from a driver

The driver probe, and the arc's compounding continues: two compositions closed most of the
remaining distance, and the second dissolved a problem the Stage 104 design had budgeted for.

| | |
|---|---|
| `scRelaunch β₁ β₂ := C (C C β₂) β₁` | applied to `rest`: three C-fires walk it into head position with both arms — `scRelaunch_beta : ⋯ r ⟶* r β₁ β₂`. Normal, storable |
| `scArm P := C (C C P)` | an arm that IS a partial re-launcher: the dispatch hands it exactly its missing slots — `scArm_step : scArm P o r ⟶* r o P` |
| **`scTraversal_step_false/true`** | **the composed full traversal step**: interrogate a word whose acting arm is a recycling arm, and the rest of the word is directly re-interrogated, arms rotated, payload installed — both symbols, one calling convention — pinned |
| `scArm_normal` | arms are storable data |

The design surprise: THE PARKED ARM IS NOT GARBAGE. Stage 104 budgeted a garbage-slot invariant
for the untaken arm — the likeliest failure point, per that ledger entry. The recycling arm
eliminates it: the dispatch's "parked" argument is exactly the re-launcher's first missing slot,
so the untaken arm becomes the next step's FIRST arm. Nothing is discarded, nothing accumulates:
the arm pair evolves as `(β₁, β₂) → (β₂, P)` where `P` is the acting arm's payload. All
axiom-free.

The single remaining obligation, sharply: PAYLOAD REGENERATION. Each traversal step installs the
acting arm's payload as the next second arm and consumes it — so a depth-`n` payload chain
supports `n` steps, and unbounded traversal needs payloads that rebuild themselves. The mechanism
must be S-duplication (`S f g x` copies `x`), and the shape is a pack `q` that, fired as some
S-redex's third argument, lands one copy as the running machinery and one as the future payload.
The no-I constraint rules out the naive quine assembly (`g q ⟶* q` needs identity), so the pack's
protocol must absorb the extra applications the calculus forces — an arity-design problem, not an
identified obstruction. If it closes, `{S,C}` hosts unbounded two-symbol word traversal, and the
hosting question's constructive half comes within reach of a genuine tag-step simulation.

### Stage 107: the driver closes — `{S,C}` hosts its first machine

Payload regeneration, discharged by a five-leaf term. The reframe that cracked it: the acting arm
need not copy ITSELF — it can copy the PARKED arm, and the queue then sustains itself with all
arms equal. The search found the machine at size five, and it is a term the program already knew:

| | |
|---|---|
| `scDup := S (C C) (C C)` | `= w (C C)` where `w = S (C C)` is the second 3-cycle's seed — the cycle engine, repurposed as the duplicator |
| `scDup_step` | `scDup o r ⟶* r o o`: the S-fire lands the parked arm in BOTH slots of a fresh re-launcher; the next C-fire assembles it exactly |
| `scRun_step` / **`scRun`** | with both arms `scDup`, the arm pair regenerates every step — **the machine walks ANY two-symbol word to its end marker** — pinned |
| `scWordS_inj` / **`tailInSC`** | **`PathEncoding RS.TailB RS.SC` — the first positive hosting certificate for rung 3** — pinned |

Every theorem in the Stage 102–107 stack is AXIOM-FREE: shredder, dispatch, words, re-launcher,
recycling arm, duplicator, traversal, and the PathEncoding itself — pure constructions.

What this settles and what it does not. Settled: `{S,C}` hosts a machine with unboundedly many
states and arbitrarily long runs — the taxonomy's rung-3 row gains its first POSITIVE entry, and
the "can a non-erasing, selector-free, I-free calculus run anything?" question is answered yes,
constructively. Not settled: the tail machine is trivial (deterministic, terminating, no
branching consequence), and the equal-arms trick that closed regeneration also ERASES the
per-symbol distinction at the arm level — both arms do the same thing, so the traversal reads the
word's structure but does not yet ACT on it differentially. A tag simulation needs arms that
differ (append different productions) while still regenerating — the queue must preserve TWO
distinct arm identities under duplication of only the parked one. That refinement — or its
impossibility — is the next question, and it is the precise residue of SK ≤ `{S,C}`.

The seed observation deserves its own line: the w-cycle (Stage 99) and the duplicator differ by
one application. Cycles and computation in `{S,C}` run on the same engine — self-application of
`S (C C)` — which is the concrete form of the intuition, standing since the ladder opened, that
cyclicity and hosting power travel together.

### Stage 108: differentiation moves into the word

The differentiated-queue probe, resolved by relocation. Negative results first, both worth their
census lines: the CATALYST route — an arm `X` with `X o r ⟶* r o X`, which is exactly
leaf-balanced for any parked arm and would preserve both identities by pure swapping — has no
witness up to 9 machine leaves; and every arm-level scheme built from the two proved primitives
(parked-copying, payload-burning) provably homogenizes the arm pair in a few steps. Arm-level
differentiation is a quine problem, and `{S,C}` keeps refusing quines.

The resolution costs nothing: per-symbol differences belong at ENCODING TIME, in the cells. And
the gadget already existed — `scRelaunch`, in its THIRD reading (Stage 103: rotator; Stage 106:
recycling arm; now): a production-carrying cell.

| | |
|---|---|
| `scPCell p rest := scRelaunch p rest` | a cell holding its symbol's production and the rest of the word |
| `scPCell_step` | `scPCell p rest ⋅ D ⟶* D p rest` — one-slot interrogation delivers both |
| **`scPCell_step_acc`** | the same fires under an accumulator: **the three-argument driver protocol `D p rest acc`** — production, remaining word, write-slot — from pure cell machinery, with the accumulator riding the passenger position — pinned |
| `scPCell_normal` | cells are storable data |

All axiom-free. The tag-machine architecture this fixes: words are chains of production cells;
interrogation is single-slot (`W D`); the accumulator (the produced future word) rides the
protocol's third position; and the driver's per-symbol work is UNIFORM — read `p`, cons it to
`acc`, re-interrogate `rest`. The two remaining obligations, both driver-internal: (a) runtime
CONS of a production onto the accumulator (assembly-with-passenger, where the passenger position
is again available to absorb); (b) driver regeneration — and the scDup transposition applies:
the driver duplicates an ARRIVING spare carried in the accumulator pair, never itself. Neither
has an identified obstruction; both are the same genre as the five compositions that closed
Stages 104–107.

### Stage 109: runtime cons — the accumulator is writable

The driver's first obligation, closed. The bare-assembly problem (every fire result glues a
passenger) had made runtime data construction look blocked since Stage 102; the resolution is a
four-fire chain where each passenger lands exactly where the next fire needs it:

| | |
|---|---|
| `scConsA := C (C C) C` | the cons engine |
| `scCons q := C scConsA q` | the gadget for payload `q` — storable (`scCons_normal`) |
| **`scCons_beta`** | **`scCons q ⋅ acc ⟶* (C q) acc` — bare, four C-fires, zero residue** — pinned |
| `scQCell_step` | the produced cell's interrogation: `(C q acc) ⋅ D ⟶ (q D) acc` |
| `scNormal_C1`/`C2` | reusable normality helpers |

The fire-by-fire anatomy, because it is the arc's thesis in miniature: fire one nests `acc` under
the engine with `q` riding as passenger; fires two and three thread the engine's own two `C`s
into head and trailing position; fire four assembles the cell with `q` as the final
passenger-turned-payload. Four passengers, four jobs, nothing wasted — the same
waste-is-input principle that produced the recycling arm and the accumulator slot.

Design consequences: the accumulator built by front-consing is itself a consumable word — its
cells `(C q) acc` have a one-fire interrogation — stored in REVERSED order, which is the
two-stack queue representation: when the front word exhausts, a reversal pass (another traversal,
same machinery) turns the accumulator into the next front. The remaining obligation for a
one-tag-step theorem is driver REGENERATION only: the orchestration (route `p` to a cons, route
`rest` to a re-interrogation) plus the scDup transposition (the driver duplicates a spare
arriving in the accumulator pair, never itself). The hosting thread's obligations have gone from
five (Stage 104) to one.

### Stage 110: the mid-spine insertion obstruction

The driver-assembly probe found the wall instead of the gadget — and mapping a wall precisely is
the arc's second-best outcome. The pile protocol crystallized first, and it is a genuine
simplification: state = `word ⋅ A ⋅ A ⋅ W₁ ⋯ Wₖ ⋅ acc`, with each step's production-wrapper
piling just behind the arms, and the queue ORDER works out — the pile accumulates LIFO and the
flip-phase fold is LIFO, and LIFO ∘ LIFO = FIFO. Everything about the tag driver then reduces to
ONE gadget: a cell delivering `[β₁, β₂, rest, W]`, i.e. its stored wrapper landing BEHIND the
later-arriving runtime arguments. That gadget is census-dead:

- fused 4-slot cell: none to 9 leaves (general search), none to 12 (C-only);
- the alternate order `[β₁, β₂, W, rest]`: none to 11;
- the 3-argument arm `A o W r ⟶* r o o W`: none to 8.

And the architectural alternatives each hit a named wall: applying wrappers to the accumulator
needs ELEMENT-CREATION (fire results make prefixes, not elements — only passengers are intact
elements, and passengers must pre-exist); onion encodings need OUTWARD GROWTH (a subterm cannot
wrap its own context); garnished arms DUPLICATE the garnish. The pattern behind all of it:
**every proved gadget edits the spine only at its front, and the passenger mechanism steps
material backward by exactly one fire-relative position** — so machine-literals stored early
cannot land arbitrarily deep behind runtime arguments that arrive later.

**CONJECTURE (mid-spine insertion).** No `{S,C}` cell machine can deliver `[β₁, β₂, rest, W]`
from a two-argument interrogation — more generally, spine positions strictly between the active
prefix and the riding tail are unreachable for stored literals. STAKES: if TRUE, the pile
protocol dies, and with it (given the other walls) plausibly every queue-growing architecture —
`{S,C}` hosting would cap near tail-machine strength, making "K is for unbounded queues" the
sharpest separation of the program and a major negative half of SK ≤ `{S,C}`. If FALSE, the
witnessing gadget (12–20 leaves, beyond blind search — hand composition required) completes the
tag driver outright. Either resolution is a headline.

Proved this stage (`scRun_tail`, `scWrap_beta`, axiom-free): the pile state SHAPE is viable —
tails ride the whole traversal untouched — and the one-fire acc-wrapper exists. The machinery is
staged on both sides of the wall; only the wall is undecided.

### Stage 111: the two regimes — the searches were sound for the model, unsound for the question

The insertion-invariant attempt produced the right analysis and the wrong-way-around conclusion,
in the best possible order: the analysis first. The member dynamics of an interrogation are
exactly three facts: fires edit the machine-headed prefix; a fire's passenger steps backward past
its `z` (the ONLY reordering primitive); and — the anchor, now formalized — when an atom reaches
the head, THE SPINE FREEZES (`scv_varHead2_step`, axiom-free, pinned): no root fire applies to a
variable-headed term, so its member sequence is permanent and only component-internal reduction
continues. Together with atoms-never-nest, this PROVES the searched statement in the model the
searches used: with `rest` and `W` opaque, nothing is ever behind the last atom until the final
fire, whose single passenger is the only literal that can land there. Stage 110's triple negative
is structural — the opaque bound is a fact, not a search horizon.

But the model was wrong for the question. The REAL `rest` is the next cell and the REAL `W` is a
wrapper — both C-HEADED COMPOUNDS. A compound in head position does not freeze; it fires. The
whole freeze-driven bound evaporates for structured components, and with it the impossibility
reading of Stage 110: a real cell may use its stored components' own firing structure as
machinery — the cell and its contents can CONSPIRE. Mid-spine insertion splits:

- **Opaque insertion: CLOSED, negative, explained** — at most one opaque literal behind the last
  atom, the final passenger.
- **Structured insertion: REOPENED** — the target `[β₁, β₂, rest, W]` with `rest`, `W` compound
  is not covered by any search run so far (they modeled both as atoms), and the weave the member
  dynamics permit (literals hiding inside compounds, unpacking at head position after riding
  backward) is exactly what the opaque model forbids.

The corrected frontier for SK ≤ `{S,C}`'s constructive half: hand-construct the structured cell —
the search space is wrong-shaped for brute force, but the member-dynamics calculus developed
here is the right tool for composition — or show the structured regime inherits the opaque
bound. The stakes are unchanged (a working cell completes the tag driver; a bound caps hosting),
but the odds moved toward construction: the freeze was the only obstruction mechanism found, and
real cells are exempt from it.

### Stage 112: the one-tag-step — the wall had a door, and the door was trivial

The structured cell, hand-built in one sitting with Stage 111's member calculus — and it is
SEVEN LEAVES plus contents, two fires, simpler than anything the searches were looking for:

| | |
|---|---|
| `scTCell W rest := C (C rest scDup) W` | the production cell — normal over normal contents |
| **`scTCell_step`** | **`scTCell W rest ⋅ A₁ ⋅ A₂ ⟶(2) rest ⋅ A₁ ⋅ scDup ⋅ W ⋅ A₂`** — pinned |
| `scDup_normal` / `scTCell_normal` | storability |
| **`scTWord_step`** | **THE ONE-TAG-STEP**: with `scDup` arms, interrogation READS the head cell, APPENDS its wrapper to the pile, ADVANCES with the arm pair regenerated — pinned |

All axiom-free. The trick is exactly what the opaque model forbids and the real system provides:
THE ARMS ARE CONSTANTS. The cell does not route the arriving arms around anything — it stores a
fresh literal `scDup` and hands the next cell `(arriving-arm, fresh-arm)`, dropping its wrapper
and the spare arriving arm into the pile. Nothing crosses, nothing freezes; the pile pattern per
step is `[W, scDup]` — fixed, so `enc` remains a function of the source state.

The three-stage arc in one line: Stage 110 proved the searches could not find the gadget;
Stage 111 proved WHY (the opaque bound is real) and that the reason does not apply to real
cells; Stage 112 built the gadget in the real regime. The mid-spine insertion question is now
fully resolved: impossible for opaque literals, two fires for structured cells.

What remains for a full tag Simulation into `{S,C}`: the FOLD phase — when the front word
exhausts, the end marker must consume the pile `[W₁, scDup, W₂, scDup, …]` and produce the next
front word. The pile is a known alternating pattern, the wrappers are one-fire appliers, and the
end marker is an encoding-time machine: this is a traversal design of the same kind as
everything since Stage 105, with named gadgets for every piece. After that: the tag Simulation
assembles, and the question "does `{S,C}` host genuine tag systems?" — the constructive half of
SK ≤ `{S,C}` — is within reach of ordinary stage work.

### Stage 113: multi-wrapper cells, and the fold's wall named

Two deliverables: the easy extension, and the honest scoping of what is not easy.

The extension (`scTCell2`, `scTCell2_step`, axiom-free, pinned): multi-symbol productions are
LAYERING — each extra C-layer in a traversal cell drops one more wrapper into the pile, one fire
per layer, arms sustained throughout. `scTCell2` covers two-symbol productions (the largest tagAB
needs); the pattern iterates to any arity. Group-internal pile order is an encoding-time choice.

The scoping, with two new structural facts:

1. **The spine's last member is permanent.** Fires insert `spine(x), z, y` strictly before the
   trailing tail; nothing, ever, lands behind the final member. Consequence: the pile is LIFO by
   necessity — and by the Stage 110 design, LIFO fold of LIFO pile gives FIFO, so the order is
   right. (This also retroactively sharpens111's member calculus: three moves, one terminator,
   one permanence.)
2. **The fold's wall**: the fold must maintain the accumulated next-front-word across steps, and
   the accumulator must be a protected ELEMENT (safe from prefix fires) — but every assembly
   gadget produces live PREFIXES: `scCons q acc` yields `(C q) acc` as a prefix which, the moment
   the fold's trailing material arrives behind it, is a C-redex again and fires wrongly. Element
   status comes only from passenger-hood, and passengers must pre-exist — the same
   element-creation circle as Stage 108, now precisely located at the fold.

Candidate route, recorded: make the cascade harmless instead of preventing it — production
payloads valued in TAGS (`C`, `C C`), so the "wrong" continued fires stay machine-headed and can
be choreographed as part of the fold protocol itself (the cascade becomes the fold). This is a
genuine design problem of the Stage 104–112 genre, not one-sitting assembly; it goes to the
ranking as its own thread. The hosting construction stands at: run phase DONE (one-tag-step, any
production arity), fold phase SCOPED with named wall and candidate route.

### Stage 114: the program review — the hosting thread, accounted

A documentation stage, overdue by its own rule (five goal-level results since Stage 97, the
review deferred four times for hot construction work — the deferrals were correct individually
and wrong cumulatively; the rule now reads "review within three stages of a goal-level result").
The refreshed accounting:

- **Scale**: 32 modules, ~843 theorems, ~439 build-enforced `#guard`s plus 62 pinned axiom
  footprints, ~17,100 lines. Growth since Stage 97 is the classification (99–101) and the
  hosting thread (98–113). RungTermination.lean is now ~3,700 lines and holds three distinct
  research arcs; splitting it is deferred until the fold thread settles (moving stable theorems
  mid-thread invites churn).
- **STATUS restructured**: the rung-3 ladder row had accreted to six kilobytes of hosting
  material; it is slimmed to the cyclicity verdict plus classification, and THE HOSTING THREAD
  is now its own section — a capability table (twelve rows, every entry axiom-free), the
  model-bound-edge-construct method note, the member calculus (three moves, one terminator, one
  permanence), and the fold's named wall.
- **The axiom-free observation, made explicit**: the entire hosting stack — every gadget,
  every step theorem, and the PathEncoding `tailInSC` itself — depends on NO axioms at all.
  The cycle-space theorems needed `[propext, Quot.sound]` (they argue by contradiction over
  Prop); the hosting theorems are constructions, and constructions are proofs Lean checks by
  computation. The program's positive results are literally programs.
- **Goals**: 1–3 unchanged (DONE/DONE/CLOSED). Goal 4's leak catalogue stands at nine across
  ten doors; no new leaks since Stage 101 — fourteen consecutive clean stages, the longest run,
  attributable to the construction-heavy diet (constructions cannot leak).
- **The ladder's afterlife**: closed at Stage 96, the ladder now reads as the SETUP for the
  hosting thread — the cycle witnesses supplied the seeds (`scDup` is the w-cycle's engine),
  the shape lemmas closed the case analyses, and the impossibility machinery became the search
  and construction toolkit. The spec's "each rung a publishable partial result" undersold it:
  the rungs composed.

What remains live: the fold thread (the last engineering before a tag `Simulation` into
`{S,C}`), the arrival-order pairing conjecture, C6 (declined 101 times), and the headline
sentence — unchanged, resting on a larger instrument: **if S alone is universal, its encoding
must be non-injective or must fail to preserve reduction paths.**

### Stage 115: one-way data flow — the fold's true shape, and a correction

The fold-cascade sitting returned structure instead of a gadget, and the structure is decisive.

**The correction first, because the program's ledger exists for exactly this.** Stage 111's
prose invariant — "atoms never nest into compound elements" — is FALSE as stated: an S-fire with
an atom in g-position creates the member `(g x)`, a compound with the atom at its head. The hole
is witnessed in-file (a two-line constructor application). The searches were sound (they explored
those fires); only the prose over-claimed. The refined invariant: atoms occur bare in argument
position OR at member heads. Re-derivation of the downstream results: head-position atoms freeze
the spine on flattening (`scv_varHead2_step`, machine-checked, untouched), and the
one-literal-behind bound survives — the only new escape shape is `[β₁, u, β₂, W]` freezes with
`u ≠ β₂` (constructing `app β₁ β₂` would need an atom-duplicating S-fire, forbidden), which does
not reach the 4-member target. Both Stage 111 conclusions stand; the invariant that proved them
needed a third clause.

**The deepening: elements are genetically closed.** Every argument-position subterm of every
reduct descends from an argument-position subterm of the initial term. The mechanism is visible
in the fire shape itself: `[C, x, y, z | T] → spine(x) ++ [z, y] ++ T` — element contents
FLATTEN onto the spine (elements → spine), and nothing ever assembles spine material back into
an element (the assembled `(x z)` pairings are function-position prefixes, permanently). Data
flows one way. CONSEQUENCE: the fold cannot build a nested next word from pile members — not
"we lack the gadget" but "the direction of data flow forbids it." The nested-word architecture
(Stages 105–113's front word) is a GENERATION-ONE structure: it exists because `enc` built it at
encoding time, and nothing at runtime can ever rebuild its like.

**The surviving architecture: boustrophedon.** The pile itself must BE the next word, consumed
from its front — which reads generation n+1 in reverse of its production order. Alternating-
direction reading is forced. The open question this reduces hosting to: are
ALTERNATING-DIRECTION TAG SYSTEMS (read left-to-right, then right-to-left, flipping per
generation) universal? They are two-stack-flavored (the machinery IS a stack plus a read
direction), which smells universal, and the simulation overhead is a per-generation phase bit —
encodable in the cells. This is now a QUESTION ABOUT TAG SYSTEMS, not about `{S,C}`: the host
machinery for boustrophedon consumption exists (flat cells, Stage 112's constants trick). If
boustrophedon tag is universal, `{S,C}` hosting of a universal machine is within the toolkit;
if it degenerates, the one-way flow theorem becomes the negative half of SK ≤ `{S,C}`.

### Stage 116: the stack, not the shuttle — and decidability as the frontier

The boustrophedon probe falsified its own premise in the first hour, which is the probe working
as intended. Tracing the actual induced dynamics of the flat machine: a consumed cell pushes its
production wrappers at the spine front, and the NEXT consumption is also at the front — push and
pop interleave, so there are no generations to alternate. The machine is a STACK: pop `σ`, push
`reverse(P(σ))` — monogenic PREFIX REWRITING over a finite wrapper alphabet. Generational
separation (true boustrophedon) would need a barrier the pile cannot have: pushes land at the
fire-front, the fire-front is the only access point, and the last member is permanent. Stage
115's "surviving route" was mis-shaped within a day of being named — the census-caveat culture
(bounded, modeled, and now MIS-INDUCED) earns its fourth qualifier.

The reframe this forces is bigger than the correction. A stack process with finite alphabet and
finite control is pushdown-flavored, and pushdown reachability is decidable — so the honest
question is no longer "which tag variant can `{S,C}` host?" but **"is `{S,C}`-reachability
decidable?"** The formal core shipped today (Defs.lean, axiom-free, `steps_iff` pinned):

| | |
|---|---|
| `Simulation.steps_iff` | reachability between encoded states is EQUIVALENT to source reachability — `fwd_steps` one way, `bwd` the other; the five-field certificate finally uses `bwd` for something structural |
| `Simulation.transferDecidable` | a decision procedure for the host's reachability decides the source's |

Consequence: a `Simulation` of SK into ANY reachability-decidable host would decide
SK-reachability (undecidable — external, cited not checked, as the repository has always scoped
such facts). So `{S,C}`-DECIDABILITY, if provable, closes the negative half of SK ≤ `{S,C}` at
the Simulation class — the certificate class the program's positive results live in. The
evidence toward decidability: the one-way-flow law (elements never reassemble), the
member-calculus's three moves, the pushdown shape of every interrogation architecture found.
The evidence against: S-duplication clones compound members wholesale, and cloning is not a
pushdown move — the honest frame for `{S,C}`-reduction is the process-rewrite-systems hierarchy
(between pushdown and Petri-flavored classes), where decidability boundaries are delicate and
the question is genuine research. Either answer is a program headline: decidable ⇒ SK has no
Simulation into `{S,C}` and "K buys undecidability"; undecidable ⇒ the proof itself will exhibit
the computational power the hosting thread was hunting.

### Stage 117: exact conservation — the fragment square closes

The decidability probe's first slice, and the cleanest fragment theorem of the program: **every
C-fire loses exactly one leaf** — its own fired `C`, nothing else — so the C-fragment obeys
exact conservation, and everything follows by arithmetic:

| | |
|---|---|
| `SCStepC` / `RS.SCC` | the C-fragment: `{S,C}` without S-fires; includes into the full system |
| **`scStepsC_conservation`** | **a fragment path of length `n` loses exactly `n` leaves** — pinned |
| `scStepsC_length_lt` | the fragment terminates: paths shorter than the starting leaf count |
| **`SCC_acyclic`** | **the fragment is acyclic: every full-system cycle fires an S** — pinned |
| `scStep_leafCount_dichotomy` | every step loses exactly one leaf or is non-decreasing; the non-decreasing steps are exactly the S-fires |

This closes the FRAGMENT SQUARE: the S-only fragment was acyclic (cycles need C — Stage 27-era),
and now the C-only fragment is acyclic (cycles need S). Neither combinator alone loops; the
loop, like everything else unbounded in `{S,C}`, is a JOINT effect — S supplies material
(duplication), C supplies arrangement (permutation), and the witness cycles spend them in exact
balance (the h-cycle: one S-fire's +2 against two C-fires' −2).

The location statement for the decidability question: C-fragment reachable sets are finite
(strictly decreasing leaf count, finite branching), so fragment reachability is decidable in
principle — the enumerator is Stage 49–58-genre engineering, unbuilt. Everything beyond finite —
cycles, unbounded traversal, the hosting machinery — lives in S-duplication. Full-`{S,C}`
decidability is therefore exactly the question of ACCOUNTING S-FIRES: whether the material
S-fires inject is structured enough (the member calculus says duplicated material enters as
intact elements with genetically-closed contents) that reachability stays decidable, or whether
duplication-of-compounds crosses into undecidable process-rewriting territory. That question is
now stated with all its supporting laws machine-checked; it is the program's live frontier, and
both answers remain headlines.

### Stage 118: the two-sided speed limit

The S-accounting probe, honestly narrowed and exactly quantified. Narrowed: the member-sequence
abstraction (finite alphabet + copy) collapses — S-fires build new members from old, so the
alphabet compounds into full terms; and non-erasing TRSs are Turing-complete in general, so
non-erasure alone decides nothing. What `{S,C}`'s specific rules give, exactly:

| | |
|---|---|
| **`scSteps_shrink_le`** | **the shrink limit: a length-`n` path loses at most `n` leaves** — no step loses more than its own fired `C` — pinned |
| `scStep_growth` | no step more than doubles the leaf count |
| **`scSteps_growth_le`** | **a length-`n` path grows by at most `2ⁿ`** — pinned |

With Stage 117's conservation, every `{S,C}` path is now metered on both sides. The shrink limit
is the anti-erasure law quantified, and it is the sharpest single contrast with SK the program
owns: K erases mountains in one step; `{S,C}` pays retail, one leaf per step, always. Whatever
undecidability `{S,C}` might have cannot come from hiding computation in erased intermediates —
any large intermediate must be paid down visibly, step by step, in the path length.

The decidability landscape after three probe stages: the C-fragment is finite-reachable
(conservation); the full system is two-sided-metered (this stage); the named missing
infrastructure is SC-CONFLUENCE (the SK proof is the template — parallel reduction, orthogonal
rules) and the BOUNDED-INTERMEDIATE question (does `t ⟶* u` ever require intermediates
essentially larger than `t` and `u`? — the metering makes largeness expensive but not
impossible). Confluence plus a bounded-intermediate theorem would yield a decision procedure;
a counterexample to bounded intermediates would be the first sign of real computational depth.

### Stage 119: Church–Rosser for `{S,C}`

The SK proof, transported arm for arm (Takahashi: parallel reduction → complete development →
triangle → diamond → strip). `SC_confluence` and `sc_nf_unique` land at `[propext]`, exactly
SK's footprint. The structural difference the transport exposed: both `{S,C}` rules are 3-ary
and non-erasing, so the C-development keeps all three pieces developing where K discarded one,
the two-argument head shapes are plain, and the triangle's app-case has two SYMMETRIC redex
sub-cases instead of SK's asymmetric pair — the proof is more uniform than its template. Also
banked: `scSteps_appR` and `scSteps_congApp`, the missing congruences. For the decidability
program: normal forms are now unique, so bounded search is meaningful, and any standardization
or normalization argument has its prerequisite.

### Stage 120: the normal forms of `{S,C}`

`SCNF_iff` (pinned): a `{S,C}` term is normal exactly when every spine carries at most two
arguments — the rung-3 analogue of `SNF_iff`, proved by the standard two-direction argument
(shape blocks every fire; steplessness forces the shape, with the three-argument case exhibiting
its own redex). With `sc_nf_unique`, "the" normal form is a well-defined, recognizable object.
Retroactive dividend: every hosting gadget — tags, cells, arms, words — is spine-width-≤-2 by
construction, which is WHY the storability lemmas kept being easy.

### Stage 121: bounded reachability is decidable

The SK bounded-region template (Stages 49–58), transported: `scSucc` (the verified one-step
successor function, sound and complete against `SCStep`), `RS.stepsN_last` (the generic
last-step peel, completing the StepsN inversion kit), and `scReachFrom_iff` (pinned) — the
n-step closure computes exactly the ≤-n cone, making bounded reachability `Decidable`. The
decidability program now has all its tools staged: conservation and speed limits (117–118),
confluence and unique normal forms (119), the normal-form shape (120), and the decision
procedure for any bounded region (121). Everything reduces to ONE question: are intermediates
on a `t ⟶* u` path boundable in `t` and `u`? A bound plus the shrink limit bounds path length,
and `scReachWithin` decides reachability outright; a counterexample family is the first genuine
computational-depth witness. This is the cleanest the frontier has ever been stated.

### Stage 122: S-count conservation, and the pairing deadlock

Formal: `scStepC_countS` (C-fires preserve the S-count exactly — they kill only their own `C`)
and `scStepsC_invariant` (the C-fragment's two-component law: S-count constant, leaf count −1
per step). Paper, upgrading Stage 103's conjecture to a proof-sketch at theorem confidence: the
ARRIVAL-ORDER PAIRING DEADLOCK. Relative member order changes only by backward crossings
(the member calculus's one reorder move); a crossing of `Y` behind `s` has configuration
`[C, machine, Y, s]` — positions one through three fully occupied by the leaf `C`, a var-free
machine member (vars in argument position are bare; var-headed members freeze wrong on
unpacking), and `Y` itself — so the OTHER variable must already sit behind `s`. Neither
variable's crossing can be first: `s` never reaches the head, and `P a b s ⟶* s a b` has no
witness at any machine size. The census bound (Stage 103, ≤ 9 leaves) is thereby explained
structurally, like every census bound this program has eventually caught up with. Formalizing
the deadlock = formalizing member positions; named as the thread's next formalization target.

### Stage 123: the member-position calculus, machine-checked

`SCMembers.lean`: every term is its spine head applied to its member list (`SCV.recon`), and —
the load-bearing theorem — `scvStep_members` (`[propext]`, pinned): every step is an S-fire on
the first three members, a C-fire on the first three members, or one member stepping in place.
Nothing else can happen. The prose theory that carried fifteen stages is now infrastructure; the
crossing lemma, the bare-vars invariant, and the pairing deadlock are formalization targets
sitting one theorem deep on this one. First-try green, whole module — the sign of a theory whose
statements were forced by use before they were written down.

### Stage 124: variable counts are monotone

The pruning law every search has used since Stage 103, machine-checked: `scvStep_countVar` (the
exact per-step law: preserved, or an S-fire adds its third argument's count),
`scvSteps_countVar_mono` (pinned), and the squeeze (endpoint-equal counts force per-step
preservation — the crossing lemma's hypothesis, derived not assumed). The stage also caught its
own gap pre-prose: the S-fire CAN move a last-position variable by duplicating it, so the
crossing configuration is forced only on count-preserving paths — the corrected lemma order is
counts first, crossing second.

### Stage 125: the crossing configuration, formalized

The deadlock's engine is a theorem: `scv_cross_last` (pinned) — on a count-preserving step with
count one, moving any member behind a last-position variable forces the source into exactly
three members with head `C`, and the result's head is the old first member's head. Nine branches
through the member-action characterization; the S-fire-duplicates-the-variable branch dies on
direct counting, every second-occurrence branch on `two_vars_dead` (the count bridge), the
internal branches on vars-don't-step and results-are-apps. The supporting kit (`appList` laws,
count-sum algebra, the bridge) is the member calculus's standard library. Remaining for the full
pairing impossibility: the path-level induction iterating this lemma to the `s`-headed target —
prose at Stage 122 confidence, now with its hard step machine-checked.

### Stage 126: the last-variable invariant

The deadlock's path glue is a theorem: `scv_lastVar_step` (pinned) — on a count-preserving step
with count one, a last-position variable either stays last or the source was the three-member
C-fire configuration — and `scv_lastVar_steps` (pinned), its lift along `RS.SCV.Steps`: the
variable rides the tail until the one configuration that can consume it, returned with its full
sandwich (the path to the configuration, the step out of it, the path onward) for the
continuation analysis. The step lemma is `scv_cross_last`'s sibling with the branch polarity
inverted — the nonempty-tail branches are now the good cases, and only the S-fire-duplicates
count kill carries over. The path lift threads `scvSteps_countVar_squeeze` at every step. What
remains for the pairing impossibility: the continuation analysis — the consumed variable's
successor is headed by the old first member, and the other two count-one variables have no legal
home in a three-member C-spine.

### Stage 127: the funnel

The deadlock's skeleton is assembled: `scv_pair_funnel` (pinned) — every pairing path
`P a b s ⟶* s a b` (machine `P` free of the three variables) threads the needle: it reaches the
var-2 crossing configuration `C x y s`, fires it to `(x s) y`, continues to the CANONICAL
PREDECESSOR `C s b a`, and fires that into the target. The configuration arrives counted out:
`x` is machine-headed (`scv_varHead_frozen`, pinned `[propext]` — a variable at the spine head
stays there forever, so a var-headed `x` could never reach the C-headed predecessor), neither
`x` nor `y` contains `s`, and the two payload variables are split one-each across `x` and `y`.
The predecessor is unique (`scv_pair_pred`, pinned): S-fires and member-internal steps would
place an application among the target's all-variable members, so the only step into `s a b` is
the root C-fire from `C s b a`. What remains for `scv_no_pair`: the continuation analysis — the
segment `(x s) y ⟶* C s b a` must move BOTH payload variables behind `s` while `s` itself
returns to third-from-last position, and the positional invariant (bare vars, head exception)
says the member traffic cannot do it. That is Stage 128's brick.

### Stage 128: the dead ends

The closure's supporting kit: `SCV.Stuck` (a variable heads the term or heads a compound
member) with STUCKNESS IS FOREVER (`scv_stuck_step`/`scv_stuck_steps`, pinned `[propext]`) — a
committed member never fires internally, never sheds arguments, and every root fire promotes,
carries, appends to, or steps it in place. Since `C s b a` has head `C` and three bare-variable
members, nothing stuck and nothing var-headed ever reaches it (`scv_stuck_no_pairPre`,
`scv_varHead_no_pairPre`). Plus the exact root-S-fire count law with arbitrary tail
(`scv_sfire_count`) — the duplication kill. The consequence (Stage 129's floor): on a
count-preserving pairing path, every term is frozen, stuck, or has ALL THREE variables riding
as bare top-level members — and the first two never reach the predecessor. Verified
computationally before formalization: 191,115 reachable states, all machines to 7 leaves, zero
violations of the trichotomy, and the ordering invariant (a, b ahead of s) held on every live
state.

### Stage 129: ARRIVAL-ORDER PAIRING IS IMPOSSIBLE IN `{S,C}` — the deadlock, closed

`scv_no_pair` (pinned): no machine `P`, however large, reduces `P a b s ⟶* s a b` on opaque
arguments. Conjectured at Stage 103 from a census bound (≤ 9 leaves); now a theorem at every
size. The proof is ONE INVARIANT: `Ahead` — both payload variables sit ahead of `s` in the
member list. It is inductive on count-preserving steps up to commitments (`scv_ahead_step`):
the only fire that could break it is a root C-fire with `s` third, but `Ahead` puts both
payloads in the two slots ahead, so one occupies first position and is PROMOTED — stuck
forever (Stage 128), never reaching the target's unique predecessor `C s b a` (Stage 127).
S-fires cannot move `s` (first promotes, second nests, third duplicates — `scv_sfire_count`);
member-internal steps leave the split intact (variables do not step). At `P a b s` the
invariant holds; at `C s b a` both payloads sit BEHIND `s`; every pairing path ends through
`C s b a`. Contradiction. Notably: the count-1 hypotheses proved unnecessary — count
PRESERVATION alone kills duplication, and var-injectivity kills the two-payloads-one-slot
configurations. Stage 122's circular-crossing argument ("each crossing demands the other
first") is subsumed: the formal invariant needed no circularity analysis at all, because the
crossing configuration self-destructs by promotion. The assembly built first-try green.

### Stage 130: program review (the Stage 114 rule, triggered by Stage 129)

Numbers: 36 modules, ~916 theorems, 371 `#guard`s + 83 pinned footprints, ~19,100 lines, zero
warnings, axiom budget `[propext, Quot.sound]` or less throughout, hosting stack still
axiom-free. The autonomous run (119–129) held the conventions: every stage a feat+docs commit
pair, every headline pinned, two self-corrections caught in-run (SCNF_iff pin, scvStep_members
pin), verify-before-formalize used twice (191k-state trichotomy check; the census refresh).
Goals 1–2 remain DONE; Goal 3 (pure-S decidability) remains closed positive; the `{S,C}`
decidability frontier — bounded intermediates — is the standing open question inherited by the
next arc. Thread re-ranking coming out of the review: (1) the IMPOSSIBILITY FAMILY — the
`Ahead`/`Stuck` machinery is order-agnostic between payloads and should retire the other
arrival orders and arity variants in one consolidation stage, completing the interrogation
wall as a theorem cluster; (2) bounded intermediates; (3) the fold/Simulation architecture
question stays parked (genetic closure); C6 stays declined. Meta-observation for Goal 4: five
eleven-branch case analyses now ride one characterization theorem (`scvStep_members`), each
landing in ≤ 2 build iterations — the calculus's proofs have become PLUMBING, which is the
strongest evidence the abstraction is right.

### Stage 131: the impossibility family — the wall's exact edge

The interrogation wall is now a CLUSTER with a witnessed boundary. Impossible (pinned): both
s-headed arrival orders — `scv_no_pair` (`s a b`, Stage 129) and `scv_no_pair_swapped`
(`s b a`) — via the generic predecessor lemma `scv_sel_pred` (the only step into `s x y` on
variable arguments is the root C-fire from `C s y x`, ANY indices; subsumes Stage 127's
concrete version). Possible (pinned, AXIOM-FREE, a two-constructor term): payload-headed
rearrangement — `scv_swap_reachable`: the machine `C C` reduces `C C a b s` to `(b s) a` in
two fires. So `{S,C}` machines can reorder and apply opaque arguments freely — as long as a
PAYLOAD ends up at the head. The wall is exactly about `s` reaching the head: what a selector
needs and what `{S,C}` cannot do. The census explanation is complete: Stage 103's bounded
searches failed at every size for a structural reason now stated as three theorems, one of
them positive.

### Stage 132: the mountain — bounded intermediates has a floor

The `{S,C}` decidability frontier is now stated precisely and has its first hard datum.
`RS.StepsLe` (generic): paths whose every term stays within a size bound, with the kit
(`head_le`, `toSteps`, `weaken`, first-step inversion) and `RS.Steps.exists_le` (pinned,
`[propext]`): every path is bounded by SOMETHING — the frontier question is exactly whether
that something is a function of the endpoint sizes. The datum, machine-checked: THE MINIMAL
MOUNTAIN. `S (C S) S (S S) ⟶* S (S (S S)) (S S)`, six leaves each (`scMt_steps`, axiom-free),
yet the source's only step climbs to seven (`scMt_forced`, via the verified successor) — so
`sc_no_max_bound` (pinned): the identity bound fails, every path exceeds both endpoints.
Behind it, the probe (minimax-bottleneck Dijkstra, all starts to 8 leaves): forced excess 1 at
six leaves, 3 at seven, 23 at eight — a 31-leaf pass is REQUIRED to reach some targets as
small as three leaves. Any frontier bound `f` needs `f(8,8) ≥ 31`; the blow-up-then-collapse
is the phenomenon, and its growth rate is the question — if `f` exists and is computable,
reachability is decidable (`scReachWithin` + the speed limits); if mountains grow beyond every
computable bound, `{S,C}` reachability is undecidable and the Simulation-class negative half
closes at rung 3.

### Stage 133: the pigeonhole and the capped engine

Toward the frontier backbone (`computable bound ⟹ decidability`): `List.nodup_length_le`
(constructive pigeonhole, pinned) and `scReachCapped` (the capped reachability engine —
duplicate-free saturation of `scSucc` under a leaf-count cap) with SOUNDNESS and COMPLETENESS
(`scReachCapped_sound`, `scReachCapped_complete_start`, pinned): the engine's cone is exactly
the capped-reachable set, fuel-indexed. TENTH `Classical.choice` leak, a first of its kind:
core's `List.erase` lemmas (`length_erase_of_mem`, `mem_erase_of_ne`) carry choice — every
prior leak was tactic-generated; this one ships with the library. Hand-rolled `listRemove`
with its two lemmas keeps the budget. Deep probe data (behind the stage's ranking): the 8-leaf
champion's bottleneck-optimal crossing is 71 steps with a 31-leaf peak and multiple re-ascents
— the profile of a computation, not a detour. Remaining for the backbone: term enumeration by
leaf count, saturation via the pigeonhole, and the assembly `sc_decidable_of_bound`.

### Stage 134: the backbone — a computable bound implies decidability

`sc_decidable_of_bound` (pinned): for ANY function `f` of the endpoint leaf counts that bounds
witnessing paths' intermediates (`RS.StepsLe`), `{S,C}` reachability is decidable — by
enumeration of the capped universe (`scEnum`/`scEnumLe`, Census-style budget recursion,
completeness proved), pigeonhole saturation of the capped engine (a stable round exists within
fuel `|scEnumLe c|`, constructively — no choice, no minimum extracted), and list membership.
Unconditionally: CAPPED reachability is decidable (`scStepsLe_decidable`, pinned). The Goal-3
frontier at rung 3 is now a single sharp alternative: either some computable `f` bounds the
mountains (then reachability is decidable and the negative Simulation half closes), or the
mountains outgrow every computable bound (then `{S,C}` reachability is undecidable — and the
hosting thread's machinery is the natural instrument for proving it). Stage 132's data pins
the floor: `f(6,6) ≥ 7`, `f(8,8) ≥ 31`.

### Stage 135: the glider — deterministic unbounded growth at eight leaves

`sc_glider` (pinned): `S (S S S) S (C (S S))` reaches terms of EVERY size. The engine is the
three-fire self-similar loop `scCore_pump` (axiom-free): with `p = S (C (S S))`, the core
`p p p` fires S-C-S back into `S p (p p p)` — itself, one wrapper deeper; sizes run `12 + 5k`.
NON-CYCLIC DIVERGENCE: all previously known `{S,C}` divergence was cyclic (h-/w-cycles, size
constant); the glider grows forever and never returns. Probe findings: the forced-march depth
(unique successor at every step) explodes with size — 0, 1, 2, 4, 12, 60+ at sizes 3–8 — and
the glider's march was traced 1500 steps without a single branch: `{S,C}` at eight leaves runs
deterministic, non-terminating, linearly-growing computation. Frontier consequences: reachable
sets of small terms are INFINITE (the capped engine is a necessity, not an optimization), and
the glider is the simplest specimen of the phenomenon the mountains, the speed limits, and the
hosting gadgets all orbit — sustained work between small endpoints.

### Stage 136: glider determinism — no normal form

The trace is a theorem: the glider's trajectory is EXACTLY five shapes (`GliderTraj` — the
seed, one intermediate, and the three phases under any number of wrappers), each with a
singleton successor list, parametrically in the wrapper count (`scSucc_wrap`: wrappers are
inert; `scSucc_wrapN`: singletons survive wrapping; the phase transitions are `rfl`). Hence
`scGlider_deterministic` (pinned) and `scGlider_no_normal_form` (pinned) — the first
machine-checked normal-form-free term in `{S,C}`. Cycles never certify normal-form-freeness
(a cyclic term may normalize down another path); determinism leaves no side exit. `{S,C}` at
eight leaves: deterministic, non-terminating, linearly growing, and now fully certified.

### Stage 137: fixpoint detection — unreachability by computation

`scReachCapped_detect`/`scReachCapped_excludes` (pinned): one stable saturation round — a
DECIDABLE check — certifies the capped engine's cone complete, so non-membership excludes
every capped path. `scMt_no_capped_path` re-certifies the minimal mountain purely by `decide`.
Machine-checked mountains are now one `decide` away wherever the capped space is
kernel-tractable. The control probe (with its instructive incident: the first version reported
TWO normal forms from one start — impossible under the proven `SC_confluence`, which exposed
the probe's bug before any conclusion shipped) confirms, exhaustively and with unique-NF
sanity asserted: 164 FUELED MOUNTAINS at machine size ≤ 6 over `C C`-towers — the star
`S (C (S C S)) S` takes fuel-`k` inputs of size `10 + 2k` through reachable peaks `34 + 28k`
and strongly normalizes to 5–7 leaves. Bounded, modeled caveats: peaks are BFS-maxima (not
yet minimax), fuel ≤ 4, one unit shape. The control question (make the pump HALT) has a
computational answer — fueled machines exist in abundance; what remains is whether fuel can be
made to encode arbitrary computation.

### Stage 138: the ledger audit

Registry swept against the run. Corrections: C1(a)'s registry header still said "probed
(open)" — it was PROVED at Stage 43 (`c1a`, pinned); stale for ninety-five stages because
stage entries are append-only and nobody re-read the header. C6 RETIRED after 124 consecutive
declines (scope decision, not resolution; rationale in its section). The registry now reads:
C1(a) proved, C1(b) proved, C2 proved, C3 retired (artifact), C4 proved, C5 proved, C6 retired
(scope). Named open questions swept: the pairing question (Stage 102) is ANSWERED — impossible
for both s-headed orders (Stages 129/131), possible payload-headed; the `{S,C}` decidability
frontier stands as the program's one open question with goal-level weight, now equipped with
its backbone (`sc_decidable_of_bound`), floor (mountains), and instruments (capped engine,
fixpoint certificates); the fold/control question stands as the identified missing piece on
both the hosting and undecidability sides, with fueled machines (Stage 137) as its newest
evidence. Rule added: REGISTRY HEADERS ARE PART OF EVERY REVIEW — a review that only reads
STATUS.md can miss a stale conjecture header, as this one did for ninety-five stages.

### Stage 139: the frontier, well-posed — decidable ⟺ bounded

`sc_decidable_iff_bound` (pinned): `{S,C}` reachability is decidable IF AND ONLY IF some
computable function of the endpoint sizes bounds the intermediates of witnessing paths. The
forward direction is Stage 134's backbone; the converse (`sc_bound_of_decidable`, pinned)
assembles a bounding function from any decision procedure — decide each same-size pair over
the verified enumerator, then search upward for an admitting cap (terminating by `exists_le`;
the searcher is a hand-rolled choice-free find, since core has no `Nat.find` — `Acc.rec`
eliminates into data without choice, and proof irrelevance makes the assembled cap independent
of the reachability proof). The program's one open goal-level question is now one equivalence.
Everything known presses on it from both sides: mountains force the bound above `max` and
probe-floor `f(8,8) ≥ 31`; the glider shows infinite reachable sets; the fueled machines show
controlled work; the hosting stack is raw material for a reduction. Either resolution closes
rung 3.

### Stage 140: the forced-march toolkit — the tall mountain

Mountains no longer need state-space saturation. A forced (unique-successor) prefix is shared
by EVERY path, so `scForced_mountain` (pinned) certifies unreachability-under-cap from a chain
check — and the chain itself is COMPUTED (`scForcedMarch`, provably forced generically by
`scForcedMarch_forced`: iterate the verified successor, no per-instance literals). Dually
`scChained_steps` (pinned) turns any computed reduction into a `Steps` theorem, cost linear in
the path. Instantiated: THE TALL MOUNTAIN — `S S C (S (C S S)) C` (8 leaves) marches forced
for 49 steps to a 44-leaf peak, then branches to a 32-leaf target seven checked steps later
(`scMt2_steps`, `scMt2_no_capped_path`, pinned). FLOOR THEOREMS (`sc_bound_floor_6`,
`sc_bound_floor_44`, pinned): every valid bounding function for the frontier equivalence obeys
`f(6,6) ≥ 7` and `f(8,32) ≥ 44` — the first pinned quantitative constraints on the
equivalence's `f`, and a template: any forced-prefix specimen the probes find is now one
`decide` from joining the floor.

### Stage 141: the march hierarchy — the glider never stalls

`scGlider_march_unbounded` (pinned, `[propext]`): the computed forced chain from the glider
seed has every length — the trajectory's singleton successors mean `scForcedMarch` never hits
a branch. The forced-march "busy beaver" at eight leaves is infinite, measured by Stage 140's
own instrument. NEGATIVE, recorded per caveat culture: one-parameter families around the
tall-mountain seed all break forcing (fuel towers in any argument slot collapse the forced
prefix to 0–7 steps; trailing `C`s ride the same march with constant excess) — unbounded-
excess mountain families remain UNFOUND, so the frontier floor stays pointwise
(`f(6,6) ≥ 7`, `f(8,32) ≥ 44`). The exhaustive n=9 minimax census continues in the
background; its harvest joins the floor when it lands.

### Stage 142: the generic engine — the equivalence at every rung

`RS.SuccKit.decidable_iff_bound` (pinned): for ANY rewriting system equipped with a size, a
verified successor function, and a complete bounded enumeration, reachability is decidable iff
a computable function of endpoint sizes bounds witnessing intermediates. The Stage 133/134/139
chain, made generic the moment its second consumer appeared (the no-premature-abstraction rule
held for nine stages and then paid out in one): SK has both ingredients already
(`succs`, `skSmallTerms`), so `sk_decidable_iff_bound` (pinned) states the RUNG-0 equivalence —
and since SK reachability is (externally) undecidable, SK has no computable intermediate
bound. The rung-0/rung-3 contrast is now exact: the SAME well-posed question, instruments
identical, expected answers opposite — which is the sharpest form of the program's thesis that
`{S,C}` sits at the boundary. Census harvest (n=9, exhaustive, 13,721 forced-prefix
mountains): the STEEP MOUNTAIN — nine leaves, thirteen forced steps to a 25-leaf peak, ten-leaf
target — certified as `sc_bound_floor_25` (pinned). The floor now reads `f(6,6) ≥ 7`,
`f(8,32) ≥ 44`, `f(9,10) ≥ 25`, and the n=9 data shows 200-step still-forced marches at eight
leaves beyond the glider — forced computation is generic at this scale, not exceptional.

### Stage 143: the ladder-wide equivalence

Rungs 1 and 2 equipped (`siKit`, `sbKit`: verified successors and budget enumerators, mirrored
from the `{S,C}` originals in one sitting), so the decidable⟺bounded equivalence holds AT
EVERY RUNG: `sk_decidable_iff_bound`, `si_decidable_iff_bound`, `sb_decidable_iff_bound`,
`sc_decidable_iff_bound` (all pinned). One well-posed question, four calibrated instances:
rung 0 externally undecidable (hence unboundable), rungs 1–3 open, rung 3 carrying the pinned
floors. The relaxation ladder — built to compare ACYCLICITY across rungs — now also compares
the reachability frontier across rungs with a single generic instrument. Lean note for the
catalogue: two-discriminant matches with MIXED-DEPTH patterns lose pattern variables in
compilation (`Unknown identifier` at the arm body); `split at` on the unfolded definition is
the robust alternative.

### Stage 144: cell synthesis — the fold's production step is one fire

The fold problem re-opened with fresh eyes and split in half. POSITIVE (pinned, axiom-free):
`sc_cell_synth`/`scv_cell_synth` — a traversal cell is all constant except its wrapper, so ONE
S-fire mints `scTCell w rest` from the constant prefab `scCellPrefab rest` for any arriving
`w`, even a variable the machine has never inspected; a continuation receives its own copy of
the wrapper, and the fire goes through under trailing material. Stage 112 built cells at
encoding time; the machine now builds them mid-run. Census agreement: synthesis machines exist
at six leaves (the probe's hit IS the formalized fire). NEGATIVE (bounded): with an OPAQUE
accumulator — the cycle-2 requirement, nesting a runtime-arrived `acc` under fresh C-wrappers —
no machine to nine leaves completes the build. The fold's difficulty is now LOCATED, not
diffuse: (a) runtime-accumulator nesting (needs the acc routed to an S-fire's third position
with the right prefab second — orchestration, count-legal since ground terms may duplicate),
and (b) driver self-regeneration across cycles (the QUINE PROBLEM: scDup solves it for
C-interrogation; the fold driver needs the S-analogue — plausible via duplication providing
the two copies that rebuild `S q q` by two nests, unproven). Modeling lesson re-learned
mid-stage, Stage 111's exactly: the first probe modeled the accumulator as opaque and missed
the six-leaf synthesizers; the honest interface (constant end marker) found them immediately.

### Stage 145: the mid-insertion obstruction — the fold's remaining half, named

The runtime-accumulator nest (cycle 2 of the fold: build `C (C acc MID) W` with `acc` a
previously synthesized cell) is CENSUS-DEAD across designed orchestrations: 8,200 start
states (heads × up to three prefabs from a nine-gadget pool × four trailing configurations,
depth 14, size slack 20) reach the target ZERO times — while the FIRST nest `(C acc)` forms
in one fire from the same envelope. The block is structural and now has a name: THE
MID-INSERTION OBSTRUCTION. After `(C acc)` forms, the second nest needs a FUNCTIONAL constant
(`scDup` or equivalent, to serve as the cell's arm-regenerator) at the fire's third position —
i.e., inserted BETWEEN `(C acc)` and the wrapper `W` — and the member calculus's complete
insertion inventory cannot put it there: prefab material spills at the FRONT (positions 1..k),
S-fire `(g x)` products land immediately behind their own bare `x` and nest simultaneously,
C-fires only swap 2↔3 or rebuild the spine head, and nothing ever enters mid-list otherwise.
CONJECTURE (new, C7): no `{S,C}` orchestration synthesizes a nested two-generation cell — the
fold's chain architecture ends at generation one, for every driver. Routes left open and
recorded: junk-tolerant cell redesign (shown non-uniform at one junk item per generation —
positional junk accumulates), and spine-level building (C-fires DO nest at the spine head;
whether the word can live as the spine rather than as a member is undesigned either way).
Escape hatch honestly noted: the pool/depth/interface envelope is finite, and Stage 144's own
lesson is that interface choices hide six-leaf answers.

### Stage 146: the queue cell — C7 REFUTED

C7 lived one day. The mid-insertion obstruction is real as a statement about MOVES — nothing
inserts mid-list — but the CONCLUSION (no two-generation cell) confused the map with the
territory: it assumed cells must have `scTCell`'s child order. The QUEUE CELL
`scQCell acc W = C (C scDup acc) W` puts every node's children in stream order with constants
only at heads, making all three runtime nests legal x-position S-fires (`sc_qcell_synth₁–₃`,
one fire each, axiom-free) — and seven fires (`scQCell_fire`, axiom-free, pinned) deliver the
one-tag-step protocol IDENTICALLY: rest promoted with two fresh arms, wrapper dropped behind
with a spare. `scQWord`/`scQWord_step`: the whole word layer, runtime-buildable. C7's census
missed it because the probe's target pattern hardcoded the old child order — the run's third
and sharpest probe-modeling lesson: a negative search certifies only its own pattern. The fold
ledger now: production ✓, accumulation ✓, protocol ✓; the full tag `Simulation` into `{S,C}`
— and with it the undecidability route for rung-3 reachability — hangs on ONE remaining
design problem: DRIVER SELF-REGENERATION (the quine). If the quine exists, `{S,C}` hosts full
tag systems and rung-3 reachability is undecidable, closing the frontier equivalence's other
side. C7 is retired-refuted; the quine is registered as C8.

### Stage 147: the arm-junk barrier — generation two, mapped and blocked

Two searches, one instructive failure. The first found 1,212 "generation-2" states — all
SPURIOUS: the target pattern (a promoted queue cell containing the wrapper) matches the
STARTING configuration, because generation 1's word is itself a queue cell; a reachability
target that the origin satisfies certifies nothing. The corrected search — from the genuine
post-traversal state `E scDup scDup W scDup`, wrapper harvested to the pile — is a ZERO across
2,286 designed end-markers (≤ 3 prefabs from a ten-gadget pool, depth 18). The block has a
shape: THE ARM-JUNK BARRIER. After traversal, the two spent interrogation arms sit between the
end-marker and the harvested wrapper; the synthesis fire needs its prefab at position two with
the wrapper at three; leaf-C drains bring the wrapper to reach but put a spent ARM in the
prefab slot, and non-erasure means arms are never destroyed, only relocated. The route
forward, mapped: CO-DESIGN of (cell constant, arm shape, end-marker) — the cell's embedded
constant need not be `scDup` and the arms need not be either; if the arm itself carries the
synthesis prefab, the barrier becomes the mechanism. That co-design space is C8's real arena.
Caveats: pool/depth-bounded, single-wrapper words, drop layout fixed by `scQCell_fire`.

### Stage 148: the biodegradable architecture — zero residue, FIFO

C8's co-design probe paid immediately. Eighteen of sixty-four (constant, arm) pairs traverse;
one dissolves Stage 147's barrier entirely: `scBCell acc W = C (C C acc) W` with arms `C C` —
every auxiliary leaf is pure C, so the C-fragment's exact conservation (Stage 117) burns ALL
machinery. The five-fire protocol (`scBCell_fire`, axiom-free, pinned): first arm consumed as
fuel, second passed inward, wrapper dropped behind, nothing else left. `scBWord_two`
(axiom-free, pinned): a two-cell word ends at literally `E W₂ W₁` — end marker promoted with
the harvested wrappers as its ONLY members, in FIFO ORDER, zero residue; the composition even
routes the harvested `W₂` through as the second cell's arm, so data is fuel-safe. Forty stages
of fighting non-erasure, and the resolution is to build the machine from the one combinator
that consumes itself. Re-erection from `E W₂ W₁` is live (`scDup W₂ W₁` reaches the running
cell `C (C C W₂) W₂ · W₁` in two fires — observed, not yet pinned) but mints a junk
accumulator; C8 now reads: from `E W₂ W₁`, erect `scBWord E' [W₂-productions]` with a WORKING
accumulator and a re-armed driver. The remaining gap is real but it is now measured in fires,
not in architecture.

### Stage 149: the fuel law

`scBWord_run` (axiom-free, pinned): `k` leading `C C` cells burn away entirely; the end marker
receives exactly the final two wrappers, in order. The n-cell generalization's price,
probe-measured before proving: wrappers 1..n−2 are consumed as ARMS two rounds after their
cell fires, so they must be arm-compatible (`C C` is; bare `C` is not — completion is exactly
the words with `C C` at all consumed positions), and their information is DESTROYED. A
two-letter fuel alphabet exists (`C (C (C C))` and `C (C C) C` are clean distinct fuels), so
encodings can survive the constraint; what no encoding survives is the information burn —
only the last two symbols arrive as data. C8's endgame is therefore sharpened once more:
either fuel must BEAR information (distinct fuels steering the traversal into distinct
continuations — undesigned), or reading must happen before burning (the dispatch-capable
`scWord` layer feeding the biodegradable fold — a composition question).

### Stage 150: fuel blindness

Information-bearing fuel is closed. Probe: the three clean fuels each reach exactly ONE end
state with ONE member signature — identical across fuels. Pinned (`scBCell_fireB'`,
`scBCell_fuel_blind`, axiom-free): the four-leaf fuel burns in seven fires to bitwise the same
delivered state as `C C`'s five — same arms in, same state out. The biodegradable furnace
erases whatever it eats, structurally. C8's route is now unique: READ-BEFORE-BURN — the
dispatch-capable word (Stage 107) fires the tag before anything burns, the acting arm mints
the production at read time (Stage 144, one fire), the minted pile chains post-hoc into a
queue word (Stage 146, three fires per cell), and the biodegradable layer is the CLEANUP
phase, not the read phase. Every piece is a pinned theorem; C8 is their composition.

### Stage 151: the generation loop — one tag generation is a cycle

`sc_generation_cycle` (axiom-free, pinned): the self-reproducing one-symbol tag `{b ↦ [b]}`
hosts as a genuine `{S,C}` cycle — the encoded configuration (Stage-107 word, `scDup` arms,
`scDup` END MARKER) returns to itself bit-identically in FIVE fires. One generation: read the
cell, regenerate the arms, re-erect the word, return. The END MARKER IS THE RETURN ADDRESS:
`tailInSC`'s marker `S` halts; marker `scDup` loops — the continuation is data. C8 is solved
for the trivial tag, and the solution re-reads the cycle-space thread: the h-/w-cycle zoo of
Stages 96–101 was never mere non-termination — (at least some of) `{S,C}`'s cycles ARE hosted
generation loops. What remains of C8 for NON-trivial tags: the loop must grow (productions
longer than the consumed prefix) or shrink (shorter) rather than return bit-identically — the
generation "cycle" becomes a generation SPIRAL, and the glider (Stage 135) is the existing
specimen of exactly that shape. The design question: a spiral whose per-loop growth carries
the tag rule's productions.

### Stage 152: the attractor — pop until empty, then pulse

`sc_words_decay` (axiom-free, pinned): every `scDup`-ended word configuration decays into the
generation loop — `scRun_step` pops symbols one at a time (the rest-word only rides), and the
empty configuration is three fires from the cycle (`sc_empty_to_loop`). A complete dynamical
description of the family: the Stage-151 cycle is its UNIQUE attractor. The naive multi-symbol
generation loop is dead — probe: the two-symbol configuration's entire 10-state closure
contains the one-symbol loop; it neither cycles at its own length nor halts. The reading for
C8: the pulse is what the marker's rebuild looks like when the harvest is empty; a non-trivial
generation loop needs the marker to rebuild FROM THE HARVESTED PILE instead — and the harvest,
by the fuel law, currently burns. The two constraints have met: C8 = design a marker whose
rebuild consumes the pile as construction material rather than fuel. Everything else about the
generation loop is now theorem.

### Stage 153: the harvest rebuilder — C8's exact address

POSITIVE (`sc_harvest_rebuild`, axiom-free, pinned): from the clean pile `E W₂ W₁`, the marker
`scDup` rebuilds a live biodegradable cell in TWO fires, generic in both wrappers — the
duplicated wrapper landing in the accumulator seat, which for tag words is self-dispatching
rather than junk (tags are C-material; the run's data/machine distinction dissolves for them).
288 designed markers rebuild; `scDup` is the smallest. NEGATIVE: the exact growth step
`config [b] ⟶* config [b,b]` has NO marker to 14 leaves (3,766 candidates) — there the marker
must appear verbatim in the target, i.e., survive its own firing, i.e., quine. C8's address
after six stages of triangulation: reading is solved, minting is solved, rebuilding is solved,
the pile is clean and FIFO — the entire remaining problem is the marker's SELF-PERSISTENCE
through the rebuild. One combinator-design question, stated in one line, with every
surrounding mechanism a pinned theorem.

### Stage 154: the growth step — the spiral's base case

`sc_growth_step` (axiom-free, pinned): with `scQuine = S (C (C C)) (C C)` — scDup's asymmetric
cousin — as marker AND arms, four fires take the one-cell configuration to the TWO-cell
configuration, marker and both arms restored verbatim. The word GREW and everything survived:
the first growth-with-full-survival witness, found only when marker and arms were co-designed
(256 pairs, one hit; all marker-only families were zero). The mechanism is the whole hosting
thread in four fires: pop (two C-fires promote the marker with two arm copies), mint (the
marker's S-fire duplicates one arm while nesting the other into the `C C` prefab), re-erect
(one C-fire). REMAINING: iteration — the two-cell configuration engages its outer cell first
and derails (14-state closure, no third cell). C8's mantle passes to the spiral's induction
step: a configuration family where growth commutes with traversal. The pattern of the whole
campaign — each wall falls to a co-design one notch wider than the last search — suggests the
next widening: co-design the CELL constant with the marker/arm pair (three-way).

### Stage 155: the cell-armed pop — the arm is the program

`sc_cellArm_pop` (axiom-free, pinned): `(CC X) (CC A) (CC B) ⟶⁶ (X A) B` — a `C C`-cell
interrogated by two `C C`-CELLS pops with the arms' contents becoming the next arms; shells
burn. THREE protocols now coexist on the one cell shape, selected purely by arm structure:
`scDup`-arms regenerate (Stage 107), flat `C C`-arms burn as fuel (Stage 148), cell-arms hand
contents forward (here). THE ARM IS THE PROGRAM. Corollaries: the scQuine sliding family's
complete law (`sc_spiral_pop`/`sc_spiral_descends`, pinned) — six fires per level down to the
base, then the probe's universal 14-cycle (closures arithmetic in k: 18/24/30/36). The
iteration diagnosis is now structural: GROWTH (Stage 154) runs on marker-arms; TRAVERSAL runs
on container- or fuel-arms; the spiral needs a configuration that alternates disciplines —
arms that traverse as containers and arrive at the marker as copies. That alternation is C8's
final form, and the content-forwarding protocol is the first mechanism that MOVES information
inward instead of burning it.

### Stage 156: the constructor gap — where the spiral actually stops

The scQuine family's dynamics are BOUNDED, measured cleanly from both directions: from
word-depth 2 the closure reaches depth 3 (the growth step firing), from depth 3 it never
exceeds 3 — the family caps at tower-3 and flows into the universal 14-cycle. The alternation
analysis explains why and names C8's true final form: container-arms STRIP one level per pop
(`sc_cellArm_pop`), the marker's growth adds one WORD cell but restores arms at the SAME
depth, so arm depth falls behind word length by one per generation — the books cannot
balance. A genuine spiral needs a marker that mints for the word AND deepens both arms in one
firing sequence while surviving — a self-reproducing CONSTRUCTOR in the von Neumann sense,
not merely a quine. THE CONSTRUCTOR GAP: everything below it is now pinned theorem (read,
mint, chain, pop in three protocols, clean piles, FIFO, growth-with-survival, complete family
laws for three architectures); everything above it is one design object whose existence is
the remaining content of C8 — and, through the frontier equivalence, plausibly of rung-3
undecidability itself. Probe caveats as always: pool- and depth-bounded searches; the run's
own history (C7, the arm-junk barrier, mid-insertion) says named walls fall to widenings.

### Stage 157: the fourteen-beat pulse

`sc_pulse14` (axiom-free, pinned): the Q-family's universal attractor is a genuine 14-cycle —
twelve C-fires and two S-fires (the arm-duplications that keep the beat alive) — and its
basepoint is the growth step's own output (`sc_growth_to_pulse`). The family trilogy is
complete: slide down by sixes, grow once by four, pulse by fourteens. Tooling milestone: the
fourteen-fire chain was EMITTED by a script that identifies each fire's spine position and
constructor arguments from traced states — the probe now writes the proof, and long concrete
reductions cost nothing to pin.

### Stage 158: the counter — the slow burner read

The aperiodic diverger `S (S S S) C (S C C)` (eight leaves) is a hosted UNARY COUNTER.
Anatomy at 12,000 forced steps (still deterministic throughout): exactly FIVE members at every
checkpoint (fixed registers), head always `C`, and the maximum C-tower height tracks `√step`
to within rounding (32/63/89/110 at steps 1k/4k/8k/12k against 31.6/63.2/89.4/109.5) — the
signature of increment-forever with per-loop cost linear in the count (Σ2h ≈ h² = steps). The
delta alphabet is −1 plus every jump 2..111: long C-grind descents (the scan) punctuated by
S-fire copies of the ever-taller tower (the increment). No delta period up to 400 — aperiodic
BECAUSE the counter never repeats. Two readings recorded: (1) the machine's data lives in
SPINE-LEVEL C-TOWERS with a fixed member skeleton — the architecture Stage 145 flagged as the
open route, already in use by an eight-leaf term; (2) counters are the raw material of Minsky-
machine undecidability constructions — this specimen increments only, but the existence of a
register discipline in `{S,C}` reframes the constructor gap: perhaps the tag/word architecture
is the wrong host idiom and the counter idiom is native. Bounded caveats: 12k steps, one seed.

### Stage 159: twin towers, one clock — the register question

The two-register hunt (n=8 exhaustive: 11 specimens; n=9 sweep continuing in background,
42 hits at time of writing): every specimen with two growing C-towers grows them in LOCKSTEP —
final heights within a few units, ratio ≈ 1 throughout. The counter idiom generalizes (twin
towers are generic in the family — the increment's duplication makes a working copy), but
INDEPENDENT registers — one growing while the other holds or shrinks, the Minsky primitive —
are absent from every specimen found. The register question is now sharp: is lockstep forced
(one clock drives everything reachable by these seeds), or do independent registers appear
at larger seeds or under designed contexts? A steering mechanism would need the machine's
head to consult one tower while preserving the other — dispatch-on-emptiness, which is the
counter idiom's version of the constructor gap. Both idioms (tag/word and counter/register)
now stand one control-primitive short of a Minsky/tag reduction, and it is recognizably the
SAME primitive: conditional behavior on runtime data that survives the test.

### Stage 160: review — and the registry grows two entries

Numbers refreshed (37 modules, ~1,055 theorems, 129 pins, 388 guards, ~21,600 lines, zero
warnings; 41 consecutive autonomous stages). Registry additions, per the Stage-138 rule that
headers are part of every review:

## C7: No two-generation cell synthesis — REFUTED (Stage 146, same-day)
Registered Stage 145 on the mid-insertion obstruction; refuted by the queue cell (child order
was a free parameter). Kept as the run's exhibit that impossibility arguments about MOVES must
quantify over DESIGNS.

## C8: The nondestructive-read problem — OPEN, the program's second frontier
Successively sharpened Stage 146→159: driver self-regeneration → marker persistence through
rebuild → constructor gap (arms strip, growth restores flat) → the kernel: READ WITHOUT
CONSUMING. Tag idiom: a marker that survives its own firing. Register idiom: an emptiness test
that spares its operand. Everything beneath it is pinned; a solution in either idiom yields a
hosted unbounded machine and, via the frontier equivalence, bears directly on rung-3
undecidability. The two open frontiers (bounded intermediates; nondestructive read) are
plausibly one: both ask whether `{S,C}` can consult data without destroying it.

### Stage 161: the one-bit machines — conditional behavior exists, at build time

Census (n=8 exhaustive, 66 pairs; n=9 sweep continuing): term pairs differing in a SINGLE
embedded `C ↔ C C` bit with qualitatively different forced-march signatures. The star: the
COUNTER `S (S S S) C (S C C)` (aperiodic, √step registers) versus `S (S S S) C (S (C C) C)`
(period 5, +15 per period — a linear glider): ONE BIT toggles counter ↔ glider. Others flip
period 13 ↔ 17, 7 ↔ 15, aperiodic ↔ 26-periodic-plateau. `{S,C}` reads embedded bits into
globally different behaviors — dispatch exists at whole-machine scale. The refinement this
buys C8: the bit here is consulted ONCE, at build time (different seeds run differently);
Minsky/tag control needs a bit consulted REPEATEDLY at runtime, surviving each consultation.
The nondestructive-read problem, final phrasing: a RE-CONSULTABLE bit — read many times,
intact after each, with divergent effects per reading. The one-bit census says the effect
side is easy; persistence of the read datum is the whole problem, exactly as non-erasure's
grain predicts.

### Stage 162: the lockstep law

The two-register hunt is complete and exhaustive at n ≤ 9: 149 specimens with two growing
C-towers, and EVERY one grows them in lockstep — final gaps ≤ 3 units over 2,400 steps,
height ratios never below 0.939. No independent registers exist at nine leaves. The census
law and its mechanism: `{S,C}`'s only copying move (the S-fire) creates both towers from the
same operand in the same fire — copies are born equal, and nothing thereafter can consult one
without consuming it (the nondestructive-read problem again, in its register costume).
Registered as the LOCKSTEP LAW (census-grade, envelope: n ≤ 9, 2,400-step marches, forced
seeds): {S,C}'s spontaneous machines have one clock. Independent registers, if they exist,
are DESIGNED objects above nine leaves — and their design problem is C8. Meanwhile the n=10
floor census is rescoped: its per-term cost (300-step marches over 2.4M terms) exceeded the
overnight budget; it continues detached, harvest deferred.

### Stage 163: the read gadget, designed — and a predicate that lied

PAPER RESULT (design, assembled entirely from pinned move types): the READ GADGET —
(1) STASH: an S-fire with the bit at third position leaves the bare bit as a member and nests
a copy into `(g b)`; (2) BUILD: three g-position nests raise a dispatcher `b P₁ P₂ x` with the
bit at its head; (3) DISPATCH: the tag fires, one C burns, different arms act per bit
(`scTagA/B_dispatch`); (4) RECOVER: promoting the stash spills its members and the bit pops
out bare, last. Read-many, intact-after-each, divergent-per-reading — every step an existing
pinned mechanism; what remains is the positional choreography (the f-slot sequencing that
every campaign meets). PROBE INCIDENT, recorded as the sixth predicate lesson: the gadget
search's divergence measure abstracted the bit ACROSS THE WHOLE TERM, so `b = C` mangled
every machinery `C` — 142/161 machines "diverged", including bit-ignorers; a null-case test
would have caught it before the run. Effect markers (distinct designed shapes produced per
branch) are the correct instrument; the demo needs design, not search. Census harvest logged:
986 conditional one-bit pairs at n=9 (66 at n=8).

### Stage 164: the register demo — the re-consultable bit exists

`sc_read_bitC`/`sc_read_bitB` (axiom-free, pinned): one template, `reg reg S (C C)` with
`reg = S bit`. Bit `C` → two fires → `S (C C) (S C S)`; bit `C C` → eight fires →
`C (S (C C)) (C C)`. The outcomes are normal and distinct (#guards via the verified
successor), differ in their register-free parts (null-case checked), and EACH STILL CONTAINS
ITS REGISTER, application-ready for the next consultation. The nondestructive read is REAL:
read, diverge, survive, at four leaves of machinery. What remains for Minsky/tag control is
now the COMPOSITION: consult in a loop (the demo consults once, at the run's start) and WRITE
(change the bit mid-run). The campaign's arc — stash-by-duplication design, two contaminated
predicates caught by null cases, the S-guarded register that made shapes collision-free —
took one day from 'the quine problem' to a pinned read-with-effect.

### Stage 165: the latch — the first pinned control primitive

`scLatch bit = S (C C) (C scDup) (S S bit) scDup` — sixteen fires, all pinned, axiom-free
(`scLatch_run_C`/`scLatch_run_B` + `scModeC_pulse`/`scModeB_pulse`): fire ONE stashes a
register copy inside `(C scDup) reg` (the Stage-163 stash, executing verbatim); fire TEN is
the CONSULTATION (the working copy fires, exposing the bit); the runs diverge into different
perpetual five-beat pulses, each carrying the stashed register as a standing subterm
(`scHasSub` guards; register shape machinery-disjoint by construction). STASH, CONSULT,
DIVERGE, SURVIVE — a set-once latch with a reusable source bit. The design was drawn on paper
at Stage 163 from pinned move-types; the search then found an eight-leaf machine already
running it; the trace was verified fire-by-fire against the design before pinning. C8's
remaining distance after the latch: the RESET (consult more than once — the stash must be
re-opened and re-stashed, the loop of Stage 163's recover step) and the WRITE. The campaign's
contamination ledger reached four: every predicate that touched C-material lied until shapes
were made disjoint; the discipline (null cases + shape disjointness + fire-by-fire reads)
is now as load-bearing as the theorems.

### Stage 166: the consultation loop — twelve reads, register alive

The reset dissolved on contact: `S C C (S S C) scDup` consults its register TWELVE times in
52 forced fires, register present throughout — kernel-certified (`#guard`s replay the march
with `scForcedMarch`, count consultation events with the structural detector `scIsConsult`
— a step rewriting `reg X ⟶ (S X)(bit X)` — and check survival at the end). The bit-`C C`
twin consults fourteen times in 132 leftmost steps (branching; probe-recorded).
`scForced_chained` (`[propext]`, pinned) links marches to `Steps`. C8's ledger: READ ✓
(register demo), LATCH ✓ (set-once mode), LOOPED READ ✓ (here). One primitive remains: the
WRITE — change which bit the surviving register carries, mid-run, by machine action. Pin-rule
violation logged and corrected same-commit: the audit output was on screen and the pin text
still guessed — the rule is READ the audit line, not run it.

### Stage 167: the write — the primitive set completes

`sc_reg_write` (axiom-free, pinned): registers are minted, not mutated — one S-fire with
prefab `S S` produces a fresh register around any bit-source. The nondestructive-read
problem's four primitives now all exist: READ (Stage 164, the register demo), LATCH (165,
set-once mode selection with reusable source), LOOPED READ (166, twelve consultations
kernel-certified), WRITE (here, one fire). C8 reduces to CHOREOGRAPHY: compose looped-read
with write into a Minsky decrement/test or a tag step. The composition is where every
campaign has paid its real costs (position alignment, junk routing, contamination
discipline) — but for the first time since C8 was registered at Stage 146, NO missing
mechanism stands between the program and a hosted unbounded machine. The remaining risk is
that composition itself hides a conservation-law obstruction; nothing found so far suggests
one, and the latch (which already composes stash + consult + diverge + survive across
sixteen fires) is evidence against.

### Stage 168: the decrement's two faces — and the composition's true name

The bare-interface decrement-write is census-dead (2,200 machines ≤ 12 leaves, zero): the
consultation chain exposes the decremented tower at HEAD position, the minting write needs it
at a MEMBER slot, and heads become members only by pre-duplication — the promotion asymmetry,
now blocking from the inside of the composition. The reframe that survives: `{S,C}` ALREADY
implements decrement-and-branch-on-zero, pinned since Stage 152 — as WORD-LENGTH counters:
pop is decrement (`scRun_step`), the end-marker's promotion is the zero-test (`sc_words_decay`
— the attractor entry IS the branch), and the growth step is increment. One register with
dec/test/inc: done. The composition's true name is therefore TWO INDEPENDENT REGISTERS UNDER
ONE DRIVER — and the lockstep law (Stage 162) is exactly the statement that this does not
happen spontaneously. The Minsky reduction runs through designing what no ≤9-leaf machine
exhibits: two clocks. All four control primitives are available as parts; the two-clock
problem is the composition campaign's opening question, and it deserves fresh eyes.

### Stage 169: the n=10 floor, partial harvest

The n=10 forced-excess census ran to ~90% coverage (4.5M of 4.98M terms) before dying without
its final report — the winners list printed only at completion, a tooling design error now
fixed (the relaunched sweep prints hits incrementally, crash-proof). What survived the
checkpoints: MAX FORCED EXCESS ≥ 44 AT n=10. The floor curve across sizes now reads 1 (n=6,
exhaustive), 3 (n=7, exhaustive), 23 (n=8, exhaustive), 15 (n=9, forced-prefix method), ≥44
(n=10, 90% coverage) — superlinear and accelerating, consistent with the doubling speed limit
and the counter/glider readings: forced computation deepens fast with seed size. The pinned
frontier floors (f(6,6) ≥ 7, f(9,10) ≥ 25, f(8,32) ≥ 44) will gain an n=10 point when the
relaunched sweep surfaces its witnesses. Methodology note for the census kit: LONG SWEEPS
PRINT INCREMENTALLY — a final-report-only design loses everything to a late death.

### Stage 170: review — the control campaign, closed as a primitive set

Fifty-two consecutive autonomous stages (119–170). Numbers: ~1,063 theorems, 137 pins, 398
guards, ~21,900 lines, zero warnings. The C8 campaign's final review: registered at Stage 146
as "driver self-regeneration", C8 was successively renamed by its own refutations — marker
persistence (147), constructor gap (156), nondestructive read (160), re-consultable bit (161)
— and then DISCHARGED AS A PRIMITIVE SET in four stages: READ (`sc_read_bitC/B`), LATCH
(`scLatch_run_C/B` + mode pulses), LOOPED READ (twelve consultations, kernel-certified),
WRITE (`sc_reg_write`). What remains of C8 is composition: two independent registers under
one driver, for which the two-clock architecture note (member-configs are independent clocks
under reachability semantics; coupling = the read gadget on member end-states) is the banked
opening. The frontier equivalence stands at all four rungs with a floor curve now reading
1/3/23/15/≥44 across seed sizes 6–10. Discipline ledger for the campaign: six predicate
lessons, four contamination catches, one pin-rule violation caught in-commit, one census
lost to final-report-only output — every one converted to a standing rule. The program's
open questions remain two, and they are the same two as at Stage 160 — bounded intermediates
and the composition — but both now have complete toolkits and named architectures.

### Stage 171: two clocks, by design

`sc_two_clocks` / `sc_independent_registers` (axiom-free, pinned): member-held configurations
reduce independently under a pair-holder — one word-register pops while the other holds, and
the mirror image. The lockstep law binds deterministic single-spine marches; reachability
quantifies over all schedules, so the architecture escapes it outright. The composition now
has its chassis: two registers with dec/test/inc (word length, Stage 152/154 machinery), four
control primitives (Stages 164–167), and independent clocks (here). ONE piece remains between
the program and a hosted two-register machine: THE COUPLING — the driver consulting member
end-states and branching, which is the read gadget aimed at a member instead of a bit. That
single design object now carries the entire weight of: full tag/Minsky hosting, rung-3
undecidability via the frontier equivalence, and with it the resolution of the program's
last goal-level question.

### Stage 172: the coupled zero-test — the branch exists

`sc_ztest_zero`/`sc_ztest_nonzero` (axiom-free, pinned): registers as INERT WORDS
(`scWord S w` — normal forms, stable data), the zero-test read off the word's own head shape.
One template (`scWReg w = S C w`, doubled, with `C C` and `S` as markers): the empty-word
register normalizes in eight fires, the one-cell register in eleven, to distinct normal forms
each carrying its intact register (#guarded: normality, presence). The driver consults a
register's VALUE CLASS nondestructively — the Minsky branch on zero. The composition ledger:
registers with dec (`scRun_step`), test (here), inc (growth step); four control primitives;
independent clocks (`sc_two_clocks`); and now the branch. What remains is ASSEMBLY — a single
machine cycling test→dec→branch on live registers — engineering on top of a complete parts
list, no unknown mechanism anywhere in it.

### Stage 173: test-and-decrement — the Minsky half-step

`sc_testdec` (axiom-free, pinned): from the nonzero word-register (marker `S S`,
machinery-disjoint and `#guard`-verified absent from the machine), sixteen fires reach a
state carrying the DECREMENTED, RE-GUARDED register — the marker's only possible provenance
being the pop itself. Three genuine machines out of 48 naive hits; the provenance null did
the sorting. The decrement completes member-internally (six appR-context fires — the first
pinned path with a mixed-context tail), leaving the new register member-resident where the
write primitive operates. The Minsky HALF-STEP is a theorem. The assembly's remainder:
CYCLE it (half-step output re-entering as input) and the zero-branch exit (Stage 172's
test). Both are choreography over today's pinned pieces; the composition has no unknowns
left, only fire-sequencing.

### Stage 174: the decrement cycles

`sc_testdec_twice` (axiom-free, pinned, with both legs): one machine, two pops — the two-cell
register descends through the `#guard`ed intermediate to the doubly-decremented register,
twenty-six fires, marker provenance intact throughout. The Minsky decrement CYCLES. Tooling:
the theorem was assembled programmatically from the trace (emit → splice → build); concrete
reductions of any length are now one script from pinned. The assembly ledger — half-step,
cycle, zero-branch, independent registers, increment — has ONE seam left: the zero-exit wired
into the cycle. The composition campaign is measured in seams now, not mechanisms.

### Stage 175: the counter-reader — and the final boss, alone at last

The cycle machine on registers 0, 1, 2 reaches UNIQUE normal forms (confluence-consistent,
closures complete) of 26, 28, 29 leaves — three values, three distinguishable halts: a
`{S,C}` function computing on unary register values, with the two-register's NF still
carrying the doubly-decremented register. But the same completeness is the finding's other
edge: the machine always HALTS — it is a bounded counter-reader, not a loop. Every register-
carrying state en route is transient except in the deepest input. The composition campaign
has now converted every mechanism — read, latch, looped read, write, zero-test, decrement,
decrement-cycling, value-dependent halts, independent clocks — and what remains is exactly
ONE thing, the thing the fold campaign met as the quine, the growth campaign met as the
constructor, and the assembly meets as loop persistence: A MACHINE THAT OUTLIVES ITS OWN
STEP. Fifty-six stages of triangulation say this is not one wall among many but THE wall —
`{S,C}`'s single remaining question, standing between bounded hosting (everything above,
theorem) and unbounded hosting (tag/Minsky, undecidability, the frontier's negative side).
Registered as C8-final: THE PERSISTENCE PROBLEM.

### Stage 176: the persistent reader — persistence solved for read-only state

`scReader_period`/`scReader_step`/`scReader_unbounded` (axiom-free, pinned): the front
`S P (C P) (C r)` reproduces itself VERBATIM every seven fires, emitting one accounted junk
block, with the register `r = S S C` consulting twice per period (`#guard`ed: forced march,
consultation count, register presence). The junk rides as trailing members, so the period
lifts to every generation by congruence — the machine outlives its own step, unboundedly,
while interacting with its state. The persistence problem's ledger: a machine can persist
while READING; the remaining question is persistence while WRITING — the reader's recurrence
is verbatim (`Front ↦ Front·J`), and a written state means the recurrence must carry a
CHANGED register while everything else survives. The reader was not designed: it is the
Stage-166 consultation loop's own tail, revealed by periodicity analysis — the calculus keeps
having already built what the program sets out to construct.

### Stage 177: writing recurrences, first pass — decay is not a write

The state-advancing-spiral detector (strip trailing junk, demand exactly one changed subterm
across a period) found 25 recurrences in 162 seeds — and inspection shows every one is
DEGENERATIVE: the changed slot is machinery burning down (`scDup → C`, wrappers stripping),
not a register advancing. The write-shaped filter (both sides register-patterned, value
successor-related) finds none in this envelope. The design analysis sharpens what a writing
reader needs: the persistent reader's consultation fire (`S_red S C X`) already produces
`(S X)` — HALF a fresh register — as a byproduct each period; a writing front must route an
`S S`-prefab (the write primitive's constant, Stage 167) to meet the new bit inside the
period, so the recurrence carries `Front X ↦ Front X' · J` with `X'` minted, not inherited.
The parts touch: the period has the byproducts, the write is one fire, the routing is the
remaining choreography — the same positional dance, one level up. Envelope caveats: 162
seeds, one register family, marches to 60.

### Stage 178: the parametric pulse — and the write's final form

`sc_pulse_parametric` (axiom-free, pinned): the mode pulse cycles in five fires with ANY
cargo — persistence is parametric. The persistence ladder now reads: pulse (state-free) →
parametric pulse (arbitrary inert cargo) → latch (cargo + one read) → reader (cargo +
unbounded reads) → writer (open). And the writer's obstruction has its final form, read off
the reader's fire anatomy: the recurrence is GENERATED by the register's own fires (the
consultation `r X → (S X)(C X)` literally mints the next front's head and second member — the
state is the engine, distributed across its own copies), and machines write FORWARD-ONLY
(products land behind; the front never reads backward; junk re-enters only by burning down).
The writing reader is a GROW/BURN ALTERNATOR — Stage 116's boustrophedon, which the program
set aside as an obstacle description, returns as the design: grow-phase emits computed junk
(the reader), burn-phase re-reads it (the biodegradable machinery), the carry rides
parametric persistence. Every phase-mechanism is pinned; the alternator is the composition.

### Stage 179: the junk is storage — the writer was writing all along

Pure-C-junk persistent fronts are probe-dead (324 seeds, zero) for a structural reason:
duplication-driven persistence copies its own S-engine into every junk block — the junk
inherits the engine, necessarily. But re-reading the reader's junk under that light inverts
the ledger: `J = C P (C r)` is C-HEADED with C-headed spills, and its payload is a REGISTER
COMPLEX — when a burn phase eventually promotes a junk block, its members spill and the
stored register re-exposes. THE JUNK STREAM IS A STACK OF STORED REGISTERS: the persistent
reader has been WRITING all along — one register copy appended to storage per period; what it
lacks is the RETURN (the front never shrinks, so storage is never revisited). The alternator's
missing piece is therefore a TRIGGER: a fueled reader — a front that runs k periods and then
exhausts, burning down into its own storage (Stage 137's fueled machines meet Stage 176's
reader). The writer's specification has moved for the last time: not mint-and-route, not
grow/burn in the abstract, but READER + FUEL — both pinned phenomena, one splice.

### Stage 180: the parking orbit — persistence without growth

C8's persistence problem is now solved TWICE, at both extremes. The reader (Stage 176)
keeps state alive by growing forever; the parking orbit keeps it alive at CONSTANT SIZE:
`scOrb = C A A A A` (A = scDup, 21 leaves) is a forced period-5 limit cycle — every term
has exactly one successor (`scOrb_forced`, kernel-checked), so the orbit is inescapable —
and the cycle turns entirely in the head, so ANY cargo appended on the right rides it
verbatim forever (`sc_park`, `sc_park_forever`: axiom-free, parametric). Better: the orbit
is REACHED BY A READ. The 9-leaf head `scParkSeed bit` consults its `S S bit` register
exactly once (kernel-counted: `SCChained` traces + `scCountConsults` guards) and parks it
in sixteen fires — bit `C` at phase 0, bit `C C` at phase 4 (`scPark_entry_C/CC`). Equal
wall-clock, different phase: THE BIT IS STORED IN THE PHASE of an eternal bounded orbit.
Probe lesson #8 (ledger): the probe reported "bit-dependent cycles"; the cycles are
rotation-equal after register abstraction — cyclic signatures must be compared up to
rotation. What survived the correction is stronger than what the probe claimed.

### Stage 181: the n=10 mountain — the census pays out

The background census (all 4,978,688 ten-leaf terms, forced-prefix marches to depth 300,
crash-proofed and incrementally printed per lesson #5) surfaced its best witness and the
toolkit pinned it the same day: `scMt4T = S (S S) C (S (C S (C C)) C)` (10 leaves) has a
FULLY FORCED 300-step prefix that climbs to 186 leaves at step 257 and hands off to a
142-leaf off-prefix target one checked step later. `scForced_mountain` closes the argument:
no path t→u stays within 185 (`scMt4_no_capped_path`), so every valid intermediate-bound
function clears 186 at (10,142) — `sc_bound_floor_186`, the program's tallest pinned
mountain. The floor ladder now reads f(6,6) ≥ 7, f(8,32) ≥ 44, f(9,10) ≥ 25,
f(10,142) ≥ 186: excess 12 → 44 in two leaves. Bounded intermediates — the frontier
equivalence's live half — keeps looking worse: if the excess keeps tripling per two
leaves, no computable bound survives, and {S,C} reachability is undecidable by
`sc_decidable_iff_bound`. (Technical first: the 300-step kernel march needed
`maxRecDepth 8000`, scoped in a section — the toolkit's first collision with an
elaborator default, resolved without weakening anything.)

### Stage 182: the fate machine — the bit decides eternity

The bounded reader exists, and it settled a bigger question on arrival. `scFate bit`
(12 leaves) holds an `S S bit` register over a duplicator. With bit `C`: seven fires onto
a period-7 cycle, sizes 15–20, that CONSULTS its register once per lap forever — the
consultation consumes a register copy and the duplicating fire re-mints it, closing the
regeneration loop that separated the parking orbit (never reads) from the persistent
reader (never stops growing). `scFate_runs` pins runs of EVERY length. With bit `C C`:
the SAME machine reduces in 36 fires to a kernel-checked normal form. `sc_fate` holds
both halves in one statement: one term, one register — spin or stop. The register is no
longer a passive payload OR a mere branch selector: its content decides whether the
machine's future is finite. Probe data (recorded, not pinned): the bit-`C C` reachable
state space is FINITE — 231 states under every schedule — with the NF its unique sink,
so the halt is schedule-independent, not just leftmost. C8's composition ladder now has
READ → LATCH → WRITE → PERSIST (two ways) → FATE.

### Stage 183: universal fate — every schedule halts, and 36 is the wall

Stage 182's halt half said "a normal form is reachable"; Stage 183 says "nothing else can
happen." New toolkit piece: the RANKED CLOSURE certificate. Emit the complete reachable
state space (231 terms, ≤ 29 leaves), grouped by height so every successor of every member
sits in a strictly lower group; `decide` checks the whole certificate in-kernel; the new
generic lemma `scRanked_bound` (five lines of recursor) converts it into a uniform bound —
no reduction from the seed outlives its rank. The seed's rank is 36 and the leftmost path
REACHES 36, so the wall is sharp: `sc_fate_all_bounded` (no schedule exceeds 36 fires),
`sc_fate_unique_exit` (every stuck reachable term IS `scFateNf`), `sc_fate_universal`
(the conjunction). The fate machine's contrast is now total: bit `C` — runs of every
length; bit `C C` — every maximal reduction, every schedule, dies at one normal form
inside 36 fires. This is the program's first pinned termination-of-all-paths result, and
the certificate is generic: any finite acyclic reachable space can now be pinned the same
way, which turns the capped engine's saturation data into termination theorems on demand.

### Stage 184: the four fates — the fate bit becomes a component

The composition campaign's payoff pattern, now at the level of TERMINATION. The pair
chassis `S c₁ c₂` is inert — `S` with two arguments is no redex — so pair dynamics
decompose completely and MODULARLY: every step is a member step (`scPair_inv`), every
reduction splits member-wise (`scPair_decompose`), walls ADD (`scPair_bounded`:
k₁-bounded beside k₂-bounded is (k₁+k₂)-bounded), and normal members make a normal pair.
Instantiated at the fate machine: (C,·) — one spinning member keeps the pair immortal
whatever sits beside it; (CC,CC) — the pair dies at `S scFateNf scFateNf` behind a SHARP
wall of 72 = 36 + 36 with unique exit. `sc_four_fates` pins the quadrants. The
significance is the method: Stage 183's certificate was checked over 231 emitted states;
the pair's certificate needed NO product space — 53,361 virtual states handled by four
little lemmas. Termination composes. Next question the ladder points at: make one
machine's OUTPUT the other's REGISTER — conditional eternity, the hosting primitive.

### Stage 185: bits are sources — and the relay that houses a fate

Conditional eternity — one machine's output feeding another's fate register — is
IMPOSSIBLE in `{S,C}`, and the impossibility is now an axiom-free theorem. Both fire
rules produce double applications, so no reduction ever ends at an atom or at `C C`:
`sc_bits_are_sources` (the only term reducing to `C C` is `C C` itself). Register
contents are sources of the reduction order — inputs forever, outputs never. Fate, in
this calculus, is decided strictly by initial conditions; there is no gadget that
computes a bit. (This closes the "hosting via computed registers" route; hosting must
route BEHAVIOR, not register values — consistent with every working machine since the
latch reading shape, not value.) The constructive half: `S S C M` fires once into the
housed pair `S M (C M)` — machine and shadow — and the four-fates calculus composes over
it: immortal in 8 fires with a spinning payload (`sc_relay_fates`), and with a halting
payload every schedule dies at machine-and-shadow normal form behind a 73-fire wall
(`sc_relay_wall`) — pinned while the probe's 53,592-state product space stays untouched.

### Stage 186: the chassis isolates — a theorem, not a suspicion

The behavior-routing question from Stage 185's ledger, answered in the negative before
lunch: `sc_pair_reachable_iff` — reachability from `S c₁ c₂` is EXACTLY the product of
member reachabilities, an iff. The chassis isolates perfectly: no schedule, however
adversarial, lets one member's state change what the other can do. `sc_shadow_drifts`
instantiates it at the housed pair: machine and shadow decouple at birth, every
combination of independent progress reachable, no synchronization ever. Two readings:
the isolation is WHY termination certificates compose over the chassis (walls add
because nothing crosses), and it is why the chassis can never host communication. The
routing question is now sharply posed for the only remaining channel: members that share
structure through FIRES — the duplicator's copies, the cell-synthesis line, arm-as-
program. Communication in `{S,C}`, if it exists, is metabolic, not architectural.

### Stage 187: the n=12 mountain — excess 57, the ladder steepens

The graft heuristic — two leaves added around the n=10 winner — outperformed millions of
random samples in 146 tries: `C S S (S S) C (S (C S (C C)) C)` runs a fully forced
400-step prefix to a 291-leaf peak and hands off to a 234-leaf target. `sc_bound_floor_291`
joins the ladder: f(6,6) ≥ 7, f(8,32) ≥ 44, f(9,10) ≥ 25, f(10,142) ≥ 186,
f(12,234) ≥ 291. The peak-to-endpoint excess — the quantity a bounding function must
absorb — reads 12, 44, 57 at n = 8, 10, 12, and the peak-to-SOURCE ratio has gone from
5.5× to 18.6× to 24× the starting size. Verification cost stayed linear (march-400,
maxRecDepth 16000, seconds of kernel time): the toolkit's price scales with the PATH
while the phenomenon's size scales with the state space — the whole reason the
forced-march technology exists. Random phase still sweeping; a taller n=12 mountain, if
one surfaces, is one emit away.

### Stage 188: metabolic assembly — the handoff exists

The isolation theorem said interaction lives in fires or nowhere; seven fires deliver it.
`scAssembly B` — three dead `C C` cells: minter head, minter arm, cargo arm — burns down
by the cell-armed pop (six fires, Stage 156's law reused verbatim), and the freed `S S`
minter executes on the freed cargo (one fire): the product is `S B (S S B)`, the inert
chassis housing the cargo NEXT TO its own freshly minted register. Delivery → execution →
housing; producer cell feeds consumer cell; axiom-free and parametric in the cargo. At
`B = C` the assembled term is a bit sitting beside the register that would spin the fate
machine on it. The composition vocabulary is now: pop delivers, S S mints, the chassis
holds, walls add, fires are the only channel — and each clause is a pinned theorem.

### Stage 189: the fate machine assembles itself — dead cells to universal fate

`scFate b` turned out to be verbatim a pop product — head cell `S (S scDup)`, arm cell
`S S b`, cargo cell `C C` — so `sc_fate_assembly` is a ONE-LINE instantiation of the
Stage 156 pop law: three dead cells, six burning fires, and the machine stands. The full
lifecycle is pinned as a pipeline: dead cells → assembly (6) → fate — spin side reaches
the eternal consulting orbit; halt side reaches `scFateNf`, with the ranked-closure
certificate (237 states, heights 0–42) making it UNIVERSAL: no schedule from the dead
cells exceeds 42 = 6 + 36 fires and every dead end is the one normal form
(`sc_fate_assembly_universal`). `sc_assembly_line` adds recursion to the vocabulary:
assemblies take assemblies as cargo, nested housing from nested shells. Note the shape
of the week: Stage 182 found the machine, 183 certified it, 184 composed it, 185 bounded
its relay, 186 proved the isolation, 188 opened the metabolic channel, 189 closed the
loop — the machine now BUILDS from the same dead matter it burns. The register's bit is
placed in a cell before the pop; bits-are-sources (185) says nothing else was ever
possible: construction chooses fate, computation never does.

### Stage 190: the frame trichotomy — one head, three registers, three futures

The fate frame is not a switch; it is a SPECTRUM SELECTOR. `scFrame r = S (S scDup) r (C C)`
(with `scFate b = scFrame (S S b)` by `rfl` — the campaigns join definitionally) sorts all
3,238 registers up to six leaves into 1,168 halting, 336 cycling, 1,661 growing; and
already at ≤ 3 leaves all three futures are selectable, each pinned in its own currency:
`C` — a FORCED 11-fire halt (the 12-state space is a single line; universal wall by
ranked certificate); `C S` — a period-8 orbit ridden forever inside nine terms
(`scFrame_runs` carries lap membership through every run length); `S S S` — unbounded
growth on a period-7 front with the exact size law `|scGrow n| = 15 + 5n`
(`sc_frame_grow_unbounded`). HALT, ORBIT, EXPLODE. One 8-leaf head realizes the full
behavioral taxonomy of the calculus, register-selected. For the hosting program this is
the instruction-set map the parity question needed: the frame's answer to an input is not
one bit but one of three FUTURES — and the interesting hosting question becomes whether
word-processing machinery can steer a register INTO a chosen class before the frame reads
it. Bits-are-sources says the register cannot be minted from thin air; the trichotomy
census says the classes are dense enough that steering may not need minting.

### Stage 191: unary parity, hosted — the first eight rungs

The steering probe (96 word-sensitive families over ≤2-leaf symbols, none binary-parity)
surfaced the unary law instead: in the fate frame, the numeral `C^k S` HALTS for even `k`
— 11 + 2k fires to a rung-specific normal form — and ORBITS FOREVER for odd `k`, period
7 + k. Verified through k = 10; pinned rung by rung for k = 0..7 (`sc_parity_hosted`).
This is the program's first HOSTED PREDICATE: an input property (parity of a unary
numeral) decided by reachability-observable behavior (eternity vs normal form). The
generic halves are now toolkit: `sc_cycle_forever`/`sc_cycle_unbounded` turn any pinned
cycle into an eternity certificate, axiom-free.

**C9 (the frame parity law).** For every k: `scFrame (C^k S)` reduces to a normal form
iff k is even; for odd k it admits runs of every length (period-(7+k) orbit). Status:
OPEN — pinned for k ≤ 7, probe-verified to k = 10; the orbits are rung-specific (traces
never merge), so a proof needs parametric trace templates (the fire skeleton is visibly
uniform: +2 halt fires and +1 period per rung — a template proof looks feasible), not
descent. The stakes: a proved C9 is an INFINITE hosted predicate family — reachability
in {S,C} deciding parity for all inputs — the first true hosting theorem of the program.

### Stage 192: C9 PROVED — the frame parity law, every k

Registered at Stage 191, closed at Stage 192. The template proof rests on three facts the
traces made visible: (1) THE PRELUDE IS UNIVERSAL — nine fires take `scFrame r` to the
triple `M M M` (`M = r·W`) for every register `r`, axiom-free; (2) `C` IS FLIP —
`C^(m+1) S · y · z ⟶ C^m S · z · y` is one constructor, so k strips sort two arguments by
the parity of k; (3) THE CLOSES ARE PARAMETRIC — even parity puts the dead cargo `W` in
operator position (normal form `C (S W M) M`, exactly 11 + 4j fires, normality by
inversion); odd parity puts the live complex `M` there, locking the machine into
`Φ = M N₁ N₂` on the N-tower with period 2j + 8 (k strips, one duplicating S-fire, six
parametric C-fires). `sc_frame_parity_law`: FOR EVERY k, the frame on `C^k S` reaches a
normal form iff k is even; odd k admits runs of unbounded length. The program's first
complete hosting theorem: an infinite input family whose parity is decided by eternity.
C9: OPEN → PROVED in one stage — the fastest conjecture close of the run, because the
probe data (halt 11+2k, period 7+k) had already written the proof's outline.

### Stage 193: the wrapper ISA — C reads, `C C` calls

The beyond-parity probe found no mod-3 in the small-symbol envelope but exposed something
better: the frame is an INTERPRETER whose instruction set is wrapper depth. C9 was the
one-C instruction (READ: strips flip, parity sorts). The two-C instruction is CALL:
`sc_frame_handoff` (axiom-free, every register) — thirteen fires take `scFrame (W r)` to
`r X X`, `X = (W r) W`: control transfers to the register itself, applied to two copies
of its own wrapped complex. Then the register is the program: executing the dead atom
halts behind a 9-leaf normal form (`sc_frame_shield`, 15 fires); executing the duplicator
orbits forever, period 9 (`sc_wrapper_isa`). Probe lesson #9 joined the ledger: an opaque
placeholder register leaks the moment a fire lands inside it — the generic prefix ends
there (the "24-fire universal shield" the raw probe suggested was really 13 generic fires
plus 11 placeholder-specific ones; the corrected law is stronger AND true).

### Stage 194: the omega instruction — the frame compiles self-application

The wrapper algebra probe returned the run's most striking single law: `W·C·W` is a
COMPILE instruction. `sc_frame_omega` (axiom-free, every register): thirty fires take
`scFrame (W (C (W r)))` to `r r r` — the register applied to itself twice, naked, no
shell, no residue. The frame's instruction set now reads: one `C` = READ (parity by
flips, C9), one `W` = CALL (handoff to `r X X`), `W·C·W` = COMPILE ω. Self-application
is the seed of every fixed-point and looping construction in combinatory logic; the
frame manufactures it from any register on demand. Instantiated at the duplicator the
compiled term is verbatim the generation-loop seed, so `sc_omega_to_loop` chains three
pinned laws into: dead frame → ω in 30 → loop in 3 → eternity in fives. The hosting
program's remaining distance: wire READ's numeral-dependence into COMPILE's choice of
`r` — an addressed fetch-execute — and arbitrary tag-style control flow follows.

### Stage 195: the addressed fetch — a numeral decides who runs

The composition stage the ISA was built for, and it cost ZERO new fires: `sc_dispatch_even`
and `sc_dispatch_odd` are `sc_frame_handoff` followed by C9's strip runs followed by one
S-fire. For the register `C^m · p` — a numeral APPLIED to an arbitrary payload — the
wrapped frame fetches, decodes the address by parity, and executes: even `m` puts the
payload in control (`p X (X X)`, 14 + 2j fires); odd `m` runs the dead complex with the
payload parked as cargo (`X X (p X)`, 15 + 2j fires). One machine shape, an instruction
pointer, a conditional transfer of control — `sc_addressed_fetch`. The frame's ISA now
reads: READ (C9), CALL (handoff), COMPILE (omega), FETCH (this). What remains for
tag-style hosting is sequencing — an executed payload that reconstitutes a new addressed
frame — and the omega instruction manufactures exactly the self-application such a
payload needs.

### Stage 196: the sequencer's first wall — spines don't reconstitute

The fetch-execute cycle's direct architecture is probe-dead: over 666 payloads built from
frame-head and duplicator prefabs (≤ 14 leaves, address-0 dispatch products marched 150
fires under a 300-leaf cap), NO trajectory re-enters the exact frame shape
`FH (W r') W` at the root. The structural reading: dispatch products grow leftward while
the frame must reconstitute at the ROOT with its register and cargo in place — but
Stage 189 already showed how frames actually arrive: as POP PRODUCTS of dead cells, not
as spine rebuilds. The sequencer's correct target is therefore a payload whose execution
EMITS FATE-SEED CELLS — the assembly line running inside the dispatch product — and the
re-entry detector should watch for cell-triples, not root frames. The hosting engine is
one architecture-probe away, and the parts (fetch, assembly, pop) are all pinned.

### Stage 197: machines beget machines — the gene

The sequencer's wall (Stage 196) fell to its own diagnosis: watch for cells, not spines.
The engine is a 14-leaf payload that deserves its name — `scGene t = C (cell FH) (cell t)`,
one cell holding the frame head, one holding the child's register. Under address-0
dispatch the gene EXPRESSES (`sc_gene_express`: nine fires, axiom-free, parametric in t)
into the fate-seed `(cell FH)(cell t)(cell t)` plus two riders, and six lifted pop fires
assemble the child `FH t t` in place: `sc_reproduction`, twenty-nine fires from addressed
parent to standing child, THE PARENT'S GENE CHOOSING THE CHILD'S REGISTER. At `t = W` the
child is verbatim `scFrame scW` — `sc_machines_beget`: one standard addressed machine
reduces to another, riders as stack (R1 is an unfinished frame head awaiting cargo, R2
the spent executed complexes — even the waste is legible). The ISA's first full
revolution: FETCH → EXPRESS → ASSEMBLE → RE-ENTER. What separates this from tag-system
hosting is now only ITERATION — a child whose own register re-encodes a gene — and the
gene is parametric, so the search space is the register slot alone.

### Stage 198: the dynasty — machines beget machines, to any depth

The self-gene search returned the right kind of zero: verbatim quines are IMPOSSIBLE for
single-slot genes (the child's register equals its cargo; an addressed parent needs
`W (S p)` against `W`) — and the fix was in the failure. `scGene2 q` carries THREE cells:
frame head, cargo, and the child's whole addressed register. `sc_lineage` (twenty-one
fires, parametric in the payload): the parent of `scGene2 q` reduces to the parent of
`q` with riders as stack — one C-fire to order the cells, six pops to assemble, on top
of the fetch. And lineage ITERATES: `sc_dynasty` proves by induction that the
generation-n ancestor `scParent (scGene2ⁿ q)` reduces to a term carrying the founder
`scParent q` in head position, n rider-stacks deep. Not self-reproduction — heredity:
a family of real addressed machines, each encoding and assembling the next, certified to
arbitrary depth. Combined with C9 (numerals as data) and the dispatch (numerals as
control), the calculus now demonstrably supports GENERATIONS of machines whose registers
carry programs. The tag-hosting question has become concrete: encode a tag step as one
generation.

### Stage 199: the branch — the payload's numeral selects the successor

Conditional control flow, and again at zero emission cost: `sc_branch_even/odd` compose
the fetch with the payload's OWN strip run — for payload `C^k · y · z`, the numeral's
parity decides whether `y` or `z` takes control, each handed the executed complexes as
arguments. `sc_conditional_dynasty` splices the branch into reproduction: a parent whose
gene carries `C^k g₁ g₂` begets a child that gives control to gene one or gene two by
the numeral — THE MACHINE TREE FORKS ON A NUMERAL. The frame ISA at end of day: READ,
CALL, COMPILE, FETCH, EXPRESS/ASSEMBLE (reproduction), BRANCH — every instruction a
pinned theorem, every composition parametric. The remaining distance to tag hosting is a
single construction: a gene whose branch numerals are STRIPPED FROM A STORED WORD as
generations advance (the word is the tape; each generation reads one symbol and forks).
All the parts exist — words as C-chains, strips as reads, genes as successors.

### Stage 200: the tape — a word, read one symbol per generation

Two hundred stages in, the hosting chassis runs. A word over {even, odd} is encoded as
NESTED BRANCH-GENES (`scTape` — linear size, 21 leaves per symbol), and the addressed
machine consumes it one symbol per generation, 22 fires each: fetch, branch on the
symbol's numeral, and — even symbol — the next gene takes control and BEGETS the next
machine (`sc_gene_anywhere`: the gene is position-independent, firing wherever it lands,
axiom-free); odd symbol — the dead atom takes the head and the machine parks
(`sc_tape_stop`). `sc_tape_run`, by induction on the word: for EVERY all-even word and
EVERY payload, the tape machine consumes the whole word and delivers the founder
`scParent q` in head position. The full pipeline, every fire kernel-certified: a stored
program (the word), an instruction pointer (the numerals), a fetch-decode-execute cycle
(dispatch + branch), reproduction (the gene), and halting (the parked atom). What
remains for full tag-system hosting is the WRITE-BACK — generations that append computed
symbols to the tape — and the metabolic assembly line (Stages 188–189) is precisely a
symbol-writing mechanism awaiting the splice.

### Stage 201: the successor — numerals are writable after all

Bits-are-sources seemed to make symbols read-only; the successor law is the loophole the
hosting program needed. `S_red` with middle argument `C` is the calculus's ONLY
C-chain-extending mechanism — `S f C · r ⟶ (f r)(C r)` — and it is a genuine computed
write: the incremented numeral is minted as an argument beside any continuation
(`sc_successor`, one constructor, axiom-free). `sc_double_increment` preserves parity
and keeps the old numeral as cargo; `sc_routed_successor` delivers the new numeral in
OPERATOR position, ready to strip and branch; `sc_successor_numeral` states it on
`C^k S` exactly. The instruction set closes its arc: the tape READS symbols across
generations, the successor WRITES them, the gene COPIES machines, the branch DECIDES.
Every mechanism of a tag machine now exists as a pinned parametric theorem; what remains
is the single integrated construction — and it is engineering, not discovery.

### Stage 202: the odometer wall — self-increment resists the ω-shape

The counting machine's direct architecture is probe-dead: over all bodies `B` up to eight
leaves (154,088 trials, both k=1→2 and the k=2→3 iteration required), NO `B B · reg(k)`
trajectory re-carries `B B · reg(k+1)` in head position. The successor writes numerals
(201) and omega grants self-application (194), but combining them into a HEAD-POSITION
self-rebuild fails in this envelope — consistent with the calculus's standing
conservation laws (no erasure, forward-only writing, arrival-order rigidity): the
incremented numeral is minted as an ARGUMENT, and hauling it back into the machine's own
address position is exactly the mid-spine re-entry that every wall of this program has
guarded. The two working self-reference architectures remain the pre-built kind: the
dynasty (depth encoded in nested genes) and the tape (symbols encoded in nested
branches). Whether {S,C} admits any UNBOUNDED self-modifying counter — or whether
conservation forbids it and hosting must always pre-build its recursion — is now the
program's sharpest open question. Registered as **C10 (the odometer question)**: does
there exist a term family M with `M ⟶⁺ M·junk` where M's own reachable dynamics DEPEND
on an internal numeral that grows across recurrences? (The persistent reader recurs
without internal state; the tape counts but is consumed; C10 asks for both at once.)

### Stage 203: the second n=12 mountain — excess 69 — and C10's widened negative

Two results, one stage. The census's random phase plateaued at a mountain of a NEW type:
modest peak (87), tiny endpoint (18 leaves) — `sc_bound_floor_87`, excess 69, the
program's highest. The floor ladder now holds two n=12 points (f(12,18) ≥ 87 beside
f(12,234) ≥ 291), and best-witness excess reads 12 → 44 → 69 at n = 8 → 10 → 12: worse
than tripling per two leaves. Meanwhile C10's positive direction took another principled
zero: 70,914 further configurations across three architectures (asymmetric heads
`B₁ B₂ reg(k)`, reversed numerals, cargo slots) — 225k total trials, no self-incrementing
recurrence. The conservation reading strengthens: the successor mints numerals as
ARGUMENTS, and no probed architecture hauls the minted numeral back into its own address
slot while restoring the head. C10 remains open, leaning refuted-in-small-envelopes;
the honest positive hope left is a DESIGNED architecture (not searched), and the honest
negative hope is an invariant on head-restoring reductions.

### Stage 204: the ISA algebra, complete — the cheap omega and the successor call

The exhaustive wrapper-word map (all thirty words of length ≤ 4 over {C, W},
placeholder-register emission with leak detection) settles the frame's instruction
algebra: EVERY word eventually hands control to the register — the word chooses only the
arguments and the price. The table's two novelties, both pinned axiom-free:
`sc_cheap_omega` — the two-letter word `C·W` compiles self-application `(r r) W` in
seventeen fires, nearly half the omega word's thirty; and `sc_successor_call` — the word
`W·C·W·C` compiles `r (C r) (C r)`, THE REGISTER EXECUTED ON ITS OWN SUCCESSOR, every
register, thirty-one fires. The successor call is exactly the C10 primitive: a register
that reads numerals can now be handed its own increment as input by a fixed four-letter
program. The other twenty-six words yield rearrangements of `r`, its wrappings, and
X-complex junk — no third novelty at this depth. The frame ISA is closed under words ≤ 4.

### Stage 205: C10 at equilibrium — the odometer resists design and refutation alike

The successor call gave C10 its best-prepared positive shot, and the shot missed: over
20,134 registers, no `r (C r) (C r)` product re-enters a successor-call frame around
`C r`, and no direct recurrence `r x x ⟶⁺ r (C x) (C x)` exists in the same envelope —
roughly 245,000 configurations across five architectures now, all zero. But the negative
direction closed a door too: the obvious conservation arguments FAIL. The head-atom
ledger shows each increment round consumes an S in mint position, but S-stock is
farmable — the persistent reader already cycles its own S-material through duplication —
so no counting invariant refutes C10. And self-reassembly of a fixed head from argument
material is demonstrably possible (the parity orbits do it every lap, cyclically). C10
therefore sits exactly on the program's edge: the positive needs an S-farming,
head-restoring, argument-incrementing design no small envelope contains; the negative
needs an invariant subtler than any counting. This is what an honest hard question looks
like. Recorded at equilibrium; the n=14 census runs in the background (graft
neighborhoods of BOTH n=12 mountain species, then a 3M random sweep).

### Stage 206: the counting chain — counting is free; regrowth is the question

The sharpest constructive statement below C10, pinned axiom-free. `scChain n y` — the
routed successor iterated, three leaves per increment — delivers the n-fold successor of
ANY numeral to any continuation in exactly 2n fires (`sc_chain_run`), the intermediate
numerals trailing as legible junk; on numerals the delivery is exact addition
(`sc_bounded_odometer`: `y` receives `C^(k+n) S`). So {S,C} counts fluently — bounded
odometers of every depth exist at linear cost. C10 now has its final form: the chain
consumes one prefab per increment, and the question is exactly whether any machine can
REGROW its own prefab stock — a self-refueling counter. The pieces stand assembled on
both sides of the gap: successor mints, chains deliver, genes copy machinery, the reader
farms S-material — and no probed or designed combination closes the loop.

### Stage 207: the n=14 mountain — excess 86

The graft heuristic keeps outrunning brute force: 352 neighborhood tries against the
n=12 champions produced a 14-leaf term whose fully forced 500-step prefix peaks at 366
leaves, with a 280-leaf off-prefix target eight checked steps out (the harvest's wider
BFS beat the census's own logged endpoint — excess 86, not 79). `sc_bound_floor_366`
extends the family; the best-witness excess ladder now reads 12 → 44 → 69 → 86 at
n = 8 → 10 → 12 → 14, and the peak-to-source ratio has reached 26×. Four census
generations in, the pattern is stable: every two leaves of source buy a step-function
increase in what any bounding function must absorb, and the witnesses concentrate in one
family (the `C S S (S S) C ...` spine with numeral-tail mutations) — a lineage of
climbers, which is itself evidence the growth is structural, not accidental.

### Stage 208: the review — ninety stages, the run recounted

Bookkeeping stage. STATUS's header now reads the truth: 36 modules, ~1,231 theorems, 437
guards, 241 pinned axiom footprints, ~25,400 lines, zero warnings, 478 commits, ninety
consecutive autonomous stages (119–208). The arc since the Stage 170 review, in one
breath: persistence solved three ways (growth, orbit, fate), the fate machine certified
universally and compositionally, the floor ladder extended two rungs with a stable
climber family, the frame discovered and its ISA completed and PROVED (C9 for all
inputs), machines taught to reproduce, fork, read tapes, and count — and the program's
open frontier consolidated to exactly two questions: bounded intermediates (the
undecidability route) and C10 regrowth (the self-refueling counter). Both are now
precisely calibrated, which is what a review is for.

### Stage 209: the S-farm study — the family search closes the design gap

The C10 design study fixed the last representational flaw in the odometer search: an
odometer is a FAMILY `F[r]` (the reader's front holds FIVE register copies), and every
previous sweep enumerated fixed terms, which cannot express multi-copy families. The
corrected search enumerates CONTEXTS — terms over {S, C, hole}, one to six holes — and
tests the family law `F[reg k] ⟶⁺ F[reg (k+2)]·junk` at two rungs. Through seven leaves:
302,903 contexts, ZERO (the eight-leaf tier still sweeping in the background). The
design analysis alongside: the reader's consultation DOES mint `C²r` every period — the
raw increment exists in a working machine — but the reader's recurrence depends on
unwrapping those mints back to `r` (the unwrap fires are load-bearing for front
restoration), and re-wiring five coherent copies of an incremented register through one
period exceeds every seven-leaf context. C10's positive now requires either an
eight-plus-leaf family (sweeping) or a genuinely multi-period design (increments
amortized across laps). The question keeps its equilibrium; the search space is now the
RIGHT one.

### Stage 210: the family search closes — C10 has no small-context positive

The eight-leaf context tier finished: 3,000,455 contexts, zero odometers — 3,337,323
families total through eight leaves with up to six register holes, each tested for the
two-rung law `F[reg k] ⟶⁺ F[reg (k+2)]·junk`. Combined with the fixed-term sweeps
(~245k) and the invariant analysis (no counting refutation exists — S-stock farms), C10
now has a clean empirical boundary: NO context family of at most eight leaves
self-increments, while every INGREDIENT (mint, delivery, farming, head-restoration)
exists separately in pinned machines. The remaining positive routes are structural, not
enumerable: multi-period designs (increments amortized across reader laps) and
larger-than-eight-leaf families with designed copy-routing — both beyond honest search,
squarely in theorem-or-counterexample territory. C10 graduates from probe subject to
conjecture proper: the working hypothesis, given the wall pattern of this calculus
(no-pair, no-erasure, bits-are-sources, forward-only), is that C10 is FALSE — {S,C}
conserves its way out of live self-modification — and its refutation will need the
program's subtlest invariant yet.

### Stage 211: the spine dichotomy — every step is a mutation or a call

The invariant program opens with the theorem the five walls were pointing at.
`sc_spine_dichotomy` ([propext] only): view any term as head-atom plus spine argument
list; then every step either MUTATES — head and list survive, exactly one argument steps
in place — or CALLS — the head atom is consumed and the FIRST argument becomes the
program (its head is the new head, its arguments prepend, the fire's products join the
list; both S- and C-call frames pinned exactly). Corollary `sc_call_source`: the
machine's next program is always its first argument. The reading: {S,C} reduction is a
call-stack discipline where the leftmost branch is the return stack. Every wall now has
one explanation — pairing, erasure, bit-production, backward writes, and self-increment
all require something to arrive at head position that was never placed in the a₁-chain.
C10 in this language: can a machine place an INCREMENTED COPY of its own address into
its own return stack? The dichotomy makes the question precise enough to attack by
induction over call sequences — the next theorem of the program.

### Stage 212: head provenance — the return stack, iterated

The dichotomy closes under reduction in nine lines: `sc_head_provenance` ([propext]) —
over any multi-step reduction, the final head atom either SURVIVED from the start (the
whole history was mutations; all computation stayed argument-internal) or was SUPPLIED
by the first argument of some reachable state. There is no third source of control.
Every recurrent machine in the program now has its mechanism named: the reader re-supplies
its front from its consultation product (a₁-chain), the orbits re-supply cyclically, the
dynasty re-supplies through genes — and C10 asks precisely whether a re-supplied head
can carry an incremented address through its own supply chain. The invariant program has
its platform: provenance is pinned; what remains is to track the ADDRESS through the
supply, which is a data-flow refinement of the same induction.

### Stage 213: the numeral speed limit — wall six, quantitative

Address flow resolved into something stronger than tracking: `sc_numerals_are_sources`
([propext]) — NO step produces a numeral, at any depth; the proof is three-pronged (root
fires make double applications; an appL-target numeral would need a produced atom; an
appR-target numeral descends infinitely through its own wrap). Numerals exist only where
they were written — bits-are-sources was the depth-1 shadow of this. The corollary is
the program's sixth wall and its first QUANTITATIVE one: `sc_numeral_speed_limit` — the
maximum numeral depth advances by at most one per fire, because a fresh wrap requires an
atom `C` meeting the x-seat and a fire has exactly one x-seat; over any reduction the
growth is linear in fires (`sc_numeral_speed_limit_run`). For C10: an odometer of period
p advances its address by at most p per lap, so a +2-per-lap odometer spends at least
two of its p fires on mints — mints that consume prefab atoms the machine must ALSO
regrow inside the same p fires. The invariant program's next target is exactly that
budget: fires per lap vs. mints plus regrowth, an accounting that may close C10.

### Stage 214: the cargo law — the rightmost argument survives every fire

The dichotomy's positional corollary ([propext]): the rightmost spine argument of any
term survives every step — verbatim in last position, stepped in place, or, in exactly
one case, displaced: a BOTTOM CALL, a call whose frame consumes the entire argument list
(arity exactly three), which slides the old cargo to second-to-last and installs the
call's product as the new tail. Cargo is never erased, never skipped, never overtaken:
to touch its own tail a machine must burn its arity down to three. This is the theorem
the biodegradable word machines have been obeying since Stage 148 — FIFO is not a design
choice in {S,C}, it is the geometry of the spine. For the hosting arc: a tag machine's
append lands exactly at bottom calls, so the tag step's shape is forced — burn down,
bottom-call with the appended production, rebuild; the walls now WRITE the architecture.

### Stage 215: the stamp — the mint family unified, and the rotation ledger

`S f g x ⟶ (f x)(g x)` read as an instruction: the prefab `g` STAMPS the x-seat.
`g = C` was the successor (201); `g = C C` is THE CELL MINT (`sc_cell_mint`, axiom-free)
— one fire builds a cell of any operand; general `g` stamps arbitrary prefab
applications (`sc_stamp`). With this the identity-tag rotation splits cleanly against
the pinned inventory: the READ half exists (the Stage 148 traversal converts a
head-chain word into FIFO arguments — `scBWord_step` appends each read symbol as the
rightmost argument, exactly where the cargo law says appends live); the WRITE half is
per-symbol cell-stamping (this stage's fire); what remains is THE WALK — a head that
stamps its arguments in turn and folds the cells back into a word chain. The 24,036-head
rotator sweep found no walk within seven leaves; the stamp analysis says the walk is a
multi-prefab design, not a wall. The tag step is now three-quarters pinned machinery.

### Stage 216: the walk resists — and the tag arc's honest ledger

The stamping walk took two principled zeros. Cells-as-arguments rotators: none in 24,036
heads through seven leaves. Args-as-queue walkers: the nine-leaf sweep produced one hit —
which the parametricity check (opaque placeholder symbols, lesson #9) exposed as a
phantom: the "walker" depended on its symbols' own internal fires; with inert symbols the
trace diverges. Parametric walkers do not exist within nine-leaf heads. The tag arc's
ledger, honestly drawn: READ half pinned (the Stage 148 traversal — word to FIFO
arguments), WRITE half pinned (the stamp — cell per fire), WALK open — the queue-advance
that routes each stamped cell aside and brings the next symbol to the x-seat exceeds
every small head, and the counting-chain trick (nested prefabs) stamps the same operand
rather than advancing. The walk is where the tag step now lives; like C10's regrowth, it
wants a designed multi-prefab machine, and the two problems may be the same problem —
both ask a head to interleave PROGRESS through material with PRESERVATION of machinery,
which is exactly the interleaving the six walls constrain.

### Stage 217: the suffix law — no overtaking on the spine

The fueled-walk sweep's zero (78,000 stage-contexts) had a reason, and the reason is the
program's seventh wall ([propext]): `sc_suffix_law` — any argument-list suffix beyond
the call frame survives every step, verbatim or with one element stepped in place.
Products NEVER overtake surviving arguments; output cannot accumulate behind an unread
queue; my detector's target shape was unsatisfiable. The constructive flip side: walk
architectures are FORCED onto the scBWord chassis — queue in the head-chain, products
appended at the tail by per-cell bottom calls — which the Stage 148 machinery already
implements for both halves separately. The entire remaining freedom of the tag step is
one dimension: THE ARM SUPPLY (each cell fire consumes a `C C` arm from the argument
side; sustained rotation needs the arms replenished — from cell contents, from the
appended products, or from pre-built fuel). Seven walls, and each one narrows the design
until the machine is almost dictated: that is either how the construction gets found, or
how its impossibility proof assembles itself.

### Stage 218: the pass-through word — the arm-supply dimension closes

The one-dimensional design space left by the suffix law collapsed in one constructor:
the PASS-THROUGH CELL `C M W` fires on any arm as `(C M W) A ⟶ (M A) W` — the arm hands
through untouched, the symbol appends behind it (`sc_passthrough`, axiom-free). A word
stored as nested C-pairs unrolls at ONE fire per symbol on a SINGLE conserved arm
(`sc_cword_run`), symbols emerging in rotation order — the front of the stored word
lands rightmost, exactly where a tag machine wants it. This retires the Stage 148
chassis's economics (seven fires and one consumed arm per symbol) and closes the arm
question: nothing is consumed at all. The identity tag machine is now a single missing
mechanism: the LOOP CLOSURE — an end-marker that re-packs emitted arguments into a fresh
C-word. And the C-word is the cheapest word representation the calculus admits: one
fire per symbol is a trivial lower bound, and the pass-through achieves it.

### Stage 219: the loop closure resists — repackers are phantoms at six leaves

The end-marker sweep produced five six-leaf "repackers" — and the two-placeholder-set
discipline (lesson #9) exposed all of them: the rebuilt C-word appears for one symbol
alphabet and not another, so the assembly routes through the symbols' own internals.
Parametric repackers do not exist within the swept envelope. What the phantom still
shows: C-word shapes CAN be assembled by fires (the target structure appeared, cells and
all — built from an S-fire's duplication and C-routing); what is missing is symbol-blind
assembly, and the stamp analysis says why it is hard — stamping `C`-applications
requires the symbol in the x-seat and the half-built word as the prefab, which means the
prefab GROWS as the word packs: the repacker needs a growing g-seat, and prefabs in this
calculus are fixed shapes. The loop closure is therefore the same species as C10's
regrowth for the third time: machinery that must grow in step with its own output. The
identity tag machine now has every part but this one, and this one has resisted three
architectures. Suspicion, recorded: the loop closure may REQUIRE the growing-front
technology (the reader's), making the tag machine a reader-variant rather than a cycle —
which would be consistent with every wall and every existing machine.

### Stage 220: the burn — the storage reads itself back

The convergence stage. The reader's junk block, identified at 218 as a pass-through cell,
proves live: `sc_junk_is_cell` (one fire unloads it onto any arm) and `sc_junk_ignition`
(three blocks applied to each other ignite in four fires, ending in the stored register's
CONSULTATION — `S S C` firing on stored material), both axiom-free. The probe trace past
the pin shows the burn does not decay: registers consult, fresh cells form around junk
PAIRS — second-order storage — and the configuration grows reader-like. So the medium the
reader writes is the medium the burn reads, and both behaviors — grow (Stage 176) and
burn (here) — belong to one substance. The alternator (C8-final's last composition), the
tag machine's loop closure, and C10's regrowth now all live in the same place: the
dynamics of the junk medium. The program's next depth is a THEORY OF THE MEDIUM — what
J-streams can compute — and its first question is whether the metabolizing burn is
itself a persistent front (the probe suggests yes: growth with recurring shapes).

### Stage 221: the medium's pulse — a period-12 wave without a front

The burning junk stream has a clock but no face: size deltas settle into an exact
period-12 pattern (+67 leaves per period, sustained through fire 262 and 1,500 leaves)
yet NO verbatim front recurs — the recurrence drifts structurally, junk accumulating
mid-spine the way `frame(S S)` did at Stage 190. So the medium's burn is a genuine
persistent process that the Front·J technology cannot pin: the program's certification
tools cover verbatim recurrence (reader), cyclic recurrence (orbits), and graded
termination (ranked closures) — the burn is a fourth kind, PERIODIC DRIFT, and pinning
it would need trace-template induction like C9's (feasible: the period is short and the
drift is additive). Registered as the medium theory's first concrete target. The week's
convergence holds: one substance, four behaviors — write (reader), park (orbit), burn
(ignition), pulse (this) — and every open question of the program is a question about
what this substance can be made to do.

### Stage 222: the pulse, pinned — the fourth recurrence technology

The periodic drift decoded into verbatim periodicity wearing a disguise: the burn's state
at fire 4 + 12m is EXACTLY `scPulseW m = S · PRE · BLOCK^m · SUF` — the front detector
missed it because the block insertion is mid-spine, before the conserved tail, precisely
where the cargo law says growth must go. The pin is complete and cheap: the Stage 220
ignition target IS phase zero; twelve concrete fires take each phase to the next inside a
six-argument window (`sc_pulse_core`, axiom-free), with everything beyond riding on the
new `scStepsN_appList` lift; `sc_pulse_law` closes all phases and `sc_burn_wave` makes
the junk medium's burn an ETERNAL WAVE — three 14-leaf junk blocks reach every phase of
an unboundedly growing periodic process. The toolkit now certifies four recurrence kinds:
verbatim (reader), cyclic (orbits), graded (ranked closures), and periodic drift (this).
The alternator's grow and burn phases are both pinned persistent processes over one
medium; what remains of C8-final is only their SPLICE — and the splice is now a question
about two pinned waves meeting, not about unknown machinery.

### Stage 223: the alternator, coexistence form — and the gap named FRONT DEATH

`sc_alternator_coexist`: one term in which the reader writes storage forever while the
burn wave consumes storage forever — every joint phase `(n, m)` reachable, by the chassis
and the two pinned wave laws. C8-final's machinery now runs jointly in a single
configuration. What separates coexistence from the full alternator (the grow-phase's own
junk igniting) is exactly ONE mechanism, and this stage's probes named it: FRONT DEATH.
In-place ignition is impossible (junk blocks are inert two-argument cells until they
reach head position — the pass-through's flip side); the immortal reader never yields the
head; and the mortal-reader candidate (the halting bit `C C` in the reader frame) turns
out to be a THIRD wave — the medium is generous with persistence and stingy with death.
A front that runs, writes, and then expires — the fate machine's halt inside a reader —
is the single remaining design target of the C8 campaign, with both endpoint technologies
pinned and waiting.

### Stage 224: the ouroboros — grow feeds burn, in one term

Front death was hiding at three leaves. Put `ρ = S (S S)` in the reader frame and the
machine becomes the OUROBOROS: fire one WRITES the junk block (verbatim reader
mechanics — `sc_ouro_writes`); the register's own consultation fires then duplicate the
written block leftward into operator position; at fire ten THE BLOCK TAKES THE HEAD and
at fire eleven it unloads its stored payload (`sc_ouroboros`, eleven fires, axiom-free).
The alternator's feeding form is real — not two coupled machines, but one machine whose
register CALLS ITS OWN STORAGE. With this, the C8 campaign's ledger closes its last
mechanism column: persistence with growth (reader), persistence without growth (orbit),
fate by register (fate machine), storage as medium (junk-is-storage), the burn
(ignition), the wave (pulse), coexistence (chassis), and now feeding (ouroboros). What
the campaign has NOT produced is the disciplined alternation — grow k, burn k, repeat —
and the ouroboros suggests why: in this calculus grow and burn are not phases to
alternate but one metabolism seen at different moments. The medium theory begins from
that observation.

### Stage 225: the ouroboros wave — three metabolisms, one substance, all pinned

Stage 222's recipe generalized on first contact: the post-splice burn is the family
`C · PRE · BLOCK^m · SUF` (160-leaf block, period sixteen), and the same four-theorem
pattern pins it — entry (forty fires: the write, the feeding, and the first full period
in one chain), core window (axiom-free), rider-lifted law, eternal reach. The junk
medium's every observed behavior is now a certified process: the READER WAVE (period 7,
verbatim recurrence), the BURN PULSE (period 12, periodic drift), and the OUROBOROS WAVE
(period 16, periodic drift). And the ouroboros resolves C8-final's koan: the machine that
writes its own food does not alternate between growing and burning — it eats and grows,
one metabolism, certified forever. The persistence campaign that began at Stage 176 with
"can state outlive the machine's step?" ends with a taxonomy: state outlives by verbatim
growth, by bounded orbit, by fate, by phase, by storage, and now by self-consumption —
and every one is a theorem.

### Stage 226: the review at one hundred eight

Counts refreshed: ~1,265 theorems, 265 pinned footprints, ~26,200 lines, zero warnings,
508 commits, one hundred eight consecutive autonomous stages. The week's shape, seen
whole: the invariant program turned seven probe-walls into five clean theorems and two
design constraints; the constraints forced the pass-through word and then the ouroboros;
the ouroboros closed C8-final; and the template method certified every observed behavior
of the junk medium. Two questions remain open, both now precisely calibrated: BOUNDED
INTERMEDIATES (the floor ladder's excess marches 12 → 44 → 69 → 86 against any
computable bound) and C10 REGROWTH (counting is free, regrowth resists 3.5 million
probes and every design; the ouroboros grows without counting, the chain counts without
growing, and whether any machine does both is the sharpest question this calculus has
produced). The program's next arcs, in standing order: the medium bestiary, an n=16
rung if wanted, and the two frontiers — which now have seven walls, four recurrence
technologies, and a complete ISA to attack with.

### Stage 227: the medium bestiary — copies multiply, depth never grows

The reader frame's full census over registers up to six leaves: 451 halting, 2,153
growing, 162 cycling, 472 undetermined-at-300 — the frame is behavior-complete over its
register slot, echoing the fate frame's trichotomy at Stage 190. And the C10 detector
came back empty in a new, sharper way: across all 3,238 fronts, NO trajectory shows
unboundedly growing numeral depth. The medium's metabolisms — including the three pinned
waves — multiply COPIES of their registers (block counts grow linearly forever) but never
DEEPEN them (max numeral depth is bounded on every observed trajectory). The speed limit
permits one deepening per fire; the medium's geometry never spends it — the wrap-mint
needs a numeral in an x-seat beside an atom-C prefab, and reader-frame dynamics never
assemble that meeting. C10's ledger gains its most structural entry yet: in the one
family of machines that demonstrably sustains eternal computation, the counter never
ticks. The refutation hypothesis strengthens; the invariant that would prove it — "no
recurrent process deepens its own numerals" — now has a natural formulation over the
pinned wave families, where it is CHECKABLE: the wave laws are explicit, so bounded
numeral depth along each pinned wave is a corollary away. The frontier stands there.

### Stage 228: the waves are numeral-free — no-deepening, certified where it counts

The medium's copies-not-depth fact is now theorem for every pinned wave:
`sc_pulse_numeral_free` and `sc_ouroWave_numeral_free` — at EVERY phase of both eternal
waves, maximum numeral depth is exactly zero ([propext], by the spine lemma
`scMaxReg_appList_zero` plus phase induction over the explicit block vocabularies). The
eternal machines of {S,C} run their entire unbounded lives without ever spending the
speed limit's budget: one deepening per fire available, zero ever used. C10's
no-deepening invariant — "no recurrent process deepens its own numerals" — now holds
certified on every pinned eternal process in the program. What remains between this and
a C10 refutation is the leap from THESE waves to ALL recurrences: an invariant proof
that periodic-drift families over numeral-free vocabularies are the only eternal shapes,
or a counterexample that carries a numeral where three and a half million probes found
none. The question is exactly balanced on the best evidence the program can produce.

### Stage 230: C10, formalized — the question is a quantifier swap

The deepening question is now a Lean proposition: `scDeepening := ∃ t, ∀ n, ∃ u,
Steps t u ∧ n ≤ scMaxReg u` — one term, every depth. The formalization exposes its
skeleton: `sc_depth_breadth` proves the SWAPPED form outright (for every n, some term
reaches depth n — the counting chain), so C10 is exactly the question of commuting
∀n∃t into ∃t∀n; and `sc_depth_cost` prices the strong form linearly (n fires minimum
from depth zero — so a witness must deepen forever at bounded amortized cost, which is
precisely what every pinned eternal machine declines to do). The conjecture registry now
holds the question in its final dress: a one-line Prop whose refutation would be the
program's deepest invariant and whose proof would be its most surprising machine.

### Stage 231: the medium reads order — the junk tape

The medium's blocks carry information in their SEQUENCE: over 231 register pairs,
twenty-seven order-sensitive burns — same multiset, different order, different fate.
Pinned at the atoms: `J(CC)·J(S)·J(S)` dies in nineteen fires at a 21-leaf normal form
(`sc_order_halts`, axiom-free) while `J(S)·J(CC)·J(S)` ignites an eternal period-2
growth wave (probe; its compound insert-and-mutate template resists the block recipe and
is recorded unpinned — the medium's first process beyond the current template
technology). The upshot joins the week's convergences: junk streams are WORDS, the burn
READS them, and fate is the readout — the medium is a tape written by machines and read
by its own combustion. The hosting program's word-representation question ("how does a
tape live in {S,C}?") has had its answer in the junk all along: Stage 179 named it
storage, 218 gave it cells, 220 lit it, and now it reads in order.

### Stage 232: the n=16 mountain — the ladder crosses one hundred

Fourth straight graft win, 208 tries: `sc_bound_floor_308` — every valid bounding
function clears 308 at (16, 207). The best-witness excess ladder now reads 12, 44, 69,
86, 101 at n = 8, 10, 12, 14, 16: five rungs, one structural family of climbers
(the `C … S S (S S) C (S (C S (C^j…)) C)` spine with the numeral tail deepening by one
per generation — the family's own parameter is a numeral, which is either a fine irony
or a hint), and kernel cost still linear in the path at march-600. Each rung is another
finger on the scale against bounded intermediates; the family's regularity suggests the
n→∞ law might itself be provable — a PARAMETRIC mountain family with excess growing in
n would refute bounded intermediates outright, and the climbers' shared anatomy is the
place to look. Registered as the ladder's endgame question.

### Stage 233: the corridor — the ladder becomes a staircase in one term

The endgame probe changed the geometry of the whole bounded-intermediates question. The
n=12 climber `scMt5T` is not a mountain — it is a CORRIDOR: its reduction path is forced
for at least sixty thousand fires (probe horizon), oscillating through peaks past 3,500
leaves with dips trailing behind. Since forced means the reachable set IS the path, every
post-peak dip is a certified mountain: the new `scForced_mountain_last` (on-path capped
exclusion) plus a march-2109 kernel decide pin `sc_bound_floor_666` — excess 151 at
(12, 515), from the term that held excess 57 three days ago, with excess 241 and 420
sitting further down the same corridor priced only in kernel time. The endgame's shape
sharpens: if the corridor's oscillation TEMPLATES (a rising wave family), then peak(k)
and dip(k) become theorems, excess(k) → ∞ along one term's corridor, and the bounded-
intermediates question resolves negatively for (12, m)-families — with the frontier
equivalence waiting. The corridor's wave archaeology is the program's next great object.

### Stage 234: the spiral — a fifth recurrence kind, exactly regular

The corridor's archaeology returned the cleanest structure of the run. The n=12
climber's forced path is a SPIRAL: cycles of EXACTLY linearly growing length (spacing
252 + 6k at cycle k), each cycle raising the peak by exactly 25 leaves, adding exactly
one 16-leaf block to the blob's run, and growing each of three towers by exactly one
3-leaf context at a fixed position (verified through eighty consecutive cycles, fires
5,400–44,300, every count exact). The macro-state at peak k is fully characterized:
`C · a₉ · (C · x · T₁ctxᵏ · T₂ctxᵏ · T₃ctxᵏ · B^(42+k))`. This is a FIFTH recurrence
kind — the spiral: linearly growing period, linear growth, exact template — and it is
C9-SHAPED: the parametric proof needs a fixed-fire prelude plus a six-fire-per-block
processing lemma iterated k times, exactly the strip-run pattern that proved the parity
law. Registered as **C11 (the spiral law)**: Φ(k) ⟶^(252+6k) Φ(k+1) for all k. Its
consequences, mapped honestly: C11 proves the corridor INFINITE (scMt5T has no normal
form; its floor staircase never ends — a PARAMETRIC floor family, infinitely many pinned
floors from one theorem); but corridor excess is linear-plus-constant in the dip size,
so C11 alone improves the bounded-intermediates constants, not the asymptotics — the
undecidability endgame still needs superlinear excess, which must come from elsewhere
(deeper climber families, or corridors that crash). The spiral proof is the program's
next major formalization; every piece is de-risked and exact.

### Stage 235: the spiral is a word machine — the corridor and the chassis are one

The cycle arithmetic is exact: every spiral cycle is SIX FIRES PER BLOCK, no remainder
(spacing 252+6k = 6·(42+k) with 42+k the block count — verified across eighty cycles).
The spiral is therefore a WORD MACHINE: the blob's block run is a tape, the cycle is one
full traversal at six fires per symbol, and each traversal appends one block (+16), one
tower layer (+3×3), and twenty-five leaves of peak. The program's two grand arcs have
converged at the bottom: the corridor that carries the floor ladder IS the tag-chassis
architecture (a walker on a self-extending word), discovered not by design but inside
the census's best climber. The C11 proof plan is now concrete: (1) extract the six-fire
block-step lemma (walker · block · rest ⟶⁶ walker' · rest · output — pass-through-family,
needs a blob-spine tracker); (2) the Φ(k) Lean family over the exact template; (3) the
traversal induction (block-step × (42+k), rider-lifted) and the cycle close. C9's proof
was this shape at period 7+k; C11 is the same theorem grown up — and with it, the
corridor's infinity, the parametric floor family, and the fifth recurrence technology.

### Stage 236: the spiral family, anchored — C11 has a formal ground floor

`scSpiral j` is now a Lean definition matching the corridor's exact template — and its
vocabulary is the PASS-THROUGH FAMILY: the tower grows by `(C C)·(C ·)` per cycle, the
blocks are C-headed cells, the whole spiral is built from the same three-leaf grammar
that runs the reader, the ouroboros, and the tape. `sc_spiral_anchor` (axiom-free):
forty-four fires take the n=12 climber exactly onto `scSpiral 0`. `scSpiralLaw` is the
registered formal target — every cycle in 30 + 6j fires — and its proof plan is fully
concrete: twelve fixed fires, a six-fire run-block lemma iterated 3 + j times with the
tower riding passively, rider lifts throughout. One probe near-miss caught by exact
assertion (TWO distinct 16-leaf blocks, not one — the honest-assembly discipline again).
When scSpiralLaw lands, the corridor is infinite, the climber has no normal form, and
the floor staircase becomes a single parametric theorem.

### Stage 237: the spiral turns — two cycles certified, one lemma left

The spiral's first two turns are kernel facts: `sc_spiral_turn0` (thirty fires) and
`sc_spiral_turn1` (thirty-six — the 30 + 6j schedule, live), both axiom-free, with
`sc_spiral_reach2` chaining the anchor through both. The family definitions survived
contact with the corridor exactly. `scSpiralLaw` — and with it the corridor's infinity
and the parametric floor staircase — now rests on a single remaining lemma: the six-fire
run-block step, whose statement the two concrete turns bracket from both ends. The
program's chapter arithmetic: five recurrence technologies, two registered conjectures
each one lemma or one idea from resolution, and a hundred nineteen consecutive stages.

### Stage 238: the third turn — the spiral's true anatomy

Three consecutive schedule points are now kernel facts (30, 36, 42 fires — `sc_spiral_
turn2`, all axiom-free, 152 fires chained from the climber). And the fire-trace analysis
corrected the mechanism: the block run NEVER ignites — it rides as passive suffix exactly
as the cargo law dictates — while every fire churns the blob's four leading arguments.
The cycle is HEAD METABOLISM: front matter burns, the tower passes through the mill and
re-emerges one layer taller, a fresh run-block is minted at the burn's bottom, the front
rebuilds. The schedule's 6j is six fires per TOWER LAYER; tower depth and block count are
locked at +1 per cycle, so arithmetic alone could never separate the two readings — the
probe discipline's oldest lesson, now at theorem scale. The spiral is the program's first
pinned process whose period grows because its own state does: it re-reads everything it
has ever written into its tower, every cycle, forever. C11's remaining lemma is therefore
a TOWER-MILL lemma (six fires per layer, layers passing through the burn), and the three
certified turns bracket its statement exactly.

### Stage 239: the mill read — C11's proof architecture, exact

The turn-diff (depth-normalized, three certified turns as data) exposes the tower-mill's
mechanism: the cycle's middle is a run of THREE-FIRE C-TRIPLETS visiting the tower's
layers — `C_red` on `(C TWR)`-pairs at descending wrap-levels — with TWO passes per
layer (a down-pass stripping toward `T₀` and an up-pass rebuilding one layer taller):
six fires per layer, as the schedule demanded. The alignment obstacle is also now exact:
the cycle's fires reference tower-wraps at EVERY level (not just the top), so the mill
lemma is not a single rider-lifted core like the waves — it is a TWO-PHASE LAYER
INDUCTION, C9's strip-run-and-rebuild shape with the tower in place of the numeral. The
C11 proof is therefore: anchor (pinned) + fixed prelude + down-pass induction over j
layers + mint + up-pass induction + fixed close, each phase's fires readable off the
certified turns. Nothing about it is unknown anymore; it is a day of careful Lean. The
spiral keeps the medal for most-structured object of the run: a machine that mills its
own history, two passes a layer, six fires a memory.

### Stage 240: THE MILL LAWS — C11 proved; the corridor is infinite

The spiral dissolved. Its engine is a two-counter machine `G a m = T_a · (C T_a) · T_m`
over the layer grammar `L x = (C C)(C x)` and a nine-leaf core — and everything the
program had named separately (B₁, Y, the tower, the junk block) turned out to be
tower-terms in disguise. Two six-fire laws, both axiom-free and parametric in EVERYTHING:

  THE DESCENT   (L x)·(C (L x))·y ⟶⁶ x·(C x)·y
  THE TURNOVER  K·(C K)·M ⟶⁶ M·(C M)·(L M)·B₂

The turnover is the heart: at counter zero the core fires and the counter is rebuilt as
a COPY of the tower — one duplication, which is why six fires suffice at every scale —
while the tower gains a layer and one junk block falls out. From these: the cycle law
(`6(m+1)` fires per revolution — C11's content, PROVED), the eternal spiral
(`sc_mill_eternal`: k revolutions for every k), the anchor identification
(`sc_spiral_is_mill`, by decide), and the headline corollary `sc_corridor_unbounded`:
THE 12-LEAF CLIMBER'S REACHABLE SET IS UNBOUNDED — certified end to end, 44 anchor fires
plus pure law. C11: registered at Stage 234, proved at Stage 240. The spiral joins C9 as
the second conjecture closed by template, and the mill joins the fate machine, the
reader, and the gene as the fourth named engine of the calculus — the one that counts
its own age in layers, rebuilds its counter from its tower, and never stops.

### Stage 241: the corridor census — the statistical mechanics of term space

The approved landscape survey, delivered. Exhaustive at n=10 (all 4,978,688 terms,
800-fire horizon): 67.1% reach normal form, 32.8% branch into nondeterminism, and
0.147% — 7,311 terms — are CORRIDORS: fully forced for at least 800 fires, of which
3,148 blow a 1,500-leaf cap outright. The n=12 sample (300,000 terms) shows the same
phase at 0.17%. The corridor phase is rare, stable across sizes, and ENORMOUS inside:
median corridor peak 1,048 leaves at n=10 (max 1,670) — ten-leaf terms routinely forced
through thousand-leaf skies. Three readings. First: the floor ladder's rungs were vast
underestimates — thousands of corridors each carry floors at the 1,000+ scale, and the
mountain censuses were sampling this phase without knowing it. Second: the spiral/mill
is not a miracle — forced eternal machines are a solid phase of term space, which makes
mill-like engines the EXPECTED anatomy of deep {S,C} dynamics. Third, and sharpest: the
bounded-intermediates endgame is now a FINITE SCREEN — scan the 7,311 corridors for one
whose path crashes far below its running peak (superlinear drop); one crashing corridor
plus the on-path mountain technology would break the linear-excess barrier that the
spiral could not. The towers-are-normal lemmas (this stage's feat) lay the forcedness
groundwork for pinning whatever the screen finds.

### Stage 242: the mill is forced — the only path, parametrically

The existence laws became uniqueness laws: `sc_mill_descent_forced` and
`sc_mill_turnover_forced` ([propext]) — with normal payloads, every state of both mill
laws has exactly one successor. The proof technique is itself a small milestone: the
first PARAMETRIC forcedness in the program (all previous SCForced facts were decide-
checked on concrete chains), possible because every live redex in the mill has a
concrete head with the opaque towers confined to argument seats, so `scSucc` computes by
structural simp against the payloads' normality. With `SCForced_append` the revolutions
concatenate; the parametric staircase — every mill peak an on-path mountain, at every
scale, in one theorem — is now pure assembly over pinned parts.

### Stage 243: the crash screen verdict — the corridor phase is linear, and the frontier flips

The finite screen ran to completion: all 7,311 n=10 corridors, deep-marched 4,000 fires,
ranked by peak-to-later-dip drop. THE VERDICT: no crasher exists. Maximum drop anywhere
is 211 (peak 628 → dip 417, ratio 1.51 — and the witness is the Stage 181 census
champion's own family); maximum peak/dip ratio anywhere is 2.50, achieved only on
20-leaf transients. The mill's own asymptotic ratio is 3 (peak 31+9m against dip 28+3m).
Within the entire exhaustively-known corridor phase, EXCESS IS LINEAR IN THE ENDPOINT
with constant ≤ ~3.

This flips the working hypothesis of the decidability frontier. The program spent forty
stages accumulating floors "against bounded intermediates" — but every floor was linear
in its endpoint, and the census now says linear is ALL THERE IS at n=10. The honest new
position: the evidence favors a computable bound of the form f(n, m) ≈ 3m + g(n) — and
by the frontier equivalence, a PROOF of any such linear law would make {S,C}
reachability DECIDABLE. The endgame question inverts from "find a crasher" to "prove
the linear law": does every {S,C} reduction admit a path whose intermediates are
bounded by C·(|t| + |u|)? Registered as **C12 (the linear-excess law)** — the program's
third live conjecture, and the first on the DECIDABLE side of its central question.
Both directions now have concrete attack surfaces: C12 via standardization-style
arguments over the call-stack discipline (the seven walls constrain what a path can
do), refutation via corridors at n ≥ 12 where the phase may behave differently.

### Stage 244: the no-normal-form principle, and C12 at two generations

Two results. THEORY: `sc_forced_forever_no_nf` — an infinite family of nonempty forced
chains, each ending where the next begins, traps every reduction: everything reachable
from the family's start still steps, so no reachable normal form exists. With the rider
lemma (`sc_forced_rider`: forcedness survives normal riders), the deep-spine root-
vanishing (`scSuccRoot_deep_nil`), and the parametric forced mill runs, every ingredient
for instantiating the principle on the corridor is pinned — the instantiation (ridden
revolutions as the chain family) is the one assembly step left before "the census's best
climber has NO normal form" becomes a theorem. EVIDENCE: the n=12 crash screen — 1,500
corridors deep-marched — returns the SAME maximum drop as n=10 (211, the same climber
family), ratio distribution median 1.23, p95 1.71, max 3.44. The linear-excess law C12
is two-generation stable with constants: no corridor at either size exceeds ratio 3.5,
against the mill's own asymptote of 3. The frontier's decidable side keeps firming.

### Stage 245: THE CLIMBER NEVER RESTS — `sc_mt5T_no_nf`

The corridor no-NF instantiation closed. The invariant that makes it work is SPINE
DEPTH: every state the mill ever visits has left-spine depth ≥ 3 (`SCSpine3`), so no
rider — junk block, junk stack, or the outer carrier — can ever complete a root redex.
Forcedness therefore survives arbitrary stacking (`sc_forced_riders`, and the mirror
carrier lemma), the revolution is forced as a named whole (`scMillRevStates_forced`:
from `G 0 m` the entire cycle of `6(m+2)` fires is the ONLY reduction), and the chain
family — anchor march, initial descent, then one ridden revolution per generation —
satisfies the no-normal-form principle. `sc_mt5T_no_nf`: every term reachable from the
twelve-leaf climber `S (S S C (S C) (S (C S (C C)) C))` still has a step. The corridor
is not just unbounded (Stage 240); it is INESCAPABLE. This is the program's first
pinned non-normalization of a census-found wild term, and the strongest possible form
of the two-regime picture: the climber's entire reachable set lives outside the
normal-form phase. Axioms: [propext, Quot.sound].

### Stage 246: THE PARAMETRIC STAIRCASE — `sc_corridor_excess`

The floor ladder, at all scales at once. `sc_corridor_excess`: for every `d` there are
`u, w` with `scMt5T →* u →* w` and `|w| + d ≤ |u|` — the full-dress peak right after
generation `j`'s turnover (`141 + 25j` leaves) stands `24 + 6j` above the ground state
it then descends to (`117 + 19j`). The size ledger is exact: towers weigh `9 + 3m`,
`G a m` weighs `28 + 6a + 3m`, junk blocks 16 each. The hand-built ladder rungs
(f(6,6)≥7 through the corridor mountain's excess 151) measured single peaks with
per-instance marches; this theorem covers every rung above them in one stroke. What it
does NOT yet say is the *must-pass* form (every path from the climber to `w` visits a
`≥ |u|` state) — that needs the reachable-set characterization (every reachable term
lies on the family), which the no-NF principle's induction already contains and which
would also make reachability FROM the climber decidable. That extraction is next.

### Stage 247: THE CORRIDOR, EXACTLY — `sc_mt5T_reach_iff`

The no-NF principle's induction knew more than it said: extracting its membership
invariant gives `sc_forced_family_mem` (everything reachable from a forced family's
start lies on the family), and with the converse this becomes an if-and-only-if:
**a term is reachable from the twelve-leaf climber iff it is a generation start or on a
generation's forced chain.** The wildest term the census found — 60k+ forced fires,
unbounded growth, no normal form — has the TAMEST possible reachable set: a single
path, in closed form. This sharpens the two-regime picture into an irony worth
recording: wildness in {S,C} (so far) is not chaos but pure rigidity. The three open
follow-ons: (a) pinned decidability of reachability-from-scMt5T (sizes grow with
generation, so the iff reduces membership to finitely many checks); (b) the must-pass
staircase (the iff makes "every path passes the peak" immediate — there IS only one
path); (c) C12 theory — whether every corridor is this rigid is exactly the question
the linear-excess law now hangs on.

### Stage 248: reachability from the climber is DECIDABLE — `scMt5TReach_decidable`

The punchline of the corridor arc. With the reachable set in closed form and a size
floor per generation (nothing in generation `j+2` weighs less than `59 + 16j`), the
membership question needs only the first `|u| + 2` generations — a terminating,
certified scan (`scMt5TReach`, with `scMt5TReach_iff` and a `Decidable` instance).
The term that the crash screens crowned wildest — no normal form, unbounded growth,
60k+ forced fires — is now the term whose reachability problem is COMPLETELY SOLVED.
The moral for C12 and the frontier: in {S,C}, the wild terms found so far are wild in
size only; dynamically they are the most predictable objects in the space. If C12's
linear-excess law holds because EVERY corridor is a mill in disguise (rigid, forced,
characterizable), then reachability is decidable not despite the corridors but
because of them. That is now the sharpest available formulation of the program's
central question.

### Stage 249: the six champions are corridors — and C13 is born

The ideonomy pass, run over the corridor arc's new inventory, opened with an
empirical question: are the n=12 crash-screen drop-leaders G-machines like the mill?
The probe answered harder than expected: **all six are fully forced — zero branch
points in 6000 fires — with revolution periods growing arithmetically** (+6/cycle for
four of them, +4/cycle for two — the +4 pair suggesting a leaner layer grammar than
`L x = (C C)(C x)`). Pinned: 500 consecutive forced fires apiece.

**C13 (THE RIGIDITY CONJECTURE), registered**: every {S,C} term that avoids both
normal form and branching — every corridor — is eventually a G-machine: its reachable
set is a finite prefix plus a parametric family of forced revolution chains. C13
would give corridor terms decidable reachability by the Stage 245–248 pipeline
(family → size floor → bounded scan), and with the census phases (NF: decidable by
normalization; BRANCH: the remaining question) it is now the sharpest route to full
decidability. C12 (linear excess) would follow from C13 with mill-style size ledgers.

Ideonomy residue (ranked leads): (a) classify two-leaf layer grammars admitting
descent laws — the +4-period champions should yield a second, smaller mill; (b) check
whether the climber's growing towers settle C10 (scDeepening) — the mill's `T m` has
unbounded depth, so if scDeepening's depth notion matches, C10 resolves POSITIVE off
the shelf; (c) the BRANCH phase: probe whether branch points reconverge (local
confluence statistics) — if corridors are rigid and branches reconverge, the whole
space may be tamer than the frontier assumed.

### Stage 250: THE CLIMBER NEVER DEEPENS — `sc_mt5T_flat`, and C10 narrows

The C10-via-towers lead resolved NEGATIVE, and the negative is a theorem: the mill's
towers are `(C C)(C ·)`-nests, not numerals (`C^n S`), and a register-shape calculus
over the closed-form reachable set shows `scMaxReg u ≤ 1` for every state the climber
ever reaches (`sc_mt5T_flat`; corollary `sc_mt5T_not_deepening`). The corridor
trichotomy is complete and pinned: the climber is size-UNBOUNDED (`sc_corridor_
unbounded`), dynamically RIGID (`sc_mt5T_no_nf`, `sc_mt5T_reach_iff`), and numerically
FLAT (`sc_mt5T_flat`). What this teaches about C10: corridor engines of the mill
species cannot deepen — their growth lives in layer-nesting, and layers are not
registers. A C10 witness, if it exists, must either be a corridor of a genuinely
different species (the +4 family's C-CHAIN counters are structurally closer to
numerals — `C^k(base)` differs from `C^k S` only in its base — but their chains bottom
out at compounds, so they too read `scIsReg = none` at every wrap) or live in the
BRANCH phase. C10 leans harder false; the sharpest attack now: prove flatness for
EVERY corridor species (C13 would industrialize this), leaving only BRANCH terms as
candidate deepeners.

### Stage 252: the BRANCH phase decomposes — confluence plus an 88% norm

Two facts reshape the third phase. First, from the shelf: {S,C} is orthogonal and the
repo already holds full confluence (SCConfluence.lean: parallel reduction, triangle,
diamond, strip) — so branch points always reconverge and BRANCH is not about
divergence of ARMS but about termination. Second, the probe: of 600 n=10 BRANCH terms,
**88.2% leftmost-normalize within 1000 fires, 10.5% grow past 2500 leaves (divergent
growers — the C13 suspicion: embedded G-machines), 1.3% linger small.** The
decidability picture now factors as: NF phase (67%) + normalizing BRANCH (~29% of all
terms) decidable by normalization-and-compare under confluence; corridors (0.15%)
decidable if C13; the residue — divergent-growing BRANCH (~3.5% of all terms) — is
where any undecidability must hide, and where the corridor pipeline (find the engine,
pin the family) is the obvious siege engine. C10's last refuge shrinks to the same
residue.

### Stage 253: the residue is NOT corridors — the S-storm regime

The C13-collapse hope for the divergent residue is dead, and the negative is sharp:
forty n=10 divergent growers, marched with a size cap — median forced-fraction 0.00
over their late fires, zero fully-forced tails, 31/40 blowing past 12,000 leaves
within 500 fires. The residue is massively BRANCHING exponential growth (S-duplication
storms), not corridors in disguise. Consequences: (a) C13's scope is clarified, not
refuted — it governs forced terms, and the storms are its complement; (b) the
decidability question's hard core is now named: the S-storm regime — confluent,
exponentially growing, maximally branchy (~3.5% of terms at n=10); (c) C12's role
sharpens — the crash screens measured single marches, but taming the storms needs the
ALL-PATHS excess bound: does ANY reduction path from a storm ever dip below the
linear-excess floor? The mountain machinery (paths must pass peaks) meets its real
test here. The space now has THREE dynamic regimes: normalizers (fast, ~96% overall),
corridors (rigid, decidable-by-pipeline), storms (branchy, open) — and the program's
central question lives entirely in the third.

### Stage 254: storm anatomy — the drop law, and C14

The storms are explosive but SHALLOW: across 150 random walks over 25 n=10 storms
(fuel 600, size cap 12k), the maximum path drop was 23 leaves and the median 5 —
against corridor drops of 200+ — while late branching width runs to hundreds of
redexes per state (median 167, max 444). Every choice in a storm goes up; the
regime's danger is width, not depth.

**C14 (THE STORM FLOOR), registered**: in the storm regime, path drops are bounded —
every reduction path from a storm term of size n has excess bounded by a slowly
growing g(n) (the data suggests g(10) ≲ 25). C14 is a decidability mechanism: if no
path from t ever dips more than D below its running peak, then deciding t →* u needs
only the finite state space of size ≤ |u| + D. The full decomposition of the central
question is now: normalizers (decide by normalization + confluence), corridors
(decide by the 245–248 pipeline, industrialized by C13), storms (decide by C14's
floor + bounded search). C12 remains the cross-regime linear form; C14 is its
storm-local, all-paths sharpening — and the all-paths quantifier is exactly what the
crash screens (leftmost-only) could not see. Verification pressure should go to
adversarial path search: can a C-heavy pocket inside a storm be steered into a deep
dig? 150 random walks say no; a targeted search is the next falsification attempt.

### Stage 255: THE LINE — `sc_mt5T_line`

Any two states reachable from the climber are comparable under reduction: the
reachable set is one infinite road, totally ordered. This is forcedness stated in its
purest order-theoretic form, and it makes every must-pass claim about the corridor a
one-liner: the peak at generation `j` and any later state are both on the road, so
whatever reaches past the peak went through it — there is nowhere else to go. Beside
`sc_mt5T_no_nf` (the road never ends), `sc_mt5T_reach_iff` (the road in closed form),
`scMt5TReach_decidable` (the road is searchable), and `sc_mt5T_flat` (the road never
deepens), the corridor's portrait is complete. Contrast is now the program's sharpest
image: a corridor is an infinite LINE; a storm is an infinite TREE that hardly ever
descends; and the calculus is confluent, so even the tree's branches all lead to the
same places.

### Stage 256: the adversary cannot dig — C14 fortified

The falsification attempt failed convincingly. Beam search steering always toward the
smallest successors (beam 10, 100 steps, sampled width 25) from storm peaks of
700–1500 leaves achieved digs of at most 26 leaves, median 6 — about two percent of
peak size, and no deeper than random walks found. The storm floor is not an artifact
of path choice: descent in a storm is structurally unavailable, not merely unlikely.
C14's mechanism firms up: S-duplication puts copies of every C-redex's future into
multiple positions, so firing a C (the only shrinking move) somewhere is always
outweighed by the S-material it leaves behind. A proof shape suggests itself — a
weighted size measure in which every storm-regime step is non-decreasing (the cargo
law's machinery, aimed at weights instead of counts). That is C14's formal target.
Must-pass note: the planned all-paths mountain theorem is SUBSUMED — THE LINE plus
the closed form already give it (there is only one road, so every route to the ground
passes the peak by definition).

### Stage 257: THE SWAPMILL — species two, core laws

The +4-period champions' engine, decoded and pinned. The counter is a bare C-chain
`C^k B`; descent is rider ping-pong (`sc_swap`, `sc_swap2`, `sc_swap_run` — one fire
per layer, two per net pair, riders home on even chains); the turnover is three fires
through the driver `S ((C S) C) C`, and its output is the FIRST mill's own driving
pattern `T·(C T)` plus the junk seed `C (C T)` (`sc_swap_turnover`). Two structural
surprises worth their weight: (a) both species run on the same `x·(C x)` self-
application pattern — the "mill" may be one phenomenon with many layer grammars, which
is exactly what C13 needs; (b) the driver lives inside the chain's ten-leaf base — the
engine carries its own blueprint, which is how the turnover can regrow the tower. Cost
ledger: species one pays 6 fires per 3-leaf layer; the swapmill pays 2 per 1 — the
leanest G-machine seen, and a hint that the G-machine space has a nontrivial
efficiency frontier (what is the cheapest possible eternal growth in {S,C}?).

### Stage 258: the swapmill cycle — regrowth is free

`sc_swap_cycle` composes turnover and descent parametrically in both the layer count
and the base: `3 + 2j` fires from the driver over `C^{2j} B` to `B·(C T)·(C (C T))` —
and `C T` is literally the next tower. Species two's regrowth mechanism is thereby
explained exactly: the turnover's junk seed `C (C T)` pays the growth, the descent
never touches the base, and the tower gains its layer by BEING WRAPPED, not by being
rebuilt. (`sc_swap_reseed` then shows the concrete base handing its riders forward in
two fires, exposing the 8-leaf junk block the probes saw in every valley.) Contrast
with species one, where each descent layer costs six fires of active machinery: the
G-machine efficiency frontier now has two data points, 6-fires/3-leaves and
2-fires/1-leaf, and the swapmill's trick — growth by wrapping — looks like the floor.
Methodology note for the placeholder rule: C-wrapped distinct tips LEAK in species-2
traces (the protocol peels C's); S-headed tips are the safe choice there.

### Stage 260: THE UNIT DROP LAW — the arithmetic beneath the storm floor

`sc_unit_drop`, the eighth wall: no {S,C} fire loses more than one leaf (S-fires
never shrink; C-fires drop exactly one). Total descent along any path is bounded by
its C-fire count. The companion probe closes the mechanism: late storm states hold a
median of NINE C-redexes (range 0–27) against S-stocks up to 77 — and the adversarial
dig maximum from Stage 256 was 26, matching the C-inventory almost exactly. The drop
budget IS the C-redex inventory. C14's formal target is now concrete: show that in
the storm regime the standing C-redex stock (plus whatever a descent exposes) stays
bounded — a potential-function argument over redex counts, with sc_unit_drop as its
per-step ledger. Between the unit drop law and the C-inventory, the storm floor has
gone from an empirical surprise to a mechanism with named parts.

### Stage 261: the descent speed limit, and the cold fragment

`sc_descent_speed` (the unit drop law, integrated): over `n` fires at most `n` leaves
are lost — the dual of the numeral speed limit, and a lower bound on the fire count of
any shrinking reduction. The probe behind it introduces THE COLD FRAGMENT — the
sub-relation of non-growing fires (C-fires, plus S-fires whose third argument is a
single leaf). Exact BFS over the cold fragment from storm states TERMINATES, fast:
cascades of at most 14 rounds, digs 0–13 with median 9 — the C-redex inventory again,
now as an exact computation rather than a correlation. The C14 proof shape that
emerges: any path's dig = cold moves it makes minus hot gains it suffers; cold supply
is consumed 1:1 and only hot fires (each costing ≥ +1) mint new cold moves — so no
schedule profits. What remains for a proof is the minting rate: bound how many cold
moves one hot fire can create (S duplicates x, so ≤ the C-redexes inside x plus one
boundary effect — a countable, local quantity). That is wall-shaped, and it is the
next formal target.

### Stage 262: THE COLD LAW — `sc_cold_law`, the ninth wall

C-fires never mint C-redexes: the inventory `scCInv` is non-increasing across every
C-fragment step. The proof's engine is a three-way shape ledger — atom `C`, C-headed
one-app, C-headed two-spine are mutually exclusive, and a C-fire converts the redex
it consumes into AT MOST one of these shapes one level up — so the invariant
`Cinv + isC3` never rises. With the unit drop law this gives the storm floor's cold
half: a C-only cascade from `t` consumes a non-increasing inventory while shrinking,
which is exactly why the exact cold-fragment BFS terminates in ≤ 14 rounds. C14's
remaining formal debt is now ONE lemma: the hot minting bound (an S-fire increases
`scCInv` by at most `scCInv x + 2`, x its duplicated argument) — measured, mechanism
understood (duplicated content + two boundary nodes), wall-shaped. The minting probe
also suggests the endgame inequality: hot fires pay ≥ +1 size for ≤ Cinv(x)+2 minted
drops, and Cinv(x) < |x|, so no reduction schedule can convert growth into unbounded
descent faster than linearly — C12's linear-excess law, derived rather than observed.

### Stage 263: THE MINTING LAW — `sc_minting_law`, the tenth wall

Across ANY fire, `scCInv + scIsC3` grows by at most the leaf growth plus two. The
S-fire's mint is dominated by its own duplication (`scCInv_succ_le_leaf`: inventory
sits strictly below leaf count — every redex owns a distinct application node), the
C-fire's is paid by the shape it destroys, and congruence rides on the cold law's two
facts, now proved for the full relation. **C14's per-step ledger is closed**: descent
comes only from C-fires (unit drop law), C-fires consume inventory without minting
(cold law), and inventory is minted only by growth, at a bounded exchange rate
(minting law). What separates this from a C14 PROOF is one integration step: summing
the ledger along an arbitrary path still lets inventory-purchased drops accumulate
linearly in total growth — the observed floor (digs ≈ initial inventory, ~2% of peak)
is TIGHTER than the walls yet imply. Either a sharper exchange-rate (the +2 boundary
mints seem almost never realized: median hot mint was 0) or a locality argument
(minted redexes sit inside the duplicated copy, where firing them cannot undo the
duplication that paid for them) is the remaining gap. That locality observation — the
mint is in the copy — is registered as the C14 attack vector.

### Stage 265: the mint is dig-inert — locality confirmed

The C14 attack vector, measured: across 96 hot fires in storm walks, the achievable
cold descent (`cold-dig`, computed exactly by BFS before and after each fire) rises
by MEDIAN ZERO — p90 two, maximum six — even though hot fires duplicate whole
subtrees of inventory. The minted redexes are nearly dig-inert: they sit inside the
duplicated copy where firing them shrinks the copy but cannot undo the duplication
that paid for it. Combined with the per-fire cost of ≥ +1 leaf, the exchange rate is
ruinous for any digging schedule: pay ≥ 1 up, receive ~0 (at most 6) of future down.
THE FLOOR THEOREM's empirical form: dig(t) ≤ cold-dig(t) + small·(hot fires), with
cold-dig(t) ≤ a few × scCInv(t). The formal version needs a copy-tracking argument
(where a redex lives relative to the duplication boundary) — registered as the C14
endgame, alongside the cheap integrated corollary of the minting law (path version,
next). C12 note: this locality is exactly why observed excess is linear with a SMALL
constant, not merely linear.

### Stage 266: the integrated minting law

`sc_minting_run`: over `n` fires, `Cinv + isC3` grows by at most the net leaf growth
plus `2n` — the tenth wall, summed along arbitrary paths. The per-path ledger is now
formal end to end: `sc_descent_speed` caps how fast leaves can fall; `sc_minting_run`
caps how fast the currency that pays for falling can be minted. The gap between these
walls and the observed floor (digs ≈ initial inventory) is the copy-tracking locality
argument, C14's endgame, next-arc scale.

### Stage 267: THE RIDDEN REVOLUTION — the swapmill's biography in one law

`sc_swap_revolution`: under ANY rider stack, `4j + 9` fires take the driver over an
even tower to the driver over the tower-plus-two, emitting the junk pair `(C C, J₁)`
in front of an untouched stack. The decomposition (cycle → reseed → trigger → second
descent → reseed → REBIRTH) exposed the engine's secret: the junk block
`J₁ = (C driver)(C C)` is a PARKED COPY OF THE DRIVER, and the rebirth fire unparks
it while the twice-wrapped old tower `C (C T)` becomes the new tower. Growth by
wrapping, rebirth by unparking, junk as self-blueprint — species two is not just
leaner than the mill, it is more elegant: the machine IS its own waste product. For
C13 this is the strongest structural evidence yet: both species' junk carries the
driver pattern, which suggests the general G-machine form is "driver + tower +
self-seeding junk," a shape one could plausibly ENUMERATE. The trichotomy pipeline
(forced → family → no-NF → decider) now has everything it needs at the swapmill's
core level; the remaining work is the anchor from scChamp170 and the forced/family
assembly — mill-1's Stages 242–248, replayed on species two.

### Stage 268: THE SWAPMILL IS ETERNAL — `sc_swap_eternal`, `sc_swap_unbounded`

The second engine's eternity, pinned: every revolution count is realized from any
tower height under any rider stack, and the fifteen-leaf pure seed has an unbounded
reachable set. Species comparison, now fully formal on both sides: the mill grows 3
leaves per layer at 6 fires each from a 12-leaf wild seed; the swapmill grows 2
leaves per revolution of `4j+9` fires from a 15-leaf pure seed whose junk is its own
driver. C13's evidence is now two complete engine cores. Remaining for the second
trichotomy: the forced version of the revolution (spine-3 argument — every swapmill
state is left-deep, same as the mill's), the chain family, and the champion anchor.

### Stage 269: THE FORCED SWAPMILL — the phases admit no alternatives

Every phase of the ridden revolution is now SCForced: the ping-pong run at every
layer (`scSwapRun_forced` — the alternating-rider chain with its last/ne plumbing),
and the four concrete phases each by one simp. Axiom footprint dropped to bare
[propext] for the phase lemmas. What remains for the second trichotomy is pure
assembly against generic theorems proved once at 244–248: compose the forced phases
into the forced revolution (SCForced_append × getLastD bookkeeping), define the
family, and instantiate family-membership, no-normal-form, and the bounded-scan
decider. Species two will then match species one theorem for theorem — C13's
strongest form of evidence short of the classification itself.

### Stage 270: THE FORCED REVOLUTION — `sc_swap_rev_forced`

All `4j + 9` fires of the swapmill's revolution are forced, composed from the five
phase chains with their handoffs. The remaining assembly for the second trichotomy is
now exactly what Stages 245–248 did for the mill: chain family (revolutions with
riders), the generic no-NF principle, family membership, size floor, bounded-scan
decider. Species two's laws needed no new ideas at any point past the probe — C13's
"one phenomenon, many grammars" reading strengthens with every reused lemma.

### Stage 271: THE SWAPMILL NEVER RESTS — the second corridor, exactly

Species two's portrait, completed to match species one theorem for theorem:
`sc_swapseed_no_nf` (no reachable normal form) and `sc_swapseed_reach_iff` (the
reachable set in closed form — one road). The entire 245+247 pipeline instantiated
verbatim: same generic principle, same membership theorem, same spine-3 invariant,
same rider machinery. What took nine stages for the mill took five for the swapmill
(257, 258, 267, 269–271), zero of them requiring a new idea — the strongest possible
demonstration that C13 is a CLASSIFICATION PROGRAM: find the engine, name the phases,
run the pipeline. Remaining for full parity: THE LINE, flatness, and the bounded-scan
decider for the seed (all mechanical), plus the champion anchor connecting scChamp170
to the pure engine. The G-machine picture after two species: driver + tower + junk
that is a parked copy of the driver — a shape begging to be enumerated.

### Stage 272: THE LINE, GENERIC

Total order is not a fact about the mill — it is a property of forced chain families,
and now a generic theorem (`sc_forced_family_line`). The swapmill's line came as a
one-line instance. The generic pipeline now contains: forcedness transport (riders,
carriers, stacks), family membership, no-normal-form, total order — every structural
theorem the first trichotomy needed, engine-independent. The per-engine residue is
exactly: the phase laws, the size ledger, and the decider's bounded scan.

### Stage 273: the second decider — parity achieved

`scSwapReach_decidable`: reachability from the swapmill seed, certified. Species two
now matches species one on every structural theorem: eternal, no normal form, closed-
form reachable set, total order, decidable reachability. The corridor program's
central claim — that corridors are DECIDABLE TERRITORY — now has two independent,
fully-machine-checked instances built from one generic pipeline. The remaining
species-specific item is the champion anchor (scChamp170 → the pure engine), and the
remaining structural item for the whole program is the storm floor (C14's copy-
tracking lemma). Then: assembly.

### Stage 274: THE CHAMPION NEVER RESTS — the anchor lands

`sc_champ170_no_nf`: the census's fifth drop-champion (a wild twelve-leaf term) has
no reachable normal form — anchored into the swapmill family in twenty-two forced
fires, then carried forever by the stack-generalized family (`scSwapFam` over any
inert base stack, a strictly more reusable form than the mill's hardcoded one). The
program now has TWO wild census terms with complete non-normalization proofs, built
from two engine species and one shared pipeline. C13's next probe target: the
remaining four n=12 champions (d211, d209, d206, d205) — species one, species two,
or a third grammar? The +6-period trio should be mills; d205's mixed signature is
the interesting one.

### Stage 275: the species census — grammars multiply, motifs repeat

Typing the five remaining n=12 champions against both pinned engines: NONE match
exactly — but their internals decompose into the SAME two motifs. d159 runs the
swap-driver `S ((C S) C) ·` with a richer layer grammar (`(C (C C))(C ·)` wraps) and
junk blocks that are whole tower snapshots — its stack is a staircase of shrinking
copies, a tape that records the engine's history. d211 is mill-family: its 249-leaf
core is woven from `scMillK` material. C13's refined picture: the G-machine SPACE is
generated by a small set of driver/layer motifs composed in different ways — species
are points in a grammar lattice, not isolated inventions. The classification program
should enumerate motif compositions, not machines.

### Stage 276: the floor probe — the inventory IS the dig, except when it's double

The sharpest C14 measurement yet: pairing each storm state's C-redex inventory with
its adversarially-achievable dig, TWELVE of fifteen match EXACTLY (margin zero) — the
inventory is not merely a bound but the realized value. The three exceptions (margins
−1, +5, +14) refine the law: hot fires can duplicate C-rich subterms and spend the
copies, roughly doubling the achievable dig in the worst observed case. The walls
explain the exchange precisely: each duplication of `x` costs `|x|−1 ≥ Cinv(x)`
leaves, so re-spent inventory is PRE-PAID — net descent below start ≤
`Cinv(t) + 2·(hot fires)`, where the `+2` is the boundary-mint allowance of the
minting law. C14's endgame is now exactly ONE sharpening: show the boundary mints
(measured median zero, max two) cannot be harvested indefinitely — either they are
S-guarded (the minted redex sits under an S that must fire hot to expose it, re-paying
the toll) or a κ-multiplicative floor (`dig ≤ 2·Cinv + c`) suffices for the bounded
search and can be proved by charging each re-spend to its duplication. The
decidability consequence is unchanged either way: peaks on any path to `u` stay below
`|u| + κ·Cinv + c`, and the state space under that bound is finite.

### Stage 277: the κ-floor falsified — duplication compounds

The falsification sweep worked as designed, against us: at n=12, digs of 48 against
inventory 11 (≈4.4×) and 25 against 6 (≈4.2×) kill both the additive and the
constant-multiplicative floors. The mechanism is compounding: a hot fire duplicates a
C-rich subterm, a second hot fire duplicates the copy, and each generation of copies
is spendable — dig grows like inventory times duplication DEPTH, not inventory times
a constant. **C14 is hereby restated (v2)**: the achievable dig from `t` is bounded
by a depth-weighted inventory — `Φ(t) = Σ over C-redexes of 2^(S-argument nesting)`
or similar — OR, more conservatively, the program should retreat to C12's original
bounded-intermediates form (peaks on any path from `t` to `u` bounded by a computable
`f(|t|,|u|)`), which the crash screens support with linear f and which suffices for
decidability by finite search. Perspective: even the worst observed dig is ~5% of
state size — the storm floor is real as a PHENOMENON; what fell is only the simplest
formula for it. The walls (unit drop, cold, minting) all survive untouched; they were
never strong enough to imply the constant floor, which is exactly why the probe could
falsify it without contradicting anything pinned.

### Stage 278: Φ falls too — and C12 becomes the single named gap

The depth-weighted potential died on the same state as the κ-floor: the fatal
duplications come from S-redexes that only COMPLETE later (an S waiting for its third
argument), invisible to any static count over the current term. This is not a defeat
so much as a clarification — the static-potential program was always a bid to prove
C12 locally, and its failure modes now map exactly onto why C12 is genuinely global.
Formal state of the endgame, now pinned: `scLinearExcess` (C12 as a Prop: some affine
endpoint-size bound covers some path between any reachable pair) and `sc_c12_decides`
(C12 ⟹ reachability decidable, via Stage 132's backbone). Everything the program has
measured supports C12 with small constants: crash screens (no drop past 211 at two
sizes), corridor ledgers (exact linear excess), storm digs (~5% of size). The
program's central question is, formally and precisely, C12's truth.

### Stage 279: the C12 landscape — a flat bulk with rare, affine mountains

Direct measurement of the quantity C12 bounds: for random starts at n=8–10, the
minimal path-peak needed to reach each target (iterative-deepening capped BFS over
548 reachable pairs) has MEDIAN EXCESS ZERO — most reachability facts need no climb
at all — and maximum 4. The mountains (f(8,8) ≥ 31, Stage 132's exhaustive minimax)
are rare tail objects invisible to sampling; the tail evidence lives in the crash
screens, which measured exactly the deep-drop terms and found excess bounded by
roughly 3|t| at both n=10 (exhaustive over corridors) and n=12. Synthesis: the C12
landscape is a flat plain with sparse mountains of observed-affine height, and every
mountain so far is an ENGINE (corridor structure — which the pipeline decides
independently). The refined attack: prove C12 restricted to the tame bulk (where the
walls plus normalization should give small bounds), and handle the mountainous tail
by C13's classification — decidability would then assemble regime by regime without
ever needing a uniform static potential. The missing heavy compute: exhaustive
minimax at n=10 to pin f(10,10) (the 6→8 jump was 1→23; corridor theory predicts
~3n ≈ 30–40, explosive growth would predict ≫100 — a discriminating experiment).

### Stage 281: THE DRIVER LAW — the first family-level theorem

`sc_driver_law` (axiom-free): the swap-driver's three-fire turnover is parametric in
its third slot — `S ((C S) C) X T ⟶³ (T (X T)) (C (X T))` for ANY `X`. The swapmill
is `X = C`; d159 (decoded: heavier slot `C (C C)`, +4-leaf layers, snapshot junk
that carries the driver motif in its base, revolution periods +4) is `X = C (C C)`.
This is what C13's classification should look like at maturity: not per-species
pipelines but family-level laws with species as instances. The driver motif's
universal grammar: pick a slot X, pick a layer grammar for the tower, and the
turnover, the self-application pattern, and the junk-carries-the-blueprint property
all come along. The enumeration attack on C13 now has its first axis.

### Stage 282: the discriminating experiment — mountain height plateaus

The exhaustive n=10 minimax landed: over ALL 4,978,688 ten-leaf terms, the maximum
excess (minimal path-peak minus target size, ten-leaf targets) is **20** — BELOW the
n=8 value of 23. The witness is a tight little mountain: `S S C (S ((C C)(S S C))) C`
must climb to 30 leaves before collapsing to a pure-C ten-leaf residue, through a
reachable set of just 70 states. (Caveats, recorded: the sweep skipped terms whose
capped reachable sets exceeded 90k states and used a 12-quiet-caps early stop —
mountains hiding inside heavy storms or with very slow approaches would be missed.)
The diagonal f-ladder now reads: excess(6)=1, excess(8)=23, excess(10)=20 —
PLATEAUING, not exploding. Combined with the corridor ladder (excess growing at
~0.32·|target| along engine structure), everything remains consistent with an affine
`f(n,m) ≈ m + 3n + c`. C12 has now survived: exhaustive diagonals at three sizes, the
corridor ladders, two crash screens, and the storm-dig program. The conjecture is as
strongly supported as probes can make it; what remains is proof, and the proof's
known shape is regime-by-regime assembly (bulk-normalization + engine-classification
+ the affine tail).

### Stage 283: the species-3 descent, and the ideonomy pass — the C13 grid

`sc_l3_descent` (axiom-free): d159's layer strips in four fires with riders home —
no parity, unlike the swapmill's ping-pong. Species 3's core is now two laws deep
(family driver law + own descent law), confirming the classification's economy.

**Ideonomy pass (due).** The C13 grid as it stands: an engine = (driver slot X) ×
(layer grammar L) × (junk policy). Observed points: the swapmill (C, bare C-chain,
junk-is-parked-driver), the mill (its own driver family — mill-K deserves the same
family-level treatment as the swap-driver got), d159 (C (C C), L₃, junk-is-tower-
snapshot). Generated leads, ranked: (a) derive the MILL's laws from a family law the
way the swap family now works — if both driver motifs admit slot-parametric laws,
the enumeration is two axes shorter; (b) the SLOT-X REVOLUTION: how much of Stage
267's seven-phase composition is X-generic? The reseed and rebirth used B's
concrete shape — parametrize B over the layer grammar and the whole trichotomy may
become a functor over the grid; (c) junk policies seem binary (blueprint vs
snapshot) — is that forced by the no-erasure wall? A snapshot IS the only other
thing the machine has to emit; (d) the grid predicts UNSEEN species — enumerate
small (X, L) pairs, synthesize seeds, and check which run; a predicted-then-found
species would be C13's strongest possible evidence.

### Stage 284: THE METRONOME — predict, synthesize, find, pin

The C13 grid passed the strongest test a classification can face: PREDICTION. Seeds
synthesized for unseen grid points behaved exactly as the grid says — the heavier
slot `X = C (C C)` runs eternal with +8-fire periods; igniting slots (`C S`, `S C`)
branch out of the corridor phase — and the grid point `X = C C` yielded a genuine
DISCOVERY: a fixed-period oscillator. `sc_metro_law`: seventeen fires return the
nineteen-leaf core EXACTLY, one junk pair emitted — a fixed point modulo emission.
`sc_metro_eternal`: pumping forever under any riders. Both theorems are FULLY
AXIOM-FREE — the metronome's eternity is pure computation, no propext, no
Quot.sound. Taxonomically this is a new dynamic class: mills climb (growing periods),
the metronome pumps (constant period) — the corridor phase contains both clocks that
tick faster and clocks that tick steadily, and the grid found the steady one before
any census did. C13's classification now has: two driver families, three layer
grammars, two junk policies, two period regimes — and a demonstrated ability to
enumerate its own unknown corners.

### Stage 286: the metronome's trichotomy — three portraits, three regimes

The third complete portrait (no normal form, closed-form reachable set, certified
decider), first-try green, one block — for a machine that did not exist in any
census and was found by asking the grid what lives at `X = C C`. The pipeline's
maturity is now measurable in stage-counts: mill nine stages, swapmill five,
metronome ONE. Portraits by period regime: climbing (mill, swapmill) and pumping
(metronome) both fall to the same generic theorems, which is evidence that the
pipeline axis of C13 (every corridor engine yields family/no-NF/decider) is
regime-independent. The classification's remaining empirical frontier: the mill-K
driver family (four undecoded champions) and the grid sweep at scale.
