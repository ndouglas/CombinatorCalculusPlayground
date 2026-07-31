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
