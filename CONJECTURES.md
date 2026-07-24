# Conjectures

Census-generated claims, each with a status:
**open** / **proved** (link the theorem) / **refuted** (link the counterexample).
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

## C1: Smallest non-normalizing pure-S term — status: open
Census (fuel N=200) finds all S-terms with ≤6 leaves normalize; at 7 leaves,
2 of 132 terms exhaust fuel. Candidates (rendered, standard combinator
notation, left-associative application):

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
machine-checked resolution is the contribution claimed. The Slice 1
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

## C3: Growth-pattern regularities observed — status: open
Two observations from the fuel=200, n=1..12 run:

1. **Head shape of the smallest exhausted terms.** Both n=7 candidates are a
   head `S` applied to exactly 5 arguments (`spineLength` 5) — two more than
   the 3 arguments an `S`-redex needs to fire. (`S S S (S S) S S` = `S`
   applied to `S, S, (S S), S, S`; `S (S S) S S S S` = `S` applied to
   `(S S), S, S, S, S`.) Sample size is only 2 terms, so this is a weak
   signal, not yet checked against the fuller n=8 exhausted set (41 terms;
   this census run does not print more than the first exhausted size's
   candidates, capped at 10 — see `Main.lean`'s `censusLine`).

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
step-faithful `fwd`/`bwd` — never over bare encoding functions. The
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
existence is exactly C1 — so the unpinned cell tracks C1, not
universality, which is precisely why it was replaced).

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
three quantify over `Simulation`). SCOPE, restated from the Slice 2
section: this refutes STEP-FAITHFUL hosting under the pinned
`Simulation` class only — it does NOT resolve the Wolfram prize
question, whose informal universality admits broader, non-step-faithful
encodings. Against the table's own reference, `RS.Tag`, this cell
remains open — the same acyclicity mechanism would refute Tag→PureS for
any tag system with a genuine reduction cycle, not formalized here.

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

## C4: No single-rule first-order combinator basis hosts SK — status: open
`no_sim_SK_iota` refutes iota specifically, via strict growth. Conjecture:
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

## C6: Divergence density grows with size — status: open
Fraction of pure-S terms at exactly n leaves that exhaust fuel 200
(leftmost-outermost; fuel-outs are NOT divergence proofs — this is a
density of *fuel-exhaustion*, a proxy observable). Exhausted counts for
n=7,8,11,12 and totals for n=7,8,9,10,11,12 are as already recorded in
this file / LAB_NOTEBOOK.md; the n=9 and n=10 exhausted counts below are
pulled from LAB_NOTEBOOK.md's census-headline entry (`276 at n=9, 1484 at
n=10`, fuel 200) rather than recomputed — re-running the n=10 census
(4862 terms) is exactly the "runtime-prohibitive, stays fuel-bounded-census
from the original runs" case the brief flags, so it was not repeated.
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
growth keeps accelerating, levels off short of 1, or (per the C3 addendum
above) enters some different regime once the n≥10 `maxFinalLeaves`
plateau mechanism is at play. (Cheap to extend: rerun `lake exe ccp` at
higher fuel to test fuel-sensitivity of the table; not done this slice.)

Reproduce the total-count cross-check with:

```lean
#eval (sTerms 9).length   -- 1430
#eval (sTerms 10).length  -- 4862
```

(the exhausted counts themselves come from the `lake exe ccp 12 200` run
already on record — see the "Runs behind this file" note above and
LAB_NOTEBOOK.md's census-headline entry — not from a scratch re-run.)

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
  program was built to map.
- **The refutation mechanism, unified:** iota fell to strict growth
  (Stage 4); pure S falls to acyclicity (this slice). Both are instances
  of one pattern — a system whose reduction order admits no return trips
  cannot host a cyclic source under injective step-faithful encoding.
  C4's strictly-size-increasing class is one cause of no-return; τ-style
  termination of the isometric fragment is another. (C4's statement is
  unchanged; this remark widens the observed pattern, not the
  conjecture.)
