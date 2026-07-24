# Lab Notebook — the Fable-vs-Lean meta-experiment

One dated entry per work session: what was attempted, what Lean resisted,
what automation could and couldn't do. This file is a first-class deliverable
(spec: if Stage 5 never terminates, the notebook is the result).

## 2026-07-23 — Stage 0

- Module split + census slice implemented: 9 tasks, 9 commits (~1 commit per
  task), each executed by a dispatched subagent with per-task review before
  the next task was dispatched.
- Proof friction encountered:
  - `stepOnce_sound` (Task 3): the plan's candidate script
    (`first | ... | simp_all`) failed because `simp_all` made progress
    without actually closing the descent-case goals. Fix: `fun_induction
    stepOnce t`, naming the binders explicitly in the descent cases. Proved
    by an Opus-tier agent.
  - `stepOnce` completeness / `stepOnce_isSome_of_step` (Task 4, the hardest
    proof in the slice): compiled on the *first* full attempt, by a
    Fable-tier agent. The `appR` descent case needed one extra step beyond
    the plan's script: `cases hst : stepOnce t <;> simp_all`. The plan's
    3-attempt escape hatch was never triggered.
  - `normalize_sound` (Task 5): the plan's induction-on-fuel candidate failed
    because the step count `k` wasn't generalized in the induction motive.
    `fun_induction normalize` worked, mirroring the Task 3 precedent — the
    second time in this slice that `fun_induction` succeeded where a
    hand-written induction principle didn't generalize enough on its own.
  - No `sorry` ever committed; zero-warning builds held throughout; every
    `#guard` passed as planned with one exception caught in pre-flight, not
    in a subagent run: a leftmost-wins guard in the plan itself expected
    `I x → x` in one step, when `I x` (i.e. `S K K x`) actually takes two
    steps to reach `x`. Corrected in the plan before Task 1 was dispatched.
  - Task 9 (this entry, the census runs themselves) hit its own piece of
    automation friction, worth recording as a tooling lesson rather than a
    proof one: `lake exe ccp 10 1000`, redirected straight to a file, was
    killed by a 10-minute timeout with **zero** output recovered — not
    because nothing had been computed, but because C stdio fully
    block-buffers stdout when it isn't a tty, so a `SIGTERM`'d process never
    flushes anything written to a redirected file. Wrapping the call in
    `stdbuf -oL -eL` (line-buffered) fixed recovery of partial output for
    subsequent runs. Separately, fuel=1000 turned out to be genuinely
    intractable at this term size within any reasonable budget — not a
    buffering artifact, since a fuel=1000 run at the *smaller* n=9 also
    exceeded 5 minutes partway through n=8 — so the census plan's fallback
    ("reduce fuel or size, say so") was exercised for real: the definitive
    numbers below come from `ccp 12 200` (fuel held at 200, size pushed to
    12), not `ccp 10 1000` as originally scripted.
- Census headline (see CONJECTURES.md for the full table and methodology
  caveats):
  - First fuel-exhausted terms appear at n=7 (2 of 132 terms, fuel 200);
    growth of the exhausted count is fast: 41 at n=8, 276 at n=9, 1484 at
    n=10, 6842 at n=11, 29337 at n=12 (of 58786 total n=12 terms).
  - No `CYCLE FOUND` line at any size, n=1 through n=12, fuel 200 — the
    S-cycle question stays open but unrefuted at these sizes.
  - Max reduction length among terminating terms (`maxSteps`) climbs from 15
    (n=7, n=8) to 174 (n=12) — reduction sequences get much longer well
    before any term fails to terminate at all.
  - Raising fuel from 200 to 1000 at fixed n=7 makes the fuel-exhausted
    candidates' final leaf count explode from 120112 to 25740409924 — real
    evidence of explosive (not merely slow) growth along those trajectories,
    though still not a divergence proof.
- Next: Stage 1 (confluence) / Stage 2 (conservation) / Stage 3 (taxonomy)
  are all unblocked per the DAG.

## 2026-07-23 — Stage 1: Confluence

- Church–Rosser for SK reduction proved via Par + complete development
  (Takahashi triangle): `Par`, `Par.rfl`, `Par.of_step`, `Par.to_steps`,
  `dev`, `Par.K_inv`/`Par.S_inv`, `Par.triangle`, `Par.diamond`, `Pars`,
  `Pars.strip`, `Pars.diamond`, `Steps.to_pars`/`Pars.to_steps`,
  `confluence`, `nf_unique` (Confluence.lean), plus `normalize_normal`
  (Census/Eval.lean) closing out the census certificate. 6 tasks, one
  commit per task, sorry-free throughout; zero deps held.
- Proof friction, task by task (per-task subagent reports and reviewer
  notes):
  - Task 1 (NormalForm move to Step.lean + congruence lemmas): candidate
    scripts worked verbatim — a pure refactor plus straightforward
    inductions.
  - Task 2 (`Par` + the Step/Steps sandwich): candidates also worked
    verbatim; independent review confirmed the Takahashi-form `S_red`
    (with `x` duplicated into the reduced term, not left as one copy) and
    that `Par.rfl` only needs induction on atoms and `app` — no redex
    cases required for reflexivity.
  - Task 3 (`dev`, the complete development): compiled on the first
    attempt with all eight hand-derived match-arm guards passing; no
    guard corrections needed.
  - Task 4 (`Par.triangle`, the summit of the stage): proved on the first
    full attempt by a Fable-tier agent. The real friction wasn't the
    induction shape but the plan's helper-lemma sketches — `Par.K_inv`/
    `Par.S_inv` were written assuming bare `K`/`S` would resolve to the
    `Term` constructors, but inside the `Par` namespace bare `K`/`S`
    resolve to `Par`'s own constructors instead, so the lemma statements
    needed explicit `Term.K`/`Term.S` qualification. Once qualified, the
    app-case's nested redex inversions (two levels of `cases hl with`
    to peel back to the K- or S-head) closed by definitional equality —
    no extra `dev`-rewriting steps were needed beyond the `simp only
    [dev]` already in the sketch.
  - Task 5 (the ladder: `Pars`, `Pars.strip`, `Pars.diamond`,
    `Steps.to_pars`/`Pars.to_steps`, `confluence`, `nf_unique`): all
    seven candidate scripts compiled verbatim, including the one piece
    flagged as risky beforehand — `Pars.strip`'s induction generalizing
    over the one-step side (`generalizing u`) while inducting on the
    many-step side. `#print axioms confluence` came back `[propext]`
    only, independently re-verified in this task's review.
  - Task 6 (`normalize_normal`, this entry): the brief's `first | ... |
    simp_all | simp_all` sketch was replaced with named `fun_induction`
    cases before ever trying the catch-all — Stage 0 already burned that
    lesson twice, so it wasn't re-litigated here. Mirroring
    `normalize_sound`'s four named cases (`case1`..`case4`) matched
    the goals exactly on the first try: the success arm reduces directly
    to `stepOnce_none_normal`, the recursive arm is the IH applied to the
    inner equation (`ih hrec`, matching `normalize_sound`'s
    `ih hrec`/`Steps.tail` pattern exactly), and the two fuel/propagated-
    `none` arms are `simp at h`. Zero-warning build on the first full
    compile of the real (non-sorry) proof — no red/fail cycle beyond
    the initial `sorry` placeholder.
- The sandwich (Step ⊆ Par ⊆ Steps) and the census payoff
  (`normalize_normal` + `nf_unique`) landed as planned, no deviations
  from the task DAG or the stated theorem signatures. `#print axioms
  normalize_normal` reports `[propext, Quot.sound]` — the `Quot.sound`
  is not new to this stage; it's inherited from Stage 0's
  `stepOnce_isSome_of_step` (via `stepOnce_none_normal`), which already
  carried it. `confluence` and `nf_unique` themselves stay at
  `[propext]` only, unaffected.
- Next per the DAG: Stage 2 (conservation laws) and Stage 3 (taxonomy)
  both remain unblocked.

## 2026-07-23 — Stage 2: Conservation laws

- The S-fragment's conservation story, machine-checked in `SFragment.lean`:
  `KFree`/`kFree`/`kFree_iff` (K-freeness, executable twin, and their proven
  agreement), `KFree.of_step`/`of_steps` (closure under reduction),
  `leafCount_pos`/`leafCount_le_of_step`/`of_steps` (no erasure),
  `cycle_leafCount_eq` (a bonus constraint on C2), and `SNF`/`SNF_iff` (the
  shape of K-free normal forms). Five tasks, one commit per task, sorry-free
  throughout.
- Proof friction, task by task:
  - Task 1 (`KFree`/`kFree`/`kFree_iff`): candidate scripts worked verbatim.
    The one real snag wasn't in the proof but in the plan's own docstring —
    the reviewer caught a citation error: "Church–Kleene 1936" misattributed
    the λI-calculus's total-completeness result. Corrected to Church 1941 /
    Barendregt §9.5, and propagated across the spec, the plan, and the
    `SFragment.lean` module docstring by the controller before the next
    task was dispatched.
  - Task 2 (`KFree.of_step`/`of_steps`, closure under reduction): candidates
    also worked verbatim. The `K_red` case is the interesting one — it
    closes not by doing anything, but by genuine inversion-to-absurdity:
    a K-free term can't contain the `K` a `K_red` step requires, so
    `cases hk`/`cases hl`/`cases hK` bottoms out in a case with no
    constructor to match, discharging the goal for free.
  - Task 3 (no-erasure: `leafCount_pos`, `leafCount_le_of_step`/`of_steps`):
    one real deviation from the brief. The plan's closers for the `appL`/
    `appR` descent cases called for `Nat.add_le_add_right`/`_left` to lift
    the inductive hypothesis across the shared addend; both failed as
    written, because `simp [leafCount]` had already cancelled the shared
    addend out of the goal before the lemma could apply to it. Bare
    `exact ih` closed both cases once that was noticed.
  - Task 4 (`SNF`/`SNF_iff`, the fiddly one): first-try success on the
    strongest model available, with case-nesting never exceeding depth 2.
    `#print axioms SNF_iff` comes back with ZERO axioms — not even
    `propext` — independently re-verified by the reviewer. The instructive
    moment was in `SNF.normal`'s inversion: Lean's elimination on indexed
    families silently discards cases whose constructor's argument-count
    (pattern depth) can't match the shape at hand, so the `K_red`/`S_red`
    redex cases never even needed to be written out as absurdities inside
    the `app1`/`app2` branches — they were dismissed before the `cases s
    with` block had to consider them, leaving only the `appL`/`appR`
    structural cases to actually discharge against the IHs.
  - Task 5 (`snf` Bool twin + census guards, this entry): candidate
    scripts weren't the mechanism here — `snf` is a plain executable def,
    not a proof, and its epistemic status is deliberately weaker than
    `kFree`'s: `snf ↔ SNF` is NOT proven, by design, only cross-validated
    against the certified `stepOnce` by a `#guard` over all 42 six-leaf
    K-free terms. That agreement guard passed on the first try, with no
    adaptation needed — the tuple-lambda guard syntax from the brief
    (`fun (a, b) => ...` over `tr.zip tr.tail`) also compiled as written,
    no `⟨a, b⟩` rewrite required.
- Running two-stage theme, now visible across both stages: candidate
  scripts for structural inductions (KFree closure, leaf monotonicity,
  the SNF shapes) survive largely verbatim; in both Stage 1 and Stage 2,
  each stage's single hardest proof (`Par.triangle` in Stage 1, `SNF`'s
  characterization in Stage 2) has landed on the first attempt when run
  on the strongest model, with the real friction concentrated instead in
  smaller things: a misattributed citation, a `simp` that already did a
  lemma's job for it, an indexed-family elimination quietly pruning cases
  nobody had to write.
- Next per the DAG: Stage 3 (taxonomy) is unblocked; C1/C2/C3 (see
  CONJECTURES.md) all remain open, with C2 now carrying a proven
  size-preservation constraint on any hunted cycle.

## 2026-07-23 — Stage 3: The universality taxonomy

- The universality definitions are now formal objects: `RS.lean` (abstract
  rewriting systems, generic `Steps`/`Conv` closures, instances `RS.SK`/
  `RS.PureS`/`RS.Tag`), `Universality/Defs.lean` (`Simulation`,
  `PreservesNormalizes`/`PreservesConv`, `UniversalReach`/`UniversalNorm`/
  `UniversalConv`), `Universality/Taxonomy.lean` (the implication lattice:
  `RS.SK_churchRosser`, `Simulation.conv_preserve`/`conv_reflect`/
  `preservesConv`/`normalizes_preserve`, `Simulation.toUniversalConv` — renamed from `UniversalReach.toUniversalConv` by the final-review fix, see addendum).
  Six tasks, sorry-free throughout; several tasks carried additional
  review-fix commits (comment precision, the .rec why-comment).
- Proof friction, task by task:
  - Task 1 (warm-ups: `snf_iff_SNF`, `SNF.spineLength_le`): both candidates
    compiled verbatim on the first try. The catch-all case everyone was
    braced for — `fun_induction snf`'s `case4` (the shapes `SNF` can't
    inhabit) — was the feared fight-site carried over from Stage 0/1; it
    never materialized as an explosion. `fun_induction` produced exactly
    four clean cases, mirroring `snf`'s four match arms, and the planned
    closer dispatched `case4` in one shot. `#print axioms snf_iff_SNF`
    reports `[propext, Quot.sound]` (inherited, same trail as
    `stepOnce_isSome_of_step`); `SNF.spineLength_le` reports `[propext]`
    only. Separately, review caught a stale comment in `Enumerate.lean`
    still describing `snf ↔ SNF` as unproven; fixed. The controller then
    went a step further and tightened the wording to state the snf/
    stepOnce agreement as the corollary chain it actually is — it needs
    `snf_iff_SNF` plus `SNF_iff` plus `stepOnce`'s own soundness/
    completeness certificates, and only holds for K-free terms.
  - Task 2 (`RS` interface): the plan's own prose miscounted its own code
    block — it said "six lemmas," the stubbed block (and the candidates)
    contained seven (`Steps.single`/`trans`, `Conv.of_steps`/`trans`/
    `snoc_fwd`/`snoc_bwd`/`symm`). The implementer followed the literal
    code, which is authoritative, and flagged the miscount rather than
    silently absorbing it. The toy `countdown` sanity examples needed
    `@[reducible]` on the local `RS` def plus explicit type ascriptions
    (`RS.Steps.refl (0 : countdown.Carrier)`) before numeral elaboration
    would resolve through a concrete instance — an artifact of the toy
    example, not of the `RS` interface itself.
  - Task 3 (instances `RS.SK`/`RS.PureS`/`RS.Tag`): the real Lean friction
    of this stage. `induction` on `RS.Steps` FAILS at a concrete carrier
    (`RS.SK.Steps`, `RS.PureS.Steps`) with an `mkElimApp` "expected first
    3 arguments of motive" error — the same tactic works fine when the
    `RS` is a bound variable (as in `RS.Steps.trans`), so the motive
    generator only chokes on a concrete literal. `unfold`,
    `induction … using RS.Steps.rec`, and `induction … with` all hit the
    identical error. Workaround: drive the recursor by hand
    (`h.rec (fun a => _root_.Steps.refl a) (fun s _ ih => ...)`), commented
    at both call sites as a regression trap for future readers who reach
    for `induction` there. The reviewer hand-verified both motives
    independently. The subtype `refl` case in `PureS_steps_iff` — flagged
    beforehand as a likely second fight-site needing `Subtype.ext` — closed
    for free instead: `⟨t, ht⟩` and `⟨t, hu⟩` are definitionally equal
    because `KFree` is a `Prop` (definitional proof irrelevance), exactly
    as the plan had predicted as the optimistic case.
  - Task 4 (`Universality/Defs.lean`): byte-exact against the brief, first
    try, zero deviations. Reviewer's mathematical audit (not just a diff
    check): `bwd`'s image-restricted quantification (reachability between
    encoded states, not encoded-to-arbitrary) is the right strength for
    blocking the answer-smuggling form of the 2007 dispute; the
    reflexive-`fwd` slack is confined to self-loops and doesn't leak into
    anything provable; even a degenerate one-state source still forces an
    antichain-shaped demand on the host under `dec_enc`. Conclusion: the
    definitions are not accidentally vacuous.
  - Task 5 (`Universality/Taxonomy.lean`, the lattice): all 8 candidates
    compiled verbatim (the brief's prose miscounted again — "seven" vs. 8
    theorem statements in its own code block, same pattern as Task 2;
    followed the code). Axiom audit: `RS.SK_churchRosser` carries
    `[propext]` (inherited from Stage 1's `confluence`); the generic
    lattice results audited directly — `Simulation.preservesConv` and
    `UniversalReach.toUniversalConv` (since renamed `Simulation.toUniversalConv`, see addendum) — depend on ZERO axioms.
  - Task 6 (this entry): the definitions ledger in CONJECTURES.md and this
    notebook entry. All cited theorem/instance names re-verified by grep
    against the actual tree before writing, per the brief's instruction.
- Running theme, three stages into this taxonomy work now: plan candidate
  scripts survive close to verbatim at the variable-abstraction level
  (`{A : RS}`-scoped lemmas, generic inductions); concrete-instance
  elaboration is consistently where Lean pushes back — numeral
  elaboration through a reducible local def (Task 2), the `mkElimApp`
  motive bug on `induction` at a literal `RS` (Task 3). Both stages'
  hardest-looking proof sites (the `snf` catch-all, the subtype `refl`)
  turned out easier than feared; the actual fights were elsewhere.
- Design decision, registered rather than formalized: computability of
  `enc`/`dec` in `Simulation` is NOT internally pinned. Every Lean `def`
  is computable by construction, but that is a metatheoretic fact about
  the ambient language, not a hypothesis these definitions can state or
  test from inside a zero-dependency development. A full internal answer
  to that half of the 2007 dispute would need a computability theory in
  the repo; short of that, the honest move is to say so in the docstring
  and the ledger rather than either silently assuming it or omitting the
  gap.
- Next per the DAG: Stage 4 (closing `UniversalReach`/`UniversalNorm`/
  `UniversalConv` cells for `RS.SK` against `RS.Tag`, per the ledger) is
  unblocked. C1/C2/C3 remain open.

### Addendum, 2026-07-23 — whole-branch review caught two Critical definitional flaws

- A final review of the whole branch (as opposed to the per-task reviews
  above) found two Critical problems that every per-task review had
  passed:
  1. `UniversalNorm`/`UniversalConv` quantified over a BARE encoding
     function, and that makes them classically trivial: a classical
     oracle encoder — decide the source term's fate, ship a canned
     answer — witnesses the bare property for ANY source system, which
     the reviewer machine-checked. Fixed by making all three Universal*
     definitions quantify over `Simulation` (step-faithful, decodable);
     the trivialization itself is now IN the tree as a negative control
     (`bareEncNorm_trivial`, Universality/Defs.lean), so the definitions
     can't be quietly re-loosened without someone noticing what the
     pinning buys. (The lattice edge was also restated at the witness
     level — `Simulation.toUniversalConv` replaces the ∀-image-closure
     `UniversalReach.toUniversalConv` — so Stage 4 can use it with one
     good simulation in hand.)
  2. `TagSystem` fixed the alphabet to `Bool` and varied only the
     deletion number m, while citing Cocke–Minsky 1964 — which is about
     deletion-number-2 tag systems over ARBITRARY finite alphabets, a
     class the `Bool`-fixed structure does not cover. Fixed by
     generalizing the alphabet to a `Sym : Type` field; the sanity
     examples instantiate `Sym := Bool`.
- Why per-task review couldn't see these: each task matched its brief
  exactly — the flaws lived in the plan's definitions themselves, and
  only a review holding the whole branch up against the external
  literature and against adversarial witness constructions had the
  altitude to catch them.

## 2026-07-23 — Stage 4: Calibration (completeness proven, iota refuted)

- The headline, worth stating plainly because it's the point of the whole
  census-first method: pre-planning analysis PREDICTED the iota
  refutation before a single line of proof code existed — the size
  argument (every first-order ι-step grows leaf count by +8, while SK has
  a genuine reduction cycle) was written into the plan up front. The plan
  then built a STOP gate around it: Task 4's `#guard` probes had to
  confirm the growth numbers empirically, cheaply, before any proof
  effort was spent. The probes passed. The proofs then landed on the
  FIRST full attempt — the third stage overall (after Stage 1's
  `Par.triangle`, Stage 2's `SNF` characterization) where this project's
  summit proof compiled first-try on the strongest model available.
- Task 1 (simulation algebra: `Simulation.id`, `Simulation.comp`,
  `UniversalReach.of_sim`): candidate scripts worked verbatim.
- Task 2 (`TermV`, `Bracket.lean`'s term layer): byte-exact transcription
  from the brief. Reviewer verified the four closure lemmas
  (`StepsV.trans`/`congL`/`congR`/`congApp`) are honest mirrors of
  `Step.lean`'s `Steps.trans`/`congL`/`congR`/`congApp` — same shape,
  same proof pattern, ported to the variable-carrying syntax.
- Task 3 (`combinatory_completeness`, `bracket_beta`): the REAL fight of
  the stage. `occurs_bracket`'s `var` case needed Nat-`beq` bookkeeping
  that a naive `simp` couldn't close cleanly — early attempts either left
  goals open or triggered the `unusedSimpArgs` linter flip-flopping under
  `<;>` (an arg needed in one branch of the case split was flagged unused
  in the other). Closed with `grind` — the first `grind` use in this
  project — which pulls `[Classical.choice, Quot.sound]` into
  `combinatory_completeness`'s axiom trail (confirmed by `#print axioms`:
  `[propext, Classical.choice, Quot.sound]`). The reviewer probed three
  alternative closers looking for a choice-free route; none was cheap —
  a manual `[propext]`-only proof of the same lemma is possible but is
  deliberate additional work, logged here for future triage rather than
  done under this stage's budget. `bracket_beta` itself, the theorem the
  stage actually needed, stays at `[propext]` only — the `grind` cost is
  fully contained in `occurs_bracket`, a supporting lemma.
- Task 4 (`Iota.lean`, the census-style probes): byte-exact against the
  brief. One empirical surprise: `fun_induction` on `stepOnce` for
  `IotaTerm` produced case arities that didn't match `Eval.lean`'s
  `Term`-level precedent — `IotaTerm` has one redex pattern
  (`app .iota x`) where `Term` has two (`K_red`/`S_red`), so
  `fun_induction`'s case count came out different from what the Stage-0
  memory of "that tactic gives four cases" predicted. Discovered
  empirically rather than by re-deriving it on paper first; corrected
  once the actual case list was in front of us.
- Task 5 (`Universality/Calibration.lean`, the refutation): both risk
  sites flagged ahead of time turned out quiet. `iota_steps_le`'s `.rec`
  call needed no explicit motive beyond what the brief's sketch already
  supplied — the concrete-instance `induction`-fails-on-`RS.Steps` bug
  from Stage 3 was worked around the same way (hand-driven `.rec`), and
  the motive Lean needed matched the plan's hand-derived one on the first
  try. The `Wdup`/`omegaSK`/`Mcycle` reduction-cycle chains
  (`omega_to_M`, `M_to_omega`) elaborated exactly as written, each step
  firing on the definitional unfolding the plan predicted (`I = S K K`
  behind the scenes). `omega_ne_M` closed by plain `decide` on the
  derived `DecidableEq` — no `native_decide` needed or used.
- Axiom audit (`#print axioms`, re-run directly against the built tree
  for this entry): `bracket_beta` → `[propext]`;
  `combinatory_completeness` → `[propext, Classical.choice, Quot.sound]`
  (the `grind` cost, see Task 3 above); `no_sim_SK_iota` /
  `iota_not_universal_for_SK` / `iota_step_lt` / `iota_steps_le` → all
  `[propext, Quot.sound]` (the `Quot.sound` here is the same inherited
  trail riding `RS.Steps`/`RS.SK_steps_iff` since Stage 3, not new).
- Meta-observation for the notebook: this is the first stage where the
  PLAN itself did original mathematics — the iota refutation wasn't a
  known result being formalized, it was discovered during pre-planning
  analysis of the leaf-count arithmetic — rather than a formalization
  exercise over an already-known theorem. The census-first gate (probe
  the growth numbers cheaply before committing proof effort) is exactly
  what made that safe: if the `#guard` probes in Task 4 had disagreed
  with the pre-planning arithmetic, the stage would have stopped there
  instead of chasing a false refutation through two proof-heavy tasks.
- How this differs from the Stage 3 atlas's own expectation: the
  Definitions ledger going into this stage listed `RS.SK` vs. the
  tag-system reference as the Stage 4 target, with iota mentioned only as
  a secondary calibration point ("under the taxonomy"). What actually
  shipped is the reverse emphasis — Tag→SK reach stays open (Stage
  5-adjacent), while iota went from "a basis to eventually calibrate
  against" to "the stage's proven negative result," entirely because the
  size argument, once looked at directly, forced the conclusion before
  any Tag-system work was even started.
- Next: `lake build` clean, zero warnings; ledger and this entry committed
  together per the task brief. Two items explicitly registered rather
  than closed this stage (see CONJECTURES.md's deviation register):
  Waldmann 2000's normalization-decidability result remains
  cited-not-formalized, and the λI ({S,B,C,I}) stretch goal was not
  attempted.
- Final review, two notes carried forward for Stage 5: (a) the
  `no_sim_SK_iota` refutation never uses `Simulation.bwd` (the
  host-steps-imply-source-steps direction) — it goes through on `enc`,
  `fwd` (via `fwd_steps`), and `dec`/`dec_enc` (via `enc_injective`)
  alone, so it survives any future weakening or removal of `bwd` from
  the `Simulation` class for free; this could be stated as an explicit
  lemma later, but isn't needed now. (b) the
  suggested first nontrivial `Simulation` inhabitant for Stage 5 is the
  PureS→SK inclusion (`enc := Subtype.val`, `bwd` via the `KFree`
  closure) — cheap to build, and landing it would blunt any
  "`Simulation` is near-vacuous" objection before harder positive work
  (e.g. Tag→SK) is attempted.

## 2026-07-24 — Stage 5, Slice 1: bounded reachability

- Where this slice came from: an ideonomy shake over the program's open
  questions surfaced a latent asset that had been sitting in the tree
  since Stage 2 — `leafCount_le_of_steps` (no K-free step ever shrinks a
  term) doesn't just explain why erasure-based encodings fail, it also
  confines any path from `t` to `u` inside the FINITE universe of terms
  with at most `leafCount u` leaves. That is a bounded-search argument
  for reachability decidability, for free, off a lemma proved for an
  unrelated reason two stages ago. The slice plan was built around
  formalizing that observation and searching honestly for where it runs
  out (the abstract `Decidable` instance; C2's theorem-level form).
- Task 1 (`succs` + the CENSUS-FIRST STOP gate): all four probes (A ×2,
  B, C) passed on the first build, confirming the bounded-path premise
  empirically before any proof effort was spent — the gate did its job
  by finding nothing wrong, which is itself useful information. The one
  real slip was in the plan's own prose: Probe C's comment described a
  stronger one-step-closure claim than what its actual guard checked;
  the controller caught and reworded it to match before Task 1 was
  dispatched, rather than letting a probe's comment silently overstate
  what it verifies.
- Task 2 (`succs_sound`/`succs_complete`): `fun_induction` — the tactic
  that had repeatedly bailed out proof friction in Stages 0-3 — turned
  out to be unavailable here because `rootRed` isn't a recursive
  function (it's a single non-recursive match), so plain `unfold` +
  `split` did the job instead. The more interesting friction was a
  reviewer catch, not an implementer one: the reviewer traced Lean core
  source to confirm `++`'s left-associativity (and the resulting
  `List.mem_append` nesting), which corrected an assumption baked into
  the controller's own prompt for this task rather than into the
  candidate proof script.
- Task 3 (`closureStep`/`boundedClosure` + membership lemmas): Lean core
  4.28 has no `mem_eraseDups`, so a small helper
  (`mem_of_mem_eraseDups`, length-recursive) had to be written from
  scratch. More consequentially: the plan's own fuel-0 guard instance
  would have FAILED as written — the closure it names saturates
  instantly at that bound, so the guard's expected verdict was wrong —
  and the implementer's replacement instance was independently
  hand-verified as necessary by the reviewer before being accepted.
- Task 4 (`mem_of_saturated`/`reachable?_correct`, the slice's summit):
  compiled on the first full attempt by a Fable-tier agent. The one
  adjustment needed was procedural, not mathematical: Lean 4's
  `induction h` on the `Steps` hypothesis auto-reverts `KFree t` into the
  motive (it depends on the moving left endpoint) and reintroduces it as
  an inaccessible hypothesis per case, so the `tail` case needed
  `rename_i hk` to reclaim it before continuing — no `generalizing`
  clause was needed, contrary to what the brief's caution suggested might
  be required.
- Task 5 (`onCycle?` + the ≤6-leaves cycle-freedom guard): this slice's
  best epistemics moment, and it was the IMPLEMENTER, not a downstream
  reviewer, who caught it. The plan's draft prose called the guard's
  result "kernel-checked"; the implementer read Lean 4.28's own doc
  comment for `#guard` (`Init/Guard.lean` — "this uses the untrusted
  evaluator, so `#guard` passing is *not* a proof") and flagged the
  mismatch before it shipped. Fixed: the guard's comment now says
  "evaluator-checked... NOT a kernel proof," and two genuine kernel-level
  theorems were added alongside it for concrete 4- and 5-leaf instances
  (`S S S S`, `S S S S S`), each via `succs_complete` + `by rfl` +
  `reachable?_correct`, so the file carries both an honest
  evaluator-level sweep and real per-instance kernel proofs, clearly
  distinguished. The stretch theorem (`no_small_cycle`, the general form
  over `⟶⁺`) was attempted 3 times and escape-hatched exactly where the
  brief had predicted it might be: it needs an `sTerms`-completeness
  theorem that doesn't exist, and attempting it further exposed a deeper
  reason why not — `sTermsTable`'s `Id.run do`/`Array`/range-loop
  definition isn't `rfl`/`decide`/`simp`-transparent even at the smallest
  instance (`sTerms 1 = [S]` doesn't close by plain `rfl`). Registered in
  CONJECTURES.md as a blocked chain, not silently dropped.
- Task 6 (the convertibility trichotomy: `Joinable`, `conv_iff_joinable`,
  `joinable_normalizes`, `joinable_iff_nf_eq`): all three theorems land at
  axiom footprint `[propext]` only. The one bookkeeping note: `nf_unique`'s
  actual orientation (`u = v` from `t ⟶* u`, `t ⟶* v`, both normal) gave
  `joinable_iff_nf_eq`'s forward direction directly — `nt = nu` in exactly
  the goal's orientation — where the brief's rough candidate had reached
  for a `.symm ▸ rfl` that turned out unnecessary. Simpler than sketched,
  not harder.
- Task 7 (`pureS_in_SK`, the `Simulation` class's first nontrivial
  inhabitant): compiled close to verbatim, `[propext]` only. Review
  caught a real gap, not a cosmetic one: the def's doc comment claimed
  the inclusion was "nontrivial" but nothing in the tree exhibited an
  actual `PureS` step — the claim was asserted, not evidenced. Fixed by
  adding a concrete machine-checked witness
  (`RS.PureS.step ⟨S S S S, ...⟩ ⟨(S S)(S S), ...⟩ := Step.S_red S S S`)
  and by replacing a vacuous "composes with itself" example with a
  genuine composition through `Simulation.id`.
- Axiom audits across the slice, `#print axioms` re-run against the built
  tree: `mem_of_saturated`/`reachable?_correct` → `[propext, Quot.sound]`
  (the `Quot.sound` is inherited, not new); `conv_iff_joinable`/
  `joinable_normalizes`/`joinable_iff_nf_eq` → `[propext]`; `pureS_in_SK`
  → `[propext]`. No `sorry`, no `native_decide`, no `Classical.choice`
  anywhere in the slice.
- Meta: this is the third time in the program that a review-or-shake
  process — not the prover — did real research work. First was Stage 3's
  whole-branch review catching the `UniversalNorm`/`UniversalConv`
  trivialization and the `TagSystem` alphabet flaw, both invisible to
  every per-task review that had already passed. Second was this slice's
  own premise: the ideonomy shake surfacing the bounded-path argument
  latent in Stage 2's monotonicity lemma before any Reachability code
  existed. Third is inside this same slice — an episode of three distinct
  within-slice catches, counted here as one event: Task 3's fuel-0 guard
  was caught as wrong and replaced under reviewer hand-verification,
  Task 5's implementer caught the plan's own "kernel-checked" overclaim
  against Lean's own `#guard` documentation, and Task 7's review caught
  an asserted-not-evidenced nontriviality claim. (The census-first STOP
  gate, by contrast, CONFIRMED the premise rather than catching an error
  — it did its job by finding nothing wrong, and belongs in a different
  column of the ledger than the catches.) None of these were prover failures — every candidate proof
  script that reached the kernel, reached it cleanly — the friction was
  entirely in catching what the plan's prose claimed versus what the
  code and the trusted kernel actually established. The process keeps
  finding the gaps between what's true and what's merely asserted; that
  is the slice's real product, alongside the theorems.

## 2026-07-24 — Stage 5, Slice 2: the isometric fragment (C2 resolved)

- Where this slice came from: an ideonomy pass over the program's open
  questions, this time explicitly cross-domain — the general technique of
  proving term-rewriting termination via a polynomial (weighted)
  interpretation was brought to bear on C2's cycle question, rather than
  growing out of a lemma already sitting in the tree (Slice 1's origin
  story). The head-weight measure τ was derived on paper first: each
  leaf's weight doubles per left-edge on its root path, so an S-redex
  firing at the head burns weight even when leaf count is flat. The
  arithmetic (τ(S S S S) = 15, τ((S S)(S S)) = 9, a drop of exactly 6) was
  hand-checked twice independently before Task 1 was dispatched, and the
  whole slice was built behind a STOP gate: no proof effort until cheap
  `#guard` probes confirmed the arithmetic empirically.
- Task 1 (`tau` + the STOP-gate probes): both probes passed on the first
  build. Probe A (τ strictly drops on every size-preserving successor
  over all ≤6-leaf pure-S terms) held unweakened. Probe B (the root
  isometric redex drops τ by exactly 6) was checked for non-vacuousness
  with a scratch probe outside the tracked tree: exactly one size-4
  pure-S term matches the root-redex pattern, and it is `S S S S` — the
  classic case the file's header comment names — so Probe B genuinely
  exercised the claimed arithmetic rather than passing on an empty case.
- Task 2 (`tau_pos`, `KFree.leafCount_eq_one`, `tau_lt_of_isometric_step`):
  the brief's named-binder `cases` syntax for the K-freeness lemma
  (`| app (t := l) (u := r) hl hr`) is not valid Lean 4 `cases` syntax;
  fixed by matching `| app hl hr` and naming the subterms afterward with
  `rename_i l r`. The real catch was the reviewer's, not the
  implementer's: a scratch `#print axioms` run showed
  `tau_lt_of_isometric_step` pulling in `Classical.choice`, traced by
  bisecting the proof's `simp` call sites down to the `appL`/`appR`
  congruence cases — the default `simp` set (not the hand-written
  arithmetic) was the source. Swapping `simp [leafCount]`/`simp [tau]`
  for `simp only [leafCount]`/`simp only [tau]` at those four call sites
  eliminated the choice dependency; re-audited at `[propext, Quot.sound]`
  only. Fixed within the same task, before the commit landed.
- Task 3 (`tau_lt_of_steps_size_eq`, `no_pure_S_cycle` — C2 itself): the
  first full attempt at this theorem. The new proofs use no `simp` at
  all (`omega`, `rcases`, `rw`, term-mode), so no choice-leak risk arose
  here in the first place. The brief's equality-orientation warning
  proved accurate: in `no_pure_S_cycle`'s case split the size-preserving
  disjunct arrives as `v = t` (the return leg's endpoint equated to the
  starting term), exactly the orientation the brief flagged as the one
  to watch rather than its mirror `t = v` — `rw [heq] at hdrop` and
  `Nat.lt_irrefl` closed it as anticipated.
- Task 4 (`Steps.head_of_ne`, `no_sim_SK_pureS`, and the three
  `pureS_not_universal*_for_SK` corollaries — the prize-adjacent
  refutation): also a first full attempt. The only adaptation needed was
  a binder rename: the brief's `fun ⟨S, _⟩ => ...` destructuring pattern
  for the Norm/Conv corollaries collided with `Term.S` under the file's
  `open Term`, so the elaborator resolved the bound name to the
  constructor instead of a fresh `Simulation` variable. Renamed the
  binder to `Sim`; the statements themselves needed no change.
- Milestone: **this is the program's first conjecture RESOLUTION** — C2
  moves from open to PROVED, and the theorem (`no_pure_S_cycle`) is
  strictly stronger than the census conjecture that produced it on both
  the strategy and size axes. It is also the second time the SK Ω ↔ M
  reduction cycle has served as the refuting witness in this taxonomy:
  Stage 4 used it against iota (strict growth means no injective
  encoding can carry a cycle into a strictly-growing system), and this
  slice reuses the exact same cycle against pure S (acyclicity means no
  injective encoding can carry a cycle into a cycle-free system). One
  mechanism — a cyclic source cannot be hosted by a system whose
  reduction order admits no return trips — with two independent causes
  now machine-checked to trigger it.
- Note for the future: C1 (the smallest non-normalizing pure-S term)
  remains the natural next research target, and it needs the other
  polarity of this slice's toolbox — NON-termination tools, not
  termination ones (a divergence proof, not a decrease measure). That
  sits alongside the two items already queued from Slice 1: the
  finite-pigeonhole saturation argument for the abstract `Decidable (t
  ⟶* u)` instance, and the `sTerms`-completeness chain blocking
  `no_small_cycle`'s general kernel form.
