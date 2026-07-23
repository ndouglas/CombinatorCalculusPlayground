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
  `preservesConv`/`normalizes_preserve`, `UniversalReach.toUniversalConv`).
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
    `UniversalReach.toUniversalConv` — depend on ZERO axioms.
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
