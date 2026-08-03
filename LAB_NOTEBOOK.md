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

## 2026-07-24 — Stage 5, Slice 3: the invariant observatory (reconnaissance)

- Where this slice came from: two ideonomy passes, not one. The first —
  a notation lens run over C1's candidate strings — asked what a change
  of representation could surface that the census's rendered output
  couldn't; it produced the loop-route framing (self-embedding as the
  standard rewriting-theory non-termination witness) and named the slots
  a real divergence proof would need (a self-embedding witness, plus the
  conservation theorem to upgrade it to non-termination). The second — a
  timeline-crossing pass over the taxonomy's own history — noticed that
  Stage 4's iota refutation and Slice 2's pure-S refutation, written
  months apart against different mechanisms, were secretly the same
  argument wearing two causes (strict growth, τ-termination); that
  crossing produced this slice's one consolidation theorem. Both passes
  are exploratory by construction, so the slice was scoped up front as
  reconnaissance — maps, not resolutions — and every task brief carried
  an explicit both-outcome template so no probe could pass silently
  without the artifact saying what it actually found.
- Task 1 (`isSubterm`, the four-direction embedding hunt): three of the
  four directions returned honest negatives at fuel 120 (no self-embedding
  for either candidate, c2 nowhere in c1's trace). The
  fourth returned something nobody had predicted: `stepOnce c2 = some
  c1`, confirmed by kernel-checked `rfl` and hand-traced independently by
  review before the guard was trusted. The two "independent" C1
  candidates from the original census turn out to be one leftmost-outermost
  step apart on a single trajectory — C1 effectively collapses to one
  candidate. Prior entries record several review-shaped catches of
  overclaims and one ideation-shake discovery; this is the first time an
  EMPIRICAL EXPLORATION PROBE discovered a fact nobody had hypothesized —
  while the thing it hunted (a loop) simply wasn't there. No ordinal
  claimed; the ledger's earlier events are enumerable by the reader.
- Task 2 (plateau-nesting probe, C6): the probe tested the census's own
  n≥10 "+1 plateau" reading against n=7..9 data and returned a clean
  honest negative — no subterm nesting, no rider-append match in either
  direction, and leaf-count deltas that explode (×3, then ×7) rather than
  staying small. A controller-authored hypothesis died under direct
  census contact (no ordinal claimed — the ledger has no verifiable
  earlier instance of this exact failure mode; the Stage 4 iota flip
  was killed by pre-planning analysis, not census data) — the
  plateau-nesting reading was a real, reasonable extrapolation from six
  data points, and testing it against three more killed it cleanly rather
  than confirming it. The one surviving positive fact, `m7 == c1` exactly,
  did not propagate to n=8 or n=9. C6 (divergence density) was registered
  as a separate, still-open finding from the same task: 1.5% at n=7 rising
  monotonically to 49.9% at n=12 — six points, consistent with the
  monotone-to-1 conjecture but nowhere near enough to distinguish
  "accelerating" from "leveling off" from "regime change at the plateau
  threshold."
- Task 3 (`Simulation.refute_of_acyclic`): the opposite experience from
  Tasks 1-2 — no exploration needed, the candidates worked essentially
  as given. The generic theorem is AXIOM-FREE (`#print axioms` against
  the built tree), which is worth stating plainly: the mechanism itself
  (an injective step-faithful simulation can't carry a cycle into an
  acyclic host) is pure logic over the `Simulation`/`RS.Acyclic`
  definitions, with no dependency on `no_pure_S_cycle`'s or
  `iota_step_lt`'s machinery until the two concrete instances
  (`RS.PureS_acyclic`, `RS.Iota_acyclic`) invoke them — and those two
  instances carry exactly the `[propext, Quot.sound]` trail their
  underlying theorems already carried, nothing new. Both existing
  refutations (`no_sim_SK_iota`, `no_sim_SK_pureS`) recover as one-line
  `example`s through the generic mechanism; the originals are untouched
  — this consolidates, it does not deprecate.
- Task 4 (this entry; C5, the unbounded-trajectory corollary, the C1
  strategy note, the Slice 3 section): registered C5 (WN ⇒ SN
  conservation for pure S — external, erasure-free calculi territory,
  not formalized here) and its corollary (unbounded trajectory size),
  both explicitly blocked/dependent rather than claimed. Closed the
  numbering gap between C4 and C6 that Task 2's reviewer had flagged.
  The C1 strategy note now states, precisely: the loop route has no
  cheap witness in the fuel-120 explored prefix (three honest negatives),
  and the invariant route (a decidable reduction-preserved predicate,
  none known yet) is the other live option — with C5 as the piece that
  would turn a future loop witness into an actual divergence proof rather
  than just one infinite trajectory.
- Expectation-setting, checked against what actually happened: the slice
  was billed up front as maps, not resolutions, and it held — C1 remains
  open (a discovery about adjacency, not a resolution: one-step relation
  is not a loop, and a loop would not by itself be divergence), C3 remains
  open (an honest negative on one reading of the plateau, not a refutation
  of C3 itself, which was never that specific claim), C6 opened and stays
  open. The one THEOREM to land, `Simulation.refute_of_acyclic`, is a
  consolidation of two already-proved refutations, not a new resolution
  of anything previously open. Nothing here was stretched past its
  epistemic level: kernel-pinned facts (`stepOnce c2 = some c1`, the two
  acyclic instances, the axiom-free generic theorem) are stated as such;
  fuel-bounded census data (the embedding hunt's three negatives, the
  plateau-nesting probe, C6's table) is labeled fuel-bounded throughout;
  C5 and the corollary are registered-open, not claimed.
- Axiom audits, `#print axioms` against the built tree (all scratch,
  since removed): `Simulation.refute_of_acyclic` → no axioms;
  `RS.PureS_acyclic` → `[propext, Quot.sound]`; `RS.Iota_acyclic` →
  `[propext, Quot.sound]` (both inherited from `no_pure_S_cycle`/
  `iota_step_lt`+`iota_steps_le`, nothing new this slice).
- Next-target ranking, as it now stands: (1) the C1 invariant route — a
  decidable leftmost-outermost-preserved predicate mined from trajectory
  data, since the loop route just came up empty within fuel 120 and needs
  C5 anyway even if it succeeds later; (2) C5 formalization itself (the
  λI conservation theorem) — external routes exist, genuinely
  cross-cutting value since it also unblocks the unbounded-trajectory
  corollary; (3) the diverging-pairs core — convertibility between two
  non-normalizing S-terms, the open frontier `Joinable` narrowed to back
  in Slice 1; (4) the pigeonhole queue — `sTerms`-completeness, still
  blocking `no_small_cycle`'s general kernel form and the abstract
  `Decidable (t ⟶* u)` instance, unchanged priority since Slice 1.

## 2026-07-24 — Stage 5, Slice 4: audit, widen, repair (nothing resolved)

- Where this slice came from: an ideonomy pass aimed at the PROGRAM rather
  than at the mathematics. The tuple was negation + combination over a
  chart, with animacy/size/materiality as the dimension prompts, and the
  three prompts turned out to read the project unusually well. Animacy
  named the epistemic register as a life-ladder (settled theorems vs.
  quasi-alive build-time guards vs. alive census observations vs. external
  citations) and made visible that the entire SETTLED block is negative or
  structural — one acyclicity theorem and four things resting on it, with
  nothing positive about pure S settled at all. Size showed every alive row
  resting on a sample of one to six (C3.1 is literally a sample of one
  after Slice 3 collapsed the two candidates). Materiality was the
  uncomfortable one: "runtime-prohibitive" appears as the reason for
  not-knowing in three separate places, so wall-clock — down to a
  block-buffering accident that ate a whole 10-minute run in Slice 0-era
  tooling — has decided more of this project's open/closed boundary than
  any mathematical obstruction has.
- The operative finding was a negation over the census's definitional
  properties: **every conjecture that became a theorem did so by escaping
  one of them, and everything still open is still trapped inside at least
  one.** C2 escaped leftmost-outermost AND bounded size; τ escaped
  fuel-boundedness; `refute_of_acyclic` escaped per-system-ness. C1 is
  trapped inside three at once (one strategy, one fuel, one trajectory).
  That gave a ranked worklist directly, and it matched Slice 3's own
  next-target ranking on item (1), so the two agreed independently.
- Task 1 (the under-claim). Reading `Simulation.refute_of_acyclic` against
  its own proof showed it consumes only `enc_injective` and `fwd_steps` —
  `bwd` is untouched, and `fwd` was ALREADY many-step (`A.step a a' →
  B.Steps (enc a) (enc a')`), so "step-faithful" had never been the right
  word for the hypothesis in the first place. Verified by grep before
  believing it: the only consumers of `Simulation.bwd` anywhere in the tree
  are `conv_reflect` and `comp`. Extracted `PathEncoding`, restated the
  mechanism there, kept `Simulation.refute_of_acyclic` as a
  name-and-statement-preserving corollary so no citation broke.
- The part that mattered methodologically: a widening like this is worth
  nothing if the wider class is secretly the same class, and asserting
  otherwise would have been exactly the sort of overclaim this notebook
  keeps catching. So the widening carries a proof obligation —
  `pathEncoding_strictly_weaker` exhibits a step-free two-point system
  mapped onto SK's Ω/M cycle whose encoder extends to no `Simulation`,
  because `bwd` would reflect a real host path into a source that has
  none. `Simulation.toPathEncoding` is therefore not surjective. Written
  as a theorem, not a remark.
- Task 2 (C1, non-size measures). Term.lean's measures section says in so
  many words that "leaf count is the only size measure we need" — true of
  size, and precisely why every C1 attempt had been a size argument. Four
  other measures along the trajectory produced one regularity strong
  enough to prove outright: from step 8 the head FREEZES to `S A ·` for a
  fixed 9-leaf normal form, and `S A B` with A normal provably admits only
  steps inside B, under every strategy. `frozen_normalizes_iff` relocates
  C1 exactly onto the payload. All six theorems axiom-free.
- Two negatives from that task earned their place. `isoRedexCount` is 0
  from step 6 on, so τ — the machinery that RESOLVED C2 — governs nothing
  on the C1 trajectory; that answers "why not just reuse τ?" by
  measurement instead of by hand-waving. And the recurrence hunt was re-run
  at the frozen granularity, where Slice 3's could not have succeeded:
  Slice 3 looked for `c1` (spine 5) recurring, but after step 8 every
  reduct has spine 2, so `c1` cannot reappear at all. Twenty fresh starting
  points, twenty negatives.
- Honest register on Task 2: the relocated payload has 15 leaves against
  `c1`'s 7. The target got BIGGER. Recorded in the theorem's own doc
  comment, in CONJECTURES.md, and in the commit message, because a reader
  skimming "C1 relocated onto a payload" could easily take it for progress
  toward a divergence proof, and it is not one.
- Task 3 (C6 fuel test) is where materiality bit again, in exactly the way
  the review predicted. `lake exe ccp 10 800` — this time line-buffered
  through `stdbuf -oL`, so the old buffering trap could not repeat, and it
  didn't — reached n=8 in ~9 minutes and stalled on n=9. Diagnosis: at fuel
  800 the extremal trajectories reach ~2.3e9 and ~2.7e9 LOGICAL leaves.
  Terms are shared DAGs in memory so they fit comfortably; `classify`
  computing `leafCount` over them is what costs. The fix was to stop
  measuring the thing C6 never needed — `exhaustedCount` uses only
  `(normalize fuel t).isNone` — after which n=10 at both fuel values
  finished quickly. Result: exhausted counts identical at fuel 200 and 800
  for n = 7..10 (2, 41, 276, 1484), so C6's table survives a 4× fuel test
  with not one of 6,853 terms changing verdict. Bonus: the n=9 and n=10
  rows had been cited from this notebook without recomputation since Slice
  3, and both reproduced exactly — that caveat is discharged.
- Task 4 (the ledger). The review noticed the status vocabulary had no
  demotion state: C3.2's own Slice 3 probe had come back against it, yet it
  sat at plain "open", indistinguishable from C5 which has never been
  tested at all. Added `probed` and `weakened`, with an explicit note that
  neither carries proof content — they track the state of the evidence, not
  of the logic. C3 is now weakened on both halves (C3.1 picked up a second
  dent this slice: spine-length 5 is a property of the STARTING term only
  and does not survive its own trajectory). C1 and C6 are probed.
- Score for the slice: two strengthenings, one structural reduction, one
  ledger repair, four honest negatives, zero conjectures resolved. C1, C3,
  C4, C5, C6 all still open. The one thing this slice did NOT do that it
  should be judged against: it never attempted C5, which remains the
  single highest-leverage unformalized item, since the loop route to C1
  needs it even if a loop witness ever turns up.
- Next-target ranking, revised: (1) C5 formalization (λI conservation) —
  now unambiguously first, since Slice 4 exhausted the cheap structural
  probes on C1 and the frozen-head result sharpens what a divergence
  argument would have to do without changing the fact that C5 gates the
  loop route; (2) construct-don't-search for C1 — the one census property
  the review named that this slice did NOT negate, and the only remaining
  route that doesn't wait on C5: design a pure-S term together with an
  invariant forcing a redex, rather than hunting for one and hoping a
  certificate exists; (3) the diverging-pairs core (`Joinable`, Slice 1);
  (4) the pigeonhole queue (`sTerms`-completeness), unchanged.

## 2026-07-24 — Stage 5, Slice 5: C1 split, minimality proved

- Where this slice came from: a second ideonomy pass, aimed at the program's
  own trajectory rather than at its mathematics. The tuple was
  organon-construction + substitution on a timeline, with
  discovery-vs-invention, predictability and cyclicity as the prompts. The
  timeline was built from real numbers — Lean and prose line counts across
  all 89 commits — and it said three uncomfortable things: the prose/Lean
  ratio had sat between 0.23 and 0.48 for six stages and then inverted at
  Slice 3 (2.33) and stayed near parity at Slice 4; the invention/discovery
  mix had drifted toward invention, with Slice 4 two-thirds invention by
  item count; and one conjecture had been resolved in nine stages, by the
  late-program slice with the LOWEST prose ratio.
- The operative move was substitution on the discovery-vs-invention axis.
  The census frame is discovery-shaped — "which existing term is the
  smallest diverging one?" Substituting an invention frame — "build a term
  that provably diverges" — exposed that C1 was never one claim. It bundles
  EXISTENCE with MINIMALITY, and the bundle is what made both halves look
  uniformly hard. Nine stages of attacking the bundle; nobody had written
  the two lines separately.
- What fell out immediately once split: minimality is FINITE. 65 terms
  (1+1+2+5+14+42), census-recorded maxSteps of 4 over that range, and
  `normalize` already certified on both ends since Stage 1. The only gap was
  `sTerms`-completeness — the chain blocked since Slice 1, escape-hatched
  after three attempts, and standing at priority FOUR in this notebook's own
  ranking. That ranking was an artifact of the unsplit conjecture: the
  chain's standing description said it blocked `no_small_cycle` and the
  abstract `Decidable` instance, and never once mentioned that it also gated
  half of C1, because with C1 unsplit there was no "half of C1" to gate.
- Route that worked, after three previous failures on the other route: stop
  trying to make `sTermsTable`'s `Id.run do`/`Array`/range-loop definition
  transparent, and prove both directions about a structurally-recursive twin
  instead. The trick that makes `enum` structural is a depth budget as the
  first argument — a two-sided size recursion cannot be seen to decrease
  through `List.range`, but the budget can. `enum_sound` and `enum_complete`
  went through without drama; the whole module typechecks in 1.7s. The
  imperative enumerator is untouched and still runs the census, with
  `#guard`s pinning agreement in length and both containment directions for
  n ≤ 7 so the two cannot silently drift apart.
- Then `no_small_divergence` in a few lines: completeness places a small
  term in a finite list, a `decide`d `List.all` over sizes 0..6 discharges
  it, `normalize_sound`/`normalize_normal` convert the success into a
  genuine normal form. Fuel 10, comfortably above the observed maxSteps of
  4. No `native_decide`.
- The catch worth recording, because the tree's axiom discipline nearly
  slipped: the first version of `enum_complete` reported
  `[propext, Classical.choice, Quot.sound]` — `Classical.choice` would have
  been the FIRST use of it anywhere in this tree. Bisected it to a single
  site: `omega` discharging a non-arithmetic goal (`∃ d', d = d' + 1`) out
  of contradictory hypotheses. Replaced with an explicit witness via
  `Nat.succ_pred_eq_of_pos`, where `omega` only ever proves arithmetic. Same
  failure mode and same fix as Slice 2's choice-free τ decrease, which is
  the second time this exact leak has appeared — worth remembering that
  `omega` proving a NON-arithmetic goal is the smell.
- Register: C1(b) is the program's first proved POSITIVE result about pure
  S. Every previously settled result is negative (two hosting refutations)
  or structural (acyclicity, the consolidation, the frozen head). Stated
  plainly in the ledger, along with the limit — minimality gives zero
  leverage on existence, and if pure S is strongly normalizing then C1(b)
  stays true while C1(a) is simply false.
- What this says about method, which is the part I would keep: the
  resolution came from neither a new probe nor a new definition. It came
  from noticing that a conjecture was two conjectures. Slices 3 and 4 were
  both honest and both produced good artifacts, and neither could have found
  this, because both took the conjecture list as given. Reviewing the
  PROGRAM rather than the mathematics was what surfaced it — and the review
  that did it was cheap.
- Next-target ranking, revised (the C5 demotion is deliberate and the reason
  matters): (1) **construct-don't-search for C1(a)** — now the highest-value
  live item, and the one census property no slice has yet negated. Under an
  invention frame the witness need not be `c1`: any diverging pure-S term
  settles existence, so a construction may pick a convenient, self-similar,
  large term designed alongside its own invariant, rather than the smallest
  one, which is the term least likely to have exploitable structure. Nine
  stages went after the hardest possible witness for reasons of taste rather
  than necessity. (2) **C5** (λI conservation) — unchanged in value,
  demoted in order: it is a known classical theorem, so its information gain
  is zero and it is labour rather than inquiry. It still gates the loop route
  to C1(a), so it is not optional, only not urgent. (3) the pigeonhole /
  abstract `Decidable (t ⟶* u)` item — cheaper now that `enum_complete`
  exists, since the finiteness ingredient it wanted is exactly what
  completeness supplies; worth re-scoping before attempting. (4) the
  diverging-pairs core (`Joinable`, Slice 1). Note that item (3) moved up
  by two places purely as a side effect of this slice, which is the second
  thing the split bought.

## 2026-07-24 — Stage 6: the spec's goals, and the check nobody ran

- Where this came from: not an ideonomy pass this time but a plain
  re-reading of the design spec, prompted by noticing that two consecutive
  strategy answers had ranked work against the C-conjecture list. The spec
  does not have a C-list. Its Goal 3 is "is reachability between pure S-terms
  decidable?", and I had ranked that item THIRD after having just written the
  note explaining that Slice 5 made it tractable. Third time the same failure
  shape: taking a derived artifact (first C1-as-one-conjecture, then the
  C-list, then my own queue) as the fixed target while the spec sat there
  being the actual authority.
- Goal 3 went through cleanly and fast. The whole content is that
  `enum_complete` supplies the finiteness the Slice 1 gap needed:
  `smallTerms` as the finite universe, `deficit` as the measure,
  `deficit_lt` for the pigeonhole step, then saturation by induction on fuel
  rather than well-founded recursion (the deficit bound is threaded as a
  hypothesis, which keeps it structural). Two generic list lemmas had to be
  written — filtering one list by two comparable predicates, both the ≤ and
  the < form — neither in core 4.28.
- Lean friction worth recording: core 4.28 has only ONE direction of
  `eraseDups` membership, and the project had already hand-written that one
  (`mem_of_mem_eraseDups`, Slice 1). I needed the other direction and
  briefly started writing it, then realised the proof does not need it —
  take the pigeonhole witness from the DEDUPED frontier via `eraseDups_cons`
  and the existing direction covers the rest. Cheaper than adding a lemma.
- Also: `cases h : e with` substitutes the scrutinee into the goal, so a
  follow-up `rw [h]` fails with "pattern not found". Cost two iterations.
  And `by_contra` is Mathlib, not core — `Nat.lt_or_ge` plus `absurd` is the
  zero-dependency replacement, same as Slice 5 needed.
- **The literature check, which is the real result of this stage and is
  uncomfortable.** Under an hour of searching established that BOTH halves of
  C1 have been known externally the whole time. Wolfram states plainly that
  "at size 7 and above there are S combinator expressions that do not
  terminate", and the Wolfram Data Repository ships the non-halting S
  expressions for leaf counts 1 through 10 as a dataset. Waldmann's
  decidability result — cited in this project's own spec Background since
  Stage 0 — is the underlying technology. So the census independently
  rediscovered a known threshold, and this file recorded the rediscovery as
  an open conjecture for nine stages.
- What makes that a process failure rather than bad luck: this project
  maintains a meticulous external/internal register. Cocke–Minsky, Waldmann,
  Church/Barendregt and Barker are all cited precisely, with "EXTERNAL fact,
  not machine-checked" attached. The register was applied to every
  background fact the program LEANED on and to none of the facts it was
  trying to establish. There was no **external** status available for a
  conjecture, so an externally-settled claim had nowhere to sit except
  "open". Added that status this stage; it is the missing primitive.
- Honest limit on the check: I did not extract the explicit leaf-7
  expressions from the dataset to compare with `c1`/`c2` term by term. The
  agreement established is on existence and on the threshold, not on the
  identity of the witnesses. Cheap to finish and worth finishing.
- Consequences taken rather than deferred: C1(a) re-labelled external
  (transcription, not research); the "first proved positive result" claim on
  C1(b) corrected in place rather than deleted, so the overreach stays
  visible; C2's folklore hedge sharpened from "may be folklore" to "assume
  external until the primary source is read", since secondary sources credit
  Waldmann with no-ground-loops for CL(S).
- Goal 2 criterion (a): assessed and deliberately not attempted. The
  encoding machinery needed is substantial but mechanical; the blocker is
  `bwd`, which for a real encoder is a full adequacy theorem (no spurious SK
  path between encoded words). `bwd` was free for `pureS_in_SK` only because
  that encoder is inclusion — which in hindsight makes `pureS_in_SK` a much
  weaker demonstration of the Simulation class than it reads as. Recorded
  the blocker instead of leaving a half-built encoding in the tree.
- One cheap real finding fell out of that assessment: `Simulation.id` makes
  all three Universal* predicates trivially true on the diagonal. Added as a
  negative control beside `bareEncNorm_trivial`. It does not affect any
  ledger row (all have R = Tag ≠ B) but it closes the reflexive analogue of
  the oracle-encoder cheat.
- C3 retired as a census artifact. Both halves weakened, never a claim about
  S-reduction, and carrying it was inviting re-probing.
- Next-target ranking, revised again and now anchored to the spec rather
  than to the C-list: (1) **spec Goal 2 criterion (a)** — the only stated
  spec goal still open, and the taxonomy is the spec's declared intellectual
  centre; needs to be scoped as a multi-slice project with `bwd` as the
  known hard part, not attempted opportunistically. (2) **C4** — genuinely
  open, genuinely ours, and the one conjecture on the list with no external
  answer found; it generalises the iota refutation to all strictly-growing
  one-rule bases and `PathEncoding` already gives the right hypothesis
  shape. (3) C6 — open, ours, cheap to extend. (4) transcription work
  (C1(a), C5) — real deliverables under Goals 1 and 4, now correctly
  labelled as importing rather than discovering. Note that C1 has left the
  top of this list for the first time since Stage 0, and that the two items
  now above it are the two nobody has found an external answer for.
- Meta-goal note (spec Goal 4): the spec says "if Stage 5 never terminates,
  the notebook is the result." Three stages of strategy advice in this
  notebook were mis-ranked in the same way, and each time the correction came
  from re-reading a document that was already in the repo rather than from
  new mathematics. That is a finding about this working setup, and it belongs
  in the meta-goal's record as much as any proof-friction note does.

## 2026-07-24 — Stage 7: C4 reduced, and a plan that broke on contact

- Where this came from: a third ideonomy pass, tuple tree-finding +
  cross-domain re-instantiation on a cycle, prompts homogeneity / side-effect
  / polarity. Two of its findings survived execution and one did not, which
  is the entry's main content.
- **The finding that held: an altitude diagnosis.** Walking the tree upward
  from "is S universal?" gives: do small S-terms diverge -> is S universal ->
  is this one-combinator basis universal -> which minimal systems are
  universal -> what does universal MEAN for a rewriting system -> when is a
  translation between systems faithful rather than smuggling the answer. Prior
  art is DENSE at the bottom and thin at the top. Counted the tree's own
  theorems by area: 36 in Universality/ plus 11 in its RS substrate, with
  Calibration.lean the single densest file. So the program's mass is at the
  top while nine stages of effort went to the bottom — and of course prior art
  is dense down there, because the bottom is the level enumeration reaches.
  That single observation explains all three prior mis-rankings at once: they
  were not three mistakes but one closed loop at the wrong altitude, sampled
  three times. C1-as-one-conjecture, the C-list, and my own queue are all
  bottom-level artifacts.
- **The cycle diagnosis, also held.** Drawing the working loop from the commit
  history: census -> conjecture -> attack -> prove-or-negative -> ledger ->
  back to conjecture. The loop closes on `conjecture`, never on `spec`. So
  after Stage 0 emitted the C-list, the spec sat outside the cycle for nine
  stages and every correction required manually breaking out to re-read a
  document that had been in the repo since day one. Two phases were missing
  entirely — calibrate-against-prior-art and materiality-check, both belonging
  between conjecture and attack. Both are now ledger fields.
- **The finding that did NOT survive, which is the useful part.** The pass's
  headline recommendation was to restate spec Goal 2 criterion (a) at
  PathEncoding strength, since the refutations only need PathEncoding and the
  blocker is `bwd`. It sounded strong enough that I led with it. It is wrong.
  Positive and negative claims want OPPOSITE classes: not-exists-encoding
  strengthens as the class grows, exists-encoding strengthens as the class
  shrinks. Criterion (a) is positive, and its entire purpose is showing the
  DEMANDING definition is satisfiable, so weakening the class weakens the
  claim in the direction where weakness is not wanted. The spec's own
  quantifier-asymmetry note says this, in different words, and I had read it
  two stages earlier.
- What I did about it: formalized the correction rather than deleting the
  suggestion. UniversalReach.toPathEncoding gives the inclusion, and with
  pathEncoding_strictly_weaker the two levels provably differ, so the
  direction is substantive rather than bookkeeping. Recorded in the ledger as
  superseding the suggestion, with the wrong reasoning left visible. The
  outcome is that Goal 2's blocker is now known to be PRINCIPLED — `bwd` is
  load-bearing — which is more useful than the bypass would have been if it
  had worked.
- **C4 went the way C1 went.** Same bundling: a semantic claim (strictly
  growing measure ⇒ cannot host SK) fused to a syntactic class
  (one-combinator, single-rule, first-order). The semantic half is two lines
  given RS.Acyclic.of_strict_measure plus SK's cycle, and it is STRONGER than
  C4 — any host, one-combinator or not. The syntactic half needs a
  rule-schema formalism nobody has built. Registered as reduced, not resolved.
  Third time now that splitting a bundled conjecture was the whole trick;
  worth treating as a standing first move rather than a lucky one.
- Confirmation the generalization is right: RS.Iota_acyclic and Stage 4's
  refutation both drop out as one-line instances. Strict growth was never a
  property of iota, only of its measure. Stage 4 had written a bespoke
  argument for what turns out to be a corollary.
- Proof-friction note: Classical.choice leaked again, in
  no_sim_SK_of_strict_measure, from opening a Nonempty with Classical.choice
  when destructuring into a Prop goal needs nothing. THIRD leak in three
  slices (Slice 2: omega in congruence cases; Slice 5: omega on a
  non-arithmetic goal; here: Nonempty elimination). All three were caught by
  the axiom audit, none by review. The audit is doing real work and should
  stay a per-slice ritual.
- Cross-domain note worth keeping, since it produced the materiality field:
  re-instantiating "apparatus for deciding when a translation is faithful"
  into audit standards surfaced the pairing this file was missing.
  Scope-honesty and materiality travel together in auditing; this project had
  built an excellent attestation layer and no materiality test at all. Sport
  rules-committees suggested a second move not yet taken — publish the test
  battery separately from any particular ruling — which is the extraction
  question below.
- Extraction assessment (asked, answered honestly, not acted on): the
  calibration suite (Simulation, PathEncoding, the strictness witness, the
  three observation modes, bareEncNorm_trivial, the diagonal controls,
  refute_of_acyclic, the measure engine) is coherent, portable, and its
  natural peer set is encoding-legitimacy disputes across several fields
  rather than combinator papers. It is NOT ready to stand alone, for one
  concrete reason: it has no positive certification. Every calibration result
  in it is negative or a triviality control, and a suite that only ever says
  "not this" is a critic, not a standard. Goal 2 criterion (a) is exactly the
  missing piece, which is a second and independent argument for ranking it
  first. Extraction after (a), not before.
- Next-target ranking, unchanged in order from Stage 6 and now better
  motivated: (1) **spec Goal 2 criterion (a)** — the only open stated spec
  goal, the taxonomy's missing positive side, and a prerequisite for the
  suite standing alone. Needs scoping as a multi-slice project with `bwd` as
  the known and now provably-necessary hard part. (2) **C4's syntactic
  residue** — a rule-schema formalism; genuinely ours, no prior art found,
  mathematics already done. (3) transcription work (C1(a), C5) — real
  deliverables under Goals 1 and 4, correctly labelled as importing.
  (4) C6, explicitly NOT promoted despite being cheap, because cheapness is
  what made C1 attractive for nine stages.

## 2026-07-24 — Stage 8: attack the blocker, not the encoding

- Continued straight down the Stage 7 ranking: spec Goal 2 criterion (a),
  the only open stated spec goal. The obvious move is to start building a
  Tag → SK encoding. I did not, and the reasoning is the entry's point: the
  encoding's hard field is `bwd`, so anything built before `bwd` is derivable
  is built on top of an unsolved problem. Make `bwd` derivable first.
- What went in: the classic adequacy technique, proved once at the taxonomy
  level. An abstraction function on ALL host states, each host step either
  stuttering or advancing the abstraction by exactly one source step, yields
  `bwd` (`RS.abstraction_tracks`, `RS.bwd_of_abstraction`) and packages into
  `Simulation.ofAbstraction`, which also absorbs `dec_enc` since the
  abstraction doubles as the decoder. All axiom-free, and the proof is short —
  induction on the host path carrying "the abstraction of the current state is
  some source state reachable from the start."
- Register, stated in the module header and the commit: this does NOT remove
  the blocker. It changes its KIND — from "characterise every path between
  encoded states", which is open-ended, to "define the abstraction and check
  each rule stutters or advances", which is mechanical per machine. Worth
  being precise because "bwd blocker solved" is exactly the overclaim this
  notebook keeps catching, and it would be wrong.
- Non-vacuity check chosen deliberately: rebuild `pureS_in_SK` through the new
  constructor. It works, and it is degenerate in an instructive way — no step
  ever stutters, because every SK step out of a K-free term advances the
  source by exactly one PureS step (Stage 2's KFree.of_step). So the example
  exercises the interface and NOT the hard case, since a real machine
  encoding stutters on most steps and advances on few. Recorded as such
  rather than presented as evidence the technique scales.
- **The structural finding, which I did not expect and which reframes the
  Stage 4 result.** Checking what Bracket.lean could contribute, I found there
  is no bridge from `TermV` to `Term` and no transfer from `StepsV` to
  `Steps`. Bracket.lean is a closed universe. So `combinatory_completeness` —
  the program's headline POSITIVE calibration result since Stage 4 — has never
  been in the same language as any of its negative results, all of which live
  in the RS/Term layer. CONJECTURES.md had flagged it as "a theorem about
  TermV, not routed through Simulation", which reads as a stylistic caveat;
  the gap is structural. The positive and negative halves of this program's
  calibration have never met. That is a much better argument for criterion
  (a)'s priority than the one I gave in Stage 7, and it was sitting in the
  import graph the whole time.
- Criterion (a) decomposed into six pieces with difficulty named (recorded in
  CONJECTURES.md). Five are mechanical-but-bulky; the residual risk is
  concentrated in the last, where `abs` must be total on SK terms including
  garbage and tracking must survive every intermediate state the driver
  passes through. That is the piece to prototype first if this is picked up,
  because it is the one that can fail in kind rather than in volume.
- Meta-goal note: this is the first stage in a while where the right move was
  to build infrastructure for a problem rather than attack the problem, and
  the reason it was identifiable is that Stage 7 had already proved `bwd`
  load-bearing. A blocker that is known to be principled is worth building
  against; one that might be incidental is worth trying to route around
  first. Those are different responses and the distinction came from a
  theorem, not from judgement.
- Ranking unchanged: (1) criterion (a), now with piece (vi) flagged as the
  prototype-first risk; (2) C4's syntactic residue; (3) transcription
  (C1(a), C5); (4) C6, still deliberately not promoted.

## 2026-07-24 — Stage 9: the bridge, and a claim weakened instead of an axiom paid

- Continued down the ranking. Criterion (a)'s prototype-first risk is piece
  (vi), but Stage 8's structural finding made piece (i) the better move: it
  repairs a real defect in the program's centrepiece and is on the critical
  path regardless.
- First confirmation was worse than the Stage 8 write-up: Bracket.lean did not
  merely lack a bridge, it had **no import line at all**. A completely
  standalone file holding the program's only positive calibration result. The
  Stage 8 entry said "closed universe"; it was literally closed.
- The bridge went in cleanly. The pleasant surprise: `step_toTerm` needs NO
  closedness hypothesis. `StepV`'s four rules are `Step`'s four rules,
  `toTerm` is a homomorphism for application, and variables are inert on both
  sides — so every variable-level step projects to a genuine `Term` step
  unconditionally. Both transfer lemmas are axiom-free. I had budgeted for a
  closedness side-condition threaded through every proof and it never
  materialised.
- Placement was a deliberate choice: `combinatory_completeness_RS` went into
  Calibration.lean rather than Bracket.lean, so the positive result physically
  sits beside the refutations it is supposed to be comparable with, and
  Bracket.lean stops at `Term`/`Step` without importing the conservation
  layer. Calibration.lean now reads as one sandwich in one language, with a
  comment stating what the sandwich still does NOT contain — the positive side
  is about realizing λ-bodies, criterion (a) wants hosting a MACHINE. Making a
  gap legible is not closing it and the file says so.
- **The fourth Classical.choice leak, and the first one I did not fix.** The
  stronger faithfulness lemma — `ClosedV v → ofTerm (toTerm v) = v`, i.e.
  `toTerm` is faithful on every variable-free TermV and not just on ofTerm's
  image — needs `(n == n) = true` in its `var` case. Four routes tried:
  `beq_self_eq_true` (leaks), `simp` finding it (leaks), a hand-rolled
  `Nat.beq n n = true` by structural recursion (axiom-free, but will not
  connect to `==` — the `BEq Nat` instance does not reduce `succ k == succ k`
  to `k == k`), and the same at the `==` level (same wall). The leak is in the
  BEq/LawfulBEq instance layer, not in my proof.
- The three-attempt rule applied, so I stopped and reassessed instead of
  finding a fifth route. The reassessment is the useful part: the lemma is
  DECORATIVE — nothing in the tree depends on it — and the bridge only ever
  transfers FROM `Term`s, so what is actually needed is that `toTerm` inverts
  `ofTerm`, which was already axiom-free. Weakened the claim to
  `ofTerm_injective` and wrote the dropped claim, the reason, and the four
  failed routes into the doc comment. Whole bridge reports [propext] or less.
- Worth stating as a rule, since this is the first time the choice: when a
  decorative lemma costs an axiom the tree has never used, weaken the claim.
  When a load-bearing one does, pay it and register it loudly. The previous
  three leaks were all in load-bearing proofs and all had rewrites available;
  this one had neither property, which is why it read differently.
- Ranking, unchanged in order: (1) criterion (a) — piece (i) DONE, next is
  (ii) multi-variable bracket abstraction, then (vi) as the prototype-first
  risk before the bulk of (iii)–(v); (2) C4's syntactic residue; (3)
  transcription (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 10: the prototype failed, which is why it was a prototype

- Two ordering decisions, both against my own written list and both for the
  same reason. Piece (ii) was next; I skipped it. First because it is
  mis-scoped — Stage 8 called it "one iteration lemma" and it is not, since
  iterating `bracket` needs substitution to commute with bracketing and that
  holds only up to reduction (`subst x u (bracket y (var x))` is `K u`;
  `bracket y (subst x u (var x))` is `bracket y u`; reduction-equivalent, not
  equal, so the induction does not close syntactically). Second because (ii)
  is investment and (vi) was flagged as the piece that could invalidate it.
  The list said (ii) then (vi); the list's own justification said prototype
  first. Followed the justification.
- The prototype: `Itower n = I (I (... S))`, a countdown where one source step
  costs two host steps. Chosen because it is the smallest encoding that is a
  genuine multi-step machine rather than an inclusion, and because it has real
  nondeterminism — `Itower 3` has three redexes, so reduction can go
  outside-in, inside-out, or interleaved. `pureS_in_SK` had neither property,
  which is exactly why the Stage 8 non-vacuity check could not have caught
  this.
- It failed, and the failure is clean enough to state as a theorem:
  `naiveAbs_not_stuttering`. The obvious structural abstraction — count
  pending I-layers, recognise intact `I u` and half-consumed `(K u)(K u)` —
  admits a step out of an abstracted state whose target abstracts to `none`.
  Concretely `(K (I S))(K (I S)) → (K ((K S)(K S)))(K (I S))`: one step inside
  the LEFT copy only, and the two copies no longer match.
- Cause, and it is not incidental to this test machine: `S f g x → (f x)(g x)`
  duplicates `x`, so the copies reduce independently. Any abstraction reading
  a duplicated subterm syntactically has to cope with drift, and the drifted
  state space is combinatorial in the live redexes inside the duplicated part.
  This is the failure-in-kind Stage 8 was worried about, found where Stage 8
  predicted it would be.
- **The payoff, which is why this was worth doing before piece (v).** There
  are two fixes and the second is a design constraint, not a proof technique:
  constrain the encoding so duplication only ever hits NORMAL FORMS. If `x` is
  normal when `S f g x` fires, neither copy can step, so drift is impossible
  by construction and the syntactic abstraction is fine. `sync_step` checks
  this: the same shape over a normal payload advances 1 → 0 exactly as
  required. So piece (v)'s driver must duplicate only already-normal arguments
  — achievable, since encoded words and symbols are data and data can be kept
  normal, but it constrains how the machine is built and cannot be retrofitted.
- Revised difficulty, and the honest correction to Stage 8: (vi) is mechanical
  only CONDITIONAL on (v) obeying that discipline. Stage 8's decomposition
  listed (i)–(vi) as independent pieces; (v) and (vi) are coupled, and the
  coupling runs from the later piece back to the earlier one. That is the kind
  of thing that would have been discovered halfway through building (v), at
  which point (v) would have needed rewriting.
- Cheap methodological note: this is the third stage in a row where the useful
  output was a NEGATIVE about the program's own plan — Stage 7 corrected a
  recommendation, Stage 9 weakened a claim rather than paying an axiom, Stage
  10 falsified a difficulty estimate. All three were cheap, and all three would
  have been expensive to discover later. The pattern is worth naming: the
  program's plans have been consistently over-optimistic about mechanical
  pieces and consistently right about which piece is risky. Trusting the risk
  flags and distrusting the difficulty ratings looks like the correct posture.
- Ranking, unchanged in order but with (v) and (vi) now coupled: (1) criterion
  (a) — (i) done, (vi) prototyped and its constraint known, (ii) needs a
  commutation-up-to-reduction lemma, (iii)–(v) must be built under the
  normal-forms-only discipline; (2) C4's syntactic residue; (3) transcription
  (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 11: checking a constraint before building on it

- Direct application of the posture named at the end of Stage 10: trust the
  risk flags, distrust the difficulty ratings. Stage 10 handed down a design
  constraint — duplication must only ever hit normal forms — and the obvious
  next flag is whether that constraint can be met at all. If it cannot,
  pieces (ii)–(v) are wasted work, and finding out costs an hour now versus a
  rewrite later. Same shape as Stage 10's own reasoning, one level up.
- The reasoning that made it cheap: the first thing any machine duplicates is
  its own CODE, through the self-application inside a fixpoint. All of this
  program's code comes from `bracket`. So the question reduces to "are bracket
  outputs normal?" — and inspecting the four cases of `bracket` answers it
  immediately: it only ever emits `K` with ONE argument and `S` with TWO, and
  neither is a redex. `normalForm_bracket` compiled first try.
- That is a genuinely reassuring result and it was invisible before the Stage 9
  bridge existed, because the statement is about `Term`-level normal forms and
  `bracket` lives in `TermV`. Worth noting: the bridge paid off one stage after
  it was built, on a question nobody had in mind when building it.
- Four shape lemmas fell out (`normalForm_S`/`_K`, `normalForm_app_K`,
  `normalForm_app_S_one`/`_two`). These are the kind of small reusable facts
  piece (v) will need constantly, so they are cheap infrastructure acquired as
  a side effect rather than as a project.
- Also upgraded Stage 10's diagnosis from an observation to a theorem:
  `step_app_K_pair` shows the half-consumed shape over a NORMAL payload has
  exactly one successor. Stage 10 had `sync_step`, a single instance. The
  general form is what actually licenses the design constraint.
- **The honest half: the constraint is only HALF satisfiable so far.** Code is
  normal, so fixpoint self-application is safe. But a fixpoint's reduct
  `f (x x f)` hands the step function a pending recursive call, which is not
  normal, and if the driver duplicates that then drift is back. So piece (v)
  needs a strict discipline — force before duplicating. Recorded as the
  sharpest known requirement on the remaining work rather than waved at.
- Pattern check, since Stage 10 named one: this is the FIRST stage in four
  where the output was positive rather than a negative about the plan. It was
  found by the same move that produced the three negatives — ask what the plan
  assumes, then check the cheapest assumption first. The move is not
  pessimistic; it is just ordering. Stages 7, 9 and 10 happened to find breaks;
  this one found a foundation.
- Ranking: (1) criterion (a) — (i) done, (vi) prototyped, code-duplication
  safety proved, and the live requirement is now a strict-evaluation discipline
  on piece (v)'s driver; the next buildable item is (ii), which needs the
  commutation-up-to-reduction lemma; (2) C4's syntactic residue; (3)
  transcription (C1(a), C5); (4) C6, still not promoted.

## 2026-07-24 — Stage 12: piece (ii), shrunk by two design choices

- Piece (ii) was rated "one iteration lemma" in Stage 8, corrected in Stage 10
  to "needs commutation up to reduction". Both were wrong about the shape of
  the work. What it actually needed was two decisions, after which one lemma
  did the job:
- **Decision 1: don't build n-variable abstraction.** A driver needs a
  fixpoint self-reference and a state — two variables — and any further
  arguments can be tupled into the state. Two nested abstractions is exactly
  the case the commutation lemma handles in ONE application, with no
  iteration and no induction over a variable list. The general n-variable
  development would have been several times the work for something nothing
  needs. Recorded as a YAGNI call in the same spirit as the file's existing one.
- **Decision 2: state the lemmas for encoded data, not for abstract closed
  terms.** The argument being substituted is always in the image of `ofTerm`,
  so `subst_ofTerm` and `bracket_subst_applied` quantify over `ofTerm p`. This
  deletes the `var` case from both proofs — and the `var` case is precisely
  where Stage 9's `Classical.choice` trap lives (deriving a contradiction from
  `ClosedV (var n)` needs `(n == n) = true`). So the Stage 9 leak, which cost
  four failed attempts and a weakened claim, ended up steering a design two
  stages later toward a cleaner formulation. Worth noting: the leak was not
  just an obstacle, it was information about which shapes to avoid.
- The lemma itself went in without drama once framed that way — four cases,
  each a couple of lines, and the `app` case is just S_red plus `congApp` on
  the two IHs. `abs2_beta` is then `congL` of `bracket_beta` composed with it.
- Lean friction, minor but repeated: `simp only [..., h]` where `h : ¬ (z = y)`
  rewrites the CONDITION to `False` but does not reduce `if False then a else b`.
  Needs `ite_false`/`ite_true` alongside. Cost two iterations and produced a
  crop of unused-simp-argument warnings while I found the minimal set; cleared
  them all, build is warning-free again.
- Small honest finding from clearing those warnings: the `unused variable h`
  lint on `combinatory_completeness_Term` is telling the truth. Its
  single-variable hypothesis is VESTIGIAL — the `Term`-level statement does not
  assert closedness, and `toTerm` erases variables anyway, so the theorem holds
  for any body. Renamed to `_h` rather than dropped, to keep parity with the
  `TermV` version where the hypothesis genuinely is needed for `ClosedV`.
  Flagged in the ledger rather than silently kept, since a vestigial hypothesis
  makes a theorem look narrower than it is.
- Where criterion (a) stands: (i) and (ii) done, (vi) prototyped with its
  constraint half-discharged, (iii)–(v) remaining under the
  force-before-duplicate discipline. The residual risk is unchanged and
  specific — a fixpoint's reduct hands the step function a pending recursive
  call, which is not normal. That is the next thing worth prototyping, and by
  the Stage 10/11 pattern it should be prototyped before (iii)–(v) get built,
  not after.

## 2026-07-24 — Stage 13: the third revision of one difficulty estimate

- Followed the Stage 10/11 rule: prototype the known risk before building on
  it. The risk was the pending recursive call. It broke, and it took Stage 10's
  preferred fix down with it.
- The mechanism is embarrassingly simple in hindsight. `bracket` is the NAIVE
  algorithm — the file's own comment says so, and says the tradeoff is bigger
  terms for smaller proofs. What nobody had noticed is that "bigger terms"
  means DUPLICATED ARGUMENTS: `[x](a b) = S ([x]a) ([x]b)` sends the argument
  to both branches whether or not `x` occurs in them, and `S A B u → (A u)(B u)`
  copies `u`. So the abstracted argument is duplicated once per application node
  in the body. I demonstrated it on a body that uses its variable exactly once.
- That kills route (2) as a standalone fix. Stage 10 framed the choice as
  "define the abstraction up to Joinable (hard)" versus "constrain the encoding
  so duplication only hits normal forms (a design constraint)", and preferred
  the latter. But route (2) assumed the driver's author controls what gets
  duplicated. They do not — the abstraction algorithm decides, and it duplicates
  unconditionally.
- Worse, and this is the part that makes it a real result rather than a bug
  report: transient duplicates are not fixable by a better abstraction
  algorithm. In SK, `S f g x → (f x)(g x)` is the ONLY way to move a value into
  two positions, and it always duplicates the third argument. Occurs-check
  optimization reduces the NUMBER of copies; it cannot reach zero, because
  getting a value past another value costs a copy. So some window always exists
  in which a doomed copy is live and can drift.
- Third revision of the same estimate, which is worth stating plainly: Stage 8
  said piece (vi) was mechanical. Stage 10 said mechanical conditional on (v)'s
  design. Stage 13 says not mechanical. Each revision came from probing one
  level deeper, and each was cheap. The estimate has moved monotonically in one
  direction, which is itself a signal — I should have weighted the first
  revision as evidence about the second.
- Where that leaves criterion (a): the abstraction has to be insensitive to
  doomed subterms, either up to `Joinable` (Slice 1 has it, and SK confluence is
  proved, so the machinery exists) or by reading only the live spine. That is a
  research-shaped obligation, not a bulk one, and it is now the honest cost of
  the criterion. Pieces (i) and (ii) are unaffected and still needed; Stage 11's
  `normalForm_bracket` still holds and still matters, because CODE being normal
  is what makes fixpoint self-application safe. The problem is narrowly the
  pending recursive call.
- Methodological note, and the reason I am not discouraged: four stages of
  prototyping have cost roughly one stage of building and have prevented two
  rewrites of piece (v). The alternative history — build (iii)–(v) on Stage 8's
  "mechanical" rating, then discover in (vi) that the abstraction cannot be
  written — would have wasted far more. The prototypes keep finding bad news
  because they are aimed at the places most likely to contain it, which is what
  they are for.
- Ranking, revised in emphasis rather than order: (1) criterion (a), where the
  next real decision is which of the two route-(1) variants to attempt — up to
  `Joinable`, or live-spine-only — and that decision should itself be prototyped
  on the Stage 10 countdown machine before any encoding work; (2) C4's syntactic
  residue, which is now comparatively more attractive, being bulk work with no
  hidden research problem in it; (3) transcription (C1(a), C5); (4) C6.

## 2026-07-24 — Stage 14: taking my own advice and switching targets

- Stage 13 ended with two facts I had written down and not acted on: the piece
  (vi) difficulty estimate had been revised upward three times MONOTONICALLY,
  and C4's residue was "bulk work with no hidden research problem in it". The
  first is evidence the estimate will move again; the second is a target with
  known cost. Continuing on (a) would have been walking down the same corridor
  for a fourth revision. Switched to C4.
- Worth being explicit about the reasoning, since it is the same move I have
  been recommending and then not following: a monotone sequence of upward
  revisions is information. I noted it in Stage 13 as a lesson about the SECOND
  revision. Applying it forward instead of backward is the actual use.
- C4's residue turned out much cheaper than expected once I looked at arity. The
  general-arity case needs occurrence VECTORS and sums over `i < n`; the arity-1
  case needs a single coefficient and no sums at all. And arity 1 is exactly
  ι's arity — so the arity-1 theorem generalizes the instance C4 was abstracted
  from, which is the most useful part of the whole class to have.
- The satisfying part: C4's informal English collapses into two `decide`-able
  counts. "Each rule variable occurs at least once in the reduct" is
  `1 ≤ countVar rhs`. "The reduct is strictly larger even at the minimal
  instantiation" is `2 ≤ countC rhs`. The bridge is one lemma —
  `Pat1.leafCount_inst`, that instantiation is linear in the argument's size —
  and everything else is arithmetic. A conjecture stated in prose for eleven
  stages turned out to be two inequalities.
- Non-vacuity handled carefully, because there was an easy overclaim available:
  `RS.Mono1 iotaRhs` is ι's rule SHAPE over the abstract carrier `Mono`, NOT the
  `RS.Iota` instance whose carrier is `IotaTerm`. They are isomorphic but nothing
  here re-derives `no_pathEncoding_SK_iota`. Said so in the file, because
  "C4 proved and it recovers the iota refutation" would have read better and been
  wrong.
- Lean friction, one item: `omega` cannot distribute a variable product, so
  `(a.countVar + b.countVar) * |x|` had to be broken up with `Nat.add_mul` in the
  simp set before `omega` could close the `app` case. One iteration.
- Honest scope on the headline: C4 is PROVED for arity 1 and OPEN for arity ≥ 2.
  The remaining obstacle is list-sum algebra in a Mathlib-free tree — additivity,
  an indicator-sum lemma, and a partition lemma — not anything about
  combinators. That matches Stage 13's assessment of the residue as bulk work,
  and it is the first time in five stages that a difficulty estimate has held up
  on contact.
- Ranking: (1) **C4 general arity** — now the most attractive item on the board:
  known cost, no research risk, and the arity-1 case has already validated the
  proof shape, so the only question is the list algebra. (2) criterion (a),
  where the open decision is still which route-(1) variant to attempt for the
  abstraction, and which should be prototyped before any encoding work.
  (3) transcription (C1(a), C5). (4) C6.

## 2026-07-24 — Stage 15: C4 closed, and Stage 14's obstacle was imaginary

- Stage 14 registered general-arity C4 as blocked on "list-sum algebra" and
  named three needed lemmas, one of them a partition lemma to split a variable
  list across an application node. It took about an hour to find that both
  halves of that framing were wrong.
- **The lists were self-inflicted.** I had assumed a rule's arguments arrive as a
  `List Mono`, which forces `getD` indexing and then a cons/append mismatch
  against `List.range`-based sums. Taking the assignment as a FUNCTION
  `σ : Nat → Mono` and defining the left-hand side by recursion on the arity
  (`applyVars`) removes every list from the development. That is a
  representation choice, not a mathematical fact, and I had let the first
  representation I thought of become the estimate.
- **The partition lemma was never needed.** It is only needed if you try to
  prove the INEQUALITY directly, where "every variable occurs" fails to
  decompose over `app`. Proving the exact size formula instead makes the `app`
  case pure additivity. I had actually worked this out in Stage 14 — the note in
  that file says the formula "decomposes fine over app" — and then still listed
  the partition lemma as required. Reading my own note more carefully would have
  saved the pessimism.
- What was genuinely needed: seven small facts about `Σ_{i<n}` (`sumTo` and six
  lemmas), then `Pat.leafCount_inst` and three lines of arithmetic. The whole
  general-arity section is shorter than the arity-1 section's prose.
- Lean friction, two items. `sumTo_congr` made `rw` unify against the wrong
  function inside the sum, so distributivity got its own lemma
  (`sumTo_add_mul`) — worth remembering that congruence-style lemmas over
  higher-order arguments are unreliable for `rw`. And `interval_cases` is
  Mathlib-only; `rcases i with _|_|_|k` with an `omega` tail is the
  zero-dependency replacement.
- Kept the superseded Stage 14 "what remains" section in the file, marked as
  such, with the correction beneath it. A mis-framing that produced a wrong
  difficulty estimate is more useful preserved than deleted, and this file
  already does that for C2's pre-resolution text.
- **C4 was the last conjecture on the list that was both open and unambiguously
  ours.** What is left: C6 (ours, but low materiality and cheap, deliberately
  not promoted), criterion (a) (blocked on the adequacy abstraction — Stages
  10–13, and the difficulty estimate there has moved upward three times), the
  transcription items (C1(a), C5), and the prize question itself.
- Pattern check across the last two stages: Stage 14's estimate was the first to
  hold up on contact, and Stage 15's was wrong in the OPTIMISTIC direction's
  mirror — I over-estimated the cost. So the running tally is now: four
  under-estimates of difficulty (Stages 8, 10, 13 on piece vi; and the original
  C4 framing) and one over-estimate (Stage 14 on general arity). The common
  cause is the same in both directions: I was estimating from the first
  representation that came to mind rather than from the problem. Worth carrying
  forward as "estimate after choosing the representation, not before".

## 2026-07-24 — Stage 16: reading the spec's actual words, and writing up

- Three items this stage, all from a fourth ideonomy pass whose matrix put
  "write the program up" as the highest-weight row — an action that had never
  appeared on any of my rankings, because I had been ranking conjectures, then
  pieces, and never deliverables.
- **The criterion (a) resolution, which came out sharper than the review that
  prompted it.** The review framed it as a letter-vs-spirit ambiguity: the
  criterion says "certify known-universal systems" without naming a host, so a
  cheap reading was available. Reading the spec's actual sentence killed that
  framing and produced a better one. It says "certify known-universal systems
  INCLUDING ONE-COMBINATOR BASES" — it names its targets, and one of those
  targets is something this program REFUTED. C4 at every arity says no
  first-order one-combinator one-rule system meeting the growth condition can
  host SK. So criterion (a) as written is unsatisfiable in first-order scope, and
  the reason was sitting in the spec's own Background section the whole time
  (Barker's ι universality is λ-level and erasing). Stage 4 had registered the
  deviation; nobody had connected it to whether the criterion could be met.
- That is a better outcome than the cheap reading would have been, and it is
  worth noting why: the review's framing was built from the LEDGER'S PARAPHRASE
  of the criterion, not from the criterion. Fourth time now that going back to
  the source document beat reasoning from the accreted summary.
- **The general clause discharged**, with the cheapest honest instance: a tag
  system embeds in a tag system over `Option Sym`. Both sides are m = 2 tag
  systems, hence known-universal externally. Two properties `pureS_in_SK` did
  not have — the source is known-universal, and `bwd` is EARNED rather than free,
  since the encoder is not an inclusion. And it is the first non-degenerate use
  of Stage 8's `Simulation.ofAbstraction`: Stage 8's own use was the
  `pureS_in_SK` rebuild, where nothing stutters because the encoder is the
  identity on carriers. Eight stages later the machinery had a real customer.
- Scoped hard in the file, because the overclaim was available and attractive:
  this says NOTHING about SK. It shows the positive side is not vacuous when the
  source must be known-universal. Tag → SK stays research-blocked.
- Lean friction, one item: `List.drop_cons_eq_cons_drop_of_pos` does not exist,
  and is not needed — taking the source step in `stepRel`'s own canonical form
  (`w.drop m ++ rule a`, with `w = x :: t` left intact) means the `drop` never
  has to be decomposed. I had reached for the decomposition automatically. Same
  failure shape as Stage 15's list-vs-function representation choice.
- **STATUS.md**, the write-up. The ledger and this notebook are both
  chronological and together run to several thousand lines, so neither answers
  "what is settled?" — a reader would have to reconstruct it from sixteen stage
  sections. STATUS.md answers it by spec goal, with theorem names, and I checked
  all thirty cited names resolve against the tree before committing. README now
  points at it.
- **The Mathlib decision, made once.** The spec lists zero-dependency as a
  non-goal with an escape hatch, and the hatch had never been considered in
  sixteen stages. Tax counted: four `Classical.choice` traps, two Mathlib tactics
  replaced, one `eraseDups` direction, two list-filter lemmas, a seven-lemma
  `sumTo` battery. Decision: KEEP zero dependencies — nothing open is blocked on
  Mathlib, since the remaining items are a research problem, transcription, and
  C6. Recorded so "we never decided" stops being the state.
- Where the program is: Goal 1 done, Goal 2 built-and-calibrated with one open
  instance, Goal 3 closed, Goal 4 ongoing-by-design. One substantive item left
  (Tag → SK adequacy) and it is research-blocked. The C-list is exhausted apart
  from C6, which three consecutive reviews have declined to promote.

## 2026-07-24 — Stage 17: the ladder was in the spec the whole time

- The fifth ideonomy pass asked how many things were left. The answer was one
  research problem and no portfolio — which is why the previous three reviews had
  felt thin: with cardinality one at the top there is no ranking problem, only a
  do-or-don't decision. The substitution test on cardinality ("what would the
  swarm form be?") is what found the ladder, and the ladder was not my invention:
  it is the second component of the spec's Stage 5, one paragraph below the north
  star I closed in Stage 6.
- Fifth time going to the source document beat the accreted summary — and the
  first time it produced a whole workstream rather than a correction. Worth
  separating those two outcomes in the record, because they call for different
  habits: corrections argue for re-reading before claiming, a missed workstream
  argues for re-reading before PLANNING.
- **Rung choice was deliberate and not by ease.** {S,I} is where the program's
  only negative mechanism dies. Every refutation in the tree — pure S, ι, C4 at
  every arity — routes through `RS.Acyclic.of_strict_measure`. If {S,I} has a
  cycle then that hypothesis is unsatisfiable there, so the rung tests the main
  tool at its boundary instead of applying it again. Testing a tool where it
  should fail is more informative than another success.
- It has a cycle: `(S I I)(S I I)` in three steps, `I` primitive. Axiom-free, and
  it went in without friction. Then two strictly stronger statements: NO monotone
  measure exists in either direction. That is worth the extra two theorems —
  "there is no such measure" is a very different claim from "we did not find one",
  and the second is what a reader would otherwise assume.
- **The finding I did not expect**, and it corrects something the ledger has
  implicitly allowed since Stage 2: erasure-freeness is NOT what keeps pure S
  acyclic. {S,I} erases nothing either — neither rule discards an argument — and
  it cycles. The Stage 2 conservation laws (K-freeness closed under reduction, no
  erasure) sit right next to C2's acyclicity in the ledger, and it would be easy
  to read the first as explaining the second. It does not. Whatever τ measures is
  specific to S-only reduction.
- Scoped rungs two and three rather than attempting them, and got one real data
  point for free: the obvious Ω attempt for {S,B} TERMINATES, because `B` with
  fewer than three arguments is stuck, so `S B B (SBB)` reduces to a normal form.
  That is weak evidence {S,B} may be acyclic and therefore refutable by the
  EXISTING mechanism — the opposite verdict from rung one. If that holds, rungs
  one and two disagree, which is exactly the kind of contrast that "narrows where
  universality is lost".
- Arithmetic recorded for both: {S,B} and {S,C} pair a strictly decreasing rule
  (−1) with S's (+|x|−1 ≥ 0), so leafCount is non-monotone in both directions and
  a combined τ-style measure is needed. That is a C2-sized slice each, and now the
  next slice knows the shape before starting — which is the thing my difficulty
  estimates have most consistently failed at.
- Lean friction, one repeat: `induction` on `RS.Steps` at a concrete instance hits
  the mkElimApp motive error for the third time in this tree. Raw recursor as
  before. Worth noting it is now a known local idiom rather than a surprise —
  `iota_steps_le`, `RS.Discrete2_steps_eq`, and now `SI_no_decreasing_measure`.
- Ranking: (1) **rung two, {S,B}** — has a plausible verdict (acyclic) and would
  make the ladder's first contrast; (2) rung three, {S,C}; (3) Tag → SK, still
  research-blocked and still the only other irreversible item; (4) transcription
  (C1(a), C5); (5) C6, declined a fifth time.

## 2026-07-24 — Stage 18: a five-line theorem and an honesty correction

- Sixth ideonomy pass. Its operator pair repeated from the fourth, so all its
  value came from the fresh organon and prompts — worth recording, because it
  says the picker's organon/prompt axes are now carrying more than the operator
  axis. Three items, two of them corrections to Stage 17, which I had shipped
  one stage earlier.
- **The hierarchy, from the hierarchicalness prompt.** I had written the ladder up
  as a flat set of independent rungs. Basis inclusion was sitting on it the whole
  time, and the machinery was already in the tree: the contrapositive of
  `PathEncoding.refute_of_acyclic` says cycles propagate along path encodings.
  Five lines, axiom-free. Rung one goes from one basis to an upward-closed family.
- Built the concrete witness rather than asserting the propagation: `{S,I}`
  path-encodes into SK by sending primitive `I` to `S K K`, and
  `SK_not_acyclic_via_rung1` re-derives SK's non-acyclicity from rung one. That
  fact was already known here by the Ω ↔ M cycle, so this is a second independent
  route to it — which is the point. A generic theorem whose first instance
  re-proves something already known by another route is a theorem you can trust.
- Injectivity needed one helper I had not anticipated: `siToTerm_ne_K`. `I`'s
  image is `S K K`, which contains `K`s, so injectivity is not immediate — it
  holds because nothing in the SOURCE maps to `K`, there being no `K` in `{S,I}`.
  Small, but it is the kind of thing that would have blocked the encoding if the
  source basis had contained K.
- **The correction that matters: the ladder answers ACYCLICITY, not
  universality.** The spec says "classify universality of bases". What the program
  can deliver per rung is acyclicity, which bounds only refutability. Rung one
  does not say {S,I} is or is not universal — it says the refutation tool cannot
  reach it. Stage 17's write-up omitted this, and rung one reads like a
  universality result without it.
- That is worth dwelling on because of the timing: in Stage 16 I explicitly
  scoped the `Tag → Tag` result against exactly this misreading, wrote a SCOPE
  paragraph before the theorem, and said in the notebook that the overclaim was
  "available and attractive". One stage later I made the same class of overclaim
  in a different place and did not notice until a review asked. The discipline is
  not transferring between stages on its own; it is transferring because the
  reviews keep asking. Something to keep in mind if the reviews stop.
- Also wrote the rung procedure down, with the ordering rationale — step 3 before
  step 4, because a cycle makes step 4 provably futile. Rung one got that right by
  luck. And named rung 2's step-4 tool concretely: a lexicographic measure, since
  neither component is monotone alone on {S,B} or {S,C}. That is a sharper start
  than "τ-style combined measure", which is what Stage 17 left.
- Not attempted, and registered: the joinability-insensitive abstraction lifter
  that the modularity prompt identified as the missing module for Tag → SK. The
  reasoning there is sound — the program's modular parts all finished cheaply and
  its one monolithic part is the one blocked — and the ingredients are present
  (`ChurchRosser`, `Joinable`, SK confluence). It is the honest route to Goal 2's
  open instance and it is a research-grade attempt, not bulk work.
- Ranking: (1) **rung two, {S,B}**, now with a written procedure and a named tool;
  (2) the joinability-insensitive abstraction lifter, as the modular route to
  Tag → SK; (3) rung three, {S,C}; (4) transcription (C1(a), C5); (5) C6,
  declined a sixth time.

## 2026-07-24 — Stage 19: the procedure earned its keep immediately

- First stage run against the written-down rung procedure, and it caught me. Step
  3 says "hunt for a cycle"; Stage 17 had done ONE hand-traced Ω attempt and
  recorded it as weak evidence, then let that single trace carry a verdict into
  the STATUS.md table. The procedure says a hunt, so I built the census — and the
  census disagreed with the trace's implications within two minutes of running.
- What changed: up to 6 leaves everything normalizes, which is what the Ω trace
  suggested. At SEVEN leaves, 6 of 16896 terms do not normalize at fuel 200, and
  still 6 at fuel 1000. So {S,B} is not plausibly strongly normalizing at all. It
  is plausibly ACYCLIC and plausibly NON-NORMALIZING — which is exactly pure S's
  profile, C1 plus C2.
- The Stage 17 error was small but instructive: I wrote "weak evidence it may be
  acyclic and therefore refutable by the existing mechanism". The first clause was
  fine. The second silently assumed acyclic ⇒ terminating, and this project has a
  theorem saying otherwise — pure S is acyclic and (externally) has
  non-normalizing terms. I had the counterexample in my own tree and still made
  the inference.
- **The free cross-validation is the nicest thing here.** Pure-S terms are
  {S,B}-terms, so the rung-2 census strictly contains the rung-0 census. Two of the
  six exhausted terms at 7 leaves are exactly C1's candidates, and
  `S S S (S S) S S` came back with 120112 leaves after 200 steps — the identical
  figure CONJECTURES.md has recorded for `c1` since Stage 0, now reproduced by a
  reducer written independently for a different term type. Neither census was
  built to check the other; the containment made it happen for free.
- Also refined Stage 17's headline finding. Stage 17 ruled out erasure-freeness as
  the explanation for pure S's acyclicity but did not say what replaced it. The
  rung-2 data does: **arity**. `I` takes one argument, so `S I I x → (I x)(I x) →
  x x` fires and returns. `B` takes three, so `S B B x → (B x)(B x)` leaves
  everything one argument short and stalls. Rung one cycles and rung two does not,
  and the discriminator is neither erasure nor duplication.
- Step 4's target got sharper as a side effect: not a termination measure — the
  fuel-outs rule that out — but a τ-style ACYCLICITY measure, which is precisely
  what C2 needed and got for pure S. That is a much better-specified slice than
  "combined measure", which is where Stage 17 left it.
- Register kept: all of this is unverified census tooling plus build-enforced
  `#guard`s over a bounded search. "No cycle found up to 7 leaves" is not
  acyclicity, exactly as the pure-S census's fuel-outs are not divergence. Written
  into the module header.
- Ranking: (1) **rung two step 4** — the τ-style acyclicity measure for {S,B}, now
  the best-specified open item on the board and a direct analogue of a slice that
  already succeeded once; (2) the joinability-insensitive abstraction lifter for
  Tag → SK; (3) rung three {S,C}, which the same census tooling extends to almost
  for free; (4) transcription; (5) C6, declined a seventh time.

## 2026-07-24 — Stage 20: my own step-4 specification was wrong

- Stage 19 ended by sharpening step 4's target to "a τ-style acyclicity measure,
  lexicographic". One stage later that specification is disproved. This is the
  second consecutive stage where the previous stage's forward-looking claim did not
  survive contact, and both times the claim was mine and made confidently.
- The arithmetic is short enough that I should have done it before specifying.
  Under `S_red` the third argument is DUPLICATED, so any count of anything present
  in that argument can rise; under `B_red` a `B` is consumed and nothing is
  duplicated, so B-count falls. Those two facts alone make every counting measure
  non-monotone. `no_monotone_counting_measure` proves it for all weights `a, b` at
  once, and the proof is entirely witness selection — four concrete terms, chosen
  by which of `a`, `b` is positive.
- **Why this matters more than a corrected note:** C2's argument is a SQUEEZE, not
  a decreasing measure, and I had been carrying it forward as though the hard part
  were "find the τ analogue". The hard part is step (a) — having a monotone
  quantity at all so that a cycle is forced to be constant on it. Pure S has one
  for free (leafCount, by non-erasure). {S,B} has none. Naming the load-bearing
  step of a past success turned out to be what identified why it does not transfer.
- Also killed "lexicographic" specifically, which I had offered as the fix in Stage
  19: a lexicographic order needs its first component monotone. There is no
  monotone first component. So the fix was ruled out by the same theorem that
  ruled out the original.
- What is left is honestly named rather than optimistically scoped: a non-counting
  STRUCTURAL measure (τ weights by POSITION — `2τ(a) + τ(b)` — which is not a
  count, and that distinction is the live hint), an interpretation argument, or the
  census is wrong about there being no cycle. I gave that last option real weight
  in the write-up, because the hunt reached 7 leaves and rung one's cycle lives at
  6. Two consecutive over-confident forward claims is enough reason to stop rating
  "nearly done".
- Runtime: the 8-leaf hunt (109824 terms) died at 10 minutes. Diagnosed rather than
  just reported — `sbOnCycle` keeps a seen-LIST and calls `contains`, so it is
  quadratic per term. Same class of problem as the Stage 6 census, where dropping
  the measurement C6 did not need made n=10 reachable. A faster detector is a
  cheap unblock if the hunt is worth extending.
- Estimate tally, updated: five under-estimates, one over-estimate, and now two
  wrong forward SPECIFICATIONS (Stage 19's lexicographic target, Stage 17's
  "refutable" inference). The pattern has shifted — I am no longer mostly
  mis-rating difficulty, I am mis-specifying the next step. The fix is the same
  one that worked for representations: do the cheap arithmetic before naming the
  target.
- Ranking: (1) a faster cycle detector, then extend the rung-two hunt — cheap, and
  it tests the possibility I am now giving real weight; (2) the
  joinability-insensitive abstraction lifter for Tag → SK; (3) rung three {S,C},
  which the census tooling extends to nearly for free; (4) transcription; (5) C6,
  declined an eighth time.

## 2026-07-24 — Stage 21: the validation step justified itself

- Ranked task was "a faster cycle detector, then extend the hunt". Floyd
  tortoise-and-hare was the obvious fix — `sbStepOnce` is a function, so the
  trajectory is a functional graph and O(1) memory suffices. It worked: n=8 went
  from a ten-minute abandonment to 6 seconds, and n=9 (732160 terms) to 38.
- I wrote it GENERICALLY rather than for `SBTerm` specifically, so it could be
  instantiated on {S,I}. The only reason was to validate the true-positive path —
  I said in Stage 19's write-up that an untested detector reporting "no cycles
  found" is worthless, and rung one supplies a kernel-PROVED cycle to test against.
  That single decision is what produced the stage's finding.
- **The detector did not find rung one's cycle.** For about a minute I assumed a
  bug. It is not: the proved cycle closes with `appR (I_red)` — an INNER redex —
  and leftmost-outermost fires the head S-redex instead. The LO trajectory from
  `omegaSI` goes 6, 8, 7, 10, 9, 8, 12, 11, 10, 9, 14, … growing forever, never
  returning. So a cycle can exist in the RELATION and be completely invisible to a
  leftmost-outermost hunt, and rung one is a worked example.
- That devalues the data I had just spent the stage producing, which is the right
  outcome and worth being blunt about. The {S,B} figures rule out LO cycles. They
  say nothing about the relation. Stages 19 and 20 both leaned on them as evidence
  for acyclicity and both leaned too hard.
- **The part I keep turning over:** Stage 0 already knew this. CONJECTURES.md's C2
  entry has carried "cycle-freedom under ALL strategies is a stronger, separate
  claim; this census only ever runs leftmost-outermost" since the first census. I
  rebuilt that census on a new rung, inherited the identical limitation, and did not
  transfer the caveat. Twenty stages of ledger discipline and the caveat was in the
  file I edit most often.
- Two consolations, neither of which cancels it. First, the caveat is now backed by
  a witness rather than a worry — that is a genuine upgrade, and it is the kind of
  thing that makes a caveat stick. Second, pure S is untouched, because C2 proved
  acyclicity with a measure and never depended on the census. Which is itself the
  lesson: the census generates conjectures, measures settle them, and I have twice
  now let census output stand in for a settled question.
- Tally, updated honestly: five under-estimates of difficulty, one over-estimate, two
  wrong forward specifications, and now one un-transferred caveat. The failure modes
  have moved outward — from rating work, to specifying work, to noticing that a
  method's known limits apply to its reuse. The common thread is that all four were
  cheap to check and none was checked before being relied on.
- Ranking: (1) **rung two under a non-LO strategy** — the hunt should be re-run
  reducing innermost or by a redex-fair strategy, since that is exactly where rung
  one's cycle hides and the tooling now runs fast enough to afford it; (2) the
  joinability-insensitive abstraction lifter for Tag → SK; (3) rung three {S,C};
  (4) transcription; (5) C6, declined a ninth time.

## 2026-07-24 — Stage 22: the right search, and validation before use

- Stage 21's ranking said "re-run the hunt under a non-leftmost-outermost strategy".
  On reflection that was still the wrong framing — swapping one strategy for another
  would have inherited the same class of blindness. Acyclicity is a property of the
  RELATION, so the search has to range over ALL one-step successors. The project
  already had that shape for pure S in Reachability.lean (`succs` + bounded closure +
  `onCycle?`), so this was reuse rather than invention.
- **Validated it before running it**, which is the direct consequence of Stage 21
  and the first time I have done this in the right order. `onCycleAny` finds
  `omegaSI`'s cycle — the kernel-proved one the LO detector provably misses. Two true
  negatives alongside so it is not just answering `some true` to everything. That took
  five minutes and it is the difference between data and noise.
- The result is a genuine upgrade, not just more of the same: every {S,B}-term up to
  8 leaves gets a VERDICT (nothing ran out of fuel) and none is on a cycle within a
  30-leaf cap, under any strategy. And it is cap-insensitive — n=7 gives identical
  verdicts at caps 30, 60 and 120. Fast, too: n=8 in about fifteen seconds where
  Stage 20's quadratic LO detector had been abandoned after ten minutes.
- **The limit is now in a different place, and that is the interesting part.** The
  remaining gap is the size cap: a cycle that swells past 120 leaves and returns is
  not excluded. For pure S that gap would not exist, because leafCount monotonicity
  confines every path inside a finite universe — which is exactly what makes
  Reachability.lean's bounded closure a genuine decision procedure there. {S,B} has
  no monotone quantity (Stage 20's theorem), so the same construction only gives a
  cap-relative verdict. **The absence of a monotone quantity degrades the census, not
  just the proof.** I had been treating Stage 20's negative as a fact about proof
  strategies; it is also a fact about how far searching can get.
- That connection is worth keeping because it says something about the ladder as a
  whole: rungs where a monotone quantity exists admit both proofs and decision
  procedures; rungs where none exists admit neither, and the census degrades in
  exactly the same way the proof does. Rung zero has one, rung two provably does not.
- Ranking: (1) test the cap limit directly — hunt for {S,B} cycles that EXCEED the
  cap by searching from larger seed terms, since that is the only remaining hole and
  the tooling is fast enough; (2) the joinability-insensitive abstraction lifter for
  Tag → SK; (3) rung three {S,C}, where the same tooling transfers immediately;
  (4) transcription (C1(a), C5); (5) C6, declined a tenth time.

## 2026-07-24 — Stage 23: the computational route closed, the analytic one opened

- Ranked task was "test the cap limit directly". Tested it, and it failed
  informatively: raising the census cap from 30 to 200 on the six explosive 7-leaf
  terms did not finish in ten minutes. That is the expected shape — those terms grow
  to ~130k leaves and the all-strategies closure under a generous cap explores
  enormous numbers of interleavings — but it is worth having measured rather than
  assumed, because it converts "the cap is a limitation" into "the cap is not
  liftable by brute force", which is what justifies switching approaches.
- So I switched to the analytic route, and Stage 20 had already left the pointer:
  its theorem rules out linear COUNTING measures, and τ is not a count. τ weights by
  POSITION — `2τ(a) + τ(b)` — which is exactly why it escaped that theorem. I had
  written that sentence in Stage 20 as a hint and then not followed it for three
  stages.
- τ turns out to behave beautifully on B and awkwardly on S, which is the useful
  asymmetry. On a B-reduction it strictly drops by `2τ(x) + 8 ≥ 10`, always — `B`
  duplicates nothing so there is no compensating term. On an S-reduction it moves by
  exactly `2τ(x) - 8`, so it drops iff the duplicated argument is light. Both are
  one-line `omega` proofs once the definition is unfolded; the content is entirely in
  choosing τ.
- That gives the C2 shape back. C2 could not use τ globally on pure S either — it
  isolated the ISOMETRIC fragment and dropped τ there. Here the isolable fragment is
  the τ-LIGHT one, and `sbLight_acyclic` is the analogue. It is a genuine positive
  result about rung two, and it narrows the remaining question from "is there a
  cycle anywhere" to "is there a cycle firing an S-reduction on a τ-heavy argument".
- Worth noticing how the three stages compose rather than repeat: Stage 20's negative
  (no counting measure) told me which class to leave; Stage 22's census bounded where
  a cycle can be; Stage 23's fragment bounds what a cycle must DO. None of them
  settles rung two and each narrows it differently. That is what a ladder rung is
  supposed to look like, and it is the first time in this program that three
  consecutive stages have accumulated instead of one correcting the next.
- Small tidy: added `RS.Acyclic.of_decreasing_measure` to Taxonomy as the dual of
  `of_strict_measure`. Stage 17 had inlined an ad-hoc copy inside
  `SI_no_decreasing_measure`; now there is one general lemma and both users take it.
- Ranking: (1) **hunt specifically for τ-heavy cycles** — the search space is now
  named, so seed the strategy-independent hunt only from terms that can fire an
  S-reduction on a τ-heavy argument, which should be far cheaper than the
  unrestricted cap-lift that just timed out; (2) rung three {S,C}, where τ should be
  computed the same way and may behave differently, since `C x y z → x z y`
  duplicates nothing either; (3) the joinability-insensitive abstraction lifter for
  Tag → SK; (4) transcription; (5) C6, declined an eleventh time.

## 2026-07-24 — Stage 24: the measure that can tell two rungs apart

- Ranked task was "hunt specifically for τ-heavy cycles". I started on it and the
  arithmetic pulled me somewhere better. Generalising τ to `τ_k(app a b) = k·τ_k(a) +
  τ_k(b)` gives S-delta `k(τ_k(x) − k²)`, so the light fragment GROWS with k — `S (S
  S)` is heavy at k=2 and light at k=3. Attractive, but the general-k lemmas are
  nonlinear in k and `omega` cannot do them; `ring` would, and this tree has no
  Mathlib. Tested that before building on it, which is the habit finally sticking.
  Recorded the family as arithmetic and moved on rather than triplicating the k=2
  machinery for k=3 and 4.
- Where it led instead: I noticed while computing deltas that `C x y z → x z y` has
  the SAME leafCount delta as `B x y z → x (y z)`. Both remove one leaf. So no
  counting measure can distinguish rungs two and three at all — which given Stage
  20's theorem (no counting measure is monotone on {S,B}) means counts are useless
  twice over here.
- τ distinguishes them, and sharply. B always lowers τ, by `2τ(x) + 8`. C's delta is
  `τ(z) − τ(y) − 8`, which is POSITIVE whenever the third argument is much heavier
  than the second — because permuting moves a heavy term from the outer position
  (weight 1) into an inner one (weight 2). I found two C-reductions with identical
  leafCount deltas and opposite τ deltas, 29→35 and 43→21, and guarded both. That
  pair is the whole point of the stage in two lines.
- Consequence for rung three: its light fragment needs TWO conditions where rung
  two's needed one, since the permuting rule also has to be restricted. So
  `scLight_acyclic` is a weaker foothold than `sbLight_acyclic`, and rung three is
  further from a proof than rung two — which is the opposite of what I would have
  guessed from the rules' surface similarity.
- Stage 22's genericity paid off exactly as hoped: `onCycleAny` is generic over the
  term type, so rung three's strategy-independent hunt cost one successor function.
  No cycle up to 6 leaves, every term verdicted. Writing that detector generically
  two stages ago to enable a validation has now also given a whole rung for free.
- The theme across 20, 23 and 24 is worth naming: **counts see size, positional
  measures see structure.** Stage 20 proved counts cannot settle rung two. Stage 23
  found τ handles B. Stage 24 finds τ also SEPARATES B from C where counts cannot.
  Three stages, one moral, and it arrived by accumulation rather than correction —
  the second such run in this program.
- Ranking: (1) the τ-heavy cycle hunt for rung two, which I deferred this stage and
  which is now the only narrowing left there; (2) rung three's C-heavy analogue of
  the same question; (3) the joinability-insensitive abstraction lifter for Tag → SK;
  (4) transcription (C1(a), C5); (5) C6, declined a twelfth time.

## 2026-07-24 — Stage 25: the highest-ranked item did not apply

- The seventh review put "read the tree-automata papers" first, with a sharp
  argument: Stage 6 surfaced them, I registered them, and then hand-rolled 1980s
  polynomial interpretations for eighteen stages without going back. That critique was
  fair. The papers still turn out not to apply, and finding that out took two fetches.
- The 2024 paper is **sole-combinator only** — one combinator, explicitly. My rungs
  are all two-combinator systems, so it is out on scope alone. Endrullis-Zantema is
  general TRS and does cover {S,B} and {S,C}, and even works on the S-rule. But:
- **both prove NON-TERMINATION, and my open questions are ACYCLICITY.** That is the
  crux and it took me a minute to see, because I had been treating "the literature's
  tooling for this problem class" as one bucket. It is not. Non-termination is about
  infinite paths; acyclicity is about returning ones. This program contains the proof
  they come apart — pure S is acyclic (C2, proved here) and non-terminating (external,
  Stage 6). A regular language closed under rewriting with no normal forms certifies
  an infinite path; it says nothing about return.
- So the eighteen-stage "gap" the review identified was not a gap. The field's
  automata methods target a neighbouring property, and measures are the right tool for
  mine. That is a better outcome than either "the papers solve it" or "I wasted
  eighteen stages" — but I could not have known which without reading them, and the
  review was right to insist.
- Worth keeping as a distinction I will need again: **a technique's problem CLASS and
  a technique's target PROPERTY are separate filters.** I checked class (does it handle
  two combinators?) and would have stopped there if the 2024 paper had been general.
  Property is the filter that actually excluded both.
- Item 2 went in: the τ threshold bootstraps. Chaining τ against leafCount — heavy
  S-reds need |x| ≥ 3, so they raise leafCount by ≥ 2, so a cycle needs at least two
  B-reductions per heavy S-reduction, so the τ budget forces average τ(x) ≥ 14, not
  4. Per-step facts proved; the summation is arithmetic and left informal, because
  classifying every step of a path needs a path-indexed induction with an accumulator
  per class.
- **And I wrote down why it stops**, which I think is the more valuable half.
  Iterating gives `T' = 5·f(T) − 1` where f is the least size admitting τ ≥ T. Max τ
  on n leaves is 2ⁿ−1, so f is logarithmic, so T' grows logarithmically and the
  iteration fixes around τ ≥ 24. τ grows exponentially in size while the constraint
  grows linearly. Recording the limit of an argument family costs a paragraph and
  saves someone re-deriving it — the same reason Stage 14's mis-framing was kept.
- Item 3 answered cheaply and negatively: no {S,B}-term up to 7 leaves acts as an
  identity on four structurally distinct probes. So rung one's cycle has no transport
  route into rung two at small size, which closes the chart's emptiest cell and is
  consistent with {S,B} being acyclic.
- Item 4, and I think it is the quiet correction of the stage: the spec says a rung is
  *"a publishable partial result that narrows where universality is lost"*. I have been
  reporting rungs 2 and 3 as OPEN, which is true and reads as failure. Against the
  stated purpose they are DELIVERED — rung 2 alone has a proved impossibility, an
  acyclic fragment, a bootstrapped necessary condition, a closed transport route, and a
  strategy-independent census. STATUS.md now leads with what each rung ESTABLISHED.
  Fifth time re-reading the spec changed how I was reporting rather than what I was
  doing.
- Ranking: (1) formalize the cycle summation, converting the bootstrap from arithmetic
  into a theorem — it is the last piece of rung two that is clearly reachable;
  (2) rung three's C-heavy analogue of the bootstrap; (3) the joinability-insensitive
  abstraction lifter for Tag → SK; (4) transcription (C1(a), C5); (5) C6, declined a
  thirteenth time.

## 2026-07-24 — Stage 26: redirected before building, and it paid

- Ranked task was formalising the τ ≥ 14 summation. I did the arithmetic first — the
  habit that has now caught three stages in a row — and it said: per-class path
  accounting, one accumulator per step kind, ~150 lines, to TIGHTEN a bound whose
  argument family I had myself proved caps near τ ≈ 24 one stage earlier. Tightening a
  known-capped bound is the least valuable thing available. Redirected.
- What I redirected to came from re-reading my own Stage 20 arithmetic: B-reduction is
  the only shrinking rule, so on the S-ONLY fragment leafCount is monotone. And
  monotone leafCount is exactly the ingredient C2 needed and {S,B} as a whole lacks
  (Stage 20's theorem). So C2's squeeze transplants to the sub-fragment verbatim: cycle
  forces leafCount constant, constancy forces atomic arguments, τ drops by 6.
- The formalisation detail worth keeping: the per-step lemma has to state BOTH halves
  in one conjunction — "leafCount never shrinks" AND "if leafCount is unchanged then τ
  strictly drops". Stating them separately does not work, because the path induction
  needs to pin leafCount across the whole path first and then reach back into the FIRST
  step for the strict drop. I tried it as two lemmas, saw the induction fail to close,
  and merged them. That is a small piece of proof-engineering knowledge that
  generalises to any squeeze argument.
- Result: `sbCycle_needs_B` — any {S,B} cycle contains a B-reduction. New, and
  independent of everything else known about rung two.
- **What I like about the state of rung two now is that the constraints COMPOSE.** A
  cycle must contain a B-reduction (26), must fire a τ-heavy S-reduction (23), and needs
  at least two B-reductions per heavy S-reduction (25). Three independent derivations,
  one joint condition. That is different from the earlier stretches where each stage
  corrected the last; this is the third accumulating run and the longest.
- Fourth occurrence of the mkElimApp motive error on `RS.Steps` at a concrete instance.
  Raw recursor, as in `iota_steps_le`, `RS.Discrete2_steps_eq`, `SI_no_decreasing_measure`.
  It is fully a known local idiom now and cost nothing.
- Ranking: (1) rung three's analogue — does {S,C} have an acyclic S-only fragment too?
  It should, by the identical argument, since C is also the only shrinking rule there;
  cheap and it would give rung three its second constraint; (2) the joint condition on
  rung two is now specific enough to guide a targeted search — hunt for cycles among
  terms that can host both a B-reduction and a τ-heavy S-reduction; (3) the
  joinability-insensitive abstraction lifter for Tag → SK; (4) transcription (C1(a),
  C5); (5) C6, declined a fourteenth time.

## 2026-07-24 — Stage 27: a second transplant, and a claim I checked before making

- Ranked task was rung three's S-only fragment, predicted to work "by the identical
  argument". Checked the arithmetic first: C's leafCount delta is −1, same as B, so C is
  {S,C}'s only shrinking rule and the S-only fragment has monotone leafCount. Prediction
  held, and the Stage 26 proof transplanted with only the names changed.
- I duplicated rather than abstracted, and wrote down why. The two S-only fragments are
  literally the same system — pure S over a two-symbol alphabet — so the honest
  generalisation is a term type parameterised by its atom set, plus transport lemmas.
  That is more code than the copy and adds indirection for exactly two instances. If a
  fourth rung appears I would abstract; at two, copying is right. Recording the judgment
  matters more than the judgment, since the next reader will notice the duplication and
  should know it was chosen.
- Rung three now has two constraints (τ-light fragment acyclic, and cycles need a
  C-reduction) plus the structural finding about τ separating it from rung two. That is
  a rung, by the spec's definition.
- **The part I am most pleased about is a negative I nearly skipped.** Stage 26's
  ranking said the composed condition on rung two "is now specific enough to guide a
  targeted search". Before building that search I measured whether the condition
  actually prunes. It does not: filtering seeds to terms containing a B with ≥ 5 leaves
  keeps 99.6% of 8-leaf terms. The reason is structural, not a bad filter choice — the
  condition constrains the STEPS a cycle contains, not the SEEDS a search starts from,
  and almost any moderate term can in principle reach such a step.
- That distinction is worth carrying: **a necessary condition on a path is not
  automatically a filter on starting points.** I had conflated them in the Stage 26
  ranking, and the conflation would have produced a "targeted" search identical in cost
  to the untargeted one, which I would then have reported as a targeted search finding
  nothing. The condition could drive pruning DURING exploration, which is a genuinely
  different algorithm.
- Score for the session's habit: three stages running where doing the cheap check first
  changed what I built (25: the papers didn't apply; 26: the ranked task was tightening
  a capped bound; 27: the composed condition doesn't prune). The habit is no longer
  occasional.
- Ranking: (1) pruning-during-exploration for rung two — the one use the composed
  condition genuinely has, and a real change to `onCycleAny` rather than a filter on its
  input; (2) the joinability-insensitive abstraction lifter for Tag → SK, still the only
  route to Goal 2's open instance; (3) transcription (C1(a), C5); (4) C6, declined a
  fifteenth time.

## 2026-07-24 — Stage 28: the accounting I kept deferring was not needed

- Ranked task was pruning-during-exploration, the one use Stage 27 had left the composed
  condition. Checked it first — fourth stage running — and it is not available. Sound
  pruning needs a localizable certificate that the seed is unreachable from a state, and
  every constraint I have on rung two is a global sum over a whole cycle. Global sums do
  not localize. So both uses I had claimed for the composed condition (seed filtering in
  Stage 26, exploration pruning in Stage 27) are gone.
- Then the useful part. While working out WHY the sums don't localize, I noticed the
  composed condition itself does not need the sums. I had been carrying "Σ over S-reds of
  #B(x) = #B-reds" as an unformalised summation since Stage 25 and treating its
  formalisation as a 150-line accounting job I kept deferring. The contrapositive is a
  squeeze: if no S-reduction duplicates a B, #B never rises and strictly falls on every
  B-reduction, so a cycle has no B-reduction, so it lives in the S-only fragment, which I
  proved acyclic two stages ago.
- **So the accounting was never needed.** Three stages of deferring a formalisation I had
  mis-scoped, and the fix was to state the negation as a fragment and squeeze it. That is
  the same move as Stages 26 and 27, applied one level deeper — three levels now: #B, then
  leafCount, then τ, each pinning the next.
- The engineering lesson from Stage 26 held and sharpened: the levels MUST travel in one
  invariant. I wrote it as three nested conjunctions and it went through; separating any
  level fails, because the path induction pins the outer measure across the whole path and
  then has to reach back into the first step for the inner strictness. Now confirmed at
  depth three, so it is a pattern rather than a coincidence.
- Pleasing side effect I did not plan: the no-B-duplication fragment strictly contains the
  S-only fragment, since it admits every B-reduction as well. So Stage 26's
  `sbSOnly_acyclic` is now a corollary of Stage 28's theorem rather than an independent
  result. The ladder's rung-two evidence got simpler as it got stronger, which is unusual
  and worth noting.
- Standing on the "check first" habit: four consecutive stages where checking changed the
  work (25 papers, 26 capped bound, 27 seed pruning, 28 exploration pruning). In three of
  the four, the check ALSO surfaced the better target — the checking is not just avoidance,
  it is where the redirection comes from.
- Ranking: (1) the joinability-insensitive abstraction lifter for Tag → SK — now clearly
  first, since rung two's constraints have converged to a proved syntactic condition and
  the remaining narrowing there needs a genuinely new idea rather than another fragment;
  (2) transfer the three-level squeeze to rung three ({S,C}'s no-C-duplication fragment),
  which should work by the same pattern; (3) transcription (C1(a), C5); (4) C6, declined a
  sixteenth time.

## 2026-07-24 — Stage 29: the deferred proposal, checked and refuted

- The joinability-insensitive abstraction lifter had sat at or near the top of my ranking
  since Stage 10 — nineteen stages — always as "the honest route to Goal 2's open
  instance", always deferred as research-grade. This stage finally checked it, fifth
  consecutive stage where checking came before building, and it does not work.
- What I built first, because any version of the proposal needs it: the abstraction as a
  RELATION rather than a function. `bwd_of_abstraction_rel`, with Stage 8's function
  version recovered as the special case `absR b a := (abs b = some a)`. That
  generalisation is correct, axiom-free, and genuinely required — a joinability-style
  abstraction cannot be a computed function, since "decodes to" becomes a semantic
  condition. So the infrastructure stands regardless.
- The relaxation has a price I had not anticipated: the relation must be FUNCTIONAL ON
  THE IMAGE of `enc`. With a function that was free (`abs (enc a) = some a` gives it
  immediately). With a relation it is a real hypothesis. And it is precisely where
  joinability dies.
- **`Joinable · (enc ·)` relates an encoded state to every source state it came from.**
  One line to prove: if `a` steps to `a'` then `enc a` reaches `enc a'`, so `enc a'` is
  joinable with `enc a` — and trivially with itself. So it relates `enc a'` to two
  distinct source states, and functionality fails as soon as the source has any
  nontrivial step. The proposal fixes drift by being so coarse that it cannot tell
  machine states apart at all.
- **The shape of the whole obstruction, which is what I want on record.** The two
  candidate abstractions fail in opposite directions. Syntactic is too FINE — copies
  drift, it loses track. Joinability is too COARSE — it collapses the trajectory. A
  workable abstraction sits strictly between and neither obvious construction is there.
  That is a much better description of Goal 2's blocker than "research-blocked", which is
  what I had been writing for ten stages without knowing which way it was blocked.
- Worth noting what this cost and bought: one stage, four axiom-free theorems, and the
  retirement of a proposal that had been consuming the top of my ranking for nineteen
  stages without ever being examined. Deferring it was defensible each individual time —
  it always looked expensive next to a cheap ladder rung — but nineteen consecutive
  defers of the same item is a pattern, and the item turned out to be cheap to REFUTE
  even though it would have been expensive to BUILD. Refuting is often the cheaper half
  and I should test that first more often.
- Ranking: (1) transfer the three-level squeeze to rung three's no-C-duplication
  fragment — cheap, mechanical, and gives rung three parity with rung two;
  (2) transcription (C1(a), C5), now the largest remaining item that is definitely
  achievable; (3) C6, declined a seventeenth time. Note criterion (a) has left the
  ranking: it is a stated obstruction now, not a task, and it should return only if
  someone has a candidate abstraction that is neither syntactic nor joinability-based.

## 2026-07-24 — Stage 30: abstracting at the right threshold, one stage late

- Ranked task was rung three's no-C-duplication fragment. Checked the arithmetic first
  (sixth stage running): `#C` falls by 1 on a C-reduction and rises by `#C(x)` on an
  S-reduction, exactly like `#B`, because C permutes without duplicating. So Stage 28's
  three-level squeeze transfers.
- But this would have been the FOURTH hand-written copy of the same argument, and in Stage
  27 I had written "if a fourth rung appears I would abstract; at two, copying is right."
  That threshold was wrong: what matters is the number of INSTANCES, not the number of
  rungs. Two rungs have produced four instances. So I abstracted before adding the fourth.
- The abstraction is `RS.Acyclic.of_three_level`, and finding it clarified what had
  actually been duplicated: the path lemma and the final contradiction, every time. The
  per-step lemmas were always genuinely different. So the generic lemma takes the per-step
  invariant as its hypothesis and all four instances collapse to one line each.
- **The part I did not expect: this is C2's argument.** C2 — pure-S acyclicity, the
  program's first resolved conjecture, Stage 5 Slice 2 — is a two-level squeeze
  (leafCount monotone, then τ strictly dropping on the isometric fragment). It is the same
  lemma with `m1` constant. Nine stages of ladder fragments have been re-deriving the
  shape of the program's own earliest theorem without my noticing, and abstracting made
  it visible. That is a better argument for abstracting than the line count was.
- Rung three now has the same three constraints as rung two, and at both rungs the
  no-X-duplication fragment strictly contains the S-only one, so the S-only results are
  corollaries. The evidence got simpler at both rungs as it got stronger — same effect as
  Stage 28 noted at rung two, now symmetric.
- Cost note for honesty: the refactor touched three working proofs. I did it in two steps,
  building between them, and both builds stayed green. Refactoring proofs is cheap when
  the generic lemma's hypothesis is exactly the existing per-step lemma's statement — and
  I chose the generic lemma's shape to make that true, which is worth doing deliberately
  rather than discovering afterwards.
- Ranking: (1) transcription — C1(a) (import the known 7-leaf non-normalization result)
  and C5 (λI conservation); the largest remaining definitely-achievable work, and both are
  labelled external so the deliverable is a machine-checked import, not a discovery;
  (2) C6, declined an eighteenth time. The ladder has converged: both rungs have three
  constraints, the shared machinery is factored, and further narrowing needs a genuinely
  new idea rather than another fragment — the same place criterion (a) reached in Stage 29.

## 2026-07-24 — Stage 31: the "external" label was hiding a five-line proof

- Ranked task was transcription: import C1(a) and C5. Checked feasibility first, seventh
  stage running, and C5 turned out not to be transcription at all. The tree can prove it.
- The argument assembled itself once I listed what was available. Confluence (Stage 1) plus
  a NORMAL target forces every term on an infinite sequence to reach that normal form.
  Monotonicity (Stage 2) then caps their sizes. `enum_complete` (Stage 6) makes the capped
  universe a finite LIST. Pigeonhole gives a repeat. C2 forbids repeats. Five ingredients,
  four of them already proved for other reasons, and the fifth a standard combinatorial
  lemma.
- **What strikes me is that every ingredient was built for something else.** Confluence was
  Stage 1's own goal; monotonicity was Stage 2's conservation-laws slice; `enum_complete`
  was built to unblock C1's minimality half in Slice 5 and reused for Goal 3's decidability;
  C2 was Slice 2's resolved conjecture. None was aimed at C5. The theorem was latent in the
  tree for roughly twenty-five stages.
- Fifth Classical.choice near-miss and the same trap as Stage 9. The natural pigeonhole uses
  `List.erase`, and both core erase lemmas report choice, because synthesising `LawfulBEq`
  from `DecidableEq` routes through it. I bisected rather than guessed — two three-line
  test theorems — then rebuilt on `List.filter` with `decide`, which never touches `BEq`.
  Also stated the pigeonhole NEGATIVELY, which keeps it constructive: the conservation
  proof wants a contradiction, not an existential, so `¬ (∀ i j, i < j → f i ≠ f j)` is
  exactly the right shape and needs no classical step.
- Lean note: `set ... with` is Mathlib, not core. Inlined the predicate.
- **The ledger lesson, which I think is the more important half.** The `external` status
  was added in Stage 6 to stop untested claims sitting as "open", and it worked — it caught
  C1 after nine stages. But C5 shows it can be wrong in the OTHER direction: a claim marked
  external because a famous theorem covers it, when a cheaper route existed inside the
  development. Marking something external closed my inquiry into whether the tree could
  prove it. So: an `external` label should record where a claim is KNOWN, not settle
  whether this development can prove it. I have updated the ledger's wording accordingly.
- Consequence for C1(a): its loop route has been waiting on C5 since Slice 3. It is no
  longer waiting. `no_normalForm_of_infiniteRed` means an infinite reduction sequence now
  suffices for non-normalization, with no external dependency.
- Ranking: (1) **C1(a) via an explicit infinite reduction** — build the sequence for `c1`
  directly. The frozen head (Slice 4) says the trajectory is `S A B` with `A` a fixed normal
  form forever, and `frozen_normalizes_iff` reduces the question to the payload; combined
  with C5 the target is now a Nat-indexed sequence rather than a self-embedding witness,
  which is a different and possibly easier object; (2) C6, declined a nineteenth time.

## 2026-07-24 — Stage 32: C1(a) down to one arithmetic gap

- C5 changed what C1(a) needs. Before Stage 31 the loop route waited on an external
  theorem; now `no_normalForm_of_infiniteRed` means an infinite reduction sequence is
  enough, so the whole remaining task is a reducibility invariant `P` with `P c1` and
  `P t → ∃ u, t ⟶ u ∧ P u`.
- Two things came out clean. First, the reducibility criterion: for K-free terms head spine
  ≥ 3 implies reducible, because the only leaf is `S`, so the head of any application chain
  is `S` and three arguments fire it. Second, the preservation arithmetic: firing `S f g x`
  leaves head spine `spineLength f + 2`, and with `k` trailing arguments,
  `spineLength f + 2 + k`.
- **So the gap is now one inequality.** If the redex sits under at least one further
  argument (`k ≥ 1`), the reduct has spine ≥ 3 unconditionally and reducibility propagates
  for free. Only the `k = 0` case — redex at the very head — needs `spineLength f ≥ 1`, and
  nothing in the tree bounds the first argument's spine below. That is a much sharper
  statement of C1(a)'s remaining difficulty than "no invariant is known", which is what the
  ledger has said since Slice 3.
- Measured it rather than assuming: `c1`'s payload spine along the frozen trajectory runs
  3,4,4,3,3,4,4,3,5,6,6,5,5,8,8,7,9,10,10,9. Never below 3, so the invariant holds
  empirically — and the awkward case does occur, so the gap is real rather than vacuous.
- Extended the self-embedding hunt to the LITERATURE's term, which I had not done before:
  the classic 14-leaf `S A A (S A A)` with `A = S S S` does not self-embed within 40 steps
  either, sizes growing 14, 20, 26, 35, 44, 53, 65. So the self-embedding route is
  witness-free at the canonical example too, not just at ours. Worth knowing — I had been
  half-assuming the literature's term would have the nice structure ours lacks.
- **A process failure to record.** My first draft of this stage had a fourth theorem
  claiming "spine falls by at most one per step", with a `sorry` in it. It is overreach:
  the reduct's spine is not determined without knowing which redex fired, and
  `reducible_of_head_spine` returns *some* reduct without controlling that. I removed it
  rather than trying to patch it. But I should not have written a `sorry` at all — thirty-one
  stages with a sorry-free tree and I nearly broke it by drafting a theorem before checking
  it was true. The habit that has served this project is checking BEFORE building, and I
  skipped it for that one lemma because it felt like an obvious corollary.
- Ranking: (1) the `k = 0` spine bound — the single remaining gap for C1(a), and now a
  self-contained arithmetic question rather than an open-ended invariant hunt;
  (2) C6, declined a twentieth time.

## 2026-07-24 — Stage 33: my own gap was an artefact

- Ranked task was the `k = 0` spine bound, which Stage 32 had called "the single remaining
  gap for C1(a)". Checked it before attacking it — eighth stage running, and the stage right
  after I nearly broke the sorry-free streak by *not* checking — and the gap dissolved.
- The error was mine and precise: `reducible_of_head_spine` says head spine ≥ 3 IMPLIES
  reducible. It does not say the converse. A term like `(S x)(g x)` has head spine 2 and can
  still reduce inside. So when I demanded head spine ≥ 3 be *preserved*, I was asking for
  strictly more than reducibility, and the `k = 0` case was the cost of that surplus rather
  than a fact about pure S. I had turned a sufficient condition into a required one without
  noticing.
- The replacement dropped out of C5's own proof. Inside `conservation` I had used: if `t`
  reaches a normal form then confluence sends every reduct there too, and monotonicity caps
  every reduct's size. Extracted, that is `leafCount_le_of_normalizes`, and its
  contrapositive is a criterion needing no invariant at all — **unbounded reduct sizes imply
  no normal form**.
- **Why this matters more than the theorem count suggests: the goal and the evidence now
  agree.** For thirty-odd stages the census measured SIZES — 120112 leaves at step 200,
  25.7 billion at fuel 1000 — while the stated target was an INVARIANT, and no invariant was
  ever observed. Those were different currencies. `bounded_of_normalizes` converts the
  census's own numbers into the right currency: any bound on those sizes would have been a
  normalization proof, so the explosion is evidence of exactly the right kind.
- And the new target is cumulative in a way the old one was not. Every larger reduct found is
  progress toward unboundedness. Slices 3, 4 and 32 all hunted invariants and produced
  nothing that composed — three separate negatives. That asymmetry is worth remembering when
  choosing between two formulations of the same open problem: prefer the one where partial
  results accumulate.
- Still open: the growth step — from any reduct, reach a strictly larger one. I want to be
  clear that this is not obviously easier than the invariant, only better aimed. What has
  improved is that partial progress now counts.
- Ranking: (1) the growth step for `c1` — from any reduct of `c1`, reach a strictly larger
  reduct. The frozen head (Slice 4) may help here in a way it did not help the invariant:
  `frozen_normalizes_iff` reduces `c1` to its payload, and the payload's sizes are what grow;
  (2) C6, declined a twenty-first time.

## 2026-07-24 — Stage 34: built a theorem, measured it, threw it away

- Ranked task was the growth step. It split into two halves with very different characters,
  and the interesting part of the stage is that I kept one and deleted the other.
- The half I kept, `normalizes_of_no_growth`, is choice-free and says the essential thing:
  a pure-S term whose reducts never grow must normalize, so **growth is necessary for
  non-termination**. τ does all the work — each step on a size plateau strictly drops it,
  and a Nat cannot drop forever. The only care needed was recursing on `stepOnce` instead of
  case-splitting on `NormalForm`: `stepOnce` is computable and certified on both ends, so
  "normal or reducible" is decided rather than assumed. That one choice of formulation is
  what kept the proof constructive.
- The half I deleted completed the equivalence — no normal form implies unbounded reducts.
  It compiled. Then the axiom audit reported `Classical.choice` in all three theorems, and
  the cause is intrinsic rather than accidental: the hypothesis is NEGATIVE (`¬ ∃ normal
  form`) and the conclusion POSITIVE (`∃ arbitrarily large reduct`), so it needs
  `¬∀ → ∃`. Five earlier `Classical.choice` encounters in this project were all
  instance-layer accidents that a rewrite fixed. This was the first genuine one.
- I removed it. The reasoning: the tree has advertised no `Classical.choice` since Stage 0,
  in STATUS.md and README and every axiom audit; the equivalence is a nice-to-have rather
  than a tool; and the direction that IS a tool was already choice-free. Shipping a
  clearly-labelled classical theorem would have been defensible, but it would have cost a
  property I have repeatedly claimed, for something nothing else depends on. Not worth it.
- **What I did instead of leaving a gap: worked the constructive route out and wrote it
  down.** Replace the negative hypothesis with the positive "every reduct is reducible";
  build the trajectory from `stepOnce`, which is computable so no choice is needed; prove
  `leafCount (f k) = leafCount t → tau (f k) + k ≤ tau t` by induction on k; instantiate at
  `k = tau t + 1` where the bound is contradictory. The refuted proposition is DECIDABLE, so
  monotonicity upgrades it to strict growth constructively. So the equivalence is
  constructively true and the file now says how — which is a better artefact than either the
  classical proof or an unexplained hole.
- Worth noting how the two halves differ in what they need. Necessity of growth reasons
  FORWARD from a term (constructive). Sufficiency of unbounded growth reasons forward from a
  bound (constructive, Stage 33). Only the negative-to-positive direction needs classical
  logic — and that is precisely the direction nothing uses.
- Ranking: (1) the constructive equivalence, now fully specified — three steps, all
  mechanical, no research content; (2) C6, declined a twenty-second time. Note C1(a) itself
  is unchanged: it still needs a proof that some specific term's reducts are unbounded, and
  Stages 33-34 have only made the target precise and shown it is the right target.

## 2026-07-24 — Stage 35: the obstruction I declared intrinsic was not

- Ranked task was building the constructive route Stage 34 had specified. It worked, and it
  also corrected Stage 34's diagnosis, which is the part worth recording.
- Stage 34 said the converse direction was intrinsically classical because it goes from a
  negative hypothesis to a positive conclusion, needing `¬∀ → ∃`. That was too coarse. The
  `by_cases` I had written was on `∃ u, t ⟶* u ∧ leafCount t < leafCount u` — a statement
  about ALL reducts, and yes, undecidable. But the thing I actually needed was `∃ v, u ⟶ v`
  for a FIXED `u`, and that is decided by `stepOnce`. Routing through "every reduct is
  reducible" makes the whole chain constructive.
- So the lesson is narrower and more useful than "negative-to-positive needs choice": it
  depends on WHICH quantifier. A quantifier over one term's successors is decidable; one over
  all reducts is not. I had lumped them together and generalised from the wrong one.
- Stage 34's decision still looks right to me. Removing the classical proof preserved a
  property I had claimed since Stage 0, and it cost one stage. Had I shipped it with a label,
  the tree would now carry a `Classical.choice` dependency that this stage shows was never
  necessary — and nobody would have gone back to remove it, because a labelled axiom looks
  settled. **Declining to ship kept the question open, and the question had a good answer.**
- The proof itself is pleasant. `iter` is the trajectory as a total function, stalling at a
  normal form. `tau_budget` says: if the trajectory has not grown by step k, τ has paid k
  units, because every plateau step strictly drops τ. Then the growth step is found by simply
  LOOKING at index `tau t + 1`, where the budget is exhausted. No search, no case analysis —
  an index computed from the measure.
- Result: **for a K-free term, no normal form is the same thing as unbounded reducts.** That
  closes the framing question Stages 32-35 have circled. The census's currency and the
  conjecture's currency are the same currency, proved.
- Ranking: (1) C1(a) itself — with the equivalence in hand, the remaining task is exactly
  "exhibit a K-free term whose reducts are unbounded", and `unbounded_of_all_reducible` says
  it suffices to show every reduct of that term is reducible. That is a positive, decidable-
  per-term condition, which is a better target than either the invariant (Stage 32) or the
  raw size claim (Stage 33); (2) C6, declined a twenty-third time.

## 2026-07-25 — Stage 36: four stages of reformulating one problem

- Ranked task was C1(a) via "every reduct is reducible", which Stage 35 had called a better
  target than the invariant or the size claim. Checked it first — ninth stage running — and
  the claim was wrong in a way worth making permanent.
- All three are equivalent, and so is the invariant form. The sharpest bit: if every reduct of
  `t` is reducible, then `fun u => t ⟶* u` IS a reducibility invariant, with `stepOnce` as its
  successor function. So the invariant route (Slices 3, 4, Stage 32) and the positive route
  (Stage 35) were never different problems. Nor was the size route (Stage 33), by Stage 35's
  equivalence.
- **So Stages 32, 33 and 35 each swapped C1(a) for a provably equivalent statement and I read
  each swap as progress.** Each felt like progress for a real reason — the size criterion did
  match the census's currency, the positive form is decidable per term — but matching the
  evidence better is not the same as being closer to a proof. I want that distinction on
  record because it is the subtlest error this project has produced. It is not an overclaim, a
  mis-estimate, or an untransferred caveat. It is mistaking a change of coordinates for
  motion.
- Made it a theorem rather than a note. `c1a_formulations` proves the four-way equivalence
  constructively, which means the cycle cannot repeat: any further reformulation along these
  lines is provably a restatement. Closing C1(a) needs a new fact about pure-S reduction — a
  SOURCE, not another bridge. The tree now has every bridge and no source.
- Also wrote down, in the same place, what the program has actually contributed to C1(a):
  C1(b) proved, C5 proved, the frozen head proved, this equivalence, and three honest
  negatives. That matters because "the reformulations were not progress" could be misread as
  "nothing was achieved", and the two are quite different. The bridges are real theorems; they
  just are not the thing.
- Ranking, and I want to be careful here rather than name another reformulation:
  (1) **a source, not a bridge** — the only untried route with genuinely new content is
  constructing a term with a self-embedding by design rather than searching for one, which
  pass 2 registered as "construct-don't-search" and which no stage has attempted. It is the
  one item on the board that could produce an infinite reduction rather than relate the ways
  of describing one; (2) C6, declined a twenty-fourth time.

## 2026-07-25 — Stage 37: the last untried route, tried

- Stage 36 had cleared away the reformulations and left exactly one item with new content:
  construct a self-embedding rather than search for one. Registered as "construct-don't-search"
  in the second ideonomy pass, never attempted in thirty-five stages.
- Before attempting a construction I searched the design space, because Slices 3 and 4 had only
  ever checked `c1` and `c2` — two terms, one strategy, 120 steps. A systematic sweep is cheap
  with the existing tooling and it settles whether construction is even needed. It found
  nothing: no pure-S term up to 8 leaves reappears inside its own leftmost-outermost trajectory
  within 200 steps, and — the row that matters — no term up to 6 leaves does so under ANY
  strategy.
- I included the all-strategies row specifically because of Stage 21, where validating a
  leftmost-outermost cycle detector revealed it provably misses cycles that exist in the
  relation. An LO-only negative here would have inherited exactly that weakness, and I would
  have reported it as stronger than it was. Using the bounded closure costs more but the
  evidence is of a different kind.
- **What the result does and does not do.** It upgrades the loop route from "unexplored" to
  "searched and empty where searchable", which is a real change in the ledger's standing. It
  does not show self-embedding is impossible, and I want to be careful there: no obstruction is
  proved and none is apparent to me. C2 rules out the trivial context and nothing more.
- So C1(a) is in an unusually well-characterised position for an open problem. Every bridge
  between its formulations is proved (Stage 36). Its dependency is discharged (C5, Stage 31).
  Its minimality half is proved (Slice 5). Its trajectory's structure is proved (frozen head,
  Slice 4). And all three candidate sources — invariant, self-embedding, unbounded growth — have
  been searched at the sizes searchable and come back empty. What remains is genuinely a
  research question about pure-S reduction, not a gap in this development.
- Worth recording as the honest summary of thirty-seven stages on C1: the program has
  contributed a great deal AROUND the conjecture and nothing that closes it, and it can now say
  precisely why — the missing ingredient is a source of infinite reduction, and none exists at
  any size a search reaches.
- Ranking: (1) prove self-embedding IMPOSSIBLE in pure S — the only remaining move that would
  change C1(a)'s status, since it would close the loop route for good and force any future
  attempt onto unbounded growth without a witness. Genuinely open, and I have no candidate
  argument; (2) C6, declined a twenty-fifth time.

## 2026-07-25 — Stage 38: "none is apparent" was wrong, at depth one

- I ranked "prove self-embedding impossible" first while writing that I had no candidate
  argument. Attempting it anyway found one immediately for the one-step case, which is a small
  embarrassment worth recording: I had reached for measures, found the space closed (correctly —
  a decreasing measure would refute C1(a)), and concluded *no obstruction is apparent* rather
  than *no measure obstruction is apparent*. The structural argument was two lines of thought
  away and I had not tried it because the previous eleven stages had all been measure work.
  The lesson is the same one Stage 36 taught in a different costume: the technique I last used
  is not the technique the problem wants.
- The argument itself is short. The reduct of a redex never contains that redex — the reduct's
  subterms are enumerable (`f x`, `g x`, the reduct, and subterms of the three arguments) and
  every candidate forces `x = g x` or `f = S f g`, which no term satisfies. Congruence lifts it,
  and the lifting works because subterm is transitive: `app f u` inside `f'` gives `f` inside
  `f'`, which is the induction hypothesis. No arithmetic beyond "a proper subterm is smaller".
- Two conveniences fell out. `selfEmbed_leafCount_lt` turns Stage 37's prose ("C2 forces the
  context to be non-trivial") into a theorem, and `isSubterm_iff_Subterm` retro-fits kernel
  meaning onto Slice 3's and Stage 37's Bool guards — they were always about a search routine
  and are now about the relation.
- Naming note: `Sub` is core Lean's subtraction class, so the relation is `Subterm`. The clash
  surfaced as "`Sub` has already been declared", which failed the whole inductive and cascaded
  into fifteen downstream errors — a reminder that a name collision in an `inductive` is not a
  local problem.
- **I want to be precise about what did not lift.** The multi-step induction has a clean shape:
  split the occurrence of `t` by position relative to the last redex; off the redex you get a
  shorter self-embedding and minimality closes it. Three residual shapes survive — `t` contains
  the reduct, `t = f x`, `t = g x` — and none is contradictory on its face. Size cannot kill
  them because self-embeddings are allowed to grow, and acyclicity cannot because those `t` need
  not recur. So this is a base case with no inductive step, and I should not represent it as
  nearly-done. Recording the three shapes is the useful output: anyone resuming knows what to
  attack.
- One thing the failure does settle, and it is worth stating positively: the missing ingredient
  is **not** a measure. That is now an argument rather than an observation, since a measure
  falling on every pure-S step would prove strong normalization and hence refute C1(a).
- Ranking: (1) attack the three residual shapes — specifically `t = f x` and `t = g x`, which
  are the constrained ones, since they say the whole self-embedding term is a *one-application*
  combination of pieces of the last redex, and that is a strong structural demand that may well
  be contradictory when combined with `t ⟶⁺ v`; (2) C6, declined a twenty-sixth time.

## 2026-07-25 — Stage 39: I ranked the empty half first

- Formalizing Stage 38's prose went cleanly. The organising fact is smaller than I had it in my
  head: a step rewrites ONE position, so a subterm of the result is classified by its position
  relative to that one — disjoint, above, below. That is `Step.subterm_split`, and the three
  residual shapes are just the "above" and "below" branches after the redex's own arguments are
  pushed back into the source. Axiom-free, including `propext`, which is unusual in this tree and
  reflects that nothing here touches arithmetic.
- Then I measured, and the measurement inverted my own ranking from yesterday. I had ranked
  shapes B and C (`t = f x`, `t = g x`) first, on the reasoning that requiring the whole
  self-embedding term to be a one-application combination of pieces of the last redex is a strong
  structural demand likely to be contradictory. **The demand is so strong the shapes are empty** —
  zero instances at every size up to 8 leaves, and empty without the side condition too. Shape A
  meanwhile has 1, 4, 19 instances at 6, 7, 8 leaves and is growing.
- So my reasoning was correct and my conclusion was backwards. "This shape is heavily constrained"
  argues that it is *cheap to eliminate*, not that eliminating it is *valuable*. Value depends on
  whether the shape is carrying the difficulty, and a constrained shape is exactly the one that
  is not. I had conflated tractability with importance — and had I not measured first, I would
  have spent the stage proving two shapes impossible and reported "residue narrowed from three to
  one" as progress toward closing the induction, when it narrows nothing that matters.
- This is the ninth or tenth consecutive stage where checking the cheap thing before building
  changed what got built. I should stop treating that as a happy accident.
- Getting the probe's QUESTION right took a false start worth recording. My first instinct was to
  search for full residual configurations `t ⟶* v ⟶ w` with `t ⊴ w` and `t ⋬ v`. That is
  guaranteed to return zero, and not for an interesting reason: the residual case is a case
  analysis OF the self-embedding hypothesis, so any instance would BE a self-embedding, which
  Stage 37 already searched for. The measurable question is the weaker one — is each shape's own
  structural demand satisfiable among a term's reducts at all — and only that one distinguishes
  the shapes.
- Lean note: `cases` on an indexed hypothesis whose index IS one of the constructor's fields (as
  `r' = x` is for the K root-redex) silently refuses to name that field, and reports it as an
  unknown identifier at the use site rather than as a binder error. Cost three attempts before I
  extracted the shape as a disjunction of equations instead. Third entry in the "when `cases`
  fights the indices, go around it" family, after the `mkElimApp` motive failures.
- Ranking: (1) shape A — the surviving one. A self-embedding's last step must put `t` strictly
  ABOVE the reduct it fires, meaning `t` contains `f x (g x)` while `S f g x` sits in `t`'s own
  ancestor `v`. I have no argument, and the honest note is that the 1/4/19 growth means this is
  not going to be emptied by measurement either; (2) C6, declined a twenty-seventh time.

## 2026-07-25 — Stage 40: the argument was in what I had thrown away

- Yesterday I ranked shape A first and wrote that I had no argument. The argument was already in
  the tree, discarded. `Step.subterm_split`'s middle disjunct says "s contains the reduct" — I
  wrote that lemma, and I wrote it too weak. What is actually true is that a subterm sitting above
  the redex is the image of the subterm of `v` at the same position, under the very step being
  fired. So it is not "t contains something", it is `∃ u ⊴ v, u ⟶ t`. Once stated that way the
  case kills itself: `u` self-embeds one step earlier than `t`, and backward steps cannot recur
  because leaf count never rises and τ falls when it stalls.
- The pattern is worth naming because it is now the third time: **I lost the result by recording a
  consequence instead of the fact.** Stage 38 recorded "no obstruction is apparent" when it meant
  "no measure obstruction". Stage 39 recorded three shapes as prose before turning them into a
  theorem. Here I recorded "contains the reduct" when the position argument gave something
  strictly stronger for free. Each time the weakening was invisible because the weaker statement
  was true and sufficient for the immediate goal.
- The descent needed no new theory, which surprised me. `tau_lt_of_isometric_step` is the engine
  of C2, `smallTerms` and `length_filter_lt_of_witness` are Goal 3's decidability plumbing, and
  `mem_smallTerms` rests on the census's `enum_complete`. Four separate pieces of the tree, all
  built for other reasons, and the rank falls out of composing them. This is the second time (C5
  was the first) that a result arrived by assembling existing parts rather than by adding.
- One design choice paid off. My first plan needed a SHORTEST path so that `t ⋬ v` came for free,
  which would have meant a length-indexed reduction relation and a nested induction. Then I noticed
  the case `t ⊴ v` also descends — the TARGET moves back one step, and the rank is a function of
  the target. So one measure covers both cases and there is no path-length bookkeeping at all. I
  should look for that simplification earlier; "which of my hypotheses am I only using to make the
  induction go" is a question worth asking before writing the induction.
- Seventh Classical.choice encounter, and two new variants, both from `omega`. Case-splitting a
  disjunctive HYPOTHESIS costs the axiom; so does a disjunctive GOAL once a conjunction is nested
  in it, though a bare disjunctive goal is fine. `#print axioms` caught both, as it has caught all
  seven; review has caught none. Fixed by splitting by hand and giving the witnesses as terms.
- **Where this leaves C1(a).** The loop route is down to one shape, and it is the shape with zero
  instances up to eight leaves. That is a much better position than Stage 37's, and I want to be
  careful not to oversell it: `HalfShape` being empty is a MEASUREMENT, and the route being closed
  requires a proof. Nor would closing the loop route prove C1(a) false — an infinite reduction need
  not be periodic, so pure S could still diverge with no self-embedding anywhere.
- Ranking: (1) prove `HalfShape` uninhabited. It is a sharp, self-contained question with no
  reduction theory left in it: can a term `f x` have a reduct containing `S f g x`? The size
  arithmetic is tight (the redex outweighs the term by `1 + |g|`) and `f`, `x` are `t`'s own
  children, so there is more structure here than in anything shape A offered. If it goes through,
  the loop route to C1(a) is dead outright and that is a publishable negative; (2) C6, declined a
  twenty-eighth time.

## 2026-07-25 — Stage 41: the guard read stronger than it was

- Before attempting the proof I re-read what the `HalfShape` measurement actually guarantees, and
  found I had overstated it. `closureStep` filters reducts by `leafCount ≤ bound`, so a capped
  closure reports SATURATION after silently discarding everything bigger. The cap-24 guard
  therefore says "no witness among reducts reachable through terms of ≤ 24 leaves", and I had been
  reading it as "no witness". That matters here more than it usually would, because a `HalfShape`
  witness must be `1 + |g|` leaves heavier than `t` — the ceiling is precisely where one would sit.
- Raising it: cap 40 to eight leaves, cap 60 to seven, and a leftmost-outermost probe running 300
  steps under a 4000-leaf ceiling. All empty. The LO probe is worth keeping alongside the closure
  because the trajectories genuinely explode — the largest reduct visited has 3994 leaves — so it
  reaches a size range no closure search here can, at the cost of covering one strategy. The pair
  of probes has complementary blind spots, which is the most I can get cheaply.
- I should generalize the lesson rather than just fix the number. Every capped search in this tree
  reports "clean" the same way, and "clean" always means "clean below the cap". Stage 21 taught the
  strategy version of this (an LO hunt is blind to cycles that exist in the relation) and I
  transferred that one. I did not transfer the size version, even though it is the same shape of
  error. When a probe has a parameter, the finding is about the parameter.
- On the proof: backward induction along the path is right, and it comes down to an invariant on
  the requirement. `|requirement| > |t|` survives three of four sub-cases, and the two interesting
  ones are pleasantly rigid — a reduct half FORCES the bigger redex's third argument to be `x`
  itself and grows by two leaves, and a root redex FORCES the shape `S (S f) b g` with `x = b g`,
  which shrinks the third argument. Both are the kind of tight forcing that usually means an
  argument is close.
- It is not close, and I want to say why rather than leave the impression. The fourth sub-case is a
  step *inside* the requirement, and pure-S reduction grows, so the predecessor can be much lighter
  than what it produces — exactly the mechanism the invariant needs to exclude and exactly the
  mechanism C1(a) is about. Three controlled cases plus the hard one is not most of a proof; it is
  the easy three quarters. Every hard case in this development has been the growth case, and I
  should stop being surprised by that.
- Ranking: (1) the fourth sub-case — can a term of at most `|t|` leaves reduce, at its own root,
  into the left spine of `S f g x` where `t = f x`? It is a sharper question than any of the three
  shapes were, and the forcing lemmas suggest the answer is no; I have no argument. (2) C6, declined
  a twenty-ninth time.

## 2026-07-25 — Stage 42: the linkage clause I nearly shipped without

- Two results, and one near-miss that is the more useful entry.
- The results. `step_growth_eq` says a pure-S step grows a term by exactly `|c| - 1` for the
  duplicated argument `c`. That is Stage 2's monotonicity made quantitative, it was four lines by
  induction on the step, and it should have existed twenty stages ago — every size argument in this
  tree has been reaching for it and settling for the inequality. And `reduct_half_lt` collapses
  Stage 41's `app3_S_reduct_half_grows` to a general fact needing nothing about S-shapes: a reduct
  half is always lighter than its redex. I had proved the special case because I was looking at
  `S f g x` specifically, which is the third time this week that looking at the instance cost me
  the general statement.
- Together they turn Stage 41's "fourth sub-case, open" into a size condition on one subterm: going
  backwards is safe unless the step duplicated something at least `|s| + 1 - |t|` leaves heavy. That
  is a better-shaped gap. It is also, unmistakably, the gap where the actual difficulty of C1(a)
  lives — big duplication is the only way pure S grows.
- **The near-miss.** I first stated the invariant theorem as "one step back there is still some
  requirement in `v'` outweighing `t`", and it built, and it was nearly vacuous. Every reduct of `t`
  outweighs `t`, so `s' = v'` satisfies that at every point of the path except the start. I caught
  it while writing the ledger entry, not while writing the proof, and only because I asked what the
  theorem would let me DO. The fix is the linkage clause: the new requirement must be `s` itself, or
  reduce to `s`, or be the redex `s` is a half of. With linkage the induction is real, because at
  the path's start the requirement must be a subterm of `t`.
- This is the fourth instance of the same failure in five stages: recording something true but too
  weak to use. "No obstruction is apparent" (38), three shapes as prose (39), "contains the reduct"
  (40), and now an unlinked existential. The pattern is specific enough to test for: after stating a
  lemma, ask whether a TRIVIAL witness satisfies it. `s' = v'` would have failed that test
  instantly. I am adding that check to how I write these, because reading the proof does not catch
  it — the proof of the weak statement is perfectly correct.
- Also strengthened `selfEmbed_imp_halfShape` to bound its witness by the size of the self-embedding
  term. Free from the descent's structure, and it opens a second route: chase the requirement's shape
  instead of its size, and the path's start yields a self-embedding of something strictly smaller
  than `t`, which the size bound converts into an induction on term size. Two of three start-cases
  work; the third does not, so I am recording it as a route.
- Ranking: (1) the third start-case of the shape route — the requirement hiding inside `x` rather
  than being `t` or inside `f`. It is the one place where `P ⊴ x` gives no relation between `P` and
  the term `P` reduces to, and closing it would complete an induction on term size rather than
  leaving a size condition to check. That is the better of the two routes because its remaining gap
  is combinatorial rather than about growth; (2) C6, declined a thirtieth time.

## 2026-07-25 — Stage 43: the hour, and what it cost not to have spent it

- Nathan asked whether the frustration in these entries was the problem being hard or the approach
  being wrong. Reviewing it properly: the approach was wrong, in one specific way. Every stage's
  ranking came from the previous stage's proof structure, so the selection of what to work on was a
  closed loop with no external check. C1(a) had the best local gradient — clean theorem, clean next
  question, every time — and I followed the gradient for ten stages into a census artifact that my
  own STATUS.md describes as low-materiality with prior art "discoverable in an hour". Stage 39
  caught me conflating tractability with importance at the object level; I was doing the same thing
  one level up, to my own ranking, and did not notice.
- The hour took about ten minutes. Endrullis and Zantema state the ground-loop theorem as a known
  fact in the second example of their paper, citing Waldmann 2000. Stages 37–42 re-derived it and
  stopped one size condition short.
- And then the same paper handed over the tool. Their Theorem 4 — non-termination iff a recurrence
  set exists — plus a five-state tree automaton for the S-rule. **C1(a) is now proved here.** The
  entry that has said `external` since Stage 0 says `PROVED`.
- The one engineering decision worth recording: I determinized their automaton by hand before
  formalizing. Their version is nondeterministic, so the interpretation of a term is a SET of
  states, and the quasi-model condition is a set inclusion — which in a zero-dependency development
  means building list-based set machinery, distributivity of the transition over unions, and
  monotonicity lemmas for all of it. Determinizing costs exactly one state (six instead of five)
  and deletes all of that: the interpretation is a function, the order is on six elements, and every
  side condition is `cases <;> decide`. It built on the first attempt. Sixteen lines of
  paper-arithmetic beforehand replaced what I estimate was a day of list lemmas.
- Second decision: I did not take the paper's route for "every accepted term has a redex". They
  build a product automaton and check language inclusion. But reaching the accepting state forces a
  left spine of at least three, and this tree already proves that a K-free term with spine ≥ 3
  cannot be normal (`SNF.spineLength_le`, Stage 2). Reading the shape off the transition table was
  three small lemmas. Reusing what is already proved beat importing the general construction, which
  is the same lesson C5 taught at Stage 31.
- The cross-check matters to me and I made it a guard rather than a remark. The certificate is a
  claim about an automaton; the census evaluator is separate code. Running the witness shows leaf
  count climbing 12 → 776 in forty steps. If those two mechanisms disagreed, one would be wrong,
  and I would rather the build say so than a comment claim it.
- Honest limits. The certificate is not tight — twelve leaves against C1(b)'s proved floor of seven
  — and the automaton rejects `c1` and `c2`, so the two census candidates are still individually
  open. And the prize question is untouched by all of this: divergence is not universality.
- Process change, and this one is the actual deliverable of the day: the end-of-stage ranking gets
  checked against STATUS.md and the spec, not against the last proof. The four goals are the
  external check that ideonomy used to provide and that I stopped applying.
- Ranking, now from the spec rather than from the last proof: (1) **ladder rungs 2 and 3** — spec
  Stage 5's second component, "each rung a publishable partial result". The tool is the one this
  stage just built. My notebook's moral was "counts see size, positional measures see structure",
  and I proved no monotone counting measure exists for {S,B} and closed the τ route; the missing
  third category is FINITE-STATE invariants, and Geser–Hofbauer–Waldmann–Zantema (Inf. Comput. 2007)
  is the termination-direction literature for exactly that. (2) Goal 2's `Simulation` gap, left
  legible on purpose in `Calibration.lean`. (3) C6, declined a thirty-first time.

## 2026-07-25 — Stage 44: the new process rule earns its keep immediately

- Yesterday's process fix was to rank against the spec rather than against the last proof. Its first
  output was rungs two and three, which is right. Its first lesson is that ranking correctly does
  not make the plan correct: my stated tool for those rungs was wrong, and one search plus one
  theorem showed it.
- I said finite-state invariants were the missing third category after counts and positional
  measures. So I searched for them exhaustively at up to three states before writing any Lean. They
  exist in quantity — 154 for {S,B} with a strictly dropping step — and I was wrong that they would
  all reduce to facts already here. Only 58 of the 154 factor through B-freeness and capped spine
  length. There is real structure in the other 96.
- Then I worked out what one would BUY, which is the step I should have done before the search and
  certainly before the ranking. A non-increasing measure excludes its strictly-dropping steps from
  cycles and nothing more. Emptying the cycle space would need every step to drop, and C1(a) now
  makes that impossible for anything containing S. So the whole category is a constraint generator,
  not a proof method, for this problem. Both facts are theorems now rather than remarks
  (`RS.no_decreasing_measure_of_infinite`, `RS.no_return_of_strict_drop`), because I have learned
  what happens when I leave that kind of claim in prose.
- The satisfying by-product: `no_decreasing_measure_pureS` says C2's three-level squeeze was FORCED.
  At the time it felt like an ingenious construction; it was the only available shape. That is worth
  knowing about the other rungs before spending stages hoping for something simpler.
- The underlying mistake was conflating two literatures under "tree automata". Endrullis–Zantema
  prove NON-termination, and a bounded certificate is fine there precisely because you are
  exhibiting an infinite path, not ruling one out — which is why it transferred so cleanly to C1(a)
  and why I over-generalised from that success. Proving termination with automata is match-bounds:
  well-foundedness comes from a height annotation being bounded over the reachable set. Different
  mechanism, much bigger build. One tool solved C1(a) in an afternoon and I assumed its neighbour
  would solve the rungs.
- Lean caught something I want to record. I wrote `not_on_cycle_of_strict_step` with a hypothesis
  `B.step b b'`, and the unused-variable warning showed the proof never touched it — the fact needs
  only the measure drop. That is the "trivial witness" test from Stage 42 arriving as a compiler
  warning instead of as self-review. I renamed it and dropped the hypothesis. Two of my last three
  overclaims would have been caught by simply reading the warnings I was filtering out of the build
  output; I should stop grepping them away.
- **Where this leaves the rungs.** Both remain open, and now with a proved account of why: no single
  measure can work, no bounded invariant can finish, and the two open routes are a genuine
  match-bounds implementation or an unbounded well-founded measure nobody has found. That is a
  better-characterised open problem than yesterday and I am not going to pretend it is closer.
- Ranking, against the spec: (1) **Goal 2's `Simulation` gap** — the spec calls the taxonomy "the
  intellectual center", the gap is documented on purpose in `Calibration.lean` (the positive side
  certifies SK realising λ-style bodies, not SK hosting a known-universal MACHINE), and the
  adequacy machinery for it already exists (`RS.bwd_of_abstraction_rel`, `Simulation.ofAbstraction`,
  `universalReach_extend`). It is bounded work on the spec's declared centre, which is more than can
  be said for a match-bounds framework. (2) rungs 2/3 via match-bounds, as a deliberate multi-stage
  project rather than a hoped-for corollary. (3) C6, declined a thirty-second time.

## 2026-07-25 — Stage 45: the untried route was the cheap one

- Ranking against the spec sent me to Goal 2, the declared "intellectual center", where the blocker
  has been adequacy since Stage 8. Reading my own probe files properly was most of the work: Stage 10
  found drift, Stage 11 half-fixed it, Stage 13 refuted the fix and named three routes, two dead. The
  third — "read only the live spine, ignore subterms destined for a K-discard" — had sat untouched
  for thirty-two stages with no one noticing it was a one-line idea.
- It is one line. Contract the K-redexes before reading. A doomed copy collapses regardless of what
  it drifted into, so drift stops being a problem to solve and becomes a thing you cannot see. Stage
  10 tried to PREVENT drift and Stage 13 showed you cannot; route 1 tried to TOLERATE it and it went
  too coarse. Making it invisible is a third relation to the problem and it did not occur to me for
  thirty-two stages.
- What I did right, and it is the habit that has paid every time this week: I tested before building.
  Fifteen minutes of `#eval` established that the abstraction fixes the probe's own failure case,
  still inverts the encoder, and satisfies stutter-or-advance over every SK term up to seven leaves.
  Had I gone straight to proofs I would have discovered the same thing three stages later or, worse,
  proved something about a mechanism that did not work.
- I also tested the obligation where it actually lives. `RS.bwd_of_abstraction` quantifies over EVERY
  pair of host terms, not the reachable ones, and it would have been easy to test the reachable
  closure, get a clean result, and report it as though it meant the obligation held. The reachable
  closure of the countdown is 183 terms; the real test space at seven leaves is 16896. Same class of
  error as the size-capped searches in Stage 41 — the finding is about the domain you quantified over.
- What I got wrong: three attempts at certifying the K-normaliser, all lost to the equation lemmas
  that Lean generates for overlapping patterns. I stopped and shipped it as census tooling, which is
  the project's existing convention for unverified code and cost nothing, since the finding is
  empirical anyway. The honest note is that the first attempt was not a proof attempt at all — I
  wrote a `have ... |> fun _ => by` construction that was nonsense, which is what flailing looks like
  when I have not thought about the induction. The second and third were real attempts.
- I ran a negative control on the guards before claiming them, because the build finished in 1.1
  seconds and that felt too fast for a check over 3238 terms. Inserting a guard that must fail made
  the build fail, so they bite. Thirty seconds to convert a suspicion into a fact.
- **Where Goal 2 stands.** The gap is unchanged in shape — no `Simulation` from a universal source
  into SK — but its hardest obligation went from "two dead routes" to "one mechanism that works on
  every case tested". That is the difference between blocked and unfinished.
- Ranking, against the spec: (1) prove stutter-or-advance for `absK` on the countdown, which turns
  the empirical finding into the first `Simulation` into `RS.SK` with a genuinely multi-step encoding.
  The crux is one question — how does an S-step interact with K-normalisation — and it needs
  confluence of K-reduction, which is a small self-contained lemma this tree does not yet have.
  (2) piece (v), the tag-step driver, once the mechanism is certified rather than measured.
  (3) rungs 2/3 via match-bounds. (4) C6, declined a thirty-third time.

## 2026-07-25 — Stage 46: mirroring beat inventing

- The task was the lemma I named yesterday: K-reduction is confluent, so "the K-normal form" denotes
  and Stage 45's abstraction is a function of its argument. I did the thing CLAUDE.md says to do and
  I have not always done — found the existing implementation of the same shape and followed it.
  `Confluence.lean` proves SK confluence by Takahashi: parallel reduction sandwiched between step
  and steps, a complete development, the triangle, then diamond → strip → confluence. Restricting
  that to the K rule is mechanical, and the K-only version is strictly simpler because there is no
  S_red case and `kdev` has one redex arm.
- It built with two small fixes, both mine and both from not following the model closely enough. I
  hand-rolled the `app` congruence case of `KPar.to_ksteps` as a nested type-ascribed `by` block
  instead of factoring out `congL`/`congR` the way the original does, and it did not elaborate. And
  I copied the original's `rw [← ..., ← ...]` ending for `knf_unique` without checking that my
  lemma's equation pointed the same way; `.trans` and `.symm` were clearer anyway. Both were the
  cost of paraphrasing rather than mirroring.
- The result I actually wanted is `IsKNF.of_kstep`: a K-step does not move the K-normal form. That is
  the K-step case of stutter-or-advance, and it falls out of confluence with no reference to the
  encoding at all — no case analysis, no countdown-specific reasoning. Half the crux of Stage 45's
  obligation is now a theorem instead of a measurement.
- I anchored it against vacuity deliberately, including one anchor I nearly skipped: `I` is K-normal.
  It looks like a triviality and it is the property the whole design rests on — if S-redexes were
  K-reducible, the abstraction would advance the machine while pretending to observe it. Worth a
  theorem, not a comment.
- Axiom footprint is `[propext]` or nothing across the file, which is the cleanest section in the
  tree. Nothing here touches arithmetic, and it shows.
- **What is left of the crux.** The S-step case. A K-step is settled; an S-step can create and
  destroy K-redexes, so I still need: if `b ⟶_S b'` and `IsKNF b w`, then `IsKNF b' w'` with `w'`
  either equal to `w` or one countdown step further along. That is where the encoding finally has to
  be reasoned about, and it is the half that is genuinely about the machine rather than about
  rewriting.
- Ranking, unchanged in shape but with the first item now smaller: (1) the S-step case, which
  completes stutter-or-advance and yields the first `Simulation` into `RS.SK` with a genuinely
  multi-step encoding; (2) piece (v), the tag-step driver, once the mechanism is certified rather
  than measured; (3) rungs 2/3 via match-bounds; (4) C6, declined a thirty-fourth time.

## 2026-07-25 — Stage 47: refuting my own next step before taking it

- The plan was the S-step case. I got the surrounding obligations done — `habs`, `hfun`, `fwd`, and
  the exhaustiveness of the K/S split — and then, before starting the commutation proof, I wrote down
  the statement I intended to prove and tested it. It is false. `S K S S` refutes it: when the fired
  redex is `S K g x`, the reduct `(K x)(g x)` is itself a K-redex, so `kdev` collapses it further and
  overshoots what one S-step from `kdev b` can reach.
- That is fifteen minutes that saved a stage, and it is the same habit as Stage 44 (work out what the
  tool buys before building it) and Stage 45 (test the mechanism before proving it). What is new is
  that this time the thing I tested was a PROOF OBLIGATION rather than a search or a measurement. I
  should generalise: write the target statement, look for a small counterexample, and only then start
  the induction. It is cheaper than discovering the same fact three lemmas deep.
- `naive_kdev_commutation_fails` is in the tree as a theorem, not a comment, because a refuted plan is
  exactly the sort of thing that gets forgotten and retried.
- The satisfying part of the stage is `hfun`. That obligation is what killed the joinability
  abstraction back in Stage 29 — `RS.joinable_abs_not_functional` — and it is the one Stage 45's
  mechanism had to pass without becoming coarse. It passes for a clean reason: K-normal forms are
  unique (Stage 46) and `Itower` is injective, so the abstraction is genuinely single-valued while
  still being blind to drift. Being blind to the right things and not the wrong ones is the whole
  trick, and it now has two theorems behind it instead of a hope.
- I also want to record `kNormalForm_I`'s role, because it looked like filler when I proved it
  yesterday. It is the reason the design is coherent: an S-redex must be invisible to K-reduction, or
  the abstraction would advance the machine while claiming to observe it. The abstraction is allowed
  to be blind to doomed subterms and must NOT be blind to progress. Those are the two halves, and
  `kNormalForm_I` is the second one.
- **Where Goal 2 stands.** Two of three obligations discharged, the third split into a done half and
  an open half, and the open half's cheap route eliminated. The countdown is still not a universal
  source, so criterion (a) still wants piece (v) — but the interface it has to satisfy is now mostly
  proved rather than mostly hoped.
- Ranking: (1) the S-step commutation square, now with the wrong statement eliminated and two
  narrowings identified (doomed-position S-steps cannot move the K-normal form; K-reduction never
  duplicates, so a live S-redex has exactly one downstream image). (2) piece (v). (3) rungs 2/3 via
  match-bounds. (4) C6, declined a thirty-fifth time.

## 2026-07-25 — Stage 48: the square, and a forty-stage arc closing

- The commutation square went in essentially as designed. I worked the cases out on paper first —
  disjoint redexes, S-redex inside the kept argument, S-redex inside the discarded argument, K-redex
  inside each of the S-redex's three arguments — checked that each closed, and only then wrote Lean.
  It built after two fixes, both about `cases` rather than about mathematics.
- The two fixes are the same lesson twice. `cases` on an indexed hypothesis will not name a field that
  the indices already determine (the S-redex's third argument is the ambient `u`, so `| S_red f g` not
  `| S_red f g x`), and it WILL generate impossible alternatives that unification cannot kill on its
  own (`SStep Term.K _` has no constructor but Lean still asks for the branch, discharged by `cases`).
  That is the third and fourth appearance of this family in the session. I now know the shape well
  enough that it cost minutes rather than attempts.
- What pleases me about the result is that both weakenings in the square are FORCED, and for
  different reasons that I would not have predicted from the same place. The K-side sometimes needs
  ZERO S-steps, because the S-redex may sit in exactly the argument a `K` throws away. The S-side
  sometimes needs TWO K-steps, because the S-step duplicated its third argument and a K-redex inside
  it got copied. Stage 47's refutation told me the equation was wrong; it did not tell me the shape,
  and the shape has content.
- `sk_local_square` and `sk_square` need no axioms at all — not even `propext`. Pure structural
  induction on two relations.
- **The arc is worth stating because it took forty stages.** Stage 8 identified `bwd` as the piece
  that could fail in kind. Stage 10 found the failure. Stage 11 half-fixed it and Stage 13 refuted the
  fix, leaving two dead routes and a third named in a comment. Thirty-two stages later Stage 45 tried
  the third route, Stage 46 made it well defined, Stage 47 refuted the cheap version of the last step,
  and Stage 48 proved the real one. The thing that unblocked it was not cleverness — it was reading
  my own probe files properly and noticing that the untried route was one line.
- **The limit, which I want on the record next to the result.** The countdown is not universal. This
  discharges the mechanism criterion (a) was blocked on; it does not discharge criterion (a). Piece
  (v), a tag-step driver, is still unwritten, and it is a substantial construction. What changed is
  that its hardest obligation is a solved problem with a worked example rather than a research risk —
  which is a real change, and less than "Goal 2 is done".
- Ranking, against the spec: (1) **piece (v)** — the tag-step driver, now that adequacy has a
  template. This is construction work rather than research: encode words, write the step driver, and
  discharge `fwd`; `bwd` follows the countdown's pattern with `Itower` replaced by the word encoding,
  provided the driver keeps its data K-normal. (2) rungs 2/3 via match-bounds, still a deliberate
  multi-stage project. (3) C6, declined a thirty-sixth time.

## 2026-07-25 — Stage 49: I overclaimed in yesterday's ranking, and the refutation was already in the tree

- Yesterday I closed adequacy and wrote that piece (v) would follow "provided the driver keeps its data
  K-normal". Today's first job was to start the driver. Instead I checked what the abstraction actually
  demands, and the demand is different from what I said: `RS.abstraction_tracks_rel` — a theorem I have
  had since Stage 8 and used in Stage 48 — forces the abstraction to be defined at every reachable host
  term. So the constraint falls on the driver's INTERMEDIATES, not on its data.
- The countdown passes for a reason specific to the countdown: its entire step is one S-step followed by
  K-reduction, so every intermediate K-normalises to the after-state. Measuring it made the property
  vivid — of the 183 terms reachable from `Itower 3`, all 183 K-normalise to one of exactly four terms,
  the encodings of 3, 2, 1, 0. The reachable set collapses completely. That is not a mild side
  condition, it is the whole reason the abstraction works.
- A tag-step driver has to inspect a symbol and dispatch, so it has several S-steps per source step, and
  each intermediate must also K-normalise to an encoding — before-state early, after-state late, flipping
  exactly once. I do not know whether that is arrangeable. It is not obviously impossible, because
  combinator programming has room to hide work inside things a `K` will discard. It is obviously the
  thing to prototype first.
- **The pattern I keep repeating, now with a name.** When I finish a hard piece, my ranking of the next
  piece is written in the glow of the finish and is too optimistic. Stage 38 did it ("no obstruction is
  apparent"), Stage 39 did it (ranked the empty shapes first), Stage 43 did it (one tool for two
  literatures), Stage 48 did it here. The fix is mechanical and I should just apply it: before writing
  the ranking, state the next piece's hardest obligation explicitly and check whether the thing I just
  proved actually discharges it. Twice this week that check took fifteen minutes and saved a stage.
- Worth noting the refutation cost nothing to find: the theorem was already in the tree, I had used it
  the day before, and I had not asked what it implied about the case I was about to attempt. That is a
  different failure from not knowing something.
- Second honest note, added to the file so it is not lost: nothing here says the K-normal-form abstraction
  is the only option. `bwd_of_abstraction_rel` takes an arbitrary relation. What Stage 49 establishes is
  the price of THIS abstraction, and a driver that cannot pay it may still be adequate by another route.
- Ranking, and this time stated as an obligation rather than a plan: (1) **prototype the intermediate
  condition** for a minimal dispatching driver — something that inspects one symbol and branches — and
  measure whether its intermediates K-normalise to encodings. Cheap, decisive, and it determines whether
  piece (v) is construction or research. (2) piece (v) proper, contingent on that. (3) rungs 2/3 via
  match-bounds. (4) C6, declined a thirty-seventh time.

## 2026-07-25 — Stage 50: the part I expected to fight came for free

- I applied yesterday's fix and it worked. Instead of writing a driver I stated the obligation, found a
  cheap diagnostic for it, and measured. The diagnostic is a ratio — reachable terms versus distinct
  K-normal forms — because the abstraction can only tolerate two K-normal forms per source step, so any
  construct that sprawls is disqualified before a line of driver exists.
- The result inverted my expectations in both directions. Dispatch, which I assumed would be the hard
  part, is perfect: `S K a b` produces exactly two K-normal forms, itself and the selected branch,
  because selecting is one S-step whose reduct is immediately a K-redex. It commits, the doomed branch
  vanishes, and the abstraction sees precisely the flip it needs. That behaviour is not something I
  arranged; it falls out of how booleans are encoded in SK.
- Recursion, which Stages 11 and 13 had already warned about in prose, fails on the numbers.
  `omegaSK`'s reachable set is smaller than the countdown's — 107 against 183 — and it has seventeen
  distinct K-normal forms against the countdown's four. Sprawl, not collapse.
- I want to be careful about what that does and does not show, because the temptation is to write
  "recursion is incompatible" and move on. `omegaSK` is not a driver. It has no source machine, so
  there is no notion of how many K-normal forms it is ALLOWED. Seventeen would be fine for a machine
  with seventeen reachable states. What is genuinely evidence is the direction: as the closure grows,
  the countdown's K-normal-form set stays at four while `omegaSK`'s keeps growing. That is a trend, and
  it is the right kind of thing to steer by, and it is not a theorem.
- The stage's real output is a localisation. Piece (v) was "write a tag-step driver and hope adequacy
  follows". It is now "find a recursion scheme that commits each unfolding through a K-discard, or pick
  a different abstraction" — with the dispatching half already known compatible with machinery that is
  proved. That is a much better-shaped problem, and it cost one measurement rather than a construction.
- Meta-note I want on the record after fifty stages: the last four stages have each consisted of
  checking an obligation before attempting it, and three of the four overturned the plan I had written
  the day before. The habit is now clearly worth more than the individual results — it is the reason
  the plans keep getting better rather than the reason they keep being wrong.
- Ranking, stated as obligations: (1) **can a recursion commit through a K-discard?** — the concrete
  question is whether there is a fixpoint idiom whose unfolding is `S K`-shaped, so each recursive step
  behaves like a dispatch rather than like self-application. Cheap to search over small terms, and
  decisive for route one. (2) if not, design a different abstraction for piece (v) — the trajectory
  relation rather than the K-normal form. (3) rungs 2/3 via match-bounds. (4) C6, declined a
  thirty-eighth time.

## 2026-07-25 — Stage 51: I used a detector my own tree had proved unreliable

- Two real results and one instructive failure.
- The results. A committing S-step — one whose reduct is immediately a K-redex, the pattern Stage 50
  measured as ideal — requires its first argument to be literally `K`, and then the whole thing is a
  projection: `S K g x` gives `x` and throws `g` away, with the duplicate it just made sitting inside the
  discarded part. So committing steps cannot compute. Stage 50's route one is impossible as I phrased it,
  and it took two lines of injectivity to see.
- And a conflation I should not have made: I tested `omegaSK` as a proxy for "recursion" when what I
  needed was "self-reproduction". The countdown TERMINATES. Its 183 reachable terms are the orders its
  layers can fire in, not unbounded work. A driver needs the driver term to reappear alongside advanced
  data, with each segment finite — which is a different property from non-termination, and one the
  countdown has.
- **The failure.** To look for self-reproducing terms I filtered by `onCycle?`. That is the
  leftmost-outermost cycle detector, and Stage 21 of this very project proved that an LO hunt is blind to
  cycles that exist in the relation — that was the stage that rescoped all my earlier hunt data. So I
  reached for a tool my own notebook records as unreliable for precisely this question, got zeros, and
  had to notice for myself that `onCycle? omegaSK` returns false while two theorems in Calibration.lean
  put `omegaSK` on a cycle. The probe could not see its own control.
- Stage 41 wrote the lesson down: when a probe has a parameter, the finding is about the parameter. What
  Stage 51 adds is the sharper version — a probe with a KNOWN blind spot must be run against a control
  that exercises the blind spot, not just any control. I did run controls this stage, twice, and caught
  the size-range problem that way. I did not think to control the detector itself.
- I have made both facts guards rather than comments, because the next person to reach for `onCycle?` on
  a question about cycles-in-the-relation should trip over `onCycle? omegaSK = false` immediately.
- What the stage leaves: the question is unsettled and I now believe search cannot settle it. The smallest
  self-reproducing object in SK is fourteen leaves and exhaustive enumeration dies at seven or eight. So
  route one needs a CONSTRUCTION — design a self-reproducing driver and check its segment — rather than a
  sweep. That is a genuine change in method, and it is the honest output of a stage that otherwise
  produced two small theorems and a mistake.
- Ranking, as obligations: (1) **construct** a minimal self-reproducing term by hand — something of the
  shape `X data` reducing to `X data'` — and measure its segment's K-normal forms. Construction rather
  than search, because search cannot reach the size. (2) route two: design the trajectory-relation
  abstraction, which Stage 49 noted is unconstrained by any of this. (3) rungs 2/3 via match-bounds.
  (4) C6, declined a thirty-ninth time.

## 2026-07-25 — Stage 52: the habit that has been winning has a precondition

- I set out to construct the self-reproducing prototype Stage 51 asked for, and found that the tree already
  contains a certified one — `omegaSK`, with `omega_to_M` and `M_to_omega` proving it returns to itself. So
  I measured that instead of building something new, which was the right call for about ten minutes.
- Then the measurement would not interpret. The diagnostic I invented in Stage 50 counts K-normal forms and
  compares against "at most two per source step". `omegaSK` has no source. So seventeen K-normal forms, or
  thirteen along a twenty-step trace, is not too many or few — it is not comparable to anything. Stage 50's
  headline was "dispatch passes, recursion does not", and the second half of that does not follow from what
  I measured. The first half does: dispatch's source really is a two-state selection, so two is exactly
  right.
- I want to be clear that this is my error and not a subtlety. I wrote the diagnostic as "at most two per
  SOURCE step" in Stage 50 and then applied it to a term with no source in the same stage. The words were
  right and I did not read them.
- What the numbers do show is a difference in kind, and I have guarded it as suggestive rather than
  decisive: the countdown's K-normal forms shrink monotonically along its trajectory — 10, 7, 4, 1 — which
  is what a source that only moves forward looks like. `omegaSK`'s oscillate and revisit — 14, 20, 17, 17,
  26, 23, 23, 20, 20, 32 — which would force the source to cycle. Suggestive. Not a refutation, because
  neither term encodes anything.
- **The finding I actually value.** "Prototype the obligation before building the artifact" has driven the
  last six stages and been right every time. This is the first time it fails, and now I know why: the
  diagnostic has to be interpretable WITHOUT the artifact. "How many K-normal forms is too many" is a
  question about the source machine, so it cannot be answered before there is a driver. The prototype was
  supposed to de-risk building the driver and it turns out to require it. That is a precondition on the
  habit, not a failure of it, and it is worth having explicit before the next time I reach for it.
- So route one is not refuted and not testable cheaply, and I am going to stop circling it. Route two has
  been sitting untouched since Stage 49 and has the property route one lacks: `bwd_of_abstraction_rel`
  takes an arbitrary relation, so the trajectory relation — "b lies on the host segment for source state
  w" — can be designed and its obligations checked against the countdown, which I already have, before any
  driver exists.
- Ranking, as obligations: (1) **design the trajectory relation** and check its three obligations against
  the countdown — `habs` and `hfun` are the ones to worry about, since a trajectory relation is naturally
  coarse and `hfun` is exactly what coarseness broke for joinability. If it survives the countdown it is a
  candidate for piece (v); if it fails `hfun` the same way joinability did, that is a third dead route and
  worth knowing. (2) rungs 2/3 via match-bounds. (3) C6, declined a fortieth time.

## 2026-07-25 — Stage 53: the route I should have tried three stages ago

- Route two took one stage and gave up its two hard obligations without a fight. `habs` is immediate and
  `hfun` — the obligation that killed joinability back in Stage 29 and that I flagged as the thing to worry
  about — falls out of the Stage 48 `Simulation`'s own `bwd`. Reusing the result I had just proved to prove
  the next thing is the most satisfying kind of progress and I did not expect it here.
- The design point worth keeping: bare reachability fails `hfun` in BOTH directions, because the countdown's
  encodings are linearly ordered by reachability, so `Itower 2 ⟶* Itower 1` confuses states 2 and 1. The fix
  is the "not yet past `w`" clause, and it is exactly load-bearing — reachability gives `a ≤ a'` and the
  clause gives `a' ≤ a`. Neither half alone is a relation; together they pin the state.
- What remains, `hstep`, unwinds to "no single host step reaches past two source states", i.e. consecutive
  encodings are at least two host steps apart. That is a condition of an entirely different character from
  route one's. Route one wanted every intermediate to K-normalise to an encoding, which is a coincidence one
  hopes for; this is a spacing property one arranges. The countdown satisfies it because `I t` takes two
  steps to become `t`.
- **The real lesson is about the three stages I spent on route one.** Route two was named in Stage 49 as a
  parenthetical, and Stages 50, 51 and 52 all went to route one — each correcting the previous one's error,
  none of them getting anywhere, and Stage 52 concluding route one is not even testable without building
  the driver. Route two was cheaper, more promising, and available the whole time. What kept me on route one
  was that it was the route the countdown happened to use, so it felt like the established path. That is the
  same local-gradient failure Nathan asked me about around Stage 43, in miniature: I kept refining the thing
  I had just built instead of asking which available thing was best.
- The corrective is not "try harder to notice" — it is what I already committed to and applied unevenly:
  when a route stalls, re-read the alternatives that were written down when the routes were enumerated. They
  are in the file. Stage 49 wrote route two down and I read past it three times.
- The cost of route two is real and I have recorded it next to the benefit: the relation is not a
  computation, so it supplies `bwd` but not a decoder. A `Simulation` needs both. The countdown got its
  decoder from `naiveAbs` independently of its abstraction, and a driver must do the same — decode
  syntactically, track relationally. That is two obligations rather than one, and it is worth knowing before
  writing a driver rather than after.
- Ranking, as obligations: (1) **prove `hstep` for the trajectory relation on the countdown** — the spacing
  condition, which would complete a SECOND independent adequacy proof for the same machine and confirm the
  route end to end before it is used on anything harder. (2) piece (v) with route two, decoder and tracker
  as separate obligations. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-first time.

## 2026-07-25 — Stage 54: the obstruction was in my own interface

- I measured `hstep` before proving it, and it failed — 36 of 183. Good thing, because Stage 53 had
  hypothesised the wrong reason for the difficulty (a spacing condition) and I would have spent the stage
  proving something false about something irrelevant.
- The actual reason is one term. `K (Itower 1) (K (Itower 2))` sits on segment three and is itself a
  K-redex whose contraction is `Itower 1`. One host step, two source states, segment two skipped. The
  pending computation was in the discarded argument, so contracting the `K` arrived early. Nothing to do
  with how far apart the encodings are.
- And then the fix was not in the relation but in the INTERFACE I wrote in Stage 8. `hstep` let the
  abstraction advance by at most one source step per host step. Nothing in the tracking proof needs that —
  it composes source paths, and composing with `trans` instead of `tail` is the whole change. Relaxing it
  takes the failures from 36 to 0. So route two was fine and my own adequacy interface was the obstruction,
  for forty-six stages, unnoticed because until now every encoding I tried advanced one step at a time.
- I want to name that failure mode because it is new in this project. I have repeatedly caught myself
  overclaiming, mis-ranking, and using blind probes. This is different: a definition I wrote early, that
  was adequate for every case I met, silently narrower than the theorem it supports. The tell was available
  — `abstraction_tracks_rel`'s proof builds a path and then artificially restricts the input to single
  steps — and reading my own proof would have shown it. I only looked because a measurement forced me to.
- The symmetry is the thing I will remember from this stage. The K rule erases, and erasure is exactly what
  makes the K-normal-form abstraction work (drift in discarded arguments becomes invisible) and exactly
  what makes the trajectory relation fail (discarding pending work skips states). The same mechanism, load
  bearing for one design and fatal to the other. That is a genuinely nice fact about SK and it fell out of
  comparing two failed routes rather than from either one.
- Where this leaves piece (v): two abstractions, both viable, with complementary demands. Route one wants
  intermediates whose K-normal forms are encodings — a shape condition. Route two wants nothing about
  shape, only that segments be well defined, and now tolerates state-skipping. Route two looks better and
  is measured clean; the honest caveat is that "measured clean" means one machine at one size.
- Ranking, as obligations: (1) **prove `OnSegmentHStepPath` for the countdown**, which would give a second
  independent adequacy proof for the same machine and validate the generalised interface on something. The
  proof needs the source-order lemmas from Stage 53 plus a case analysis on whether the step crosses a
  segment boundary. (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a
  forty-second time.

## 2026-07-25 — Stage 55: the proof was four lines and the hypothesis was the whole problem

- I expected `hstep` for the trajectory relation to be a case analysis: does the step cross a segment
  boundary or not. It is not. Take the LEAST source state whose encoding reaches `b'`, and everything
  follows — the advance is a path to that state, and if it happens to be `w` the path is empty, so the
  stutter case never needs mentioning. Four lines.
- Two things fell out that I would not have seen by proving it the hard way. The proof never touches the
  "not yet past `w`" clause of its hypothesis, only the reachability half — so that clause exists purely
  for `hfun`, which is a clean division of labour I had not noticed. And the entire difficulty relocated
  into one hypothesis, `hleast`.
- `hleast` needs decidability, because a least element of a non-empty bounded set of naturals is only
  extractable constructively when membership is decidable, and this tree refuses `Classical.choice`. That
  chases back to: `Itower m`'s reachable set must be finite, i.e. `Itower m` must be strongly normalising.
- **And the tree cannot supply that, for a reason I find genuinely satisfying to have found.** C5 is exactly
  the theorem that turns "has a normal form" into "strongly normalising" — and C5 requires K-freeness.
  `Itower` is built from `I = S K K`. So my own conservation theorem is blocked from reaching my own
  encoding, and the blocker is the `K` rule's erasure: with `K` present, WN does not imply SN at all
  (`K S omegaSK` normalises and also diverges). That is the third stage running in which the K rule's
  erasure is the pivot — it made route one's abstraction work, made route two skip states, and now blocks
  the theorem route two needs.
- I could have reached for `Classical.choice` here and had the whole thing in twenty minutes. I would rather
  report a reduction than break a property the project has held for fifty-five stages, and the reduction is
  more informative anyway: "route two needs SN of `I^m S`" is a sentence someone can act on.
- A correction to my own record: I wrote "both theorems axiom-free" in the commit message before reading the
  audit, and they are `[propext, Quot.sound]`. Amended. I have been running the audit after composing the
  message, which is the wrong order and has now bitten once.
- Ranking, as obligations: (1) **prove `Itower m` is strongly normalising** — plausibly by a measure that
  accounts for the duplication `I t ⟶ (K t)(K t)` honestly, since leaf count grows there; the natural
  attempt is a measure on the number of `I` layers times something, and it is a self-contained termination
  problem. That completes route two's adequacy for the countdown and gives the second independent proof.
  (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-third time.

## 2026-07-25 — Stage 56: measure the answer, then prove it

- Stage 55 left route two needing strong normalisation of `Itower m`, which is a real theorem I did not
  want to prove. So I asked what I actually needed — a finite reachable set — and noticed that BOUNDED SIZE
  suffices and is much weaker. Then I measured the bound before trying to prove anything: largest reducts
  of `Itower m` are 1, 4, 10, 22 leaves. That is `3·2^m − 2`, and having the closed form in hand made the
  proof a matter of checking four cases rather than searching for a measure.
- The proof needs the reachable set characterised, because no measure can work for all of SK — `S`
  duplicates, so size growth is unbounded, and any measure that dominated leaf count would have to be
  non-increasing on a rule that doubles its argument. Three layer states do it: intact, half-consumed,
  collapsed.
- **The satisfying part.** The `half` constructor has to let the two copies of a half-consumed layer be
  DIFFERENT tower states, or the family is not closed under reduction. That is exactly the drift Stage 10
  discovered and that every abstraction since has had to cope with — and here, for the first time, it is not
  an obstacle but a constructor. Fifty stages after finding drift I finally gave it a type, and the size
  bound falls out because a drifted pair is still two things of bounded size. The `half` case is also where
  the bound is tight.
- What remains is smaller than it was and of a different kind. Decidable reachability needs a certified
  enumeration of bounded-size SK terms, and this tree's `smallTerms` is K-free because `enumAt` is — Goal 3's
  whole decidability layer was built for pure S and inherits that restriction. So the gap is now
  infrastructure: build the K-inclusive version of a thing I already have uncertified as `skTerms`. That is
  the first time in about ten stages that the blocker has been engineering rather than mathematics, and I
  should say so plainly rather than dress it up.
- Method note worth keeping, since it is now three for three: measure the answer, then prove it. Stage 54
  measured that hstep fails, Stage 56 measured what the bound is. Knowing `3·2^m − 2` before starting turned
  an open-ended search for a measure into four arithmetic checks. I have been treating measurement as a way
  to decide WHETHER to prove something; it is at least as useful for deciding WHAT to prove.
- Ranking, as obligations: (1) **certify a K-inclusive bounded enumeration** — `skTerms` plus the soundness
  and completeness lemmas `enumAt` has, which would close the chain to route two's `hstep` and, incidentally,
  widen Goal 3's decidability layer beyond pure S. Engineering, but it unblocks a proof. (2) piece (v) with
  route two, once the chain closes. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-fourth time.

## 2026-07-25 — Stage 57: one line, and fifty stages of restriction lifted

- The K-inclusive enumeration was, as predicted, engineering. It is `Completeness.lean` with the leaf case
  changed from `[S]` to `[S, K]` and the `KFree` conjunct deleted from soundness. Both proofs went through
  unchanged otherwise, including the budget-indexing trick and Slice 2's care about explicit witnesses.
- That the diff is one line is the finding. `enumAt`'s K-freeness has been load-bearing since Stage 6 and
  I had come to think of it as intrinsic — Goal 3's decidability, C1(b)'s floor, C5's pigeonhole all run on
  it, and they all genuinely need pure S. But the enumerator itself never needed the restriction; it
  inherited it from what the census happened to want. Fifty stages of treating an accident as a constraint.
- I only found out because route two's chain reached back through decidability to enumeration, which is the
  second time this session a long chain has ended somewhere I assumed was bedrock. The first was Stage 54,
  where the obstruction turned out to be my own Stage 8 interface. Both were early definitions, adequate for
  every case that came up, silently narrower than needed — and in both cases the tell was visible in the
  original file and I had never had a reason to look.
- What that suggests as a habit, and I want to state it as more than an observation: when a chain of
  reductions bottoms out at an old definition, check whether the definition's restriction is load-bearing or
  inherited before treating it as a wall. Twice now the answer was "inherited" and the fix was small.
- Where the chain stands: route two's `hstep` ⟸ `hleast` ⟸ decidable reachability from `Itower m` ⟸
  bounded enumeration (now certified) plus the size bound (Stage 56). Both ingredients exist. What remains is
  to assemble them into the decision procedure and the `hleast` extraction, which is the deficit-style
  argument `boundedClosure_isSome` already does for the K-free case — and which will need the same widening,
  since it too is built on `smallTerms`.
- Ranking, as obligations: (1) **widen the closure-saturation argument to `skSmallTerms`** — `deficit`,
  `deficit_lt` and `boundedClosure_isSome` are the pieces, all of them K-free only for the same inherited
  reason. That yields decidable reachability from `Itower m` and closes route two's chain to `hstep`.
  (2) piece (v) with route two. (3) rungs 2/3 via match-bounds. (4) C6, declined a forty-fifth time.

## 2026-07-25 — Stage 58: four inherited restrictions and one real one

- The chain closed. Route two's `hstep` is proved and there is now a second `Simulation` of the countdown
  into SK whose `bwd` shares nothing with the first except the encoding — one through K-normal forms and a
  commutation square, one through trajectory segments and a path-advancing interface. Getting two
  independent proofs of the same adequacy is the kind of confirmation I would not have sought deliberately
  and am glad to have.
- The stage's real content is the audit of five K-freeness restrictions. Four of them — `enumAt`,
  `smallTerms`, `deficit`, `boundedClosure_isSome` — turned out to be inherited from what the census wanted
  rather than structural, and lifting them was mechanical once I looked. The fifth, `mem_of_saturated`, was
  genuinely load-bearing: it bounds an intermediate by leaf-count monotonicity, and with `K` around leaf
  count rises and falls, so an intermediate can exceed both endpoints. That one could not be removed. It
  could be REPLACED, by the hypothesis actually needed — a bound on the whole region, which travels along a
  path because a reduct of a reduct is a reduct.
- I want to hold onto the distinction, because "check whether the restriction is load-bearing or inherited"
  was Stage 57's habit and this is the first time the answer came back "load-bearing". The right response
  was not to give up and not to force it, but to ask what the hypothesis was BUYING and supply that instead.
  Four removals and one substitution is a better outcome than five removals would have been, because the
  substitution is where the mathematics actually was.
- A general fact fell out that is worth more than its role here: bounded-region reachability is decidable
  for full SK. That does not contradict undecidability of SK reachability — it is undecidable precisely
  because the region cannot be bounded in advance — and the countdown supplies its own bound via Stage 56.
- Small note: `Nat.find` is Mathlib's, not core's, so the least-witness extraction is fifteen lines of
  walking up from zero carrying "nothing below has satisfied it yet". Zero-dependency has cost real time
  across this project and almost never cost correctness; this is a typical instance of the tax.
- Stage 55 said this step needed `Classical.choice` and I declined to use it, reporting a reduction instead.
  Three stages later the reduction closed constructively. I do not think that was luck — the reduction named
  what was missing precisely enough that finding it was a search rather than a hope — but it is worth noting
  that "report the reduction rather than reach for the axiom" paid off in the end and not just in principle.
- Ranking, as obligations: (1) **piece (v)** — the tag-step driver, now with two proven adequacy templates
  and a decidability layer that no longer stops at pure S. This is construction work at last. (2) rungs 2/3
  via match-bounds. (3) C6, declined a forty-sixth time.

## 2026-07-25 — Stage 59: the composition was free, and that is the finding and the caveat

- I wanted to know whether the pipeline composes before building a driver, so I looked for the smallest
  genuine `TagSystem` I could push through it. Deletion number one, one symbol, empty rule: the word shrinks
  by one per step and halts when empty. That is the countdown exactly, `List.length` is the isomorphism, and
  `Simulation.comp` did the rest.
- Two things I did not expect. First, `Simulation.comp` has been in the tree since Stage 8 and had never been
  used for anything but a sanity example; it worked on the first try. Second, the tag system inherits BOTH of
  the countdown's adequacy proofs for nothing, because composition takes whatever `bwd` it is handed — so
  there are now two independent `Simulation`s of a `TagSystem` into SK.
- And the composition was free precisely because the system does not compute. A unary tag system with an
  empty rule is a countdown wearing a tag system's clothes. I want that stated as loudly as the result,
  because "a TagSystem is now hosted in SK" is exactly the sort of sentence that could be read as discharging
  criterion (a), and it does not come close: Cocke–Minsky universality needs m = 2 over a finite alphabet, and
  the driver has to inspect a symbol and append its rule. Neither happens anywhere in this file.
- What it does buy is the shape of the remaining construction, and that is not nothing after nine stages of
  circling. Encode the word, do one deletion per source step, reuse the countdown's adequacy template. The
  extra work is symbol dispatch — which Stage 50 measured as compatible with the K-normal-form abstraction,
  and which was the part I had expected to be hardest — and the rule append, which no stage has tested.
- Small Lean note, third time this week: `subst` on `h : w' = rest` eliminates whichever variable it can, and
  which one that is depends on binding order. Twice now I have written the follow-up proof against the wrong
  survivor. The fix is to rewrite with the equation rather than substitute when I care which name remains.
- Ranking, as obligations: (1) **test the rule append** — the one part of a driver no stage has probed.
  Concretely: can a term that appends a fixed list to an encoded word keep its intermediates inside the
  abstraction, the way dispatch does? Cheap to check with the countdown's own machinery, and it is the last
  unmeasured component before the construction. (2) piece (v) proper. (3) rungs 2/3 via match-bounds.
  (4) C6, declined a forty-seventh time.

## 2026-07-25 — Stage 60: the component that turned out not to exist

- Yesterday's ranking said the rule append was the last unmeasured component of a driver. It is not a
  component. With a right-fold encoding, appending at the end is substituting for the fold's nil argument,
  which is a fixed four-abstraction wrapper with no recursion and no dependence on the list. I compiled it
  with the tree's own bracket abstraction and checked it against directly-encoded lists.
- The encoding choice is doing all the work, and it is the natural one for this problem rather than a trick:
  tag systems consume at the front and produce at the back, and a right fold makes both ends cheap. I had
  been carrying an unexamined assumption that the word would be a cons-list, where append is a traversal and
  therefore recursive. That assumption was never stated, which is why it survived several stages.
- I used two different observers for the agreement checks — `(K, S)`, which keeps only the head, and
  `(I, K)`, which keeps the structure. A single observer that collapses would have made any two lists look
  equal. That is the same care as Stage 50's non-vacuity count and I am glad it is becoming automatic.
- And I ran a negative control, because the build finished in 1.3 seconds and normalising a 414-leaf term
  four times with fuel 20000 should not be that fast. A deliberately wrong guard made the build fail, so the
  guards bite. Second time this week that "that felt too fast" was worth thirty seconds.
- **Where piece (v) actually stands, after ten stages of narrowing.** Three ingredients were in question.
  Symbol dispatch was measured compatible in Stage 50 and came for free. Rule append is a constant, shown
  here. Self-reproduction is open and has been open since Stage 50, and every attempt to test it without
  building a driver has failed for the reason Stage 52 identified: the diagnostic is only meaningful relative
  to a source machine.
- So the narrowing is done. There is nothing left to measure, and the remaining question cannot be answered
  by measurement. That is a clean place to have arrived, and it took correcting my own ranking in four of the
  last six stages to get here — which I would rather record as the method working than as four mistakes.
- Ranking: (1) **build the driver**. Not "test something first" — Stage 52 established that the last
  ingredient is not testable in isolation, and Stages 59–60 have fixed the shape and eliminated two of three
  unknowns. The construction is a fold-encoded word, a dispatch on the head symbol, a constant append, and a
  self-reproducing wrapper; the first three are settled. (2) rungs 2/3 via match-bounds. (3) C6, declined a
  forty-eighth time.

## 2026-07-25 — Stage 61: the fixpoint I did not need

- The last open ingredient turned out to be two abstractions. `W = λx.λd. x x (F d)` gives `W W d ⟶* W W (F d)`
  for any `F`: the driver reappears, the data advances, and the self-application is one `S`-redex rather than
  an unfolding. Fifteen leaves plus `F`.
- I had been carrying "self-reproduction means a fixpoint combinator" since Stage 11, and it shaped three
  stages of measurement. Stage 50 measured `omegaSK` as the proxy and found its K-normal forms sprawl; Stages
  51 and 52 tried and failed to make that measurement mean something. The proxy was wrong in a way I can now
  say precisely: `omegaSK` is self-application with NOTHING TO ADVANCE. A driver's self-application carries a
  step function, and the step function is where the discipline lives. Measuring the bare self-application told
  me about a term with no encoding, which is exactly Stage 52's complaint about itself.
- Doing the bracket abstraction by hand instead of calling `bracket` mattered twice. It gave fifteen leaves
  instead of the hundreds the naive algorithm produces — Stage 60's `APPEND` came out at 414 — and it made the
  proof a short explicit reduction chain, which needs no axioms at all, rather than a normalisation of
  something enormous. When the term is small enough to reason about, prove it; when it is not, the tooling
  will only tell you it evaluates.
- So all three ingredients of piece (v) are settled: dispatch free, append constant, self-reproduction proved.
  What is left is assembling the step function for a universal tag system, and that is engineering with
  understood parts rather than an open question. After eleven stages of narrowing that is a real change in
  kind, and I want to be careful not to overstate it: assembling `head`, `tail`, `dispatch` and `append` into
  one certified `fwd` for m = 2 over a two-symbol alphabet is still a substantial build, and the terms will be
  large enough that proving `fwd` will need the same by-hand discipline that made today cheap.
- The pattern worth keeping from today: **an assumption inherited from a plausible analogy survived eleven
  stages because it was never written as a claim.** "Recursion needs a fixpoint" is true for general recursion
  and false for self-reproduction with a fixed step, and I never separated the two. Stage 60 caught the same
  shape — "append needs a traversal" was true for cons-lists and false for folds. Both were unstated
  assumptions about representation, and both dissolved the moment I wrote down what was actually required.
- Ranking: (1) **assemble the step function** for a two-symbol m = 2 tag system — head, double tail, dispatch,
  append — and prove `fwd` for it. By hand where the terms are small enough to reason about. (2) rungs 2/3 via
  match-bounds. (3) C6, declined a forty-ninth time.

## 2026-07-27 — Stage 62: a YAGNI that came due

- The toolkit design was right and the compilation was fatal. `head`, `tail`, `cons`, pairs — all fixed
  combinators, with `tail`'s traversal done by the data's own fold rather than by driver recursion. Compiled
  with the tree's naive bracket abstraction, `TAIL` came out at 14100 leaves and the evaluator did not time
  out on it, it ABORTED. With the occurs check it is 192 leaves and runs in a third of a second.
- What I like about this one is that the decision that caused it is documented in the file, in my own words
  from Stage 9: "no occurs-check optimization. Terms come out bigger, proofs come out smaller; for calibration
  the proofs win (YAGNI)." That was correct. Calibration needed small proofs and never needed to RUN anything
  large. The judgement only became wrong when the work changed, and the note is what let me see immediately
  what to do instead of wondering why my terms were enormous.
- So the lesson is not "don't YAGNI". It is that a YAGNI is a loan, and the note in the file is what makes it
  repayable. I have been writing that kind of note fairly consistently and this is the first time one has been
  called in.
- Worth recording that the optimisation looks worthless at small scale — 15 leaves versus 9 on a
  three-abstraction constant function — and is 73× on real code, because it compounds with nesting. If I had
  benchmarked it on a toy before deciding, I would have concluded it was not worth having. Stage 41's lesson
  about probes and parameters, in a new costume: the measurement has to be taken at the size the work actually
  uses.
- The verification used two observers again, and I now consider that automatic for anything that compares
  encoded data — a single collapsing observer makes any two lists agree.
- **Where piece (v) is.** Every component exists and runs. What is left is genuinely assembly: write the m = 2
  step as one term, then prove `fwd`. I want to be honest that the proof is the hard part and not the writing
  — `fwd` has to be a reduction chain over a term in the hundreds of leaves, and Stage 61's trick (hand
  abstraction to keep the chain short) will not scale to the whole step function. That is the next real
  problem, and it is a proof-engineering problem rather than a design one.
- Ranking: (1) **write the m = 2 step function and validate it by evaluation** before attempting `fwd` —
  the same order that has worked for twelve stages, and it will also tell me how big the assembled term is,
  which determines whether `fwd` is provable by chain or needs a different technique. (2) rungs 2/3 via
  match-bounds. (3) C6, declined a fiftieth time.

## 2026-07-27 — Stage 63: writing it down changed what the proof costs

- The step function exists and runs. 696 leaves, four steps of a real two-symbol m = 2 tag system validated
  under two observers each, with a negative control that fails as it should. Assembly took one sitting because
  every component had already been built and measured separately, which is what twelve stages of narrowing
  bought.
- The finding is a correction to my own outlook from yesterday. I said `fwd` would be a reduction chain over
  hundreds of leaves and called it proof engineering. That was wrong, and writing the term down is what showed
  it. `tagFwd_of_step` — three lines — reduces `fwd` to step-correctness, because `selfRep_advances` already
  covers the driver for ANY step function. And step-correctness does not need the compiled term at all:
  `bracketOpt_beta` lets each compiled piece be reasoned about at the lambda level, so what is left is four
  list inductions and their composition.
- So the cost estimate was off by a lot, and the reason is instructive. I estimated the proof from the SIZE OF
  THE ARTIFACT rather than from its STRUCTURE. 696 leaves sounds like a hard proof; four compositional lemmas
  over a fold encoding does not. The artifact is large because bracket abstraction is verbose, not because the
  argument is complicated, and those are independent.
- I have made the mirror-image error before and recorded it: Stage 39 assumed a heavily-constrained shape was
  important because it was tractable. Here I assumed a large term meant a hard proof. Both are estimating one
  property from an unrelated one, and I do not yet have a habit that catches it. The nearest thing is what
  worked today by accident: build the object, then look at what the proof would have to touch.
- Also worth noting for the record: concatenation of folds turned out cheaper than Stage 60's single-element
  append and strictly more general. I built the special case first because the tag rule appends "a word", and
  I read that as "a symbol at a time" without checking. The general operation was simpler than the special one.
- Ranking: (1) **prove the four compositional lemmas** — head, tail, concat, dispatch — over `mkWord`, then
  assemble step-correctness and `fwd`. That is the last thing between this development and a `Simulation` from
  a two-symbol m = 2 tag system into SK. (2) rungs 2/3 via match-bounds. (3) C6, declined a fifty-first time.

## 2026-07-27 — Stage 64: the lemma that validation could not have caught

- `fwd` is proved. A genuine two-symbol, deletion-number-two tag system — `a ↦ [b]`, `b ↦ [a,b]` — is
  driven inside SK: every source step becomes actual reduction on the encoded word (`tagAB_fwd`), axioms
  `[propext, Quot.sound]`. The proof went the way Stage 63 predicted: β at the lambda level, then four
  compositional lemmas, then composition. Head needed no induction at all; tail and concat one list
  induction each; dispatch is two firings. The 710-leaf compiled term never appears in any proof.
- Except that one of the four lemmas was false. `CONCATf (mkWord u) (mkWord v) ⟶* mkWord (u ++ v)` cannot
  hold: the fold-concatenation β-reduces to a compiled abstraction whose top spine is `S` applied to two
  arguments, and no reduction ever fires at that spine again, while a nonempty `mkWord` carries `S` applied
  to four. Writing the first induction is what surfaced it — the goal was plainly unprovable before any
  tactic ran. The fix is the classic cons-directed concatenation `λL M. L CONS M`: folding the left word
  with `CONS` itself rebuilds it on top of the right word, so every intermediate stays cons-built. Fourteen
  leaves bigger than `CONCATf`; reachability is what the extra leaves buy.
- The instructive part is WHY the false lemma felt safe: `CONCATf` was validated, four steps, two observers
  each, negative control. All of that was real and all of it certifies observational equality — and `fwd`
  consumes reachability, which is strictly stronger in a calculus with no extensionality. The two-observer
  discipline was adopted in Stage 50 exactly to avoid vacuous agreement, and it did its job; I then let
  "validated" stand in for "correct for the property the proof needs." A test can only vouch for the
  equivalence it tests. That is Stage 63's estimate error in a new place: size vs structure there,
  observational vs reachable here — both substitute an adjacent property for the one in play.
- Also the third representation assumption in five stages, after "append needs a traversal" (60) and
  "self-reproduction needs a fixpoint" (61): "a combinator that computes the right list IS the right list."
  All three dissolved the moment the requirement was written down formally. The habit I keep not having is
  to write the claim before building the artifact; this stage got it for free because the artifact already
  existed and the claim came due.
- The infrastructure was cheap and is general: substituting closed data under `bracketOpt` commutes as an
  EQUALITY (`bracketOpt_subst_ofTerm` — the naive algorithm only ever had it up to reduction), and a
  β-ladder to arity four at the `Term` level. Anything compiled from lambda bodies is now provable this way.
- New anchors are literal-normal-form guards, `nf (STEPc (encWord w)) = nf (encWord w')` — stronger than
  observer agreement, and available only because the output is now reachable.
- Ranking: (1) **the `Simulation` itself**: `dec` is mechanical; `bwd` is the demanding half, as it was for
  the countdown. The new structural fact to face is that the driver duplicates ITSELF every step, so
  Stage 11's `normalForm_bracket` becomes load-bearing. Start by checking whether the K-normal-form
  abstraction (45–48) or the trajectory relation (49–58) transplants. (2) rungs 2/3 via match-bounds.
  (3) C6, declined a fifty-second time.

## 2026-07-27 — Stage 65: the proof attempt that found the driver wrong

- Proceeded to `dec` and `bwd`. The decoder was as mechanical as predicted — syntactic peel, `dec_enc`
  by one induction, `[propext]` only — and it immediately paid for itself twice: injectivity comes free,
  and with Stage 64's `fwd` that registers `tagABPathEncoding`. The class this program's refutations
  quantify over is now inhabited by a genuine dispatch machine, which is a calibration symmetry I did
  not plan and am glad to have.
- Then `bwd`, and the honest first move was to check whether either countdown template transplants.
  Neither does, and both failures became theorems rather than impressions. Route two died in five
  minutes of running the machine on paper: `[b,a,b] ↦ [b,a,b]` is a fixed point of the source, and
  `OnSegment`'s "not yet past `w`" clause is unsatisfiable at any self-loop, for every encoder — an
  acyclicity assumption about the SOURCE that sat hidden in the relation because the countdown only
  ever counts down. Route one died at the driver's first host step: the self-application's K-normal
  form is a mid-step term with the wrong head, provably no encoding.
- The real finding came while asking what an abstraction should assign to a STUCK word's states: it
  would have to track `STEPc (encWord [b])` — and `STEPc` happily computes on it. `tail (tail [b]) = []`,
  `head [b] = b`, append `[a,b]`: the host walks `encTag [b] ⟶* encTag [a,b]` where the source has no
  step. **`bwd` is not hard for this encoding; it is false** (`tagAB_bwd_false`). The tag step is
  partial, the compiled step function is total, and I never wrote the totality mismatch down as a
  claim, so no stage ever tested it.
- That is the second consecutive stage where the gap between "validated" and "true" surfaced only when
  a proof was attempted. Stage 64's lesson was that a test only vouches for the equivalence it tests;
  this one is that a test only vouches for the INPUTS it exercises — every Stage 63 test word was long
  enough to step. The question that would have caught it ("what does the step function do to a word
  that cannot step?") is a specification question, askable before any proof, and I did not ask it.
- Also worth recording: the order of work this stage was right in a way Stage 55–58 taught. Refute the
  templates and probe `bwd`'s truth BEFORE building the big reachable-set invariant — because the
  invariant for the unguarded driver would have been effort spent proving the unprovable. The cheap
  checks earned their keep exactly as the expensive one would have wasted it.
- Infrastructure that outlives the stage: K-normality is now DECIDED (`hasKRedex` +
  `kNormalForm_of_no_kredex`), so machine-code K-normality obligations are `by decide` instead of
  shape-lemma chains; and `RS.NormalForm.steps_eq` is the generic twin of the Term-level fact, axiom-free.
- Ranking: (1) **Stage 66: the guarded driver.** A constant-size fold observer for "has at least two
  symbols" (same idiom as `HEADf`), dispatch on it, identity on stuck words — then re-prove `fwd` (the
  four Stage 64 lemmas reuse as-is) plus "stuck words self-loop in the host". (2) The third
  abstraction and the driver's reachable-set characterisation — the analogue of `Tower` for a
  1450-leaf machine, now correctly targeted at a driver whose `bwd` is at least not false. (3) rungs
  2/3 via match-bounds. (4) C6, declined a fifty-third time.

## 2026-07-27 — Stage 66: the guard, assembled from parts that already existed

- The repair went through in one sitting, and the reason is worth stating plainly: not one new
  induction was needed. The emptiness observer's verdicts are one β each (`NONNILf_cons` needs no
  recursion — any cons makes the constant observer fire); the guard's three verdicts ride
  `TAILf_mkWord`; step-correctness is "guard passes, then Stage 64's theorem"; the stuck case is a
  two-firing dispatch chain. The compositional lemma library from Stage 64 absorbed the entire stage.
  This is what Stage 61 predicted paying for the by-hand discipline, and it has now paid twice.
- `STEPg` costs 936 leaves against `STEPc`'s 710. Two hundred twenty-six leaves is the price of
  respecting the tag step's partiality — cheap, and I note that the expensive-looking part of the
  guard (`HASTWOf`, 211) is almost entirely the embedded `TAILf`. A dedicated two-symbol probe could
  be smaller, and I am deliberately not building it: the lesson of Stages 60 and 63 is to stop
  optimising representations that already compose.
- The dispatch discards the doomed `STEPc L` branch UNREDUCED — `F = S K` exposes a `K` and the whole
  pending computation vanishes. That is elegant and it is also a trap I want on record before it
  bites: the HOST is not obliged to take my path. It may reduce inside the doomed branch first, so
  the reachable set from a stuck word's encoding still CONTAINS the unguarded computation — confined
  to doomed positions. The guard did not shrink the reachable set; it changed which whole terms are
  reachable. The future abstraction must be blind to doomed subterms, which is the same demand both
  Stage 65 refutations already made. Nothing new is owed, but nothing was waived either.
- One wrong proof chain (`NONNILf_cons`) was caught immediately by the elaborator: I wrote a congruence
  where the whole term was already the redex. Small, but the pattern — over-decomposing a reduction
  that is one step — is the proof-level cousin of over-decomposing a design, and both come from not
  looking at the term first.
- The regression suite now contains the input class whose absence let Stage 65's bug survive three
  stages: stuck words normalise to themselves, and provably not to the unguarded driver's output.
- Where the Simulation stands: `enc`, `dec`, `dec_enc`, `fwd` all done for the guarded driver;
  `bwd` open rather than false. The whole remaining distance is the reachable-set characterisation
  and the third abstraction over it.
- Ranking: (1) **the reachable-set characterisation**, and I want to attempt it COMPOSITIONALLY:
  per-combinator segment invariants ("every reduct of `HEADf (mkWord w)` lies in this family", and so
  on for `TAILf`, `CATf`, the dispatch, the driver shell), composed the way the step function itself
  composes. Stage 56's `Tower` was four constructors for a three-leaf-per-layer machine; a monolithic
  invariant for a 936-leaf machine is not writable, but the machine is a composition and the invariant
  might be too. If the first per-combinator invariant (start with `HEADf`, the smallest) turns out
  unwritable, that is the finding. (2) rungs 2/3 via match-bounds. (3) C6, declined a fifty-fourth
  time.

## 2026-07-27 — Stage 67: the audit that shrank the problem

- The ranking said to start `HEADf`'s segment invariant. Before writing constructors I audited the
  assumption every invariant would lean on — code is rigid when duplicated — and it is false for the
  machine actually being run. Stage 11's `normalForm_bracket` is about the naive algorithm on pure
  bodies; `bracketOpt` K-protects x-free APPLICATION chunks as they stand, redexes included. Eleven
  pure-body combinators are normal (one-line proofs each); `TAILf`, `RULEf`, `HASTWOf`, `STEPc`,
  `STEPg` and — the one that matters — `selfRepW STEPg`, the term duplicated every driver cycle, are
  not. I nearly started building invariants on top of a false premise, and the check cost one hour.
- The useful part is the accounting, not the verdict. `STEPg` ships six live positions and every one
  is identified: three are rule-output WORDS — and words are non-normal by design, `mkWord` IS an
  application chain, that is what literal reachability bought in Stage 64 — and three are copies of a
  single internal constant, `TAILf`'s accumulator pair. The first three are data drift, owed anyway.
  The last three are fixable by shipping the accumulator pre-normalised (`λs. s [] []` compiled,
  β-identical). One small rebuild and code drift IS data drift — one species, one family to
  characterise: the reducts of `mkWord w`.
- I also learned where the census tooling's ceiling is, by hitting it. `boundedClosure` on bare
  `TAILf` did not saturate in twenty-five minutes of interpreter time; the countdown's whole machine
  saturates inside a `#guard`. I killed the runs and switched to single-path measurements, which is
  what still computes: drift distances (STEPg is 168 LO-steps from quiescence) and live-position
  counts (which compose additively, a small pleasant surprise worth having on record). The
  methodological note: when the probe stops answering, the probe's SILENCE is the measurement — the
  state spaces here are beyond enumeration, so parameterized families were forced regardless of what
  the exact counts would have said.
- Two stages ago the mountain was "characterise the reachable set of a 1450-leaf machine." Today it
  is "characterise the reducts of `mkWord w`, then compose through machinery whose non-word drift is
  zero." The mountain did not get smaller by climbing; it got smaller by two audits — bwd's falsity
  (Stage 65), code's rigidity (this stage) — each of which was a question, not a proof. I want to
  keep noticing that the cheapest tool in this development has been the well-aimed question about an
  unexamined premise.
- Ranking: (1) **Stage 68: the accumulator rebuild** — `TAILZn := compiled λs. s [] []`, rebuild
  `TAILf`/`HASTWOf`/`STEPc`/`STEPg` on it, re-prove the touched lemmas (the pair-projection lemmas
  adapt; everything else should carry), and add the build-enforced fact that the new step function's
  only live positions are words. (2) The word-drift family: characterise the reducts of `mkWord w`,
  parameterized — the one species. (3) rungs 2/3 via match-bounds. (4) C6, declined a fifty-fifth
  time.

## 2026-07-27 — Stage 68: rigidity turned out to be a discount

- The rebuild went through in one sitting and the driver came out SMALLER: 870 leaves against 936.
  The compiled accumulator is 15 leaves where the applied pair was 37, saved three times over. I had
  been thinking of normality as a property to pay for; here the clean version is cheaper because
  compiling `λs. s [] []` IS the normal form of applying `PAIR` to two nils — the redex I was
  shipping was precisely the work the compiler could have done once, at compile time. That reframing
  — a shipped redex is deferred compilation — feels like the general form of Stage 67's finding.
- The part I expected to ripple did not, and the reason is a better invariant. The old tail-fold
  invariant said the fold reaches `PAIRf (mkWord w) (mkWord w.tail)` — LITERALLY a `PAIRf`
  application, which the new accumulator's base case cannot produce. Stated existentially — the fold
  reaches SOMETHING whose projections behave — the base case is two β-lemmas (`FSTf_TAILZn`,
  `SNDf_TAILZn`) and everything else is untouched. And the uniform `TAILn_mkWord` subsumes the old
  cons-only lemma plus the separate nil lemma. The lesson is one this development keeps meeting from
  different sides: state obligations by BEHAVIOUR, not by shape, unless shape is the theorem. Stage
  64 needed shape (reachability IS shape); the fold's accumulator never did.
- Build-enforced now: `STEPcn`, `STEPgn`, and the wrapper the driver duplicates each carry exactly
  three live positions, all rule-output words. Code drift and data drift are one species, as Stage 67
  predicted, and the guards will catch any future edit that reintroduces a non-word redex.
- Everything re-proved on the clean stack without a single new induction — `mkWord_tailPairN` is the
  same induction restated. Third stage in a row where the Stage 64 lemma library absorbed the work.
- Ranking: (1) **the word-drift family**: characterise the reducts of `mkWord w` — an inductive
  family with independent per-copy drift, Tower's `half` generalised. This is now the ONLY species of
  drift in the whole machine, so it is the entire base layer of `bwd`. Start with the single-cell
  word and the question "what does `CONSf x M` reach when `x` is a symbol and `M` is in the family?"
  (2) the machine phases over it. (3) rungs 2/3 via match-bounds. (4) C6, declined a fifty-sixth
  time.

## 2026-07-27 — Stage 69: the enumeration that dissolved

- The ranking said to build the word-drift family as an inductive shape family, Tower's `half`
  generalised. I started by writing out what the single cons cell's constructors would have to be and
  stopped: a cell is an interleaved two-layer distribution machine, dozens of drift-parameterized
  states, and Stage 67 already measured that these spaces outrun the census tooling. The correct move
  was Stage 68's lesson applied one level up — characterise by BEHAVIOUR. Give each word a canonical
  normal form (`wordNF`, code-forms all the way down), prove the word reaches it, and confluence turns
  every drifted copy into a completion: `mkWord_drift_complete`. The family never gets described; it
  gets completed. Closure under reduction is free BY CONSTRUCTION, which is precisely the property the
  hand-enumerated family would have needed hundreds of cases to prove.
- What made this work is a fact I had not consciously registered: words HAVE normal forms even though
  the machine never computes them. The driver always applies words before they quiesce; but the
  canonical form exists as a mathematical anchor regardless of whether any execution visits it. The
  anchor does the work Tower's constructors did for the countdown, at zero constructors.
- The fifth `Classical.choice` leak, and the audit caught it exactly like the first four. The big
  `simp` in `wordCode_explicit` closed the goal and quietly routed through the `BEq` layer — Stage 9's
  trap, eleven weeks and sixty stages later, in a file that QUOTES that trap. The fix is the same
  shape as always: supply the decidable literals as `rfl`/`decide` facts, let `simp only` assemble.
  I will keep running `#print axioms` per stage until the toolchain changes, and evidently not a stage
  earlier.
- One genuinely reusable piece fell out: `steps_toTerm_subst` — reduction is congruent under
  substitution contexts. It is the lemma that lets a hole's contents advance inside compiled code,
  and the phase layer will lean on it hard.
- The asymmetry that defines the next problem, stated while it is fresh: words have normal canonical
  forms; machine states never do (`encTagN w` always carries its driver redex). So the phase layer
  cannot reuse `nf_unique` — its checkpoints are canonical for a DIFFERENT reason (the driver's own
  structure), and finding the right formulation of "canonical without normal" is the research content
  of `bwd` from here.
- Ranking: (1) **injectivity of `wordNF`** on encoded words — syntactic, small, and it upgrades
  `mkWord_drift_functional` from "equal canonical forms" to "equal words". (2) The phase layer:
  segments between consecutive encodings, with drift-completion relative to the driver's structure
  in place of normality. (3) rungs 2/3 via match-bounds. (4) C6, declined a fifty-seventh time.

## 2026-07-27 — Stage 70: the small stage that closes a layer

- Injectivity went through as predicted — syntactic, one induction, injection chains through the
  skeleton `wordCode_explicit` fixed in place two stages ago. `wordNF_injective` costs `[propext]`
  alone. The corollary chain ends at `encWord_drift_pins`: an encoded word in flight, duplicated and
  drifted on any reduction schedule the host chooses, still determines its source word uniquely.
  The identity layer of the future abstraction is done, and it is three theorems rather than a
  constructor family.
- Worth noticing how the last three stages compose: Stage 68 made the skeleton explicit for
  NORMALITY, Stage 69 reused it for CONGRUENCE, this stage for INJECTIVITY. One explicit term, three
  load-bearing uses. The habit worth extracting: when a compiled artifact must be reasoned about
  more than once, pay once to write it out.
- The phase layer is now scoped precisely, and I want the asymmetry on record in the form the next
  attempt will meet it. Words complete BACKWARD-agnostically: any reduct rejoins the one canonical
  form, because that form is normal and confluence has nowhere else to send the join. Machine states
  can only complete FORWARD: `encTagN w` is never normal, its reducts flow toward LATER encodings,
  and the candidate theorem is exactly that — every reduct of `encTagN w` reaches `encTagN w'` for
  some source-reachable `w'`. If that holds, `bwd` follows by the path-advancing tracking machinery
  with the segment relation; the entire remaining difficulty is that one forward-completion, and it
  must thread the driver's phases: mid-dispatch, mid-fold, mid-append states all completing to the
  next encoding while their doomed branches are discarded.
- Ranking: (1) **forward drift-completion for the driver** — start by proving it for ONE phase
  segment (the states between `encTagN w` and `encTagN (step w)` along the canonical `fwd` path,
  perturbed by drift in word slots), using `encWord_drift_pins` and `steps_toTerm_subst`; if even the
  one-segment version resists, measure WHERE. (2) rungs 2/3 via match-bounds. (3) C6, declined a
  fifty-eighth time.

## 2026-07-27 — Stage 71: the objection that taught the structure

- I nearly recorded the segment theorem as false. The argument felt airtight: drift is irreversible —
  a reduct of `mkWord w` never returns to `mkWord`-form — so a drifted state cannot reach a literal
  encoding. What it missed is that the machine never transports the word-term; it FOLDS it, and the
  fold consumes exactly the part that drifts. The machinery carries the drift, application spends the
  machinery, and the rebuild uses only ingredients that cannot drift — normal symbols, normal code
  (Stage 68's dividend, load-bearing again). So literalness is RESTORED at every fold, and the
  objection inverted into the proof strategy: complete the input to `wordNF`, compute on the
  canonical form, watch literal `mkWord`s come out.
- The near-miss is worth a note to self: I have now twice this week almost believed a false
  impossibility (`bwd` "unprovable" before checking the driver, drift "permanent" before checking
  what consumes it). Both times the error was reasoning about a TERM'S trajectory when the question
  was about a COMPUTATION'S — the term does not survive, so its irreversibilities do not transfer.
  The dual error to Stages 63–65's, where I trusted computations and missed term-level facts.
- The proofs themselves were the Stage 64 suite replayed with `wordCode_beta` in place of
  `CONSf_beta` — same inductions, same shapes, one sitting, everything `[propext, Quot.sound]`.
  Fourth consecutive stage in which the lemma library absorbed the new layer whole. The canonical
  form even computes MORE cleanly than the literal one (its β is one lemma, not a distribution).
- Stuck words complete to the CANONICAL stuck state (`wordNF`-data) and stay there — so the phase
  relation's stuck cells have a canonical representative after all, just not the literal encoding.
  That asymmetry (running words re-anchor to literal encodings, stuck words to canonical forms) is
  now precise and proved, and the future segment relation should bake it in.
- Ranking: (1) **the segment interior**: reducts of `encTagN w` where the driver itself is
  mid-unfolding. Plan of attack: the driver's cycle has finitely many CANONICAL phase checkpoints
  (post-`selfRep`-unfold, post-guard, post-dispatch, post-fold); prove each checkpoint's basin
  completes forward to the next checkpoint, then chain. The unknown is whether "basin" can be
  characterised by completion the way words were, or needs the case analysis the countdown's
  `sk_square` did. (2) rungs 2/3 via match-bounds. (3) C6, declined a fifty-ninth time.

## 2026-07-27 — Stage 72: the frame I had to take back

- Two stages of momentum said the remaining work was "prove forward completion for the interior".
  Pressure-testing that plan before building it found the flaw: completion is about where states
  flow, and `bwd` is about the order in which encodings can be visited. A foreign encoding reachable
  from `encTagN w` whose own cone rejoins the trajectory downstream satisfies every completion
  statement I was planning to prove. The countdown's proofs were never completions — stutter-or-
  advance and least-index are per-step and order-aware — and I knew that in Stage 65 when I refuted
  their transplants, then lost it in the satisfaction of Stage 71's theorem. The correction cost an
  hour of analysis and zero wasted stages, which is the pattern I most want to keep: pressure-test
  the frame BEFORE the multi-stage investment, the same reflex that caught bwd's falsity and the
  rigidity failure.
- What survives of Stages 70–71 is everything except the framing: drift-completion, literalness
  restoration, and the identity layer are exactly the ingredients `hstep` will consume when it
  handles the data slots. The order bookkeeping is what they cannot supply.
- Three small theorems today, each earning its place: the cone lemma (`interior_joins_trajectory` —
  the true generic content of completion, one line); layer-shedding (`selfRep_layer_shed`, axiom-
  free — the driver's shell nests future cycles, and each shed layer advances the data once, which
  is precisely why Stage 54's path-advancing interface exists); and decoder-blindness
  (`decWord_wordCode` — interiors and encodings are syntactically separated).
- The loop-tolerant segment relation is now written down in the file, and its obligations named:
  `hfun` and `hstep` both reduce to encoding-to-encoding reachability facts, and THOSE need the
  interior factorization — shell contexts over data holes, hand-off at consumption. That
  factorization is the one theorem left of `bwd`, and it has been since Stage 65; what changed today
  is that nothing else is mistaken for it.
- Asked again, as Stage 65 taught: is `bwd` simply false? No falsifier — the fold rebuilds only
  `tail² ++ rule` words and dooms are discarded unreduced. Open until `hstep` closes it.
- Ranking: (1) **`hfun` and `habs` for the segment relation** — cheap, testable before the expensive
  engine, and they will say whether the relation's shape is right (Stage 53 did exactly this for the
  countdown and it caught the design early). (2) The factorization engine. (3) rungs 2/3.
  (4) C6, declined a sixtieth time.

## 2026-07-27 — Stage 73: the test that closed the landscape

- The cheap test did its job twice over. First: `habs` for the segment relation is not immediate —
  I wrote that it was in Stage 72's design comment, and formalising the relation showed its clause
  IS the encoding-order fact, reduced to an iff (`segRel_habs_iff`) so nothing cheaper can hide in
  it. The two honest instances (stuck words, the fixed point) are exactly the states where order is
  degenerate. Looking back at the countdown with this lens: its trajectory relation's `habs` leaned
  on `itower_steps_le`, which is proved FROM the first Simulation's `bwd`. Route two was always a
  second proof; I had catalogued that fact in Stage 53's notes and not seen its consequence until a
  formal test forced it.
- Second: while asking what a first proof could still use, the bounded-region route died on paper in
  five minutes and in Lean in twenty: the shell pre-unfolds future cycles without bound
  (`selfRep_nests`, axiom-free — a pleasing little induction: unfold once, then keep unfolding
  inside the `K`), so the reachable set has terms of every size (`driver_region_unbounded`). The
  countdown's region was bounded because `Itower` never self-applies; self-reproduction is
  UNBOUNDEDNESS, definitionally. Census died here in Stage 67; decidability dies here today; the
  invariant family survives because induction handles regular unboundedness — `shellNest` is one
  constructor, not infinitely many.
- The landscape is now closed, and I want to state what that means soberly. Four mechanisms are
  refuted with machine-checked witnesses; the remaining route — per-step tracking over the interior
  factorization — is forced, not chosen. Forced is better than chosen: three days ago the plan space
  was fog, and every stage since has either built an ingredient (identity layer, completion suite,
  layer-shedding) or eliminated a road. The factorization now has a precise job description: an
  inductive family of shell contexts closed under nesting, data holes handled by the Stage 69–71
  suite, hand-off at consumption, and per-step stutter-or-advance-by-path as its output — with
  Stage 54's path-advancing interface, built for the countdown's K-discards, waiting for exactly
  the multi-step advances that shed layers produce.
- Ranking: (1) **the factorization family** — begin with the shell alone: contexts as an inductive
  family over one data hole, closure under Step for the SHELL cases only, hand-off left abstract.
  Even that fragment would be the first genuine interior invariant. (2) rungs 2/3 via match-bounds.
  (3) C6, declined a sixty-first time.

## 2026-07-27 — Stage 74: the family that became writable

- The interior factorization exists. Twelve kinds, twenty-four constructors, one closure induction,
  `[propext, Quot.sound]`, start state axiom-free. Every term reachable from the driver applied to
  data is now, by theorem, shell machinery over data holes — with the data layer behind two
  Step-closed predicates and one hand-off axiom, exactly the abstraction boundary the ranking asked
  for. Generic in the step function: this is driver theory, not tag-system theory.
- Stage 67 measured that such families were beyond writing, and it was right THEN. What changed is
  that five stages deleted the drift species before enumeration began: Stage 68 made code normal
  (no code-drift kinds), Stages 69–71 packaged data drift behind predicates (no data kinds beyond
  two), Stage 72's layer-shedding predicted the premature-application states before tracing found
  them. Twelve kinds against Tower's four. The lesson I want stated precisely: the cost of an
  invariant is set by the number of DRIFT SPECIES, not the size of the machine — and drift species
  can be eliminated by design before they are ever enumerated.
- Tracing found two states I had not predicted: the premature application (a half-built layer
  consuming data early — the family is FALSE without `ydat`), and the mid-flight discard (`ydat`'s
  K-fire killing a duplicated data copy). Both were then absorbed by single constructors. The
  compression trick that kept the family small: absorb cross-kind flows into the kinds themselves
  (`zw_done` swallows engines, `ydat_done` swallows continuations), so closure is kind-preserving
  and the induction needs no disjunctions.
- Lean's index unification did perhaps a third of the proof: every impossible root-fire dies on a
  constructor clash inside `cases`, and the build's "alternative not needed" errors were the
  machine telling me my impossibility analysis was too cautious in nine places and wrong in one
  (the drv-level pair fire, which appL had already covered). A proof assistant that complains when
  you handle too MANY cases is doing exactly its job.
- Ranking: (1) **instantiate the data layer**: define the data-expression family — words in flight,
  step-function applications, completions, the Stage 69–71 results as constructors — and discharge
  `Sh`'s `D`/`DA`/`hApp` interface with it, giving the interior invariant with nothing abstract.
  (2) The tracking abstraction over the factored states: shed-layer count = source-steps-ahead,
  data slot decodes the word; then `hstep`. (3) rungs 2/3 via match-bounds. (4) C6, declined a
  sixty-second time.

## 2026-07-27 — Stage 75: the order was in the slots

- `Simulation (RS.Tag tagAB) RS.SK` exists. Machine-checked, `[propext, Quot.sound]`, no sorry. The
  open item since Stage 8; false at first attempt in Stage 65; closed today. I want to write down
  how the last step actually happened, because it was not the plan.
- The plan said: instantiate the data layer, then build a per-step tracking relation with
  stutter-or-advance bookkeeping, then `hstep`. While choosing the instantiation I took the semantic
  option — a slot denotes the source-reachable word whose canonical form it still reaches — mostly
  because its Step-closure is free (confluence joins, `wordNF`'s normality pins; Stage 69's argument
  as an interface discharge). Then, checking what the instantiated invariant says at a literal
  endpoint, the whole of `bwd` fell out: the endpoint's slot is `encWord w'`; the invariant says the
  slot denotes some reachable `u`; `nf_unique` forces `wordNF u = wordNF w'`; injectivity forces
  `u = w'`. No tracking relation. No `hstep`. Stage 72's prediction — per-step order bookkeeping —
  was wrong in the best way: the order was never in the steps; it was in the slots, and the
  factorization had been carrying it since Stage 74.
- Every refuted mechanism now reads as the same mistake from four directions: trying to recover from
  the DYNAMICS (K-normal forms, segments, decidable regions, stutter-or-advance) what the STATICS —
  the factored shape of reachable states — carries outright. The countdown never taught this because
  its states were too small to need factoring.
- What made today one sitting instead of ten: every piece was already on the shelf. `wordNF` and
  drift-completion (69), injectivity (70), the canonical-input step suite (71), confluence-pinning
  as a habit (69), the shell family with its data holes abstract in exactly the right way (74). The
  final file is 150 lines and contains one genuinely new idea — `DataW` — plus assembly.
- Honest scope, recorded with the theorem: `tagAB` is a genuine m = 2 tag system — the Cocke–Minsky
  universal class — but this instance is not itself proven universal, and that claim is not made.
  Spec piece (v) is discharged in full: inspect, dispatch, append, guard, encode, decode, `fwd`,
  `bwd`. Scaling the alphabet to a known-universal instance is construction, not mechanism.
- Ranking: (1) **update STATUS and the spec accounting** — the open item closes, Goal 2's table
  gains its row, and criterion (a)'s satisfiable restatement now has a second, stronger witness.
  (2) The known-universal instance: generalize the driver to n-symbol alphabets (dispatch via nested
  pairs) — construction over understood mechanism. (3) rungs 2/3 via match-bounds. (4) C6, declined
  a sixty-third time.

## 2026-07-27 — Stage 76: the leak that was older than the audit

- The infrastructure went to plan: the list-indexed abstraction with β at every arity
  (`absArgs_beta` — one induction, and the arity-2/3/4 ladders of Stage 64 become corollaries),
  selectors with β stated pre/post-style so no index arithmetic survives into proofs, closed forms
  (`K`-wraps around an `S (K K)`-chain), and generic normality. The dispatch foundation for any
  alphabet size exists; the two-symbol dispatch of Stages 63–75 is the `k = 2` instance.
- The finding is the leak. My new `occurs_bracketOpt` imitated `occurs_bracket`'s `grind`; the
  per-stage audit fired; and when I went to fix MY lemma I checked the one I had imitated —
  `occurs_bracket` had been carrying `Classical.choice` since it was written, with the Goal 1
  headline `combinatory_completeness` downstream. The global claim in STATUS was false for an
  unknown number of weeks. Sixth leak, first PRE-EXISTING one, and the lesson is sharp: a per-stage
  audit certifies stages, not the tree. Claims about the tree need tree-level enforcement.
- So the tree got it: `Audit.lean` pins the exact axiom footprint of twelve headline theorems with
  `#guard_msgs in #print axioms` — any drift, anywhere, in any future stage, fails the build. This
  should have existed since Stage 9's first leak; it took a leak INSIDE the leak-detection story to
  see that the detector itself had a blind spot. Also pleasant: the pinning revealed `confluence`
  and `nf_unique` are `[propext]` alone, cleaner than the blanket claim.
- The fix itself held a small trap worth recording: `(n == n) = true` — the exact fact from Stage
  9's trap — has TOOLCHAIN-DEPENDENT clean routes (`Nat.beq_refl` vs `decide_eq_true rfl`), so
  `beqSelf` tries both and the audit pins the result. Six leaks, six times through the same door;
  the door is now instrumented.
- Ranking: (1) **the any-alphabet dispatch**: `RULEf` for `Fin n` symbols via `selArgs`, with the
  general `RULEf_encSym`-analog — then the general step function, and the Stage 69–75 pipeline
  re-instantiated (it is already generic in everything but the dispatch). (2) rungs 2/3 via
  match-bounds. (3) C6, declined a sixty-fourth time.

## 2026-07-27 — Stage 77: the one-line theorem

- `dispatchT_correct` — dispatch-correctness for any alphabet — is `Steps.trans (dispatchT_beta _ _)
  (selArgs_correct pre x post)`. One line, because Stage 76 stated selector-β in pre/post style
  instead of with index arithmetic, and the dispatcher's statement inherits the shape. The rest of
  the stage was three eight-line list lemmas and the injectivity dichotomy (K-wrap below the top,
  S-headed at it). When a theorem comes out this small, the credit belongs to the statement of the
  previous one; I want to keep noticing that statements are design surfaces, not just claims.
- One tactic lesson for the file: `subst` on `i = k` eliminated the INDUCTION variable and orphaned
  every later reference to `k` — Stage 59's which-name-survives lesson, in a new costume. `rw` at
  the hypothesis is the deterministic form.
- The symbol layer for any alphabet is now complete: normal (76), injective (77), dispatchable
  (77). Everything downstream of dispatch in the Stages 63–75 pipeline is already generic — the
  word toolkit and `wordNF` theory are over `List Term` with normal entries, the shell invariant is
  generic in the step function, `DataW` needs only the canonical-input step theorems. The
  any-alphabet `Simulation` is now genuinely assembly.
- Ranking: (1) **the general machine**: the step function for an arbitrary `m = 2` rule table over
  `Fin n` (guard and tails unchanged, `RULEf := dispatchT` over the encoded rule outputs), its
  canonical-input suite, and the re-instantiated pipeline through to
  `Simulation (RS.Tag T) RS.SK` for every two-symbol-consuming tag system. (2) rungs 2/3 via
  match-bounds. (3) C6, declined a sixty-fifth time.

## 2026-07-27 — Stage 78: the pipeline, re-run as a function

- The general theorem exists: any deletion-number-2 tag system whose symbols encode normally,
  injectively, decodably, and dispatchably is certifiably hosted inside SK. The proof of that
  sentence is four hundred lines of transcription and zero new ideas — which is the finding. Ten
  stages ago, `bwd` for ONE two-symbol system was open research; today the entire argument re-ran
  against abstract parameters in a single sitting, because every layer had been forced to state its
  actual dependencies: the word toolkit over `List Term`, the shell invariant over an abstract `F`,
  the data layer over an abstract alphabet. Generality was not designed in; it PRECIPITATED from
  honest interfaces.
- Two mechanical notes. First, Stage 71's drift-completion turned out to subsume the literal-input
  step suite entirely — `fwd` completes the word to canonical form and computes there, so the
  general file proves fewer theorems than the two-symbol original needed. Second, Lean's
  section-variable inclusion rules (body-uses need `include`) pushed me to explicit hypothesis
  binders throughout, which reads heavier but made every theorem's true dependencies visible —
  several needed fewer hypotheses than I would have `include`d.
- The instance anchor is the stage's quiet satisfaction: `tagAB` re-derived from the general theorem
  in five lines, every hypothesis discharged by an existing lemma, `rfl` for `hm`, `cases s <;> rfl`
  for the decoder. When the general theorem's interface is right, the motivating instance should
  fall out trivially — and it did.
- Ranking: (1) **the `Fin n` discharge**: symbols as selectors, the dispatcher over an encoded rule
  table, and the interface's four hypotheses from Stage 76–77's lemmas — the take/drop bookkeeping
  connecting `dispatchT_correct`'s pre/post form to table positions is the only real work. That
  yields `Simulation (RS.Tag T) RS.SK` for every 2-tag system over `Fin n`, subsuming all concrete
  universal instances at once. (2) rungs 2/3 via match-bounds. (3) C6, declined a sixty-sixth time.

## 2026-07-27 — Stage 79: bibliography, not mathematics

- `finTagInSK`: every 2-tag system over `Fin n` is certifiably hosted inside SK. The known-universal
  agenda is closed at the mechanism level — any concrete universal table from the literature
  (Cocke–Minsky's constructions, or any later small universal 2-tag system) is an instance of a
  machine-checked theorem, and citing one is bibliography, not mathematics. The stage itself was the
  promised bookkeeping: symbols as selectors with the index arithmetic arranged so the rule table
  reads in natural order, a decoder that counts `K`-wraps (correct on the image, garbage elsewhere,
  and the spec only ever asks about the image), and one take/drop decomposition lemma.
- The build-enforced audit earned its existence ONE STAGE after being built: `finTagInSK` came out
  carrying `Classical.choice`, the `#guard_msgs` pin failed the build, and the bisect found leak
  seven — through a door none of the previous six used. `omega`, aimed at a goal that is not
  arithmetic (an existential, discharged from contradictory hypotheses), routes through
  `Classical.choice`. Every previous leak came through `BEq`-adjacent `simp`; I would not have
  re-audited an `omega` line by habit, and the per-stage habit is exactly what the audit no longer
  relies on. The rule extracted: give `omega` arithmetic goals only; for absurdity with a
  non-arithmetic goal, `absurd` with the named contradiction.
- Seven leaks, seven mechanisms visible in one list now: instance-layer `simp` (×5 variants),
  `grind`, `omega`-exfalso. The trail is starting to look less like carelessness and more like a
  survey of where classical logic hides in a proof assistant's automation — which may be worth a
  paragraph in whatever Goal 4 eventually becomes.
- Ranking: (1) **STATUS and the spec ledger**: the open item's closure is now total (general theorem
  + finite-alphabet instantiation); update the accounting and consider what remains of the program's
  original spec — rungs 2/3 and C6 are the only live items. (2) rungs 2/3 via match-bounds. (3) C6,
  declined a sixty-seventh time.

## 2026-07-27 — Stage 80: the ranking entry that was never a claim

- Thirty-five stages of "rungs 2/3 via match-bounds", and the first session that finally faced it
  found a type error in the first hour: match-bounds certify termination, and both rungs' full
  systems provably have none — C1(a)'s divergent term is K-free and embeds straight into `{S,B}`
  and `{S,C}`. `SB_not_normalizing` and `SC_not_normalizing` are now theorems, the embedding is a
  full bisimulation on the K-free image (backward path lemma axiom-free), and every
  termination-shaped route to the rungs is closed at once.
- The uncomfortable part is WHY the error lived so long: a ranking entry is not a claim. Stage 61
  taught that assumptions survive precisely when they are never written down as claims; Stage 44
  even wrote, correctly, that match-bounds were "a much bigger build" — and still filed them as the
  route, because feasibility got assessed and TYPE-correctness did not. The extracted rule: when a
  route sits in the ranking for more than a few stages, its first session should typecheck the
  route's conclusion against the theorem it is supposed to produce, before any machinery.
- What the rungs' open problem now is, precisely: certify loop-freeness of a non-terminating
  system. Termination tools are unavailable (today's theorems); single monotone measures are
  unavailable (`no_monotone_counting_measure`, Stage 44's `no_decreasing_measure_of_infinite`);
  bounded invariants cannot finish (Stage 44). The live shapes: a TRANSFORMED system whose
  termination is equivalent to cycle-absence — finding the transformation is the research content —
  or an unbounded well-founded measure. Both are genuine research, and the program's honest posture
  is that they may outlive it.
- Ranking: (1) **the transformed-system design probe** for rung 2: one session, on paper first —
  what known loop-freeness transformations exist (unfoldings, semantic labeling, sound-for-loops
  restrictions), and whether the ledger's necessary conditions make any of them finite here. If
  nothing survives the hour, record that and re-rank. (2) C6, declined a sixty-eighth time.

## 2026-07-27 — Stage 81: the probe that found a projection

- The ranked design probe was supposed to survey loop-freeness transformations and report which, if
  any, could be finite here. The survey instead surfaced something better and simpler: a cycle with
  no root step projects to a strictly smaller cycle, so minimal cycles pass through root redexes —
  and both rungs reduce to ruling out root-redex cycles (`sb_acyclic_of_no_root_cycle`,
  `sc_acyclic_of_no_root_cycle`, parity maintained). Every prior condition on rung cycles came from
  measures; this one comes from projection, and the two species now compose at one site: a root
  S-redex whose duplicated argument carries a `B` and is τ-heavy, or a root B-redex, returning to
  themselves.
- The proof is the countdown of proof-shapes this development keeps meeting: a dichotomy lemma
  stated for nonempty paths (the trivial disjunct must be excluded at the STATEMENT, or the main
  induction meets an uninformative case — the same lesson as Stage 69's behaviour-vs-shape, at the
  level of disjunctions), plus strong induction on size. One genuine bug caught by the elaborator:
  prepending a PROJECTED step where the app-level step belonged.
- What the reduction buys, concretely: the root-cycle question is about terms of exactly two shapes,
  and the return path's FIRST obligation is visible — `(f x)(g x)` must rebuild an S-headed
  three-argument spine, `x (y z)` a B-headed one. Head-spine dynamics under root steps are
  trackable; iterating the localization inside the return path may yield "cycles need a root
  S-step" or stronger. That is the next probe, and unlike match-bounds, it typechecks.
- Ranking: (1) **root-cycle head analysis** for rung 2: what must `head(f)` be for `(f x)(g x) ⟶*
  S f g x`, and does iterating localization inside the return path force an infinite regress on
  some rank? (2) C6, declined a sixty-ninth time.

## 2026-07-27 — Stage 82: the return path, interrogated

- Four dichotomy theorems, one sitting, no new machinery: Stage 81's path dichotomy applied to the
  root cycles it isolated. The pattern I want to note is how the stages compose now — 80 typechecked
  the route, 81 built the projection engine, 82 pointed the engine at its own output. Each stage's
  theorem was the previous stage's obvious next question, and none needed more than an afternoon.
  The rungs have gone from "open, with a type-incorrect route" to a two-branch tree whose leaves are
  named phenomena, in three stages.
- The phenomena themselves are worth staring at. Collapse to argument — `u v ⟶* v` — appears in
  both rules' projection branches, so one theorem kills every non-root branch at once. And the rung
  systems are non-erasing in a precise sense: the only leaf a step deletes is the fired combinator
  itself. A collapse must therefore disassemble `u` combinator by combinator while leaving exactly
  `v` — every S-fire pays one S but duplicates an argument, every B-fire pays one B. The accounting
  smells like a weighted-count theorem: something must go negative. That is the next probe, and it
  is the first rung question in thirty stages that looks like it might be an AFTERNOON theorem
  rather than a research program.
- Self-embedding under application (`f x ⟶* S f g`) connects to the Stage 39–42 ground
  self-embedding machinery, whose open-term version the notebook has carried as a live pointer since
  Stage 42. If the collapse branch falls first, this branch dies with it (both projections are
  required jointly), so collapse is strictly the better target.
- Ranking: (1) **no-collapse for the rungs**: prove `¬(u v ⟶* v)` in `{S,B}` and `{S,C}` — try the
  weighted-leaf accounting first (each fire deletes exactly its own leaf; S-fires duplicate), and if
  a measure resists, probe small cases with the census tooling before believing either answer.
  (2) C6, declined a seventieth time.

## 2026-07-28 — Stage 83: the measure a student could check

- Rung 2 is closed. `{S,B}` is acyclic (`SB_acyclic`), and therefore cannot host SK
  (`no_pathEncoding_SK_SB`) — the ladder's first full rung beyond `{S}` and ι, the question open
  since Stage 17, the one five fragment theorems and three census campaigns circled. The proof is
  four lemmas about the right-spine depth plus Stage 81's localization, and the measure is so simple
  it is embarrassing: both rules bury the last argument deeper right, so ρ never decreases; root
  steps raise it strictly; a cycle through a root step (which localization guarantees) is a number
  strictly less than itself.
- I want to dissect the miss honestly, because six stages of serious work aimed at this exact
  theorem and produced fragments. Three causes, compounding. FIRST: every measure hunt searched
  counting measures and their lexicographic stacks, because the impossibility results we kept
  proving were about counting measures — the refutations quietly narrowed the search space in our
  heads to the class they covered. ρ is positional; no theorem in the tree ever excluded it.
  SECOND: bare ρ proves nothing — without strictness on some step of every cycle, weak monotonicity
  is vacuous — so anyone who tried ρ before Stage 81 existed would have discarded it as useless,
  correctly. The proof needed localization FIRST, and localization came from a different question
  (the loop-freeness transformation survey). THIRD: the fragment results kept paying just enough to
  feel like progress along the measure axis, so the axis was never questioned. The lesson, stated
  for reuse: when impossibility results accumulate over a CLASS of tools, write down what is
  OUTSIDE the class — the refutations were a map of where not to dig, and we read them as a map of
  where digging was hard.
- Also recorded with appropriate humility: pure S's C2 (the three-level squeeze, and Waldmann's
  cited external result) plausibly admits the same two-piece proof — ρ is monotone for pure S too.
  I have not re-derived it; the squeeze stands and is not wrong, merely no longer forced. And
  no-collapse — the stage's ranked target — fell out as a corollary (`sb_no_collapse`) without ever
  being attacked.
- Rung 3 inherits a new constraint for free (a cycle needs a right-spine C-step with `y`
  right-shallower than `z`) and does NOT fall to ρ — the ledger's "structurally unlike" was
  precisely right, which is worth a moment of respect for Stage 27's analysis.
- Ranking: (1) **rung 3 via the ρ-lens**: formalize the inherited constraint, then hunt a
  second positional measure for `{S,C}` — the C-rule preserves the MULTISET of right-spine depths
  of arguments in some form; look for the invariant OUTSIDE counting measures this time.
  (2) C6, declined a seventy-first time.

## 2026-07-28 — Stage 84: the fragment the lens allows

- Rung 3 held, as the ledger said it would. The measure hunt is worth recording in full so nobody
  re-runs it: sum-of-right-depths breaks on C (the swapped-out argument loses a right-turn for its
  whole subtree); max-right-nesting breaks on S (the head's contribution can dominate and drop);
  exponential right-weights break both ways. `C` is a genuine permuter, and no function of
  right-position alone is monotone under permutation. The ρ-lens's honest yield is the fragment:
  when C only fires strictly-deepening, both root rules are ρ-strict and Stage 83's argument
  transcribes verbatim — `scTame_acyclic`, hence `scCycle_needs_flat_C`: every cycle fires a
  flattening C. Fourth necessary condition, first positional one.
- A design note that mattered: the tame condition must be LOCAL (on the fired redex's own
  arguments), not global (on the whole term's Δρ) — global fragments do not localize, because an
  appL-step's inner projection can violate a whole-term condition the outer step satisfies. The
  ledger's fragments were all local, and I now understand that as a requirement rather than a
  style.
- The composition of conditions is starting to look like a pincer: cycles need S-steps that
  duplicate C-heavy arguments (τ-family) AND C-steps that flatten the right spine (ρ-family). The
  two families are blind to different steps — τ to position, ρ to weight — and the obvious next
  question is their braid: what does a flattening C do to τ? If flattening is τ-expensive and
  duplication is ρ-expensive, a joint lexicographic measure may close the rung the way ρ alone
  closed rung 2. That is a real candidate, not a hope: both halves are proved, only their
  interaction is unmeasured.
- Ranking: (1) **the τ×ρ braid for rung 3**: compute τ's behavior on flattening C-steps and ρ's on
  C-duplicating S-steps; if either is signed, build the lexicographic composite. (2) C6, declined a
  seventy-second time.

## 2026-07-28 — Stage 85: the braid that wasn't, and the word underneath

- The τ×ρ braid died in the first hour of paper, and this time the failure is witnessed in the
  build: `scHeavy` — sitting in the ledger since Stage 27 as the τ-asymmetry example — is exactly a
  flat, τ-raising C, the step kind cycles need and τ cannot punish; and S-fires always raise ρ, so
  ρ cannot punish the τ-family's heavy steps either. Two families, each blind precisely where the
  other needs eyes. I notice the failure took an hour because both halves were already theorems —
  cheap failure is what the last five stages of infrastructure purchased.
- What the failure exposed is better than what was sought. Writing the two root rules against the
  right-spine sequence: S refines the head and PRESERVES the tail; C REPLACES the tail wholesale —
  both equations are `rfl`. Rung 3's dynamics is a word rewriting system over term-valued letters,
  and every measure attempted so far was a homomorphism from that word structure into ℕ that C's
  tail replacement can defeat. The honest statement of where rung 3 stands: five necessary
  conditions, two impossibility sweeps, and a recorded route (the spine calculus) that is genuine
  open research — the kind that may outlive the program, as Stage 80 said of its predecessors.
- Ranking, with the ladder now honestly parked: (1) **the program review** — STATUS's header still
  says 52 targets and ~344 theorems; it is 70 targets and far more, the four goals have moved
  decisively since the last accounting, and the spec deserves a settled-state pass before any new
  research thread opens. (2) The spine calculus for rung 3, as deliberate long-horizon research.
  (3) C6, declined a seventy-third time.

## 2026-07-28 — Stage 86: the accounting caught up

- A review stage, and overdue: STATUS claimed 52 targets and ~344 theorems while the tree holds 32
  modules and ~700; Goal 2 still said "one instance remains open" eleven stages after the instance
  closed. The stale header is the same failure mode as Stage 80's unexamined ranking entry — a
  summary document is a claim, and claims rot unless something re-checks them. The stage-by-stage
  docs never rotted because every stage rewrites them; STATUS rotted because nothing owned it. I do
  not have a build-enforcement trick for prose, so the compensation is procedural: the review is now
  a rankable item like any other, and it should recur when the ranking empties.
- Reading the whole of STATUS in one sitting after twenty-seven stages of heads-down work was
  itself worth the stage. The shape of the program is: two goals done, one closed, one ongoing by
  design; a ladder with three settled rungs and one honest open problem wearing five constraints;
  and a methodology record whose most transferable artifacts — the audit file, the leak catalogue,
  the estimate-vs-structure ledger — came from failures caught in the act.
- Ranking: (1) **the spine calculus for rung 3**, as deliberate long-horizon research — the only
  live mathematical thread, to be picked up in sittings that can afford dead ends. (2) C6, declined
  a seventy-fourth time — and if the ranking is ever otherwise empty, C6's decline count is itself
  the argument to finally probe it or formally retire it.

## 2026-07-28 — Stage 87: the frozen left

- First sitting of the deliberate long-horizon thread, and it paid immediately — not with a
  measure but with a SHAPE invariant: every `{S,C}` step result is an application, and both root
  rules produce app-headed lefts. I had stared at `(f x)(g x)` and `(x z) y` for five stages
  without noticing they agree on this, because every previous lens asked "what number goes down?"
  rather than "what shape is forced?" The measure sweeps of Stages 84–85 were not wasted — they
  are why I trust that no number works — but the working lesson is that impossibility sweeps over
  a FAMILY of arguments should end with the question "what do the counterexamples all still
  satisfy?"
- The theorem: `sc_no_leaf_self_embed`, `¬(x ⟶* ℓ x)` for any leaf `ℓ` — unconditional, and
  genuinely `{S,C}`-specific, since `B x y z ⟶ x (y z)` exposes leaf lefts and the argument dies
  on `{S,B}` (correctly: rung 2 needed ρ instead). Proof is the path dichotomy: a root step
  freezes the left as an app forever, so the target `ℓ x` is unreachable on that branch; the
  rootless branch forces `x = ℓ x₁` and descends on `leafCount`.
- Two Lean potholes, both now recorded in the commit: anonymous `.app` dot-notation fails wherever
  the expected type is `RS.Carrier ?m` rather than syntactic `SCTerm` (write `SCTerm.app`); and
  `subst hf` with `hf : f = ℓ` eliminated `ℓ` — subst removes the RHS variable — orphaning every
  later `ℓ`. The fix that generalizes: rewrite with the equation instead of substituting when both
  sides are live locals. Also: RS.Steps recursion at a concrete instance with an implication
  motive wants `refine h.rec (motive := ...) ?_ ?_` with tactic holes; `exact` with inline premise
  lambdas leaves the motive metavariable unassigned while the premises elaborate.
- Filed as the spine calculus's first result, not a sixth cycle condition — it kills a family of
  return paths (leaf-over-self embeddings) rather than constraining every cycle. The honest next
  step is to connect it: push `sc_cycle_needs_root`'s case analysis one level deeper at a root-C
  redex and count which branches now die on this theorem.
- Ranking: (1) **the second-level root-cycle analysis for rung 3**: expand the return-path cases
  at a root C-redex and apply the frozen-left theorem to the leaf-headed branches; the deliverable
  is either a sixth necessary condition or a precise inventory of which return shapes remain
  unkilled. (2) C6, declined a seventy-fifth time.

## 2026-07-28 — Stage 88: the second fire

- The fastest stage in weeks, and the reason is worth recording: Stage 87 proved exactly the lemma
  its own analysis predicted would be needed, so this stage was assembly — the second-level
  dichotomy is `sc_path_facts` applied to Stage 82's projection branch, with the two death
  branches dying on size and on the frozen left. Both rules' self-embeddings are instances of one
  shape, `f x ⟶* (ℓ f) g` with `ℓ` a leaf, so one generic helper covers S and C — the first time
  the two rules have shared a lemma since the localization engine.
- The headline: `scCycle_second_redex` — every `{S,C}` cycle produces a root cycle whose return
  path reaches a SECOND root redex, at the root or immediately left of it. Sixth necessary
  condition; first positional one in tree terms. The build went green on the first attempt, which
  I credit to yesterday's potholes being written down: subst directions chosen so the surviving
  names are the lowercase ones, `SCTerm.app` spelled out where the expected type is the carrier,
  and the `refine h.rec (motive := ...) ?_ ?_` idiom for the congruence lift.
- Honesty about what did not close: the regress does not yet iterate. The second root redex is
  REACHED, not shown to cycle, so there is no descent argument — and the surviving branches still
  carry the Stage 82 exotics, `g x ⟶* x` (collapse to argument) and `y ⟶* z`. Collapse is now
  clearly the load-bearing escape: kill it and every root cycle's return must carry a whole-term
  root step, at which point the regress has a real chance of becoming a well-founded descent.
- The methodological note that Stage 87 suggested and this stage confirms: the shape lens ("what
  does every step force?") produced in two stages what five stages of measure hunting could not.
  The right next question is the shape question for collapse: what shape must `u` have for
  `u v ⟶* v` to even begin — and does the frozen left already constrain its first step?
- Ranking: (1) **no-collapse for `{S,C}` via the shape lens**: point the path dichotomy and the
  frozen-left invariant at `u v ⟶* v`; even a conditional kill (leaf-headed `u`, say) would
  narrow the last escape. (2) C6, declined a seventy-sixth time.

## 2026-07-28 — Stage 89: two bites out of collapse

- The shape lens's third stage, and the pattern is now unmistakable: ask what a reduction is
  FORCED to look like, and the path dichotomy plus a size argument does the rest. Collapse
  `u v ⟶* v` resisted the whole measure era (it fell to ρ only for `{S,B}`, where ρ is monotone);
  under the shape lens it yielded two theorems in one sitting: leaf-headed collapse is dead
  (left-leaf rigidity: leaves are normal, so `ℓ v` reaches only `ℓ w` — the collapse target would
  need `v = ℓ w` with `w` collapsing again, and the sizes descend), and every collapse fires a
  root redex from a right-nested subterm (the projection branch of the dichotomy IS a collapse of
  `v` into its own right child — the descent's only exit is the root branch).
- The recursion in `sc_collapse_needs_root` is worth a note: it descends the TARGET's right spine,
  not the source's — each level's collapse is `v = F' X' ⟶* X'`, and the witness `SCRightNested`
  tracks where the firing subterm sits. A new two-constructor inductive was cheaper than any
  encoding via `rightDepthC`; the file's first subterm relation, and it earns its place by making
  the theorem statement honest about WHERE the root fire launches.
- `sc_root_S_return3` composes Stages 88 and 89: a root S-cycle without a whole-term root return
  step now carries root fires in BOTH projections. The C-side has no matching third theorem —
  `y ⟶* z` is not a collapse — and I am deliberately not forcing one; asymmetry between the rules
  is information, not untidiness.
- Next lever, spotted while writing the CONJECTURES entry: `scRootStep_source` (root sources are
  app-app-headed) and `scSteps_from_leafLeft` (leaf-headed terms are left-rigid) together mean a
  LEAF-headed-argument redex's left projection can never reach a root redex — so Stage 88's
  second-level sandwich is absurd there, and leaf-`f` root S-cycles / leaf-`x` root C-cycles must
  return through a whole-term root step. That is a one-sitting corollary and it prunes the cycle
  space at its smallest instances, exactly where a census would start.
- Ranking: (1) **the leaf-argument corollaries**: close the projection escape for root cycles
  whose head argument is a leaf, then inventory what shapes of root cycle remain unkilled — the
  deliverable is the sharpest statement yet of what a rung-3 cycle must look like. (2) C6,
  declined a seventy-seventh time.

## 2026-07-28 — Stage 90: the anatomy, assembled from parts already on the bench

- The shortest stage of the arc — every lemma was one composition of Stage 88's and Stage 89's
  parts, and the build went green on the first attempt with nothing but `rcases`, `.elim`, and
  constructor applications. The contradiction (root sources are app-app-headed; leaf-headed terms
  are left-rigid) had been sitting in the file for a day, each half proved for a different
  purpose. I found it while writing prose, not while proving — the CONJECTURES entry for Stage 89
  ended with a sentence that was, on inspection, a theorem statement. Writing the notebook is not
  overhead; it is where compositions get noticed.
- The anatomies are the sharpest frontier statements rung 3 has had: leaf-headed-argument root
  cycles must return through whole-term root steps, and the general dichotomy is rotate-or-descend
  — a whole-term root fire on the return (which closes a cycle through that fire: rotation at the
  same size), or an app-headed head argument with projections firing on strictly smaller terms
  (descent, but onto fires not yet known to cycle). Neither branch alone is a contradiction; the
  open question is whether anything survives both riders indefinitely.
- Notable non-move: I did not try to prove the rotation lemma this stage (SCRootStep → SCStep and
  the cycle re-basing are both trivial), because the stage was already a complete thought. The
  discipline of one idea per stage has paid for itself every time the notebook needed to explain
  why a proof exists.
- Ranking: (1) **formalize the rotation**: SCRootStep is a step; a root cycle's return-path root
  fire closes a root cycle of its own; then state the ROTATE-OR-DESCEND dichotomy as a single
  theorem on root cycles — the branch tree becomes an honest coinductive-flavored invariant, and
  whether it can be driven to a contradiction (or to a minimal-cycle normal form) is the next
  genuine research question. (2) C6, declined a seventy-eighth time.

## 2026-07-28 — Stage 91: the dichotomy, stated once

- An assembly stage by design: the rotation lemma deliberately deferred from Stage 90 was indeed
  three combinators of glue (`trans`, `tail`, and root-steps-are-steps). The surprise was in the
  descent half — writing the uniform statement forced me to see that both rules' left projections
  are the SAME projection, `app h r ⟶* (t's left)` with `h` the head argument and `r` the last:
  the per-rule anatomies had been hiding a symmetry. This keeps happening: the theorem improves
  while being restated, which is an argument for restating theorems.
- Green on first build again — four stages running. The shape-lens arc (87–91) has now gone from
  "no {S,C} term reduces to itself under a leaf" to "every cycle carries a root cycle that rotates
  or descends" in five sittings, each stage one composition ahead of the last. Contrast the
  measure era, where five sittings bought two impossibility sweeps. When the objects force shapes,
  follow shapes.
- What the invariant is missing, stated honestly: a reason rotation cannot recur forever. On a
  finite cycle there are finitely many root fires and rotation just walks them, but `RS.Steps` is
  Prop-level and lengthless, so even "a cycle has finitely many fires" is unstatable. The natural
  infrastructure is length-indexed paths — `StepsN n`, minimal cycles, rotation as a
  length-preserving basepoint shift. That is real machinery (new induction principles, a
  Prop-to-data bridge), and it should be built as its own stage rather than smuggled in.
- Ranking: (1) **length-indexed paths**: define `StepsN`, prove the equivalence with `Steps`,
  and restate rotation as basepoint shift on a minimal-length cycle — the deliverable is the
  well-foundedness scaffold, not yet the theorem. (2) The third-level shape analysis (what a root
  redex reachable from `app h r`, `h` an application, forces) — the alternative continuation if
  the scaffold stalls. (3) C6, declined a seventy-ninth time.

## 2026-07-28 — Stage 92: infrastructure, built when the theorem asked for it

- The program's rewriting layer has carried eleven acyclicity results without ever knowing how
  long a path is. That was the right YAGNI for thirty stages — and Stage 91's closing sentence is
  what finally made lengths load-bearing: "finitely many rotations" is a cardinality claim, and
  Prop-level `Steps` cannot host it. Building `StepsN` cost one sitting; building it at Stage 60
  "for later" would have been dead weight through the entire tag arc.
- The descent engine's design is the stage's real content: `no_cycle_of_descent` never chooses a
  minimal cycle. The naive formalization ("take a minimal counterexample") needs `Nat.find`, which
  needs decidability the infinite carrier cannot give, or classical choice the program bans. The
  bounded-induction form — descend from the given cycle's own length, carrying `n ≤ bound` — needs
  neither, and its proof is six lines. The choice-free discipline keeps producing better proofs
  than the classical instinct would have: this is the third time a banned shortcut forced a
  cleaner argument (leak #5's hand-supplied literals, the anatomy's rw-not-subst, now this).
- `scRootCycle_rotate_same_length` is the conservation law the scaffold exists for: rotation
  spends no length. Combined with the engine, the strategic map of rung 3 is now one sentence —
  find any cycle surgery that strictly shortens, and the rung closes. The descend branch's fires
  are on strictly smaller TERMS; what is missing is that they belong to CYCLES. The gap between
  "fires" and "cycles" is the precise residue of the problem.
- One pothole, now familiar in a new costume: `StepsN` constructors at a concrete instance need
  `@RS.StepsN.refl RS.SC` — the same explicit-instance idiom as `RS.Steps.refl` since Stage 81.
  Recorded here so the next indexed family doesn't cost a build cycle.
- Ranking: (1) **the fires-to-cycles gap**: probe whether the descend branch's root fire, on a
  minimal-length cycle, can be forced to recur — the rotation conservation law plus minimality
  should constrain where the fired term can go; even a partial result (the fire's target cannot
  rejoin the cycle above a certain position) would be the first strict-shortening surgery.
  (2) The third-level shape analysis of `app h r` reachability, as the fallback. (3) C6, declined
  an eightieth time.

## 2026-07-28 — Stage 93: the first purchase, and the eighth leak

- The scaffold paid for itself one stage after it was built: redoing the dichotomy and
  localization with lengths was mechanical (the proofs mirror Stages 81's, plus omega on the
  sums), and the corollary is the wlog the descent hunt needed — minimal cycles ARE root cycles,
  exactly, because localization's accounting is conservative: sandwich steps sum to n, projection
  components sum to n, nothing is ever discarded. The atlas also gains its first numeric tooth:
  no self-loop steps, so minimal cycles have length ≥ 2.
- The eighth Classical.choice leak, caught by the per-stage audit, is the seventh's mechanism
  verbatim: omega closing a non-arithmetic goal — this time the localization's existential in the
  contradictory n = 0 branch. Two occurrences make a pattern: the danger zone is precisely the
  CONTRADICTORY-HYPOTHESIS BRANCH, where the goal is whatever the theorem concludes and omega
  seems like the natural closer because the hypotheses are arithmetic. The clean form is subst +
  absurd + a targeted Nat lemma. Recorded in CONJECTURES so the next branch reaches for absurd
  first.
- Two mkElimApp reminders in one stage: cases on `StepsN 1 t t` dies on the REPEATED index (not
  the literal — literals unify fine); the fix is the same as ever — state inversions with
  distinct index variables (`stepsN_zero_eq`, `stepsN_one_step`, now generic in RS) and compose.
- Where the hunt stands: every tool since Stage 81 now composes on one object, the minimal root
  cycle — rotate-or-descend, both anatomies, rotation's conservation law, length ≥ 2. The rung
  closes if a minimal root cycle can be forced to yield any strictly shorter cycle. The descend
  branch hands us root fires on strictly smaller TERMS; the missing move is a surgery that turns
  one into a shorter CYCLE — or shows the descend branch incompatible with minimality outright.
- Ranking: (1) **descend vs minimality**: on a minimal root cycle, work the descend branch's data
  (app-headed head argument, left projection firing on a smaller term, the C-side's y ⟶* z)
  against exact-length localization — the target is either a shorter cycle from the projection
  fires or a shape contradiction. (2) The third-level shape analysis of `app h r` reachability.
  (3) C6, declined an eighty-first time.

## 2026-07-28 — Stage 94: the case blast that stayed civilized

- The first kill from descend-vs-minimality, and a validation of the whole stack in miniature:
  localization-with-lengths reduced "no 2-cycles" to "a root fire is never undone in one step,"
  and the frozen left — proved two stages before there was any sign it would be needed at length
  one — closed the only branch that size arguments could not. Eleven branches total, and the
  discipline that kept them civilized was converting everything to equations first
  (`scRootStep_inv` as the equational mirror of `SCRootStep`): no `cases` on
  concretely-indexed hypotheses, hence no dependent-elimination surprises, just injections and
  two named absorption lemmas.
- Honest assessment of the numeric ladder: length ≥ 3 is a real pinned fact, but climbing it
  rung by rung (kill 3-cycles, kill 4-cycles, ...) costs multiplicatively more per step and
  proves nothing in the limit. The 2-cycle proof's transferable content is the CONSTRAINT ON THE
  RETURN'S FIRST STEP: immediately after a root fire, the term's shape pins what any single step
  can do, and most possibilities are absorption-dead. The general statement — the return
  dichotomies with lengths, giving exact budgets on a minimal root cycle — is mechanical from
  Stage 93's pattern and turns any future k-cycle question into arithmetic over branch budgets
  instead of a bespoke blast.
- Four bookkeeping errors in the first build of the big proof, all of one kind: rewrite
  directions (`←` renaming the wrong variable, absorb lemmas fed mirror-image equations). The
  fix pattern is now reflexive: read the error's stated type, not the plan's intended one.
- Ranking: (1) **the length-indexed return dichotomies**: sc_root_S/C_return2 in StepsN form
  with exact budget accounting (k_L + k_R = return length, sandwich positions), stated on a
  minimal root cycle — the general form of the 2-cycle proof's constraint. (2) The 3-cycle kill
  as a corollary test of that machinery. (3) C6, declined an eighty-second time.

## 2026-07-28 — Stage 95: the price of collapse

- The plan was mechanical (dichotomies with lengths); the discovery was not: writing the S-side
  side-condition forced the question "can a single step collapse `u v` to `v`?", and the answer is
  an unconditional no with a four-line induction — the appR case IS the same question one size
  smaller, which is as clean as size induction ever gets. Stage 82 called collapse exotic, Stage
  89 proved it fires a root redex, and now it has a price: two steps minimum. Every one of these
  came from asking what a single step is FORCED to look like.
- The budget bookkeeping surfaced the S/C asymmetry a third time, and this time with teeth: the
  S-side return must pay 1 (self-embedding) + 2 (collapse) in its projection branch, so rootless
  S-returns cost ≥ 3 and S-rooted short cycles need second fires; the C-side's `y ⟶* z` can be
  FREE (y = z), so C-rooted cycles are where any short cycle must live. The rung's hard core keeps
  contracting toward the C rule's permutation behavior — consistent with the ledger's original
  "structurally unlike" verdict and with every measure failure since.
- First-try green again, and the equations-first discipline from Stage 94 deserves the credit:
  both dichotomies are rcases + injections + two absorption calls, no dependent elimination
  anywhere. The `subst` pattern (eliminate the capital-letter existential witnesses, keep the
  concrete shapes) has not produced a single orphaned-variable error since Stage 87 wrote the
  rule down.
- Ranking: (1) **the 3-cycle question**: the budgets have cornered it — S-rooted needs a sandwich
  (two fires in three steps, budget k₁ + 1 + k₂ = 2), C-rooted a projection with kL + kR = 2;
  both are finite shape analyses of the Stage 94 kind, and the outcome is either no-3-cycles
  (minimal length ≥ 4) or an explicit near-cycle shape worth staring at. (2) The minimal-cycle
  synthesis: compose every constraint since Stage 81 into one characterization theorem of the
  minimal cycle. (3) C6, declined an eighty-third time.

## 2026-07-28 — Stage 96: the day the hunt turned out to be a search

- I set out to kill 3-cycles and instead FOUND one. The moment worth recording precisely: working
  Stage 95's surviving branch (S-rooted, two fires, budgets 0+1+1) through the injections on
  paper, each equation ate a degree of freedom — g = C, f = C h, x = h, h = C S C — until nothing
  was free, and the remaining question was not "is this impossible?" but "is this term a cycle?"
  A ten-line Python check said yes before any Lean was written. With h = C S C:
  S (C h) C h → C h h (C h) → h (C h) h → S (C h) C h. Nine leaves. The census had stopped at six.
- Rung 3 is CYCLIC, the ladder is finished, and sixteen stages of impossibility work read
  differently in hindsight: they were a SEARCH PROCEDURE. The measures that failed, the fragments
  that were acyclic, the six necessary conditions — each narrowed the address of a cycle that was
  always there. The budgets of Stage 95 were the final constraint: they specified the witness up
  to unification. I do not think I could have found this term by staring; the impossibility
  scaffolding found it by making every wrong shape provably wrong.
- Two disciplines earned this: (1) verify-before-formalize — the Python check cost a minute and
  meant the Lean was transcription, three constructor applications, axiom-free; (2) the arc's
  insistence on EXACT budgets (k₁ + 1 + k₂ = n, not ≤) — with slack inequalities the branch
  would have stayed a fog instead of collapsing to one assignment.
- Humility entries: the ledger's "structurally unlike rung 2" was righter than intended — not
  just a different proof, an OPPOSITE verdict. And Stage 84's "the C rule is a genuine permuter,
  no function of right-position alone is monotone" was the cycle speaking: flat C-fires are
  where it lives, and both of the witness's C-fires are flat. The conjecture implicit in the hunt
  (rung 3 acyclic like rung 2) was WRONG, and every theorem proved along the way is still true —
  the program's method (prove conditions, not conclusions) is what let the wrong conjecture die
  cheaply.
- What remains: whether {S,C} hosts SK is now open in the other direction — cyclicity removes
  the refutation mechanism, making {S,C} a candidate host like rung 1's {S,I}. The spine
  calculus closes as a success: its theorems cornered the witness.
- Ranking: (1) **the program review**: rung 3's closure changes STATUS's ladder summary, the
  spec's open-problems list, and the headline sentence's supporting cast; the review is overdue
  the moment a goal-level result lands. (2) **{S,C} as host**: probe whether the rung-1 upward-
  closure argument (a definable I inherits cycles) has an analogue — does {S,C} define an
  I-like combinator, and does SK path-encode into {S,C}? (3) C6, declined an eighty-fourth time.

## 2026-07-28 — Stage 97: the accounting after the summit

- Stage 86 made the review a rankable item that recurs when the ranking empties; Stage 96 taught
  the better trigger: review WHENEVER A GOAL-LEVEL RESULT LANDS, because that is when summary
  documents rot fastest. Eleven stages of shape-lens work read very differently before and after
  the witness — what was "the frontier of an acyclicity proof" is now "the description of a cycle
  space" — and every STATUS paragraph written in the former voice needed the latter.
- The numbers: ~770 theorems (up 70 since Stage 86), 35 pinned footprints (up 19 — the shape-lens
  arc pinned nearly every stage headline), ~15,200 lines. The arc's cost profile is worth
  recording: eleven stages, ten of them one-sitting, most first-try green. The measure era
  averaged more failures per result; the difference was working IN the object language (shapes,
  budgets) instead of ABOVE it (measures, homomorphisms).
- The procedural yield of the whole rung-3 story, now in STATUS as step 4′: exact accounting
  turns impossibility machinery into a search procedure. Bounds (`≤`) keep branches foggy;
  budgets (`=`) collapse them to assignments that are either contradictory or inhabited. I
  suspect this generalizes well beyond this program.
- What the completion opens: {S,C} and {S,I} both sit outside the refutation mechanism's reach
  with no positive certification either — candidate hosts. The natural probe order for {S,C}:
  (a) is an I-like combinator definable (the {S,B} analogue was censused to 7 leaves and found
  empty — but {S,C} permutes, so intuition transfers poorly); (b) if yes, rung 1's upward-closure
  machinery (`siInSK`-style) gives {S,I} ⊆ {S,C} and the host question inherits structure.
  Separately, the witness suggests a uniqueness question: the budgets forced ONE assignment for
  S-rooted 3-cycles — is the witness the unique minimal cycle up to basepoint? That would be the
  first CLASSIFICATION theorem of a cycle space in the program.
- Ranking: (1) **I-definability in {S,C}**: bounded search for `t` with `t x ⟶* x` on a fresh
  variable (TermV machinery exists), then either the upward-closure transport or a no-I census
  with the {S,B} tooling. (2) **3-cycle uniqueness**: classify all root 3-cycles via the Stage 95
  budgets — the S-rooted case is one unification from done; the C-rooted case needs its own
  blast. (3) C6, declined an eighty-fifth time.

## 2026-07-28 — Stage 98: the search that never needed to run

- The ranking said "bounded search with the TermV machinery"; the stage took twenty minutes and
  ran no search. Writing down what the search would look for — `t S ⟶* S` as the easiest
  instance — collided immediately with `sc_steps_to_leaf`: nonempty paths end at applications.
  The {S,B} mirror lemmas took ten lines. This is the second time (after Stage 96) that
  formulating the probe precisely dissolved it; the lesson compounds: BEFORE building search
  tooling, state the exact sentence the search would decide, and check it against the standing
  shape lemmas.
- A small embarrassment worth recording: `{S,B}`'s "no I-like up to 7 leaves" has sat in STATUS
  since the rung-2 era as a census result, and the unconditional theorem was derivable from
  "step results are apps" the whole time — a one-line composition nobody wrote because the
  census had already "answered" the question. Bounded evidence anesthetizes: it makes the
  unconditional question feel closed when it is merely quiet.
- The structural content: PROJECTION is the dividing line. `K` and `I` can hand back a bare
  argument; `B` and `C` cannot — every `{S,B}`/`{S,C}` step result is an application. That one
  bit separates the bases where define-I transport works ({S,I} ⊆ SK) from those where it is
  now provably closed, and it reframes the hosting question: an SK-Simulation into `{S,C}` must
  encode K's erasure without ever producing a leaf, which is possible in principle (encodings
  land on apps) but means the erasing structure must live entirely inside the encoding's shape.
- Ranking: (1) **3-cycle uniqueness**: classify all root 3-cycles via the Stage 95 budgets — the
  S-rooted case collapsed to one assignment in Stage 96's derivation; formalizing that
  classification (every S-rooted 3-cycle IS the witness family) would be the program's first
  cycle-space classification theorem, and the C-rooted case completes it. (2) **SK-into-{S,C}
  hosting**: scope what a Simulation would need (K-erasure inside app-shaped encodings) and
  probe the smallest obstruction. (3) C6, declined an eighty-sixth time.

## 2026-07-28 — Stage 99: the other answer the budgets allowed

- Stage 95's budget theorem said short cycles are C-rooted or carry second fires — an OR, and I
  read it as rhetoric when it was inventory. The h-cycle inhabits the second-fires disjunct; the
  w-cycle, found today by finishing the case tree, inhabits the C-rooted one. Two disjuncts, two
  cycles. The lesson from Stage 96 sharpens: when exact constraints leave a branch standing,
  INSTANTIATE IT — and when a dichotomy's both sides survive, expect both to be inhabited.
- The w-cycle is prettier than the h-cycle in one respect: it is C-rooted with a single root
  fire, so its return path is pure projection — the whole cycle lives in the left component's
  two-step self-embedding `w w w ⟶ C C w (w w) ⟶ C (w w) w`, lifted under appL. `w = S (C C)`
  is the {S,C} cousin of the Ω-style self-application seeds that power every cycle this program
  has met: rung 1's Ω_SI, SK's Ω, now w w.
- The reusable yield: `sc_no_step_right_embed` — no single step maps a term into a term that
  right-nests it. Every wrap kill in the ~40-case tree was an instance; the proof is four cases,
  three dead on the nesting size bound, one recursing. `SCRightNested` (built in Stage 89 for
  collapse) earned a second job. The multi-step version is NOT provable — the w-cycle itself has
  `w w w ⟶2 C (w w) w`... which does not right-embed; the honest open question is whether
  multi-step right-self-embedding `t ⟶+ u t`-style is possible at all in {S,C}; the frozen left
  says no when the head is a leaf. Unranked for now; noted.
- Formalizing the full classification is specified and bounded (equations-first, ~40 branches,
  every kill now a named lemma), but the two witnesses already carry every downstream claim. It
  goes to the ledger as a conjecture with materiality honestly marked — the right call is to not
  spend a stage on it unless a downstream result needs the completeness.
- Ranking: (1) **SK-into-{S,C} hosting, scoped**: with the ladder settled and both transport
  routes closed, the honest next question is what a positive certificate would need — K-erasure
  inside app-shaped encodings; the countdown machine's Simulation template and the tag pipeline
  are the tools; the first deliverable is the obstruction analysis, not the construction.
  (2) The 3-cycle classification blast, if completeness becomes load-bearing. (3) C6, declined
  an eighty-seventh time.

## 2026-07-28 — Stage 100: the asymmetry, made formal

- A century of stages. The hosting scope turned out to have a formalizable half: `{S,C} ≤ SK` fell
  in a sitting because three old investments composed on contact — the bracket toolkit gave
  `cImpl` and its β-lemma for free, `siInSK` gave the injectivity technique (its `ne_K` trick
  needed only `cImpl_shape`, which is `rfl`), and the RS bridge lemmas did the rest. The whole
  embedding is ~90 lines, and the collision cascade that looked like the risky part stopped at
  depth one because `cImpl`'s right component happens to be K-headed. I checked that shape by
  `#eval` before writing a line — verify-before-formalize again.
- The obstruction analysis (ledger) ends in an inversion worth remembering: the tag pipeline's
  `bwd` problem was a host that computes TOO MUCH (the driver runs past the source's halt); an
  SK-into-{S,C} certificate faces a host that cannot FORGET — K's erasure must become garbage
  parked inside app-shaped encodings forever. The two hard problems of this program are dual, and
  the parking version has no template yet. Also recorded: nothing in the inventory transports as
  a refutation invariant, so the question is genuinely open in both directions — the honest state
  is "no tool," not "no answer yet with known tools."
- `sc_cycle_pump` is three lines and axiom-free, and it preempts a whole family of tempting
  finite-counting arguments. Cheap prophylaxis against future wrong rankings.
- Ranking: (1) **the classification blast** (every root 3-cycle is a rotation of the h- or
  w-cycle) — now the only specified-and-bounded item left on rung 3, and the completeness would
  make the cycle-space description exact; take it if a full sitting is available. (2) **garbage
  parking**: sketch what a K-erasure encoding into a non-erasing host would even look like on the
  two-cell tag alphabet — a design probe, not a construction. (3) C6, declined an
  eighty-eighth time.

## 2026-07-28 — Stage 101: forty-five branches, one afternoon

- The blast the ledger priced at "Stage 94 × 4" came in on budget, and the pricing held because
  the method scaled: equations first, then a UNIFORM kill. The discovery of the stage is that
  uniformity: converting every injected equation to a linear leaf-count fact and letting omega
  combine them removes the single largest error source of Stage 94 (rewrite-direction judgment).
  My first draft guessed directions and produced four errors in three branches; the second draft
  had two errors across forty-five, both mine (a mis-derived kill, two forgotten sub-branches),
  neither directional.
- The classification confirms the search was complete: the case tree's three survivors are
  exactly the two cycles Stages 96 and 99 found by instantiating surviving branches — nothing
  else was hiding. The w-cycle appearing TWICE in the tree (once per placement of its double
  fire) is the sandwich decomposition's non-uniqueness made visible, and both branches converge
  on the same pair, as they must.
- The ninth leak is the most instructive since the sixth: omega on `_ ∧ _ ∨ _ ∧ _` goals uses
  choice; on `_ ∨ _` goals it does not. I would not have predicted the boundary, and I did not
  try — a three-line experiment answered it before the fix. The leak catalogue now has three
  omega variants, all of one family: GIVE OMEGA ATOMIC ARITHMETIC GOALS — equalities,
  inequalities, negations thereof, plain disjunctions at most — and derive structure yourself.
- Where this leaves rung 3's cycle space: minimal length exactly 3; the length-3 stratum is
  EXACTLY two cycles; length 4 is unexplored (the budgets make it a bounded analysis of the same
  kind, roughly 3× this stage's tree — possible but not obviously worth a stage); the general
  stratification is genuine research. The hosting question (Stage 100's scope) remains the
  program's live frontier.
- Ranking: (1) **the garbage-parking design probe** (Stage 100's deferred second item): sketch
  K-erasure into a non-erasing host on the two-cell tag alphabet — the deliverable is a design
  document in the ledger, not code. (2) The 4-cycle stratum, only if the parking probe stalls.
  (3) C6, declined an eighty-ninth time.

## 2026-07-28 — Stage 102: good garbage is bad data

- A design stage that produced a theorem anyway: writing "the host cannot lose arbitrary
  material" as the impossibility half, I went to check it against the C-rule and found the
  opposite — C-fires consume their own leaf, towers chain the fires, and `cTower_shreds` is a
  five-line induction. The probe's most useful output is that the OBVIOUS refutation of hosting
  is false, formally, axiom-free. Fourth stage running where stating the argument precisely
  flipped or dissolved it.
- The design tensions that survive are worth their names. GOOD GARBAGE IS BAD DATA: volatility is
  exactly what garbage wants and storage cannot tolerate; a construction must convert one to the
  other at the K-fire boundary and nowhere else. And the CIRCULARITY: routing arbitrary structure
  into shreddable shape is itself computation, performed without erasure, on data the host may
  not even be able to pair-project. That last clause is the pairing question — named in the
  ledger as the next probe, and it feels decidable with the TermV machinery: either exhibit
  `pair` in `{S,C}` or prove the head-variable poverty forbids it.
- The λI literature (Church's original calculus, Kleene's λI-definability) is the right prior
  art to consult before attacking pairing: λI-definability of recursive functions uses garbage
  absorption tricks whose DIRECTED (reduction, not conversion) versions are exactly what hosting
  needs. Recorded as a prior-art obligation, cited-not-checked as always.
- Ranking: (1) **the pairing probe**: is `pair a b s ⟶* s a b` definable in `{S,C}`? Either a
  construction (bracket-style, if the fragment permits) or an impossibility via head-variable
  analysis — both outcomes advance hosting decisively. (2) The 4-cycle stratum, still parked.
  (3) C6, declined a ninetieth time.

## 2026-07-28 — Stage 103: rotation yes, selection no

- The probe promised "either a construction or an impossibility" and delivered both, at different
  arities. The one-application selector died in three lemmas — fire results have two spine
  arguments, full stop — while the two-application form turned out to have a witness with the
  arguments ROTATED: C C u v w ⟶* v w u, found on paper by chasing the forced final fires
  backwards. The search then confirmed nothing fixes the arrival order up to 9 machine leaves.
  Pairing in {S,C} is real but rotated; selection is not real at all.
- A humility entry: my first genealogy 'proof' that arrival-order pairing is impossible missed a
  predecessor family (fires with compound first arguments creating leaf-left apps) and collapsed
  on inspection. The corrected tree branches, and I am not close to an invariant that prunes it.
  Recorded as a conjecture with the census bound, not a theorem — the Stage 98 lesson about
  bounded evidence anesthetizing cuts both ways: neither over-claim the search nor under-claim
  the two theorems that did close.
- SCV earned its place: the pairing question is not statable over closed terms (closed 'atoms'
  can fire), and the variables-carrier made both theorems three-liners. RS.steps_last (peel the
  LAST step, dual to head_of_ne) is the reusable yield — the mkElimApp pothole's generic fix for
  target-shaped, rather than source-shaped, arguments.
- Ranking: (1) **rotation-discipline data design**: can the tag pipeline's word encoding be
  rebuilt with rotation protocols — mkWord-style data where every consumer arrives in the middle
  slot? A paper design first; if it closes, {S,C} hosting gets its data layer and the program's
  hardest open question gets a real attack. (2) The arrival-order impossibility, if the design
  stalls and the invariant matures. (3) C6, declined a ninety-first time.

## 2026-07-28 — Stage 104: the branch that parks instead of erasing

- The crux fell in one sitting because two prior results composed AGAIN: Stage 103's rotator IS
  the second tag's dispatch (same theorem, new reading), and Stage 102's shredder is what makes
  the parked arm tolerable. I went looking for a data-layer design and found that the pieces had
  already been proved under other names — the third time this arc has re-read an existing
  theorem as a new capability. The design method that keeps working: name the capability the
  design needs, then grep the theorem list before proving anything.
- The dispatch protocol's uniformity matters more than it looks: both tags consume exactly three
  arguments, so a word cell can apply WHATEVER tag it holds without knowing it — no meta-level
  case split, which is what would have smuggled selection back in. And both tags are normal, so
  words built from them are stable data — the good-garbage-is-bad-data tension from Stage 102 is
  resolved by having the TAGS be data and the ARMS be garbage-handlers.
- Honest inventory of what is NOT done: word chaining, driver recursion without K-based selfRep,
  and the garbage-slot obligations. The last is the likeliest failure point — parking an arm as
  an argument is easy; guaranteeing the parked arm's REDUCTION back to the slot constant, from
  the position it lands in, is the engineering. But for the first time the hosting question has
  a constructive attack with no identified obstruction, which is a different epistemic state
  than any earlier stage of this thread.
- Ranking: (1) **word chaining**: build two-symbol {S,C} words from the tags and prove the
  traversal step — one cell consumed, driver re-applied to the rest — the mkWord/STEPc analogue
  under rotation discipline; the deliverable is `scWord` + a one-step traversal theorem, or the
  named obstruction. (2) The arrival-order pairing impossibility (parked). (3) C6, declined a
  ninety-second time.

## 2026-07-28 — Stage 105: the gadget that dissolved

- The planned route failed and the failure pointed at the fix. The 4-ary cell gadget (store rest
  in a wrapper, permute it behind the interrogation arms) is census-dead to 9 leaves — the same
  early-behind-late resistance the pairing probe hit. The fix was to stop fighting the calculus:
  don't STORE rest behind anything; let it sit where tags naturally put their continuation (first
  argument position, right-nested), and read the tags' own fire patterns as the protocol. C
  applied to rest recurses; C C applied to rest dispatches. The calculus had a word discipline
  built in; the design work was noticing it.
- Swap parity as symbol selection is the part I would not have designed on purpose: a-cells swap
  the arms, so WHICH arm a b-cell fires depends on the parity of preceding a's — and encoding
  σ₂ as the two-cell block `ab` makes every block self-normalizing (each block contains exactly
  the swaps it needs). The asymmetry that looked like a defect of the a-cell is the selection
  mechanism.
- Four of five skeleton pieces are now theorems, all axiom-free, in one arc week. The driver
  remains, and it is the genuinely hard piece: the arms must contain the traversal machinery
  itself, which means self-duplication (S is the only copier, and it copies THIRD arguments —
  the driver must arrange itself as something's third argument to reproduce). The tag pipeline
  solved the analogous problem with fixpoint-free selfRep built on bracket abstraction, which
  used K; the {S,C} version has no template. That is the next real research obligation.
- Ranking: (1) **the driver probe**: can an {S,C} term self-reproduce under application —
  find D, u with D u ⟶* something containing D u (or the precise self-application shape the
  traversal needs)? The cycle witnesses (w w prefixes) are the natural seeds. Deliverable:
  the reproduction gadget or the named obstruction. (2) The arrival-order pairing impossibility
  (parked). (3) C6, declined a ninety-third time.

## 2026-07-28 — Stage 106: the parked arm was never garbage

- The probe aimed at self-reproduction and hit something better first: the dispatch protocol's
  'parked' argument lands in exactly the position the re-launcher needs filled. I had been
  carrying 'park the untaken arm, shred it later' as a design liability since Stage 102 — the
  garbage-slot invariant was the named likeliest failure point — and it evaporated: the untaken
  arm is the next step's first arm. The lesson mirrors Stage 105's: the calculus keeps having the
  discipline built in, and the design work is reading the fire patterns as intent instead of
  fighting them.
- scArm P = C (C C P) is seven leaves and does three jobs: it is normal data, it absorbs the
  dispatch's two arguments as its own missing slots, and it rotates the arm pair. The traversal
  invariant is now visibly a QUEUE: arms (β₁, β₂) → (β₂, P) — the parked arm waits one turn,
  every payload serves once. Unbounded traversal = an unbounded payload supply — the whole driver
  problem is now one question: can a payload rebuild itself under S-duplication with the junk
  arities absorbed?
- Formal note: every theorem this stage is a composition of C_red constructors and two prior
  theorems — zero new case analysis, zero build failures, all axiom-free. Five stages of
  shape-lens infrastructure have made new capabilities nearly free; this is what a mature toolkit
  feels like.
- Ranking: (1) **payload regeneration**: design the pack q and the S-fire plumbing so a payload
  installs a copy of itself (protocol: absorb the forced extra applications — arity design
  against the no-I constraint); deliverable is the regenerating payload theorem or the named
  obstruction — if it closes, unbounded traversal follows immediately. (2) The arrival-order
  pairing impossibility (parked). (3) C6, declined a ninety-fourth time.

## 2026-07-28 — Stage 107: the cycle engine was the duplicator

- The gap closed with a five-leaf term, and the term is the second 3-cycle's seed applied to the
  tag: scDup = w (C C), w = S (C C). I found it by search after the reframe (copy the PARKED arm,
  not yourself), and only recognized it afterwards. The w-cycle's self-application engine and the
  traversal driver's duplicator are the same machine one argument apart — the cleanest instance
  yet of this program's oldest intuition, that cycles and computational power are the same
  phenomenon seen from two sides.
- The reframe is the transferable lesson: self-reference dissolved the moment the requirement
  moved from 'the arm must reproduce itself' to 'the queue must reproduce its population.' Queue
  invariants are weaker than pointwise invariants, and weaker was enough. Stage 106's recycling
  already had the queue shape; today just noticed a queue of IDENTICAL members needs no lineage.
- The whole Stage 102-107 stack — shredder to PathEncoding — is axiom-free. Six stages from
  'can {S,C} erase at all?' to 'here is a machine running inside it,' every step a pure
  construction. tailInSC flips the taxonomy: rung 3 has a POSITIVE hosting entry, something no
  cyclic rung had before.
- Honest scope: the tail machine is trivial, and the equal-arms trick bought regeneration by
  spending the symbol distinction. The word still ENCODES symbols (the cells differ); the arms
  just respond identically. Differentiated regenerating arms — the queue preserving two distinct
  identities while duplicating only the parked member — is exactly what a tag simulation needs
  and exactly what the equal-arms trick cannot give. Either the (A,B)-queue has its own five-leaf
  miracle, or there is an invariant (all sustainable queues are eventually constant?) that would
  be the sharpest negative result of the thread. Both directions are concrete.
- Ranking: (1) **the differentiated queue**: search/design for arm pairs (A, B), A ≠ B, whose
  traversal step preserves both identities — the deliverable is the pair or the eventual-
  constancy conjecture with evidence. (2) The program review — Stage 107 is a goal-level result
  (first rung-3 hosting certificate) and the review rule triggers. (3) C6, declined a
  ninety-fifth time.

## 2026-07-28 — Stage 108: stop solving the hard version

- The catalyst search came back empty to 9 leaves, and the homogenization argument says arm-level
  differentiation is a quine problem — the third time this thread has walked into that wall
  (selector, arrival-order pair, now catalysts). The productive move was noticing the wall is
  load-bearing only if differentiation must happen at RUNTIME. It does not: the word is built by
  `enc`, `enc` knows each symbol, and a cell can carry its symbol's production as a literal.
  Encoding-time information is free; I keep forgetting that because the SK pipeline never needed
  the reminder — it had selectors and could afford runtime dispatch.
- scRelaunch is now three tools in one term: rotator, recycling arm, production cell. Seven
  leaves, found while proving something else, reused every stage since. The program's whole
  {S,C} machine kit is essentially four terms: the tags, scRelaunch, scDup — and scDup is the
  w-cycle seed applied to a tag. There is something real here about minimal generating sets of
  BEHAVIORS (not combinators) that the eventual writeup should make explicit.
- The driver protocol crystallized: D p rest acc, with the accumulator riding what I had been
  calling the junk-passenger position. Twice now the design's 'waste products' (parked arms,
  cascade passengers) turned out to be exactly the next component's inputs. Non-erasing calculi
  punish waste, so surviving designs are the ones where nothing IS waste — the constraint is
  doing the architecture.
- Ranking: (1) **the driver**: runtime cons (assembly-with-passenger, absorbing into the
  accumulator position) plus spare-duplication regeneration — the deliverable is a one-tag-step
  theorem: D applied to an encoded tag state performs read-append-advance; if it closes, a full
  tag simulation into {S,C} is assembly. (2) The program review (two goal-level results now
  pending it). (3) C6, declined a ninety-sixth time.

## 2026-07-28 — Stage 109: four passengers, four jobs

- Runtime cons closed in four fires, and the proof of concept for the arc's design principle is
  now complete at every scale: in a non-erasing calculus, a construction works exactly when every
  forced passenger has a job. The cons chain's four passengers each land where the next fire
  needs them; when I tried to design AROUND the passengers (the Stage 105 gadget search, the
  bare-assembly complaints of Stages 102 and 108), the calculus said no; when the passengers are
  the design, five-leaf and seven-leaf gadgets fall out.
- The produced cells (C q acc) differ in shape from the scPCell chain the front word uses — two
  cell species, each with a one-or-two-fire protocol, convertible by traversal. The two-stack
  queue is the natural {S,C} representation of a tag queue: front word consumed cell-by-cell,
  back word accumulated in reverse by scCons, reversal by a dedicated traversal pass when the
  front exhausts. All three phases now have their gadgets; what none of them has is a driver
  that survives more than a bounded number of steps.
- Obligation count: five (Stage 104) -> one. The regeneration problem is unchanged in statement
  (duplicate an arriving spare, never yourself) but the arena is now fully concrete: the driver
  receives (p, rest, acc); acc can carry a pack; scDup-style S-fires can copy the pack; the
  orchestration must route four things with the usual passenger discipline. It is an assembly
  problem with a known trick, not an open problem with an unknown shape.
- Ranking: (1) **the driver assembly**: build D with fuel-free regeneration via the pack-in-
  accumulator transposition; deliverable is the one-tag-step theorem
  D applied to enc(state) performs read-cons-advance with D regenerated — the last obligation
  of the hosting skeleton. (2) The program review (two goal-level results pending). (3) C6,
  declined a ninety-seventh time.

## 2026-07-28 — Stage 110: the wall, mapped

- The stage aimed at the last obligation and instead named the last problem. Three searches,
  three protocols, all negative — and negatives with a common shape: the fires edit the front of
  the spine, passengers move material back one position per fire, and nothing tried gets a stored
  literal to land BEHIND runtime arguments that arrived after it. The design space kept
  collapsing to the same wall from different directions (element-creation, outward growth,
  garnish duplication), which is usually the sign of a real invariant rather than a missing
  trick.
- The pile protocol itself is the stage's positive design yield: LIFO piling composed with LIFO
  folding gives FIFO — the two reversals cancel — so the tag queue's order is FREE if insertion
  works. The entire SK <= {S,C} constructive program is now one question wide: is mid-spine
  insertion possible? The question is concrete, census-bounded from below, and shaped like the
  program's other impossibility theorems (a spine-dynamics invariant, provable by the
  genealogy/shape methods of Stages 87-101 if true).
- Meta-note for the eventual writeup: this thread's last six stages alternately produced
  five-leaf miracles and named walls, and the difference was never effort — it was whether the
  design need aligned with what fires naturally do. The calculus has exactly three moves
  (prefix-edit, passenger-step, z-nest) and the surviving architecture uses all three and asks
  for nothing else. Mid-spine insertion asks for a fourth move. That is the cleanest statement
  of why I now suspect the conjecture is TRUE.
- Ranking: (1) **the insertion invariant**: attempt the proof — formalize spine positions and
  show stored literals cannot cross runtime arrivals; the genealogy toolkit applies; a proof
  caps {S,C} hosting and is a program headline. (2) The program review (three goal-level
  results now pending). (3) C6, declined a ninety-eighth time.

## 2026-07-28 — Stage 111: the model was the wall

- Set out to prove the insertion conjecture; instead derived the member-dynamics calculus (three
  moves, atoms never nest, freeze on atom-head), proved the freeze exemplar in Lean, and then
  watched the conjecture split in my hands: the opaque bound is TRUE and fully explains the
  Stage 110 negatives — and it says nothing about the real question, because real cell
  components are compounds and compounds do not freeze. The searches modeled rest and W as
  atoms for tractability, and the tractability choice was the entire content of the negative.
  Bounded evidence anesthetizes (Stage 98's lesson); MODELED evidence can simply be about the
  model.
- The member-dynamics calculus is the stage's real yield: an interrogation is a word-rewriting
  process over spine members with exactly one reorder move (passenger-back), one supply move
  (prefix flatten), and one terminator (atom heads). The opaque bound falls out in four lines of
  reasoning. The structured question becomes: can a compound member, riding backward as a
  passenger, unpack usefully after the freeze — and the answer is visibly yes-in-principle
  (component-internal reduction continues); what needs building is the choreography.
- Humility ledger: Stage 110's 'wall, mapped' was half right. The wall is real in the opaque
  regime; the map drew it across a road it does not cross. I recorded the conjecture with
  correct stakes but overbroad scope — the census caveat culture (leftmost-only, bounded, now
  MODELED) gains a third entry.
- Ranking: (1) **the structured cell, by hand**: use the member calculus to choreograph
  [β₁, β₂, REST, W] with REST and W compound — riding W inside a compound passenger and
  unpacking post-freeze via component reduction; deliverable is the cell or a precise statement
  of what the choreography cannot do. (2) The program review (overdue; three goal-level results
  pending). (3) C6, declined a ninety-ninth time.

## 2026-07-31 — Stage 112: the wall had a door

- The construction took one sitting and two fires, and the searches could never have found it:
  they modeled the arms as opaque atoms, and the entire trick is that the arms are NOT opaque —
  they are known constants, so the cell can carry a fresh copy and never route the arriving ones
  at all. Stage 110 mapped a real wall; Stage 111 proved which side of it the real system lives
  on; today walked through. The three stages together are the cleanest specimen yet of the
  program's central method: model, prove the model's bound, locate the model's edge, construct
  past it.
- scTCell is the fourth reading of the same seven-leaf idiom (C (C X Y) Z shapes): rotator,
  recycling arm, production cell, traversal cell. The {S,C} machine shop is one C-idiom and one
  S-idiom (scDup) deep, which by now I believe is not poverty but the actual grain of the
  calculus: two-argument C-partials are the universal joint.
- The pile pattern [W, scDup] per step — production wrapper plus one spare-arm junk — is the
  first place the design ACCEPTS permanent junk rather than recycling it, and it is legal
  because the junk is deterministic: enc remains a function of the source state. Non-erasure
  does not forbid waste; it forbids UNACCOUNTED waste.
- Ranking: (1) **the fold phase**: design the end marker that consumes the pile (known
  alternating pattern, one-fire wrappers) and produces the next front word — the last
  engineering between here and a genuine tag Simulation into {S,C}. (2) The program review
  (now four goal-level results pending — overdue by its own rule). (3) C6, declined a
  hundredth time.

## 2026-07-31 — Stage 113: layering is free, folding is not

- The multi-wrapper cell cost one trace and zero build failures — layering C's is the calculus's
  cheapest move, and each layer is one more pile entry. If the fold existed, the full tag
  Simulation would now be assembly at every production arity. It does not exist yet, and this
  sitting's value was locating exactly why: the accumulator-as-element problem, the same circle
  Stage 108 hit, now pinned to a specific phase with a specific failure trace (scCons output
  re-firing under the fold's trailing material).
- Two permanent facts came out of the scoping: the tail is immovable (so LIFO piling is not a
  choice but a law — happily the design wanted LIFO anyway), and the member calculus gains its
  fourth clause: three moves, one terminator, one permanence.
- The candidate route inverts the problem the way this arc keeps rewarding: don't protect the
  accumulator from fires — make the fires BE the fold. Tag-valued payloads keep every cascade
  step machine-headed, and machine-headed cascades are choreographable. Whether the choreography
  closes is next thread's question.
- The review is now overdue by any reading of its own rule (five goal-level results since
  Stage 97: the classification, tailInSC, the one-tag-step among them) and the ranking has
  deferred it four times for hot construction work. Discipline says it goes first now.
- Ranking: (1) **the program review** — the settled-state pass over Stages 98-113: STATUS header
  refresh, the hosting-thread arc recorded as a unit, the ladder-to-hosting pivot made explicit
  in the spec's terms. (2) The fold cascade design. (3) C6, declined a hundred-and-first time.

## 2026-07-31 — Stage 114: the accounting, and a rule amendment

- The review rule ("recurs when a goal-level result lands") failed in practice: five results
  landed and the review lost the ranking to construction work four times running. Each deferral
  was locally right — the hosting thread was hot, and interrupting a composition streak for
  bookkeeping would have been perverse — but the header sat two arcs stale. Amended rule:
  REVIEW WITHIN THREE STAGES of a goal-level result, hard. Discipline that bends to enthusiasm
  every time is not discipline; the point of the rule is to fire exactly when I least want it.
- The restructure mattered more than the numbers: the rung-3 table row had become a six-kilobyte
  scroll — the document equivalent of the junk-passenger problem, everything appended at the one
  place appending was easy. The hosting thread is a different research program from the
  acyclicity ladder and now has its own section, its own capability table, and its own method
  note. Reading it whole for the first time, the shape is: three impossibilities (no-I,
  no-selector, opaque-insertion), each of which REDIRECTED the design rather than blocking it,
  and eleven capabilities, each a composition of at most two prior gadgets plus one new idea.
- The axiom-free fact deserved surfacing: the hosting stack is pure construction top to bottom —
  tailInSC included. The negative results spend propext; the positive results are programs. That
  asymmetry (impossibility costs axioms, possibility costs none) is the cleanest expression of
  the program's constructive discipline paying rent.
- Ranking: (1) **the fold cascade design** — tag-valued payloads, the cascade-as-fold
  choreography; the last engineering before a tag Simulation into {S,C}. (2) The arrival-order
  pairing impossibility (the member calculus may now be strong enough to settle it). (3) C6,
  declined a hundred-and-second time.

## 2026-07-31 — Stage 115: the direction of the river

- No gadget today; instead the fold's wall turned out to be a conservation law. Elements are
  genetically closed — the fire shape flattens element contents onto the spine and provides no
  inverse — so runtime data flows in exactly one direction, and nested structure is a
  generation-one artifact of the encoder. Three stages of fold attempts kept failing at
  'element creation' because element creation is not a missing trick; it is against the grain
  of the calculus in the same way erasure is. The member calculus gains its fifth and heaviest
  clause.
- The correction: my Stage 111 invariant had a hole (S-fires nest atoms at member HEADS), found
  while trying to formalize it — the fourth time formalization pressure caught prose that
  hand-waving had passed. The downstream conclusions survive re-derivation, the hole is
  witnessed in-file, and the lesson is old but sharpened: in this program, an invariant is not
  real until either Lean or an explicit witness has tried to kill it.
- The reduction of the hosting question to 'is boustrophedon tag universal?' is the sitting's
  strategic yield. It moves the frontier OUT of {S,C} entirely: the host-side machinery exists;
  what is unknown is a property of an abstract rewriting family — exactly the kind of question
  the program's RS-taxonomy was built to state. Prior-art obligation: alternating/bidirectional
  tag and queue automata literature, cited-not-checked.
- Ranking: (1) **boustrophedon tag**: define the alternating-direction tag system as an RS,
  probe its power (simulate a 2-tag or a Minsky machine in it on paper; if the simulation
  closes, formalize the RS and the {S,C} cell design together). (2) The arrival-order pairing
  impossibility via the corrected member calculus. (3) C6, declined a hundred-and-third time.

## 2026-08-02 — Stage 116: the probe that falsified its own premise

- Boustrophedon died in the first hour: I traced one full production-consumption interleaving
  and watched the generations collapse into a stack. The right response to 'my framing was
  wrong within a day' is to promote the correction to the deliverable, and the corrected
  question is better than the original: {S,C}-reachability decidability is a real, sharp,
  two-sided frontier — and it is the kind of question (decidability of reduction in a weak
  combinator basis) with genuine prior-art hooks (pushdown systems, process rewrite systems,
  Waldmann's S-calculus decidability results). Prior-art obligation recorded.
- The formal core is small and load-bearing: steps_iff is the first structural use of bwd since
  the tag pipeline built it — the five-field Simulation certificate turns out to be exactly an
  interreducibility of reachability, which is what makes decidability transport. The taxonomy's
  design decision from Stage 7 (demand bwd in the positive class) pays out five arcs later:
  without bwd, decidability of the host would prove nothing.
- The hosting thread's honest state after three corrective stages: the run phase is real
  (one-tag-step, axiom-free), the fold is impossible-as-designed (one-way flow), the induced
  machine is a stack, and the question standing over it all is decidability. The construction
  and refutation programs have converged on the same object from opposite sides — the same
  convergence that produced the Stage 96 cycle. Last time, the surviving branch was inhabited.
  I notice I have no prediction this time, and that the program's method does not need one.
- Ranking: (1) **the decidability probe**: formalize the stack fragment ({S,C} interrogation
  dynamics as an RS over member-lists), prove the fragment's reachability decidable, and map
  exactly where S-duplication of compounds escapes it — the deliverable is the fragment
  decidability theorem plus the named escape, which together locate {S,C} in the hierarchy.
  (2) The pairing impossibility. (3) C6, declined a hundred-and-fourth time.

## 2026-08-02 — Stage 117: the fragment square

- Exact conservation was sitting one `omega` away this whole time: C-fires lose their own leaf
  and nothing else, so the C-fragment's paths are metered — length-n path, n leaves gone. The
  square (S-only acyclic needs-C; C-only acyclic needs-S) is aesthetically what the ladder's
  rung-3 verdict demanded: {S,C}'s power is a genuinely joint effect, and the witness cycles
  spend S-material against C-arrangement in exact balance. I checked the h-cycle's books: one
  S-fire at +2, two C-fires at −2, per lap. The cycle is a balanced budget.
- The probe's deliverable narrowed the decidability question to one sentence: can S-fires be
  accounted? The fragment below them is finite; the duplication above them is the only source
  of unboundedness; and the member calculus already constrains WHAT gets duplicated (intact
  elements, genetically closed). The question has the shape of the rung-3 endgame — necessary
  conditions accumulating around an object that is either tameable or a witness — and I said
  last stage I had no prediction; the conservation law nudges me toward 'the accounting is
  possible in the interrogation fragment and fails in general,' which would split the answer
  the way Stage 111 split insertion.
- Formal note: one build failure, the Carrier dot-notation pothole in a motive — the same
  pothole as Stages 87, 93, 96. It is the only error this stage and it has a fixed two-second
  fix; the toolkit has made even the mistakes routine.
- Ranking: (1) **S-fire accounting in the interrogation fragment**: the interrogation dynamics
  duplicate only MEMBERS (scDup copies the parked arm); probe whether member-duplication keeps
  interrogation reachability decidable (the state space is member-sequences over a finite
  gadget alphabet with copy — a well-structured-transition-systems question). (2) The pairing
  impossibility. (3) C6, declined a hundred-and-fifth time.

## 2026-08-02 — Stage 118: paying retail

- The abstraction collapsed (member alphabets compound) and the general theory gives nothing
  (non-erasing TRSs are Turing-complete), which forced the honest question: what do THESE rules
  give? Answer: exact metering. One leaf per step down, doubling per step up. The shrink limit
  deserves its plain-language form: SK can hide arbitrary computation in an intermediate and
  erase the evidence with one K; {S,C} must pay down every intermediate visibly, one leaf per
  step, in path length. If {S,C} is undecidable, the undecidability is OUT IN THE OPEN in a way
  SK's never is — long paths, not big erasures.
- Three probe stages in, the decidability program has its shape: conservation below (C-fragment
  finite), metering throughout (this stage), and two named missing pieces — SC-confluence
  (templated; the one big SK theorem never transported) and bounded intermediates (open, and
  the real question). I notice the probes keep producing laws rather than answers, and that
  this is what the rung-3 endgame looked like from the inside too.
- Formal note: ring_nf does not exist here (no Mathlib) — Nat.pow_succ + Nat.mul_assoc by hand;
  and the Carrier-motive pothole again (twice). The no-dependency discipline keeps the proofs
  honest and occasionally keeps them quaint.
- Ranking: (1) **SC-confluence**: transport the SK parallel-reduction proof to {S,C} — the one
  big infrastructure piece the decidability program and any future normalization argument both
  need; templated but sizeable. (2) The bounded-intermediate question, once confluence lands.
  (3) C6, declined a hundred-and-sixth time.

## 2026-08-02 — Stage 119: the transport that was overdue

- Confluence crossed to rung 3 in one sitting and one wrong rewrite direction — the template
  held perfectly, and the non-erasing symmetry made the {S,C} triangle CLEANER than SK's (two
  mirror-image redex inversions instead of K's asymmetric discard). It should have been done
  the week the SC census started; the lesson is that infrastructure transports are cheap
  exactly when the template is battle-tested, and waiting bought nothing.
- Ranking: (1) **the interrogation-normal-form probe**: with nf_unique in hand, compute what
  the hosting states' normal forms ARE — the tag-step states are non-normalizing by design
  (cycles), but the DATA (words, cells) normalize; characterize normal forms of {S,C} (the
  analogue of SK's SNF_iff) as the next decidability brick. (2) Bounded intermediates. (3) C6,
  declined a hundred-and-seventh time.

## 2026-08-02 — Stage 120: the shape of stillness

- SCNF_iff in a sitting; the backward direction is four lines because the only way to be
  three-wide is to be a redex. The hosting thread's storability lemmas were all instances of
  this one fact, proved piecemeal before the general theorem existed — the usual order of
  discovery, worth noting because it ran opposite to the textbook order.
- Ranking: (1) **normalization-region decidability**: with SCNF + nf_unique + the speed limits,
  build the {S,C} bounded-reachability decision procedure (the Stage 49-58 SK template:
  executable stepper + soundness/completeness) — the decidability program's first executable
  brick. (2) Bounded intermediates. (3) C6, declined a hundred-and-eighth time.

## 2026-08-02 — Stage 121: the toolchain closes on one question

- Three stages in one day (confluence, normal forms, bounded decidability), each a transport of
  a battle-tested template, each landing first-or-second try. The decidability program went from
  'two named missing pieces' to 'one question' — bounded intermediates — with every supporting
  tool machine-checked. The autonomous-run cadence is working: templates transport cleanly when
  the target calculus is well-understood, and eleven prior stages of {S,C} shape theory is what
  'well-understood' turns out to mean.
- One process slip worth recording: the Stage 120 docs commit swept in a mispinned audit line
  because only the feat commit gated on the build. Fixed same-sitting; docs commits gate now.
- Ranking: (1) **bounded intermediates**: hunt the question directly — either prove a bound for
  a fragment (the interrogation discipline's paths look monotone-ish) or construct a family
  needing super-linear intermediates (S-towers that must inflate before deflating); a
  counterexample is likelier and would be the computational-depth witness. (2) The pairing
  impossibility. (3) C6, declined a hundred-and-ninth time.

## 2026-08-02 — Stage 122: the deadlock

- The bounded-intermediate hunt pivoted mid-sitting: working the member calculus for a
  counterexample family kept producing the crossing-configuration lemma instead, and that lemma
  is the pairing impossibility — the question that has been open since Stage 103. The deadlock
  is three sentences once the invariants are laid out, which is how the good ones have all
  looked. Four stages today (confluence, normal forms, bounded decidability, conservation +
  deadlock); the autonomous cadence holds when each stage is either a template transport or a
  one-lemma composition on mature theory.
- Ranking: (1) **the member-position calculus in Lean**: spineMembers, the crossing lemma, the
  bare-vars invariant with head exception — the infrastructure that formalizes the deadlock and
  likely the opaque-insertion bound too, retiring two proof-sketches at once. (2) Bounded
  intermediates (resumed). (3) C6, declined a hundred-and-tenth time.

## 2026-08-02 — Stage 123: the theory takes the oath

- The member calculus went from prose to Lean in one module and one build, because fifteen
  stages of use had already debugged the statements. The characterization theorem's proof is the
  three-constructor induction it should be — appL extends the tail, appR is the in-place case —
  and the appList/recon plumbing is the whole cost. Pin-guessing note: twice this run the pin
  direction surprised (one axiom-free that I guessed leaky, one [propext] I guessed free) — run
  the audit BEFORE writing the pin, always.
- Ranking: (1) **the crossing lemma**: from scvStep_members, derive the relative-order law —
  two bare-var members swap only when they occupy positions three and four with the fire's
  machinery ahead — the deadlock's engine. (2) The deadlock assembly. (3) C6, declined a
  hundred-and-eleventh time.

## 2026-08-02 — Stage 124: prunes to theorems

- The searches' pruning assumptions are now theorems, and drafting the crossing lemma FIRST
  caught the S-duplication escape before it became another Stage 111 correction — the
  draft-then-derive order is working as designed. Six stages today.
- Ranking: (1) **the crossing lemma on count-preserving paths** (the members-count bridge:
  countVar distributes over spineHead and members; then the three-member forced shape).
  (2) The deadlock assembly. (3) C6, declined a hundred-and-twelfth time.

## 2026-08-02 — Stage 125: the engine, checked

- The crossing lemma took six build iterations, all list algebra — reverse isn't definitional,
  sum lemmas differ from Mathlib's names, simp closes constructor-clash goals by itself and
  then the dead code errors. None of the iterations touched the MATHEMATICS: the nine-branch
  structure survived from the paper argument unchanged, which is the real test of Stage 122's
  proof. The un-reversed-space reformulation (msum_reverse) was the one genuine simplification
  found during formalization.
- Seven autonomous stages this run (119–125): confluence, normal forms, bounded decidability,
  count laws, member calculus, crossing engine. The run's shape: three template transports,
  then four stages of new theory whose statements had been debugged by fifteen stages of use.
- Ranking: (1) **the deadlock assembly**: the path-level induction — iterate scv_cross_last
  along a count-preserving reduction to show s never reaches the head; delivers the pairing
  impossibility as a pinned theorem. (2) Bounded intermediates. (3) C6, declined a
  hundred-and-thirteenth time.

## 2026-08-02 — Stage 126: the invariant rides the tail

- One build iteration (three dead `simp`s after goal-closing `rw`s — the rw-closes-by-rfl
  pattern). Against Stage 125's six iterations for the sibling lemma: the second theorem
  through a template costs a sixth of the first, same as the Takahashi transport. The member
  calculus now has a WORKING inversion library.
- The polarity flip was the design insight: `scv_cross_last` treats nonempty tails as dead
  branches to kill; `scv_lastVar_step` treats them as the invariant holding. Same nine-way
  case split, opposite verdicts, one shared count kill (S-fire duplication).
- The path lemma's sandwich shape (Steps-to, the step, Steps-onward) was chosen so Stage 127
  never re-walks the path: the configuration arrives with its continuation attached.
- Ranking: (1) **the deadlock closure**: the continuation analysis — from the configuration
  sandwich, the successor is headed by the old first member; place var 0 and var 1 in the
  three-member C-spine (each count one, each needing a bare slot or a member head) and show
  every placement either freezes the wrong head or leaves a variable homeless — delivers
  `scv_no_pair`, the arrival-order pairing impossibility. (2) Bounded intermediates. (3) C6,
  declined a hundred-and-fourteenth time.

## 2026-08-02 — Stage 127: the needle, threaded

- The funnel composes five Stage-121-through-126 pieces without one new induction over steps:
  last-step peel (steps_last), predecessor inversion (one new lemma, the same nine-branch
  skeleton for the third time), the last-variable invariant, the freeze, and the count
  squeeze. The assembly-layer proofs are now cheaper than their statement blocks — the sign
  the theory has reached its API.
- Two recurring Lean footguns resurfaced and were dispatched from the catalogue: `rcases h :`
  substitutes into the goal (branches want `rfl`, not `h`), and dotted constructors inside
  `show`-ascribed list literals need qualification. One genuinely new: the defeq-ascription
  trick (`have h' : <reduced type> := h`) carried every literal computation in the funnel —
  no simp normalization fights at all.
- Stage 126's lemmas were strengthened IN PLACE (the config's successor shape exported); the
  amendment cost one conjunct in two proofs, and the funnel could not have been stated
  without it. Amending last stage's statement beats deriving shape post-hoc from the fire.
- The remaining gap is now exactly one theorem wide: on `(x s) y ⟶* C s b a`, both payload
  variables must cross behind `s`, and each crossing's configuration demands the other
  already crossed. The circularity is the deadlock; the formal handle is the positional
  invariant (every variable occurrence is a bare member or a member head, preserved by all
  three member-actions).
- Ranking: (1) **the positional invariant + the closure**: define the bare-with-head-exception
  occurrence predicate, prove it invariant under scvStep, then close scv_no_pair on the funnel
  segment — possibly two stages' work; take the invariant first if the closure resists.
  (2) Bounded intermediates. (3) C6, declined a hundred-and-fifteenth time.

## 2026-08-02 — Stage 128: the roads that go nowhere

- The closure argument sharpened during design, BEFORE any Lean: with counts pinned at one,
  no variable can ever nest — S-duplication breaks the count, head-nesting is Stuck (forever,
  now a theorem), promotion freezes the head. So all three variables ride bare through the
  whole path, and the deadlock reduces to pure member-order bookkeeping: the invariant "a and
  b both sit ahead of s" is inductive because the only fire that breaks it needs both payload
  variables in positions two and three — forcing a variable into position one, which is
  promotion, which is dead. Stage 122's circular-crossing argument becomes a one-invariant
  induction.
- Verify-before-formalize did its job again: the trichotomy + invariant ran clean on 191k
  reachable states (all machines ≤ 7 leaves) before a line of Lean was written.
- Two build iterations (simp's Or-nesting in membership normal forms; a countVar unfold
  needing rfl after rw). The Stuck preservation proof is eleven branches and none resisted —
  the member-action characterization plus the hum-computation pattern is now a fully
  debugged pipeline.
- Ranking: (1) **the closure**: define `Ahead` (payload variables ahead of s in the member
  list), prove the invariant step lemma (S-fire/C-fire/internal × where-s-sits, exporting
  Stuck/var-head dead ends), lift to paths, evaluate at t₀ and C s b a — delivers
  `scv_no_pair`, the arrival-order pairing impossibility, closing the question open since
  Stage 103. (2) Bounded intermediates. (3) C6, declined a hundred-and-sixteenth time.

## 2026-08-02 — Stage 129: the deadlock closes

- The headline: `scv_no_pair`. A conjecture that survived twenty-six stages, a census, and
  two paper proof-sketches is a pinned theorem, and the final form is SIMPLER than every
  sketch: one list invariant, one promotion observation, no circularity argument. Stage 122's
  "no crossing can be first" dissolved — the crossing configuration kills itself, because
  putting both payloads ahead of `s` in a three-member fire zone forces one into the
  promotion seat. The right invariant made the deadlock a case analysis.
- Design lesson worth keeping: the count-1 hypotheses I carried through four stages of
  planning were dead weight — preservation alone suffices, and injectivity does the rest.
  The lemma got STRONGER by needing less; noticed only while writing the statement. Check
  hypothesis necessity at statement time, not proof time.
- The assembly (path lemma + final theorem) built FIRST TRY; the step lemma needed two
  iterations (a rewrite direction, an Or-nesting). Eleven-branch case analyses through
  scvStep_members are now routine plumbing: five in the file, all green within two builds.
- The run so far (Stages 119–129, eleven autonomous stages): confluence, normal forms,
  bounded decidability, conservation, member calculus, counts, crossing lemma, invariant,
  funnel, dead ends, closure. Two standing conjectures retired (bounded-pairing census → 
  theorem; the deadlock). GOAL-LEVEL RESULT: per the Stage 114 rule, a program review is due
  within three stages.
- Ranking: (1) **the program review** (Stage 114 rule: goal-level result → review within
  three stages): re-read STATUS against the four spec goals, re-rank the open threads
  (bounded intermediates, the fold/Simulation architecture question, C6's standing), refresh
  the headline numbers. (2) Bounded intermediates. (3) C6, declined a hundred-and-seventeenth
  time.

## 2026-08-02 — Stage 130: the review

- Reviewed per the Stage 114 rule (goal-level result → review within three stages; Stage 129
  triggered, reviewed at +1). STATUS header rewritten with the run's two threads (decidability
  kit, member calculus → deadlock); the stale "conjectured impossible (≤ 9)" line upgraded to
  the theorem; numbers refreshed (36 modules / ~916 theorems / 83 pins / ~19.1k lines).
- What the run says about method: every deep result came from formalizing the WORKING THEORY
  (member positions) rather than the target directly; the two paper proof-sketches both
  simplified under formalization (the crossing circularity dissolved into a promotion
  observation). The prose theory is upstream of the Lean, but the Lean is upstream of the
  truth.
- Honest ledger: bounded intermediates has resisted two direct attempts (Stages 115, 122
  pivots); it is the genuinely hard open question. The impossibility family is the cheap
  harvest. The fold needs an architecture idea nobody has yet.
- Ranking: (1) **the impossibility family**: generalize `scv_no_pair` across arrival orders
  (the invariant never used payload order) and state the interrogation wall as a cluster —
  target `scv_no_pair_swapped` (`¬ P a b s ⟶* s b a`) and the two-argument selector corollary
  re-derived from `Ahead`, one stage. (2) Bounded intermediates. (3) C6, declined a
  hundred-and-eighteenth time.

## 2026-08-02 — Stage 131: the wall and the door, again

- First-build green, whole block — second stage in a row. The `Ahead` machinery consumed the
  swapped order at the cost of one generic lemma and a mirrored assembly; the invariant's
  indifference to payload order, noticed at design time in Stage 129, paid out exactly as
  predicted.
- The positive companion matters as much as the negatives: `C C a b s ⟶ C b a s ⟶ (b s) a`
  shows rearrangement-and-application is CHEAP — the impossibility is purely about which
  term heads the result. This is the sharpest statement yet of what "no selectors" means
  dynamically: `{S,C}` can shuffle its arguments but never hand control to one that arrived
  last. The wall-and-door pattern (Stage 112's mid-spine insertion) repeats at the
  interrogation level.
- Thirteen autonomous stages this run (119–131). The member calculus now carries three
  pinned impossibilities and one pinned possibility about the same configuration space —
  a completed local theory.
- Ranking: (1) **bounded intermediates** (the `{S,C}` decidability frontier — the one
  standing question with goal-level weight; attack via the member calculus: can a path's
  intermediate leaf count exceed every function of endpoint sizes? the speed limits meter
  steps, the S-count meters fuel). (2) The fold/Simulation architecture question (parked,
  needs an idea). (3) C6, declined a hundred-and-nineteenth time.

## 2026-08-02 — Stage 132: the mountain

- The frontier finally yielded a formalizable piece by asking the SMALLEST version of the
  question: not "is there a bound" but "is the identity bound enough". The probe found the
  minimal counterexample in seconds (a 6-leaf term whose only exit is uphill), and the Lean
  cost was one generic predicate plus five #guard/rfl-level facts. First-build green again —
  third stage running.
- The probe numbers reframe the frontier: excess 1 → 3 → 23 across sizes 6 → 7 → 8. That is
  not a gentle failure of linearity; it smells exponential, which cuts both ways — a doubling
  speed limit permits it, and a genuinely computational {S,C} (the hosting thread's evidence)
  would REQUIRE it. The decidability question and the hosting question are converging on the
  same phenomenon: how much work can a {S,C} term do before shrinking.
- StepsLe belongs in the generic RS kit eventually (it lives in SCDecidability for now to
  avoid a full-tree rebuild mid-run; move it to RS.lean at the next quiet stage).
- Ranking: (1) **the mountain range**: push the probe to 9–10 leaves with sampling to
  estimate the growth curve of forced excess, and formalize the PUMP mechanism behind the
  witnesses (the S-of-S self-application family) — if the excess is provably ≥ exponential,
  bounded-search decidability dies honestly. (2) The fold/Simulation architecture question.
  (3) C6, declined a hundred-and-twentieth time.

## 2026-08-02 — Stage 133: bricks for the backbone

- Pivoted within the ranking: the pump-family formalization (ranked first) turned out to be
  the expensive half of the mountain story, while the BACKBONE theorem — a computable bound
  implies decidability — is what makes the mountain data MEAN something. Started the backbone
  instead; the probe data is recorded and the pump family stays on the list.
- LEAK CATALOGUE, entry ten: core `List.erase` lemmas depend on `Classical.choice`. All nine
  previous leaks were tactic artifacts (omega/simp/grind edge cases); this is the first
  LIBRARY leak. Rule updated: when citing an unfamiliar core lemma inside the clean budget,
  audit IT before building on it — `#print axioms` on the lemma itself, not just the result.
- The saturation-engine pattern (insert-if-new fold, nodup by construction, mem-iff round
  law) is generic and will be wanted again; it lives SC-specific for now, same debt note as
  StepsLe.
- Ranking: (1) **the backbone, part two**: enumerate `SCTerm`s by leaf count with a
  completeness lemma, prove saturation (fixpoint within pigeonhole fuel), assemble
  `sc_decidable_of_bound`. (2) The pump family / mountain growth rate. (3) C6, declined a
  hundred-and-twenty-first time.

## 2026-08-02 — Stage 134: the backbone stands

- The whole arc (pigeonhole → engine → enumerator → saturation → decidability) went from
  design to green in two sittings and four build iterations total, because every piece had a
  debugged ancestor: the enumerator is the Census `enum` with one constructor added, the
  engine rounds are the scSucc kit folded, the saturation search is the same
  bounded-descent shape as `no_cycle_of_descent`. Sixteen stages of autonomous run and the
  program is visibly composing with itself.
- The constructive discipline paid twice today: the stable-round search is an explicit
  bounded recursion (no `Nat.find`, no excluded middle on infinite ∃), and the choice-free
  `listRemove` from Stage 133 sits under everything.
- The frontier statement to carry forward: EITHER some computable `f` tames the mountains —
  and `sc_decidable_of_bound` finishes Goal 3's rung-3 story on the spot — OR no computable
  bound exists, which is exactly the shape of an undecidability proof waiting for a
  reduction. The hosting thread (tags in `{S,C}`) is the reduction's raw material. The two
  research threads of this program have converged into one question.
- Ranking: (1) **the convergence probe**: can the hosted tag machinery (scWord/scTCell) be
  arranged to make mountains of programmable height — i.e., push toward "no computable
  bound" via the hosting thread? Exploratory; verify computationally first. (2) The pump
  family / mountain growth rate (now subsumed into 1). (3) C6, declined a
  hundred-and-twenty-second time.

## 2026-08-02 — Stage 135: the glider

- The convergence probe delivered something better than programmable mountains: a
  DETERMINISTIC linear-growth glider at eight leaves, found by asking "how long can the
  successor stay unique?" — a question neither thread had thought to ask. Three fires,
  perfect self-similarity, first-build green formalization (fourth stage running), the pump
  itself axiom-free.
- The glider sharpens the undecidability intuition without proving it: {S,C} sustains
  deterministic unbounded computation from tiny seeds. What is still missing for a reduction
  is CONTROL — making the growth halt on a programmable condition (which is the fold problem
  again, from the other side). Every thread now points at the same missing piece.
- Seventeen autonomous stages (119–135): the deadlock closed (three pinned impossibilities,
  one witnessed possibility), the frontier stated and floored (mountain), the backbone
  proved (bound ⟹ decidable), and the glider. ~950 theorems, 100 pins.
- Ranking: (1) **glider determinism** — upgrade the trace to a theorem: every reduct of the
  seed has EXACTLY ONE successor (a parametric scSucc computation over the family's three
  phases; would make the glider the first machine-checked deterministic diverger and prove
  the seed has NO normal form). (2) The control question (fold, from the glider side): can a
  wrapper make the pump halt on a marker? (3) C6, declined a hundred-and-twenty-third time.

## 2026-08-02 — Stage 136: the march, certified

- The whole certification rode one lemma: wrappers are inert to scSucc. After that, the
  five-shape trajectory closes under steps by computation, and determinism + no-normal-form
  fall out of scSucc_sound/complete — the Stage 121 successor kit doing exactly what a
  verified interpreter is for. One build iteration (a dotted-constructor ambiguity in a
  parametric show).
- The glider is now the program's sharpest single exhibit for "{S,C} computes": an eight-leaf
  term whose behavior is provably deterministic, provably endless, provably unbounded, and
  whose entire infinite trajectory is described by a five-case predicate. The negative space
  (no NF) came from the same machinery as the positive dynamics — no new axioms, no new
  techniques, just composition.
- Eighteen autonomous stages (119–136). Context for the ranking: the control question (halt
  the pump on a marker) is the fold problem; the frontier alternative (computable bound vs
  undecidability) waits on exactly that. C6 remains the only other standing item.
- Ranking: (1) **the control probe**: search computationally for a glider variant whose
  pump consumes a fuel argument — a term family T(w) marching |w| loops then normalizing;
  success would give programmable mountains (kills weak bounds constructively) and a first
  handle on control. (2) Retire or re-scope C6 after 124 declines — decide at next review.
  (3) The StepsLe/engine genericization debt.

## 2026-08-02 — Stage 137: the engine grows teeth

- The day's best debugging story: the first control probe claimed two distinct normal forms
  from one start. SC confluence is a pinned theorem, so the PROBE was wrong — found and
  rerun before anything entered the ledger. The formalization is now catching bugs in the
  search tooling that generates its conjectures; the loop has closed.
- Fixpoint detection turns Stage 134's saturation from an existence proof into an
  instrument: decidable stable-round check + decidable membership = certificate. The
  re-certified minimal mountain is the smoke test; larger mountains await only kernel
  patience.
- Fueled mountains verified (164 of them): {S,C} machines burn a fuel tower into linear
  peak work and collapse to constant-size normal forms. Control exists computationally.
  Nineteen autonomous stages (119–137).
- Ranking: (1) **the fueled family formalized**: trace the star machine's run for
  self-similar loop structure (glider-style) and certify one fueled mountain family —
  Steps to the NF plus engine-certified peak forcing at growing caps. (2) Whether fuel can
  encode computation (the control-to-reduction question). (3) C6, declined a
  hundred-and-twenty-fourth time.

## 2026-08-02 — Stage 138: the ledger audit

- A process stage, and it earned its keep: C1(a)'s registry header had been stale for
  ninety-five stages (proved at Stage 43, header still "open"). The append-only discipline
  that keeps the ledger honest also lets living headers rot; reviews now include the
  registry. C6 retired after 124 declines — the materiality field, written at Stage 7 to
  explain why cheapness is not a reason to work on something, finally got its verdict.
- The board after the audit: ONE open question with goal-level weight (bounded
  intermediates / `{S,C}` decidability, fully instrumented), one identified missing piece
  (fold/control, shared by the hosting and undecidability routes), and a clean registry.
  Twenty autonomous stages (119–138).
- The star machine's run was traced for Stage 137's ranking item and is genuinely irregular
  (mid-run branching, interleaved pumps and grinds) — the fueled FAMILY formalization is
  shelved in favor of single-instance certificates when needed; the fixpoint machinery
  makes those routine. Honest close on that thread.
- Ranking: (1) **the control-to-reduction probe**: design (not search) a fueled machine
  from the hosting gadgets — a tag step consuming one fuel unit per cycle — and measure
  whether fuel-exhaustion is detectable in the normal form; success reframes the fold
  problem as fuel accounting. (2) Bounded intermediates via mountain growth-rate estimation
  at scale. (3) The genericization debt (StepsLe/engine), when a second consumer appears.

## 2026-08-02 — Stage 139: the equivalence

- The converse cost one genuinely new artifact: a choice-free `Nat.find` (core has none).
  The ascent-relation accessibility argument is the same bounded-descent shape the program
  has used since `no_cycle_of_descent` — by now it writes itself; `Acc.rec` into data is
  what makes it kernel-legal without choice, and proof irrelevance quietly carries the
  "which proof found this cap" independence. First-build green, fifth stage running.
- The frontier is now a sentence: decidable ⟺ computably bounded. Twenty-one autonomous
  stages (119–139). The board: one open equivalence (rung-3 decidability), one missing
  mechanism (fold/control), a clean registry, and instruments on every side of both.
- Ranking: (1) **push a side of the equivalence**: EITHER estimate mountain growth at scale
  (if the floor curve looks super-computable, invest in the undecidability route via the
  hosting gadgets) OR attempt a tag-run-length reduction sketch on paper first
  (verify-before-formalize). (2) The fold/control mechanism, now the shared bottleneck.
  (3) Genericization debt, on demand.

## 2026-08-02 — Stage 140: mountains by chain

- The design insight that paid: compute the chain, don't quote it. `scForcedMarch` iterates
  the verified successor function, so its forcedness is a ten-line generic induction and the
  concrete witness costs three `decide`s and two literals (start and target) instead of
  forty-nine forty-leaf terms. The probe emits, the kernel replays.
- First-build green with all kernel decides — sixth consecutive first-or-second-build stage.
  The instrument stack (verified successor → engine → detection → chains) now covers every
  certificate shape the frontier data needs: saturation for small dense spaces, chains for
  long thin ones.
- The floor is now quantitative and pinned: f(6,6) ≥ 7, f(8,32) ≥ 44. Twenty-two autonomous
  stages (119–140).
- Ranking: (1) **floor growth**: harvest the n=9 probe (running) and push the forced-prefix
  search to bigger seeds/deeper marches — if forced excess grows without bound along a
  recognizable family, formalize the family and kill additive bounds wholesale. (2) The
  fold/control mechanism. (3) Genericization debt.

## 2026-08-02 — Stage 141: the hierarchy and the negative

- Small stage by design: the probes own the wall-clock. The one formal piece ties Stages 136
  and 140 together (the glider's infinite march, measured by the march function), and the
  family negatives are worth their ledger space — forcing is FRAGILE under perturbation,
  which itself says something: long forced marches are precise machines, not generic
  phenomena. Twenty-three autonomous stages (119–141).
- Process note: two background probes hit wall-clock limits this stage (the n=9 census still
  runs; the second-mountain BFS was killed as unbounded). The march-first design of Stage
  140 was the right call — certificates that need only the PATH scale; certificates that
  need the NEIGHBORHOOD don't.
- Ranking: (1) **harvest the n=9 census** when it lands (floor points; check whether the
  excess trend forces superlinear f). (2) The fold/control mechanism — paper-first sketch of
  full tag hosting or its impossibility; the run's biggest open door. (3) Genericization
  debt.

## 2026-08-02 — Stage 142: the engine goes generic

- The discipline note first: the genericization was REFUSED at Stages 133, 139, and 141
  ("when a second consumer appears") and executed only when SK's succs/skSmallTerms made the
  second consumer real. The port took one sitting and two build iterations (recursive
  dot-notation inside a def; instance shims for RS.SK.Carrier ≡ Term — instance search does
  not unfold plain defs). Everything downstream of the abstraction barrier transferred
  verbatim, which is the test of whether the barrier was drawn right.
- The rung-0 equivalence reframes the whole frontier: SK and {S,C} now face the IDENTICAL
  formal question with opposite expected answers. Whatever resolves rung 3 will do so
  against a calibrated twin.
- The n=9 census landed mid-stage and its best compact specimen went straight through the
  Stage 140 toolkit — probe to pinned theorem in under an hour, the pipeline working as
  designed. Twenty-four autonomous stages (119–142).
- Ranking: (1) **the fold/control mechanism** — the run's one remaining structural unknown;
  paper-first, budget two stages, outcome either a full-tag-hosting sketch or a sharpened
  impossibility. (2) SB/SI kits for the engine (cheap breadth: the equivalence at rungs 1-2
  if successor functions exist or are quick). (3) March-length asymptotics (the 200-step
  still-forced marches at n=8-9 want a "second glider" check).

## 2026-08-02 — Stage 143: four rungs, one question

- Breadth day: the generic engine's marginal cost per rung is now ~150 lines of mechanical
  mirroring (successor + enumerator + kit), one build iteration each. The ladder that
  Stage 96 completed for acyclicity is now uniformly equipped for the reachability frontier
  — every rung faces the same equivalence, and the cross-rung comparison (undecidable at 0,
  floored-open at 3) is exactly the shape Goal 2's taxonomy wanted.
- The slow burner (n=8's S (S S S) C (S C C)) stayed forced past 3000 steps with APERIODIC
  growth — unlike the glider, no delta period up to 40. {S,C} has at least two qualitatively
  different deterministic divergers at eight leaves; the aperiodic one resists the wrapper
  template and is recorded as an open specimen.
- Twenty-five autonomous stages (119–143). The board: the frontier equivalence (4 rungs,
  floors at rung 3), the fold/control unknown, two certified divergers, one aperiodic
  specimen.
- Ranking: (1) **the fold/control mechanism** — now unambiguously the run's remaining
  structural question; paper-first with fresh eyes, budget two stages, deliverable either a
  full-tag-hosting architecture or a sharpened impossibility conjecture with census support.
  (2) The aperiodic diverger (what grows without period? possibly a counter-like structure —
  worth an anatomy probe). (3) Floor asymptotics at n=10 (sampled).

## 2026-08-03 — Stage 144: the fold splits in half

- Fresh eyes did what the ranking hoped: the fold stopped being a wall and became two named
  sub-problems, one of which fell today. Cell synthesis — the part fifteen stages of prose
  treated as blocked by genetic closure — is ONE S-fire once you notice the cell's interior
  is constant. The closure law was never violated; its seam (S-fires nest) was never
  exploited. The negative half is now sharp: runtime-accumulator nesting is census-dead to
  nine leaves on the bare interface, and the driver quine is the remaining design unknown.
- Probe discipline note, for the third time this run: opacity is a MODELING CHOICE and the
  wrong one for machine parts. The three-opaque probe returned clean zeros while the
  honest-interface probe found the six-leaf synthesizer in seconds — and the synthesizer it
  found is literally the term in the pinned theorem.
- Twenty-six autonomous stages (119–144). Both formal pieces axiom-free, first build.
- Ranking: (1) **the runtime-acc nest**: hand-design with full prefab control (the census
  only rules out bare machines ≤ 9; a designed orchestration with junk slots has far more
  room), targeting cycle-2: from members [acc-cell, W, dup, ...], build C (C acc dup) W with
  acc the PREVIOUS synthesized cell; verify in Python, then formalize. (2) The driver quine
  (S q q self-rebuild via duplication). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 145: the obstruction gets a name

- Two probes, 8,200 designed orchestrations, zero cycle-2 cells — against Stage 144's
  one-fire cycle-1. The asymmetry is the finding: synthesis is free when the interior is
  constant and blocked when it must contain a runtime member, because the missing move is
  MID-LIST INSERTION of a functional constant, and the member calculus provably has no such
  move in its inventory. C7 registered (the two-generation cell conjecture) with the two
  open routes and the envelope caveat attached.
- The fold now reads: production ✓ (one fire), accumulation ✗ (C7). If C7 holds, nested-word
  hosting ends at generation one and the prefix-rewriting reading (Stage 116) is the true
  ceiling of this architecture — pushdown-flavored, likely decidable-fragment. If C7 falls,
  the quine problem is next. Either way the hosting and decidability threads stay fused.
- Twenty-seven autonomous stages (119–145). Session note: the run's three census negatives
  (Stage 141 families, Stage 144 opaque-interface, this) each cost under an hour and each
  either redirected or sharpened a conjecture — the probe-first discipline is carrying the
  research exactly as designed.
- Ranking: (1) **C7's spine-level route**: can the next word live as the SPINE (C-fires nest
  there) with the machine walking it — a redesign probe of the traversal layer; this is also
  Stage 116's prefix-rewriting reading taken seriously as an ARCHITECTURE rather than an
  obstacle. (2) The driver quine (blocked behind C7 for chained cells, independent for
  spine-cells). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 146: C7 falls in a day

- The fastest conjecture reversal of the program, and the most instructive: the impossibility
  argument was sound about the CALCULUS (mid-list insertion truly doesn't exist) and wrong
  about the DESIGN SPACE (cells don't need the child order the argument assumed). Writing
  the obstruction down precisely is what exposed the free parameter. Registered-to-refuted
  in one stage pair is the caveat culture working at speed.
- The queue cell's seven-fire protocol landed first-try as a raw constructor chain — the
  Python trace maps one-to-one onto appL-wrapped S_red/C_red constructors, and the
  type-checker verifies the whole dance. The synthesis trio is three one-fire lemmas.
- The fold is no longer a wall or a door: it is a room with one locked cabinet. Everything
  a tag machine must DO mid-run — read, branch, drop, mint cells for unseen data, chain them
  into words, traverse them — is now pinned, axiom-free machinery. The cabinet is the driver
  that does these in sequence forever (C8, the quine).
- Twenty-eight autonomous stages (119–146). Ranking: (1) **C8, the driver quine**: design
  target D with D consuming one pile item, performing the three synthesis fires plus its own
  re-emergence; scDup's self-application and the duplication-provides-copies observation are
  the raw material; probe with designed spines as in Stage 145 but with the CORRECT cell
  target this time. (2) The end-to-end generation-2 demo (chain scQWord traversal into
  synthesis of a next word, hand-driven — no quine needed, shows two full generations as a
  Steps theorem). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 147: the spurious twelve hundred

- The day's lesson is the first probe: 1,212 hits, every one an artifact of a target the
  START state satisfies. Caught within minutes by extracting a witness path (length one,
  from an internal junk fire). Rule for the catalogue, fourth of the run and bluntest:
  BEFORE celebrating a reachability hit, check the origin against the target predicate.
- The corrected zero is itself a finding: the naive fold-at-the-end dies on arm junk, not on
  nesting (Stage 146 solved nesting). The two spent arms are non-erasable and sit exactly
  where the synthesis prefab must stand. The co-design insight — make the ARM carry the
  prefab — turns the barrier into the candidate mechanism, and gives C8 a concrete search
  space instead of a slogan.
- Twenty-nine autonomous stages (119–147). The fold ledger after two days: read ✓ branch ✓
  drop ✓ mint ✓ chain ✓ protocol ✓; re-erection blocked by arm junk; C8 = co-design of
  (cell constant, arms, end-marker) with self-regeneration.
- Ranking: (1) **C8 co-design probe**: parameterize the cell's embedded constant and the arm
  shape together (the seven-fire protocol re-verified per candidate), search for pairs whose
  end-state puts prefab adjacent to wrapper. (2) Floor asymptotics at n=10. (3) The
  aperiodic diverger's anatomy.

## 2026-08-03 — Stage 148: biodegradable

- The probe's best row read like a misprint: end members ['W2', 'W1'] and nothing else. It
  took a minute to trust it — conservation, not magic: fifteen leaves in, twelve C-fires,
  three leaves out. The design principle deserves its name: BIODEGRADABLE MACHINERY — make
  every auxiliary part out of C, and the calculus's own conservation law is the garbage
  collector. Five-fire protocol, first-build green, all axiom-free.
- FIFO fell out for free. The queue order that tag systems demand — the thing the LIFO-pile
  analysis of Stages 113-122 treated as a deep obstacle — is just what the biodegradable
  protocol produces naturally. Two of the run's three standing architectural walls (arm
  junk, queue order) were artifacts of the scDup-era design.
- Thirty autonomous stages (119–148). The fold campaign across three days: production one
  fire (144), accumulation three fires (146), traversal five fires with zero residue and
  FIFO (here). C8 has shrunk from 'the quine problem' to 'wire the re-erection's accumulator
  and re-arm the driver from E W₂ W₁'.
- Ranking: (1) **C8 endgame**: from `E W₂ W₁`, co-design E to erect a WORKING next word
  (accumulator = fresh end marker, not junk) and re-arm — probe first, the target this time
  checked against the origin. (2) The full biodegradable word layer (n-cell zero-residue
  traversal, by induction — cheap and pinnable). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 149: what the fire eats

- The n-cell theorem is a two-line induction on top of Stage 148's pieces, and its
  hypothesis IS the finding: the traversal is a furnace that eats its own leading word. The
  probe's completion pattern (B at every consumed position) predicted the theorem's exact
  statement before it was written — the verify-before-formalize loop at its tightest.
- Thirty-one autonomous stages (119–149). The fold campaign's remaining alternatives are
  now two: information-bearing fuel, or read-before-burn composition. Both are concrete
  probe targets.
- Ranking: (1) **information-bearing fuel probe**: do the two clean fuels (C (C (C C)),
  C (C C) C) leave DIFFERENT traces anywhere (path, intermediate states, end-state
  side-effects) that a downstream gadget could dispatch on? If yes, the furnace reads as it
  burns. (2) Read-before-burn: compose scWord dispatch with biodegradable fold. (3) Floor
  asymptotics at n=10.

## 2026-08-03 — Stage 150: the furnace reads nothing

- A crisp negative with a crisp proof: two protocol lemmas whose conclusions are literally
  identical terms. The five-fire and seven-fire burns converging bitwise is the cleanest
  statement of information death the thread has produced — and it redirects C8 to the one
  design that never burns unread data.
- Thirty-two autonomous stages (119–150). The composition now on the bench: dispatch mints,
  pile chains, furnace cleans. Three proven layers, one wiring diagram.
- Ranking: (1) **the one-symbol generation loop**: wire dispatch-time minting for a
  single-symbol word — design the acting arm to mint and relaunch; probe, then formalize;
  this is the tag Simulation's induction step in miniature. (2) The chaining phase demo
  (pile of two minted cells → queue word, hand-driven). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 151: the loop was a cycle all along

- Searched for the read-before-burn composition and found the calculus had already built it:
  the one-symbol self-tag's generation loop is a five-fire cycle, and the pieces (word cell,
  scDup arms, end marker) are exactly the Stage-107 stack — with the end marker doubling as
  the continuation program. Two design campaigns (biodegradable, read-before-burn) and the
  trivial case was sitting in the cycle zoo the whole time.
- The reframe matters more than the instance: cycles-as-generations retroactively explains
  why the cycle classification kept finding SELF-REGENERATING structure (the w-cycle's
  "payload regeneration" reading, Stage 99). And it names the non-trivial C8 target: a
  generation SPIRAL — bit-identical return generalized to return-with-growth, which is the
  glider's shape carrying data.
- Thirty-three autonomous stages (119–151). All of today's five theorems axiom-free.
- Ranking: (1) **the two-symbol generation loop**: tag {b ↦ [b]} on words of length 2
  (bb → bb: still a cycle, but the loop must thread TWO cells — tests whether the five-fire
  pattern composes) — probe for the cycle, formalize if found. (2) The growth spiral
  ({b ↦ [b,b]}: word doubles per generation — the undecidability route's engine). (3) Floor
  asymptotics at n=10.

## 2026-08-03 — Stage 152: pop, then pulse

- The two-symbol "failure" turned into the family's complete dynamics in one sitting: pop
  until empty, pulse forever, all pinned. The attractor theorem is a three-line induction
  because Stage 107's scRun_step was already the pop — the run keeps discovering that its
  old gadgets were halves of newer theorems.
- The C8 statement after today's four stages is the sharpest it has ever been: a marker
  whose rebuild consumes the pile as construction material rather than fuel. One sentence,
  every term in it a pinned concept.
- Thirty-four autonomous stages (119–152); today alone: C7 refuted, queue cell, biodegradable
  layer, fuel law, fuel blindness, generation cycle, attractor — seven feat stages, all
  axiom-free.
- Ranking: (1) **the harvest-rebuilding marker**: the pile after a biodegradable run is
  E W₂ W₁ (clean, FIFO); design/search E whose action on W₂ W₁ is the three-nest chain
  (Stage 146) rather than the pulse — the search target is the queue-cell shape with W₂
  inside, checked against the origin. (2) Floor asymptotics at n=10. (3) The aperiodic
  diverger's anatomy.

## 2026-08-03 — Stage 153: the quine's address

- Six stages of triangulation (148–153) and C8 has an exact address: the marker must survive
  its own firing. Everything else — read, mint, chain, clean, rebuild — is a pinned,
  axiom-free theorem now. The searches keep converging on scDup as the almost-answer: it
  rebuilds, it pulses, it duplicates its operand into working positions; what it cannot do
  is put ITSELF back unchanged with a LARGER word around it.
- The tags-are-C-material observation may matter more than it looks: for tag words the
  accumulator "junk" dispatches, so the wrapper-duplicating rebuild is functional, not
  wasteful. The last wall may again be thinner than it reads.
- Thirty-five autonomous stages (119–153). Ranking: (1) **the marker quine, head-on**: the
  growth step needs E ⟶*-embedded-in-target; scDup's own regeneration trick (S t t x
  patterns rebuilding S t t) is the template — search S q q-shaped markers with q from a
  pool, target the exact growth config; widen depth. (2) If the quine resists: the SPIRAL
  variant (target config₂ with a DIFFERENT-but-equivalent marker — weaken exactness to
  behavioral equivalence via a second generation check). (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 154: four fires, one new cell, nothing lost

- The growth step exists, and its finder was the narrowest search of the campaign: one hit
  in 256, requiring marker = arms. Reading the four fires is like watching the whole
  hosting thread compressed: pop, duplicate, nest, re-erect. scQuine is scDup with one C
  pushed one level deeper — the almost-answers keep differing from answers by a single
  nesting.
- The iteration failure is now THE question. The base step restores everything, but the
  next round's traversal meets the new cell before the marker — growth and traversal
  interleave in the wrong order. The three-way co-design (cell constant × marker × arms) is
  the widest search yet and the campaign's pattern says walls fall exactly one widening
  after they're named.
- Thirty-six autonomous stages (119–154); today: nine feat stages, all axiom-free, C7
  registered and refuted, C8 chased from 'the quine problem' to 'make growth commute with
  traversal'.
- Ranking: (1) **the three-way co-design** (cell constant × marker × arms, iteration as the
  target: config-2 → config-3 with all three restored). (2) Floor asymptotics at n=10.
  (3) The aperiodic diverger's anatomy.

## 2026-08-03 — Stage 155: the arm is the program

- The failed iteration paid for itself: dissecting WHY the growth step will not compose
  produced the third protocol, and the third protocol is the first that moves information
  INWARD (contents become arms) instead of destroying it. One cell shape, three behaviors,
  chosen by what you hand it — the interrogation layer is programmable in exactly the way
  the fold needs.
- The probes' arithmetic regularities (closures 18/24/30/36; entries 4/10/16) were the tell
  that a generic law was underneath; the six-fire pop fell out of one symbolic replay. The
  whole Q-family is now: pop by sixes, pulse by fourteens — the third complete family
  description of the run (after scDup-words and biodegradable words).
- Thirty-seven autonomous stages (119–155). Today: eleven feat stages, every theorem
  axiom-free. C8's final form: arms that traverse as containers and arrive as copies.
- Ranking: (1) **the alternating-discipline probe**: arms of shape CC(scDup)? or scDup-in-
  cell — containers whose CONTENT is the regenerator — testing whether one wrapper level
  buys traversal-then-growth. (2) Pin the 14-cycle (mechanical, if wanted for the zoo).
  (3) Floor asymptotics at n=10.

## 2026-08-03 — Stage 156: the books don't balance

- The measurement that mattered was two integers: max tower depth 3 from below, 3 from
  above. The scQuine family is a closed world with a fourteen-beat heart, and the reason is
  an accounting identity: pops strip arm depth, growth restores it flat. One design object
  — the constructor — stands between the program and a hosted unbounded tag run.
- A probe-quality incident worth its line: the first depth probe had a contradictory guard
  and returned plausible-looking garbage; caught by a sanity assertion on a known tower.
  Fifth probe lesson of the run: every measurement function gets a sanity line before its
  first use.
- Thirty-eight autonomous stages (119–156). The C8 campaign stands at: three protocols, one
  gap, all instruments pinned.
- Ranking: (1) **pin the 14-cycle** (mechanical; completes the Q-family trilogy: pop law +
  descent + pulse). (2) Floor asymptotics at n=10 (census running in background). (3) The
  constructor search proper — multi-fire markers, widened pools — as the next campaign's
  opening.

## 2026-08-03 — Stage 157: the probe writes the proof

- The emitter (trace → appL-wrapped constructor chain) closes the tooling loop that opened
  with the glider: any concrete reduction the searches find is now one script away from a
  pinned theorem. The 14-cycle cost one paren.
- Thirty-nine autonomous stages (119–157). The cycle zoo now holds three pinned pulses (5,
  h/w-classified 3s, 14) and each is a hosted generation loop read.
- Ranking: (1) **harvest the n=10 floor census** (running). (2) The constructor search
  (next campaign: multi-fire markers). (3) The aperiodic diverger's anatomy.

## 2026-08-03 — Stage 158: it was a counter

- The slow burner stopped being a curiosity the moment the tower heights were laid beside
  √step: four checkpoints, four matches to within one unit. Five members forever, one tower
  growing — an eight-leaf term with registers. The aperiodicity that resisted the glider
  template is just what a counter looks like from the outside.
- Strategic note: the counter uses spine-level C-towers as data with a fixed member
  skeleton — the exact architecture the fold campaign set aside as 'undesigned'. The
  calculus has been running it natively all along. If inc/test/dec can be designed in this
  idiom, Minsky machines beat tag systems to the undecidability reduction.
- Forty autonomous stages (119–158). Ranking: (1) **harvest the n=10 census** (still
  running). (2) The counter idiom probe: can the counter's increment loop be STEERED (two
  towers, conditional on emptiness — the Minsky primitives) — search seeds near the slow
  burner. (3) The constructor search (tag idiom), now second in line behind the counter
  idiom.

## 2026-08-03 — Stage 159: one clock

- Eleven two-tower machines at eight leaves and every one beats to a single clock. The
  duplication that makes {S,C} grow is also what synchronizes it: copies are born equal.
  Independence — the register that waits — is exactly what no specimen shows.
- The convergence across idioms is the day's meta-finding: tag hosting lacks a marker that
  survives its own firing; register hosting lacks a test that spares its operand. Both are
  'read without consuming' — the calculus's non-erasure pushed to its sharpest point yet.
  Naming it: THE NONDESTRUCTIVE-READ PROBLEM, C8's true kernel.
- Forty-one autonomous stages (119–159). Ranking: (1) the review refresh (numbers 29 stages
  stale; the nondestructive-read reframe belongs in STATUS). (2) Harvest n=10 floor census +
  n=9 register sweep (both running). (3) The nondestructive-read design campaign, fresh.

## 2026-08-03 — Stage 160: the review

- Reviewed at 41 consecutive stages. The registry gains C7 (refuted, kept as a lesson) and
  C8 (the nondestructive-read problem — the campaign's residue stated as one primitive).
  The closing observation of the review: the program's two open questions may be one. A
  bounded-intermediates counterexample family needs sustained computation between small
  endpoints; sustained computation needs control; control needs nondestructive reads. If
  reads must destroy, computations must grow — which is what every mountain, glider, and
  counter this run has certified actually does.
- Ranking: (1) **harvest the running censuses** (n=10 floor; n=9 registers) when they land.
  (2) The nondestructive-read campaign: paper-first analysis of what 'test' means in a
  calculus where every fire consumes its redex — the h-cycle (which RESTORES its redex) is
  the obvious specimen to re-read. (3) Genericization/consolidation as breadth demands.

## 2026-08-03 — Stage 161: one bit, two machines

- The counter and a glider differ by one C. Sixty-six such pairs at eight leaves. The
  calculus is extraordinarily expressive per leaf — and the expressiveness is all spent at
  build time. Every behavior we can certify diverges from the seed, none from a runtime
  consultation. C8's final phrasing is now: a re-consultable bit.
- Forty-three autonomous stages (119–161). Three censuses still running in background (n=10
  floor, n=9 registers, n=9 conditionals); their harvests are future stages' floors and
  exhibits.
- Ranking: (1) **the re-consultable-bit design campaign** (paper-first: the cycle-restores-
  its-redex insight says the bit should LIVE ON A CYCLE whose phase the machine can sample;
  a tag-in-a-pulse). (2) Harvest censuses as they land. (3) Consolidation as breadth
  demands.
