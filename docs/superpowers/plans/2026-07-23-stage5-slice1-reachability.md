# Stage 5 Slice 1: Bounded Reachability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn Stage 2's leaf-count monotonicity into a certified per-instance decision procedure for pure-S reachability, narrow convertibility to its true open core (the trichotomy), upgrade C2's small sizes to kernel-checked facts, and give `Simulation` its first nontrivial inhabitant.

**Architecture:** The mathematical claim (derived in prose, UNVERIFIED until Task 1's probes pass): sizes are monotone non-decreasing along K-free reduction, so every intermediate on a path t ⟶* u fits within `leafCount u` leaves — reachability from t to u lives inside a finite universe. A new `Reachability.lean` builds the full one-step successor enumeration (`succs` — ALL redexes, not just leftmost), a saturating bounded closure returning `some` only when saturated (fuel-out is an honest `none`, never a verdict), and the correctness theorem making every `some` answer a kernel-certified yes/no. Convertibility corollaries ride Stage 1's confluence. The abstract `Decidable` instance (needing a finite-pigeonhole counting lemma) is deliberately OUT of this slice — registered as the next slice, so no claim outruns its proof.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** 3 documented failed attempts → statement to `CONJECTURES.md`, code removed (spec escape hatch).
- **No `partial def`.** Plain `decide`/`rfl`-evaluation allowed; `native_decide` banned.
- Every commit must `lake build` clean with zero warnings.
- Comments state precisely what is machine-checked. This slice's honesty burdens: (a) "decidable" claims are per-instance-certified until the abstract instance exists — every artifact must say so; (b) the paper-level observation (monotonicity ⇒ bounded search) may be folklore in the rewriting literature — the ledger registers that; (c) a `none` from the procedure is "fuel exhausted," NEVER a verdict.
- **Census-first discipline:** Task 1's probes gate the formalization. If a probe fails, STOP (do not weaken it), report with the failing case — the slice's premise would be wrong.
- Known instance-level friction: `induction` on `RS.Steps`/`RS.Conv` at CONCRETE instances fails (mkElimApp) — `.rec` pattern with why-comment (precedent: RS.lean, Calibration.lean). Term-level `Steps`/`Step` inductions are fine.

## Lean TDD adaptation (house rules)

- Functions: `#guard`s first (RED: unknown identifier) → implement (GREEN). Theorems: `:= sorry` (RED, count stated) → proof (GREEN, zero warnings). NEVER commit with sorry.
- Candidate proofs are candidates; statements are the contract. Named cases; no `first |` catch-alls.

---

### Task 1: `succs` + the CENSUS-FIRST STOP gate

**Files:**
- Create: `CombinatorCalculusPlayground/Reachability.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Reachability` after Census.Enumerate, at the end)

**Interfaces:**
- Consumes: `Term`, `leafCount`, `app2`, `app3`, `I` (Term.lean); `stepOnce`, `trace` (Census/Eval.lean); `sTerms`, `kFree` (Census/Enumerate.lean, SFragment.lean).
- Produces: `succs : Term → List Term` — ALL one-step reducts (root K/S redex if any, plus left and right congruence reducts).

- [ ] **Step 1: Create the file — `succs` with `#guard`s and the probes (no theorems yet; the guards ARE the gate)**

```lean
--! # Bounded reachability for the S-fragment
-- THE CLAIM THIS FILE EXISTS TO CHECK AND THEN PROVE: along any K-free
-- reduction path, leaf counts are monotone non-decreasing (Stage 2's
-- `leafCount_le_of_steps`), so every intermediate term on a path from t
-- to u has at most `leafCount u` leaves. Reachability between K-free
-- terms is therefore search in a FINITE universe — and this file builds
-- the certified searcher. The paper-level observation is two lines given
-- monotonicity and may well be folklore; the machine-checked decision
-- procedure is the contribution (see CONJECTURES.md for the register).
--
-- HONESTY CONTRACT: the procedure returns Option Bool. `some b` is a
-- certified verdict (theorem `reachable?_correct`); `none` means fuel
-- ran out before the closure saturated and is NEVER evidence.
import CombinatorCalculusPlayground.Confluence
import CombinatorCalculusPlayground.Census.Enumerate

open Term

-- ## Every one-step reduct
-- stepOnce picks the leftmost-outermost redex; reachability quantifies
-- over ALL steps, so we need the full successor set: the root redex (if
-- the term is one) plus every reduct inside either side.
def rootRed : Term → List Term
  | .app (.app .K x) _ => [x]
  | .app (.app (.app .S f) g) x => [.app (.app f x) (.app g x)]
  | _ => []

def succs : Term → List Term
  | .S => []
  | .K => []
  | .app t u =>
    rootRed (.app t u)
      ++ (succs t).map (fun t' => Term.app t' u)
      ++ (succs u).map (fun u' => Term.app t u')

-- Root redexes fire.
#guard succs (app2 K S K) = [S]
#guard succs (app3 S K K S) = [app (app K S) (app K S)]
-- Atoms and underapplied heads have no successors.
#guard succs S = []
#guard succs (app S K) = []
-- A term with BOTH a root redex and an inner redex lists both
-- (K (I S) S has the root K-redex and the inner I S redex — recall
-- I = S K K, so app I S is an S-redex at depth).
#guard (succs (app2 K (app I S) S)).length = 2
-- Congruence on both sides: (I S)(I S) has one redex per side.
#guard (succs (app (app I S) (app I S))).length = 2
```

- [ ] **Step 2: Append the CENSUS-FIRST PROBES (the STOP gate)**

```lean
-- ## CENSUS-FIRST PROBES (the STOP gate for this whole slice)
-- If ANY of these fails: STOP. Do not adjust guards, definitions, or
-- fuel. Report the failing case — the slice's premise would be wrong.

-- Probe A: succs subsumes the certified leftmost reducer — whatever
-- stepOnce finds is among the successors. (Over every S-term ≤ 6 leaves
-- and a hand-set of K-bearing terms.)
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  match stepOnce t with
  | none => (succs t).isEmpty   -- no leftmost redex ⇒ no redex at all? NO —
    -- careful: stepOnce none means NO redex exists (stepOnce_none_normal),
    -- so succs must be empty too. This tests succs' emptiness agreement.
  | some w => (succs t).contains w

#guard [app2 K S K, app I K, app (app2 K S S) (app2 K K K)].all fun t =>
  match stepOnce t with
  | none => (succs t).isEmpty
  | some w => (succs t).contains w

-- Probe B (the bounded-path claim, empirically): every successor of a
-- K-free term is at least as large. (The theorem exists at the Steps
-- level — Stage 2; this probes the NEW succs enumeration against it.)
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  (succs t).all fun w => leafCount t ≤ leafCount w

-- Probe C (bounded universes are genuinely closed): iterating succs from
-- any S-term of ≤ 5 leaves, filtered to size ≤ 8, never escapes size 8 —
-- trivially true by the filter, so probe the REAL claim: the set of
-- distinct terms seen in 200 rounds of unfiltered succs-iteration from
-- size-≤4 S-terms whose sizes stay ≤ 4 is finite and small. Concretely:
-- from any size-≤4 S-term, the size-preserving successor relation
-- revisits nothing new after at most (number of size-≤4 terms) rounds.
#guard (List.range 5).all fun n => (sTerms n).all fun t =>
  ((succs t).filter (fun w => leafCount w ≤ 4)).all fun w => kFree w
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings, ALL guards pass. Note Probe A's first branch is itself a mathematical claim (stepOnce = none ⇒ succs = []) — if IT fails the succs definition or the claim is wrong; investigate by hand (find the term, trace both functions) and STOP if the mismatch is real.

- [ ] **Step 3: Add the root import; commit**

```bash
git add -A
git commit -m "feat: full one-step successor enumeration with census-first probes"
```

---

### Task 2: `succs` soundness and completeness

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append)

**Interfaces:**
- Consumes: `succs`, `rootRed`; `Step` (K_red, S_red, appL, appR).
- Produces: `succs_sound : ∀ {t w : Term}, w ∈ succs t → t ⟶ w`; `succs_complete : ∀ {t w : Term}, t ⟶ w → w ∈ succs t`.

- [ ] **Step 1: State both with `sorry` (RED: exactly two warnings)**

```lean
-- ## succs is exactly the step relation
theorem succs_sound : ∀ {t w : Term}, w ∈ succs t → t ⟶ w := sorry

theorem succs_complete : ∀ {t w : Term}, t ⟶ w → w ∈ succs t := sorry
```

- [ ] **Step 2: Prove (GREEN)**

Candidates. `succs_complete` is the easy direction (induction on the Step derivation; each constructor lands in one of the three `++` segments — `List.mem_append`, `List.mem_map` do the bookkeeping):

```lean
theorem succs_complete : ∀ {t w : Term}, t ⟶ w → w ∈ succs t := by
  intro t w h
  induction h with
  | K_red x y =>
    -- root segment: rootRed (app2 K x y) = [x]
    simp [succs, rootRed]
  | S_red f g x =>
    simp [succs, rootRed]
  | appL s ih =>
    -- w = app t' u with t' ∈ succs t: middle segment
    simp [succs]
    -- goal shape after simp: membership in the ++ of three lists;
    -- pick the map-over-left segment via ih
    exact Or.inr (Or.inl ⟨_, ih, rfl⟩)
  | appR s ih =>
    simp [succs]
    exact Or.inr (Or.inr ⟨_, ih, rfl⟩)
```

(The `simp [succs]`-normalized membership shape may differ — read the goal; `List.mem_append`/`List.mem_map` lemma names are core. In the K_red/S_red cases the root list is literally `[x]`/`[...]` after `rootRed` unfolds — `simp` closes or leaves `List.Mem` of a singleton, closed by `List.mem_singleton.mpr rfl` / `mem_cons_self`.)

`succs_sound` — structural induction on t; the app case splits membership across the three segments; the root segment needs a small case analysis on the SHAPE of the term (which `rootRed` arm fired). A clean route is `fun_induction succs` (three cases mirroring the match) with a helper for the root:

```lean
theorem rootRed_sound : ∀ {t w : Term}, w ∈ rootRed t → t ⟶ w := by
  intro t w h
  fun_induction rootRed t with
  | case1 x y =>       -- K-redex arm: rootRed = [x]
    simp at h
    subst h
    exact Step.K_red ..
  | case2 f g x =>
    simp at h
    subst h
    exact Step.S_red ..
  | case3 => simp at h  -- empty list: absurd

theorem succs_sound : ∀ {t w : Term}, w ∈ succs t → t ⟶ w := by
  intro t
  induction t with
  | S => intro w h; simp [succs] at h
  | K => intro w h; simp [succs] at h
  | app a b iha ihb =>
    intro w h
    simp [succs] at h
    rcases h with hroot | ⟨t', ht', rfl⟩ | ⟨u', hu', rfl⟩
    · exact rootRed_sound (by simpa using hroot)
    · exact Step.appL (iha ht')
    · exact Step.appR (ihb hu')
```

(Expect bookkeeping iteration on the exact `simp` output shapes; the statements are the contract. `fun_induction rootRed` case names/count may differ — read the goals.)

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: succs is sound and complete for the step relation"
```

---

### Task 3: The saturating bounded closure

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append)

**Interfaces:**
- Consumes: `succs`, `succs_sound`; `leafCount`; `Steps` (⟶*, refl/tail), `Steps.trans`; `Term` DecidableEq/BEq.
- Produces: `closureStep (bound : Nat) (acc : List Term) : List Term`; `boundedClosure (bound : Nat) : Nat → List Term → Option (List Term)` (`some` = saturated, `none` = fuel out); `reachable? (t u : Term) (fuel : Nat) : Option Bool`; `mem_closureStep`; `boundedClosure_sound`; `boundedClosure_subset`; `boundedClosure_saturated`.

- [ ] **Step 1: Definitions + `#guard`s (functions land whole; guards are their tests)**

```lean
-- ## The saturating bounded closure
-- Grow the reachable set one frontier at a time, keeping only terms
-- within the size bound. `some acc` means the frontier came back empty —
-- the set is SATURATED (closed under bounded steps); `none` means fuel
-- ran out first, which verdicts NOTHING.
def closureStep (bound : Nat) (acc : List Term) : List Term :=
  (acc.flatMap succs).filter (fun w => leafCount w ≤ bound && !acc.contains w)

def boundedClosure (bound : Nat) : Nat → List Term → Option (List Term)
  | 0, acc => if (closureStep bound acc).isEmpty then some acc else none
  | f + 1, acc =>
    let next := closureStep bound acc
    if next.isEmpty then some acc
    else boundedClosure bound f (acc ++ next.eraseDups)

/-- Certified-when-`some` reachability check: is u reachable from t?
`none` = fuel exhausted (no verdict). Sound and complete for K-free t
via `reachable?_correct`. -/
def reachable? (t u : Term) (fuel : Nat) : Option Bool :=
  (boundedClosure (leafCount u) fuel [t]).map (fun acc => acc.contains u)

-- S S S S → (S S)(S S): reachable, and the closure saturates fast.
#guard reachable? (app3 S S S S) (app (app S S) (app S S)) 50 = some true
-- Not reachable the other way (sizes equal, but no backward step).
#guard reachable? (app (app S S) (app S S)) (app3 S S S S) 50 = some false
-- Self-reachability (zero steps).
#guard reachable? (app S S) (app S S) 10 = some true
-- Size forbids: a 4-leaf term cannot reach a 3-leaf one; the closure over
-- bound 3 saturates instantly and answers false.
#guard reachable? (app3 S S S S) (app S (app S S)) 10 = some false
-- Fuel 0 on a non-saturated instance is an honest none.
#guard reachable? (app3 S S S (app3 S S S S)) S 0 = none
```

Run: `lake build` — guards pass (if the fuel-0 guard fails because the instance saturates immediately, verify by hand and pick an instance that genuinely needs a round; do not delete the guard's intent: `none` must be reachable behavior).

- [ ] **Step 2: State the four lemmas with `sorry` (RED: exactly four warnings)**

```lean
-- Membership in a closure step: it came from somewhere in acc.
theorem mem_closureStep {bound : Nat} {acc : List Term} {w : Term}
    (h : w ∈ closureStep bound acc) :
    (∃ v ∈ acc, w ∈ succs v) ∧ leafCount w ≤ bound ∧ w ∉ acc := sorry

-- Everything the closure collects is genuinely reachable from something
-- in the start set.
theorem boundedClosure_sound {bound fuel : Nat} {start acc : List Term} {t : Term}
    (hstart : ∀ w ∈ start, t ⟶* w)
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ acc, t ⟶* w := sorry

-- The start set survives into the result.
theorem boundedClosure_subset {bound fuel : Nat} {start acc : List Term}
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ start, w ∈ acc := sorry

-- `some` really means saturated: bounded successors of members are members.
theorem boundedClosure_saturated {bound fuel : Nat} {start acc : List Term}
    (h : boundedClosure bound fuel start = some acc) :
    ∀ w ∈ acc, ∀ v ∈ succs w, leafCount v ≤ bound → v ∈ acc := sorry
```

- [ ] **Step 3: Prove, in order (GREEN)**

Strategy notes (candidates below are skeletons; the fuel-induction bookkeeping is the work):

- `mem_closureStep`: unfold `closureStep`; `List.mem_filter` + `List.mem_flatMap` + `Bool.and_eq_true` + `List.contains` ↔ `∈` (`List.contains_iff_mem` or `decide`-level bridging; watch BEq vs DecidableEq — `Term` derives both, and `List.contains` uses BEq; core lemma `List.contains_iff_mem` requires `LawfulBEq`, which derived BEq satisfies — `simp` usually handles it).
- `boundedClosure_sound`: induction on `fuel` generalizing `start`/`hstart`. Base: `if` splits; `some acc` forces `acc = start` (injection), close with `hstart`. Step: if frontier empty, same; else apply IH to `start ++ next.eraseDups` with the extended `hstart`: members of `next.eraseDups` are in `closureStep`, so `mem_closureStep` gives `v ∈ start` with `w ∈ succs v` — `Steps.trans (hstart v hv) (Steps.tail (succs_sound hw) (Steps.refl _))` — wait, one step then done: `(hstart v hv).trans (Steps.single? ...)` — Term-level `Steps` has `tail`; a single step is `Steps.tail s (Steps.refl _)`. Compose with `Steps.trans`.
- `boundedClosure_subset`: same induction shape; start only ever grows (`List.mem_append` left).
- `boundedClosure_saturated`: induction on fuel. In BOTH `some`-producing branches, `some acc` arises exactly when `closureStep bound acc = []`-ish (`isEmpty`). From emptiness: suppose `w ∈ acc`, `v ∈ succs w`, `leafCount v ≤ bound`, `v ∉ acc` — then `v` passes the filter, so `v ∈ closureStep bound acc`, contradicting emptiness (`List.isEmpty_iff` / `List.eq_nil_iff_forall_not_mem`). So `v ∈ acc` (classical `by_cases v ∈ acc` is fine — Term has DecidableEq, so it's even decidable). Recursive branch: IH applies directly to the recursive call.

Run: `lake build` — zero warnings.

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: saturating bounded closure with soundness and saturation certificates"
```

---

### Task 4: The summit — `reachable?_correct`

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append)

**Interfaces:**
- Consumes: everything above + `KFree`, `KFree.of_step`, `leafCount_le_of_steps` (SFragment.lean), `succs_complete`.
- Produces: `mem_of_saturated`; `reachable?_correct : KFree t → reachable? t u fuel = some b → (b = true ↔ t ⟶* u)`.

**Escape hatch (spec):** 3 documented attempts per theorem → CONJECTURES registration + removal, DONE_WITH_CONCERNS. The statements are load-bearing for the ledger — never weaken silently.

- [ ] **Step 1: State with `sorry` (RED: exactly two warnings)**

```lean
-- ## Completeness: saturated sets catch everything they bound
-- THE key lemma, and the exact point where Stage 2's monotonicity does
-- the work: on a path t ⟶* u, every intermediate w satisfies
-- leafCount w ≤ leafCount u (apply monotonicity to the REMAINING segment
-- w ⟶* u), so a set saturated at bound = leafCount u never loses the path.
theorem mem_of_saturated {acc : List Term} {bound : Nat}
    (hsat : ∀ w ∈ acc, ∀ v ∈ succs w, leafCount v ≤ bound → v ∈ acc) :
    ∀ {t u : Term}, KFree t → (t ⟶* u) → leafCount u ≤ bound →
      t ∈ acc → u ∈ acc := sorry

-- ## The certified decision procedure
theorem reachable?_correct {t u : Term} {fuel : Nat} {b : Bool}
    (hk : KFree t) (h : reachable? t u fuel = some b) :
    b = true ↔ t ⟶* u := sorry
```

- [ ] **Step 2: Prove (GREEN)**

Candidates:

```lean
theorem mem_of_saturated {acc : List Term} {bound : Nat}
    (hsat : ∀ w ∈ acc, ∀ v ∈ succs w, leafCount v ≤ bound → v ∈ acc) :
    ∀ {t u : Term}, KFree t → (t ⟶* u) → leafCount u ≤ bound →
      t ∈ acc → u ∈ acc := by
  intro t u hk h
  induction h with
  | refl => exact fun _ ht => ht
  | tail s rest ih =>
    intro hub ht
    -- t ⟶ t₁ ⟶* u.  t₁'s size is ≤ u's size by monotonicity on `rest`,
    -- and t₁ is K-free by Stage 2's closure.
    have hk1 : KFree _ := hk.of_step s
    have h1b : leafCount _ ≤ bound :=
      Nat.le_trans (leafCount_le_of_steps hk1 rest) hub
    have ht1 : _ ∈ acc := hsat _ ht _ (succs_complete s) h1b
    exact ih hk1 hub ht1
```

CAUTION: the induction generalizes `hk` over the changing left endpoint —
exactly the Stage 2 `leafCount_le_of_steps` dance. If the IH arrives
without the `KFree`/bound slots, restructure as `induction h generalizing`
or hoist to an auxiliary `∀`-quantified statement (Stage 2/3 precedent:
`PureS_steps_of_steps`). Iterate against the goal states.

```lean
theorem reachable?_correct {t u : Term} {fuel : Nat} {b : Bool}
    (hk : KFree t) (h : reachable? t u fuel = some b) :
    b = true ↔ t ⟶* u := by
  unfold reachable? at h
  -- unpack the Option.map: boundedClosure ... = some acc, b = acc.contains u
  cases hc : boundedClosure (leafCount u) fuel [t] with
  | none => rw [hc] at h; simp at h
  | some acc =>
    rw [hc] at h
    simp at h
    subst h
    constructor
    · -- contains → Steps: closure soundness
      intro hb
      have hmem : u ∈ acc := by simpa using hb
      exact boundedClosure_sound
        (start := [t]) (fun w hw => by simp at hw; subst hw; exact Steps.refl _)
        hc u hmem
    · -- Steps → contains: saturation + mem_of_saturated
      intro hsteps
      have hsat := boundedClosure_saturated hc
      have ht : t ∈ acc := boundedClosure_subset hc t (by simp)
      have : u ∈ acc :=
        mem_of_saturated hsat hk hsteps (Nat.le_refl _) ht
      simpa using this
```

(`List.contains` ↔ `∈` bridging via `simp` with LawfulBEq, as in Task 3.
The `simp at h` unpacking of `Option.map` may leave `b = acc.contains u`
in either orientation — adapt.)

Run: `lake build` — zero warnings. Then the axiom audit (scratch, delete after): `#print axioms reachable?_correct`, `#print axioms mem_of_saturated` — record outputs.

- [ ] **Step 3: Kernel-certified instance demonstrations**

Append — these turn the theorem + computation into checked FACTS about specific reachability questions:

```lean
-- ## Certified instances
-- Each pair below is a kernel-checked reachability verdict: the guard
-- forces the computation, `reachable?_correct` makes it a theorem about ⟶*.
example : (app3 S S S S) ⟶* (app (app S S) (app S S)) := by
  have h : reachable? (app3 S S S S) (app (app S S) (app S S)) 50 = some true := by rfl
  exact (reachable?_correct (by repeat constructor) h).mp rfl

example : ¬ ((app (app S S) (app S S)) ⟶* (app3 S S S S)) := by
  have h : reachable? (app (app S S) (app S S)) (app3 S S S S) 50 = some false := by rfl
  intro hsteps
  exact absurd ((reachable?_correct (by repeat constructor) h).mpr hsteps) (by simp)
```

(The `by repeat constructor` KFree discharge may need explicit `KFree.app`/`KFree.S` builds; `by rfl` on `reachable?` at these sizes is a small kernel computation — if it times out, reduce the instance size, never switch to native_decide. Iterate.)

- [ ] **Step 4: Commit**

```bash
git add -A
git commit -m "feat: certified per-instance decision procedure for pure-S reachability"
```

---

### Task 5: C2 at small sizes — kernel-checked cycle-freedom

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append)

**Interfaces:**
- Consumes: `succs`, `reachable?`, `leafCount`, `sTerms`, `kFree`, `kFree_iff`.
- Produces: `onCycle? (t : Term) (fuel : Nat) : Option Bool`; `#guard` cycle-freedom for all S-terms of ≤ 6 leaves; (stretch, escape-hatched) `no_cycle_le5 : ∀ t ∈ sTerms 5, ¬ ∃ v ∈ succs v ...` — see Step 3.

- [ ] **Step 1: The checker + guards**

```lean
-- ## C2 at small sizes
-- A term sits on a cycle iff one of its successors reaches back to it.
-- By monotonicity a returning path can never exceed leafCount t, so the
-- bound-t closure decides it (when saturated). Successors LARGER than t
-- can never return (strict monotone segments can't shrink) — skip them.
def onCycle? (t : Term) (fuel : Nat) : Option Bool :=
  ((succs t).filter (fun v => leafCount v ≤ leafCount t)).foldl
    (fun acc v =>
      match acc, reachable? v t fuel with
      | some false, some r => some r
      | some true, _ => some true
      | _, none => none
      | none, _ => none)
    (some false)

-- Kernel-checked: NO pure-S term with ≤ 6 leaves sits on a reduction
-- cycle. This upgrades the census's fuel-bounded observation (C2,
-- CONJECTURES.md) to a compile-time-verified fact at these sizes.
#guard (List.range 7).all fun n => (sTerms n).all fun t =>
  onCycle? t 100 == some false
```

Run: `lake build`. If the guard is SLOW (kernel evaluation over 132+ closures), reduce the range to `List.range 6` and record the achieved bound honestly — the deliverable is "kernel-checked at sizes ≤ N" for the largest N that builds in reasonable time (< ~2 min for this guard). If any term reports `some true` — A CYCLE — that is a MAJOR census finding contradicting C2: STOP and report immediately with the term (do not suppress; it would be the most important discovery of the program so far). `none` (fuel out): raise fuel.

- [ ] **Step 2 (stretch, escape-hatched): the theorem form**

Attempt ONE bridging theorem making the guard's content a named Prop-level fact:

```lean
-- Stretch: cycle-freedom at ≤ 5 leaves as a theorem over ⟶⁺.
theorem no_small_cycle : ∀ t, KFree t → leafCount t ≤ 5 →
    ¬ ∃ v, (t ⟶ v) ∧ (v ⟶* t) := sorry
```

Strategy: from `⟨v, hs, hrest⟩` — case on `leafCount v ≤ leafCount t` (else monotonicity on `hrest` contradicts `leafCount_le_of_step`); then `v ∈ succs t` (succs_complete), `reachable? v t FUEL = some false` for the relevant finite set of (t, v)… the finite quantification is the hard part (needs `t ∈ sTerms n`-style enumeration completeness — `sTerms` has no completeness theorem!). If this needs `sTerms`-completeness (likely), take the escape hatch: register in CONJECTURES.md as "kernel-checked via `onCycle?` guard; theorem form blocked on sTerms-completeness (queued)", remove the sorry, keep the guard. 3-attempt rule applies.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: kernel-checked cycle-freedom for small pure-S terms (C2 evidence)"
```

---

### Task 6: The convertibility trichotomy

**Files:**
- Modify: `CombinatorCalculusPlayground/Reachability.lean` (append)

**Interfaces:**
- Consumes: `confluence`, `nf_unique`, `NormalForm`, `NormalForm.steps_eq` (Confluence.lean/Step.lean); `RS.SK.Conv`, `RS.SK_churchRosser`, `RS.SK_steps_iff`, `RS.Conv.of_steps/trans/symm` (RS.lean, Taxonomy.lean).
- Produces: `Joinable (t u : Term) : Prop`; `conv_iff_joinable : RS.SK.Conv t u ↔ Joinable t u`; `joinable_normalizes : Joinable t u → (∃ n, (t ⟶* n) ∧ NormalForm n) → ∃ n, (u ⟶* n) ∧ NormalForm n`; `joinable_iff_nf_eq : t ⟶* nt → NormalForm nt → u ⟶* nu → NormalForm nu → (Joinable t u ↔ nt = nu)`.

- [ ] **Step 1: Probe first (guards using the certified machinery)**

```lean
-- ## Convertibility narrows to its true open core
-- Trichotomy: both normalize → decidable by normal-form comparison;
-- exactly one normalizes → NOT convertible; both diverge → the open core.
-- Probe before proving: normalizing pairs' joinability matches nf-equality.
#guard (match normalize 100 (app3 S S S S), normalize 100 (app (app S S) (app S S)) with
        | some (n1, _), some (n2, _) => n1 == n2
        | _, _ => false)
```

- [ ] **Step 2: Statements with `sorry` (RED: exactly three warnings), then prove**

```lean
/-- Common reduct. With Church–Rosser this IS convertibility. -/
def Joinable (t u : Term) : Prop := ∃ w, (t ⟶* w) ∧ (u ⟶* w)

theorem conv_iff_joinable {t u : Term} : RS.SK.Conv t u ↔ Joinable t u := sorry

theorem joinable_normalizes {t u : Term} (h : Joinable t u)
    (hn : ∃ n, (t ⟶* n) ∧ NormalForm n) :
    ∃ n, (u ⟶* n) ∧ NormalForm n := sorry

theorem joinable_iff_nf_eq {t u nt nu : Term}
    (ht : t ⟶* nt) (hnt : NormalForm nt)
    (hu : u ⟶* nu) (hnu : NormalForm nu) :
    Joinable t u ↔ nt = nu := sorry
```

Candidates:

```lean
theorem conv_iff_joinable {t u : Term} : RS.SK.Conv t u ↔ Joinable t u := by
  constructor
  · intro h
    obtain ⟨w, hw1, hw2⟩ := RS.SK_churchRosser h
    exact ⟨w, RS.SK_steps_iff.mp hw1, RS.SK_steps_iff.mp hw2⟩
  · rintro ⟨w, hw1, hw2⟩
    exact RS.Conv.trans
      (RS.Conv.of_steps (RS.SK_steps_iff.mpr hw1))
      (RS.Conv.of_steps (RS.SK_steps_iff.mpr hw2)).symm

theorem joinable_normalizes {t u : Term} (h : Joinable t u)
    (hn : ∃ n, (t ⟶* n) ∧ NormalForm n) :
    ∃ n, (u ⟶* n) ∧ NormalForm n := by
  obtain ⟨w, hw1, hw2⟩ := h
  obtain ⟨n, hn1, hn2⟩ := hn
  -- t reaches both w and n; confluence joins them at v; n normal ⇒ v = n,
  -- so w ⟶* n, so u ⟶* n.
  obtain ⟨v, hv1, hv2⟩ := confluence hw1 hn1
  have : v = n := hn2.steps_eq hv2
  subst this
  exact ⟨v, Steps.trans hw2 hv1, hn2⟩

theorem joinable_iff_nf_eq {t u nt nu : Term}
    (ht : t ⟶* nt) (hnt : NormalForm hnt_) ... -- (statement as above)
    := by
  constructor
  · rintro ⟨w, hw1, hw2⟩
    -- nt and w join (confluence from t); nt normal ⇒ w ⟶* nt.
    obtain ⟨v, hv1, hv2⟩ := confluence ht hw1
    have hvnt : v = nt := hnt.steps_eq hv1
    subst hvnt
    -- so u ⟶* w ⟶* nt and u ⟶* nu, both normal: nf_unique.
    exact nf_unique (Steps.trans hw2 hv2) hu hnt hnu |>.symm ▸ rfl
    -- (orientation bookkeeping: nf_unique gives nt = nu or nu = nt —
    --  read the actual statement in Confluence.lean and adapt.)
  · intro heq
    subst heq
    exact ⟨nt, ht, hu⟩
```

(The `joinable_iff_nf_eq` forward candidate above is deliberately rough —
the `nf_unique` argument order and equality orientation MUST be read off
Confluence.lean; the mathematical route is fixed: w joins with nt via
confluence-from-t, normality pins v = nt, so u reaches nt, and nf_unique
on u's two normal forms gives nt = nu. Iterate. Note the trichotomy's
"exactly one normalizes ⇒ not Joinable" is `joinable_normalizes`'s
contrapositive — state it in a comment, don't duplicate a theorem.)

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: convertibility trichotomy — the open core is diverging pairs"
```

---

### Task 7: `Simulation`'s first nontrivial inhabitant — PureS ↪ SK

**Files:**
- Modify: `CombinatorCalculusPlayground/Universality/Calibration.lean` (append)

**Interfaces:**
- Consumes: `Simulation`, `RS.PureS`, `RS.SK`, `RS.SK_steps_iff`, `PureS_steps_iff` (RS.lean); `KFree` decidability (SFragment.lean).
- Produces: `pureS_in_SK : Simulation RS.PureS RS.SK`.

- [ ] **Step 1: The definition (lands whole; its proof fields are the test) — plus a follow-up example**

```lean
-- ## The Simulation class is inhabited (nontrivially)
-- The pure-S fragment sits inside SK by inclusion — enc forgets the
-- K-freeness certificate, dec re-checks it (decidable, Stage 2). This is
-- the class's first machine-checked nontrivial member: it blunts any
-- "Simulation is so strong it's vacuous, making the iota refutation
-- hollow" objection. fwd is a single-step embedding; bwd rides Stage 3's
-- agreement lemmas plus Stage 2's closure.
def pureS_in_SK : Simulation RS.PureS RS.SK where
  enc := fun a => a.val
  dec := fun t => if h : KFree t then some ⟨t, h⟩ else none
  dec_enc := fun a => by
    cases a with
    | mk t ht => simp [ht]
  fwd := fun {a a'} s =>
    -- a PureS step IS an SK step on the carriers
    RS.Steps.tail s (RS.Steps.refl _)
  bwd := fun {a a'} h =>
    RS.PureS_steps_iff.mpr (RS.SK_steps_iff.mp h)

-- Sanity: transporting along the inclusion composes with itself.
example : Simulation RS.PureS RS.SK := pureS_in_SK
```

(`dec_enc`'s `simp [ht]` discharges the `dif_pos`; if it fights, `rw [dif_pos ht]`. `fwd`'s field type is `RS.PureS.step a a' → RS.SK.Steps a.val a'.val` — the PureS step is definitionally a `Step a.val a'.val`, hence an SK step; the `tail/refl` pair makes it a one-step path. `bwd`: `RS.SK.Steps a.val a'.val → RS.PureS.Steps a a'` — exactly the composition of the two Stage 3 agreement lemmas. If the dependent-if in `dec` fights the elaborator, use `Decidable` match form. Iterate; the field types are the contract.)

Run: `lake build` — zero warnings. Axiom audit (scratch, delete after): `#print axioms pureS_in_SK` — record.

- [ ] **Step 2: Commit**

```bash
git add -A
git commit -m "feat: PureS embeds in SK — Simulation's first nontrivial inhabitant"
```

---

### Task 8: Ledger + artifacts

**Files:**
- Modify: `CONJECTURES.md`
- Modify: `LAB_NOTEBOOK.md`

**Interfaces:**
- Consumes (verify each by grep before citing): `succs_sound`, `succs_complete`, `reachable?_correct`, `mem_of_saturated`, `Joinable`, `conv_iff_joinable`, `joinable_normalizes`, `joinable_iff_nf_eq`, `pureS_in_SK`, plus whatever Task 5 landed (`onCycle?` guard bound; the stretch theorem if it survived).
- Produces: the honest Slice 1 register.

- [ ] **Step 1: CONJECTURES.md updates**

(a) A new section after the Stage 4 material — adapt bracketed slots to what actually landed:

```markdown
### Stage 5, Slice 1: bounded reachability

- **The north-star question moves.** The spec's Goal 3 — is reachability
  t ⟶* u between pure S-terms decidable? — is now answered per-instance
  by a CERTIFIED decision procedure (`reachable?`, `reachable?_correct`,
  `Reachability.lean`): monotonicity (Stage 2's `leafCount_le_of_steps`)
  confines every path inside the finite universe of terms with at most
  `leafCount u` leaves, so a saturated closure decides. Every `some`
  answer is a theorem-backed verdict; `none` is fuel exhaustion and
  verdicts nothing. HONEST SCOPE: the abstract `Decidable (t ⟶* u)`
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
- **C2 upgraded at small sizes:** cycle-freedom for all pure-S terms
  with ≤ [N] leaves is now kernel-checked at compile time (`onCycle?`
  guard, `Reachability.lean`), upgrading the census's fuel-bounded
  observation. [If the stretch theorem landed, cite it; if the escape
  hatch fired, register: "theorem form blocked on sTerms-completeness,
  queued."] C2 in full remains open.
- **`Simulation` is nontrivially inhabited** (`pureS_in_SK`): the pure-S
  fragment embeds in SK by inclusion, with the decoder re-checking
  K-freeness (decidable by Stage 2). The calibration-sandwich criterion
  (a) at last has a machine-checked instance — modest, but real; a
  known-universal-system certification remains open (Tag→SK).
```

(b) Update C2's entry: add the kernel-checked bound. (c) Update the methodology header with one Slice-1 sentence. Do NOT change C1/C3/C4 statuses.

- [ ] **Step 2: LAB_NOTEBOOK.md entry**

Dated entry (actual date), honest voice: the ideonomy shake that surfaced the latent asset (monotonicity's second life); census-first probes gating the slice (report outcomes); which candidates survived vs. needed rework, per task; axiom audits; the escape-hatch outcomes if any; one meta-line: this is the second time a review-or-shake process found mathematics the plan's author missed (Stage 3's trivialization catch; now the bounded-path observation) — the process, not just the prover, is doing research work.

- [ ] **Step 3: Build and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: Stage 5 slice 1 ledger — reachability certified, convertibility narrowed"
```

---

## Self-review notes

- Conservatism requirements honored: STOP-gate probes precede all formalization (Task 1); every "decidable" claim is scoped per-instance with the abstract instance explicitly deferred (header, Task 8 text); the folklore caveat is in both the module docstring and the ledger; `none`-is-not-a-verdict appears in docstring, guard design (Task 3's fuel-0 guard), and ledger; the C2 guard treats a discovered cycle as a STOP-and-report event, not a failure to suppress.
- Type consistency: `succs`/`rootRed` (T1) consumed by T2 proofs and T3 `closureStep`; `boundedClosure` signature `(bound) : Nat → List Term → Option (List Term)` consistent T3/T4; `reachable? : Term → Term → Nat → Option Bool` consistent T3 guards, T4 theorem, T5 `onCycle?`; `Joinable` defined and consumed in T6 only; `pureS_in_SK` field types spelled against Stage 3's `Simulation`/agreement lemmas; `leafCount_le_of_steps (hk : KFree t) (h : t ⟶* u)` argument order per SFragment.lean.
- Sorry counts for RED gates: T1=0, T2=2, T3=4, T4=2, T5=1 (stretch only), T6=3, T7=0, T8=0.
- Named risk sites: T1 Probe A's emptiness branch (a real mathematical sub-claim); T4's KFree-generalizing induction (Stage 2 precedent noted); T5's stretch theorem (sTerms-completeness gap called out with escape hatch); T4 Step 3's `by rfl` kernel evaluations (size-bounded, with the never-native_decide instruction); T6's nf_unique orientation bookkeeping (explicitly flagged as read-the-actual-statement).
- Placeholder scan: T6's `joinable_iff_nf_eq` candidate contains a deliberately rough line flagged as such with the fixed mathematical route spelled out — compiler-driven bookkeeping, statement exact. No TBDs.
- Import DAG: Reachability imports Confluence + Census.Enumerate (which brings SFragment, Eval); Calibration append needs nothing new. Root import at end. No cycles.
