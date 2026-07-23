# Stage 1: Confluence of SK Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove Church–Rosser for SK reduction — `t ⟶* u → t ⟶* v → ∃ w, u ⟶* w ∧ v ⟶* w` — with the corollary that normal forms are unique, via the parallel-reduction + complete-development (Tait–Martin-Löf/Takahashi) method, hand-rolled with zero dependencies.

**Architecture:** A parallel-reduction relation `Par` (contract any subset of redexes simultaneously) sandwiched between `Step` and `Steps`. An executable complete development `dev` (contract ALL redexes) gives the triangle property `Par t u → Par u (dev t)`, from which the diamond for `Par` is a two-liner. A strip lemma lifts diamond to the multi-step closure `Pars`, and the `Step ⊆ Par ⊆ Steps` sandwich transfers confluence back to `Steps`. Combinatory logic makes this far tamer than lambda calculus: no binders, no substitution lemma.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0` (pinned in `lean-toolchain`). Zero dependencies.
- **No `sorry` on main.** A theorem that resists 3 documented attempts gets its statement recorded in `CONJECTURES.md` and is removed from the code (spec escape hatch).
- **No `partial def`** anywhere.
- Every commit must `lake build` clean with zero warnings.
- Preserve the pedagogical comment style (explain *what Lean is doing*, not just the math) — this repo doubles as a Lean tutorial for its owner.
- Comments must state precisely what is machine-checked (post-final-review discipline from Stage 0): never label a claim as certified unless a theorem with that exact content exists.

## Lean TDD adaptation (same as Stage 0)

- **Functions**: `#guard` tests first → `lake build` fails with unknown identifier (RED) → implement above them → build (GREEN).
- **Theorems**: state with `:= sorry` → build confirms the statement elaborates with only the `declaration uses 'sorry'` warning (RED) → replace with proof → build with zero warnings (GREEN). NEVER commit while a `sorry` remains.
- Verification command: `lake build` from the repo root; expect `Build completed successfully`, no warnings.
- Proof scripts below are best-effort candidates: iterate against the compiler; the acceptance criterion is the exact theorem statement compiling sorry-free, not the tactic text. Precedent from Stage 0: `fun_induction` on the function's own structure was the workhorse for every function-shaped theorem (`stepOnce_sound`, `normalize_sound`); expect the same for `dev`-shaped goals.

## Naming note (read before Task 1)

`Step` has constructors `appL`/`appR`, and `Step`/`Steps` are both `open`ed in existing files. To avoid ambiguity, the new `Steps` congruence lemmas are named `congL`/`congR`/`congApp` (NOT `appL`/`appR`).

---

### Task 1: Steps congruence lemmas + move `NormalForm` to `Step.lean`

**Files:**
- Modify: `CombinatorCalculusPlayground/Step.lean` (append)
- Modify: `CombinatorCalculusPlayground/Census/Eval.lean` (remove the `NormalForm` def only; keep `stepOnce_none_normal` and everything else)

**Interfaces:**
- Consumes: `Step`, `Steps` (constructors `refl`, `tail`), `Steps.trans` from Step.lean.
- Produces: `NormalForm : Term → Prop` (now in Step.lean, same definition `¬ ∃ u, t ⟶ u`), `Steps.congL : t ⟶* t' → app t u ⟶* app t' u`, `Steps.congR : u ⟶* u' → app t u ⟶* app t u'`, `Steps.congApp : t ⟶* t' → u ⟶* u' → app t u ⟶* app t' u'`, `NormalForm.steps_eq : NormalForm t → t ⟶* u → u = t`.

- [ ] **Step 1: State the four lemmas with `sorry` in `Step.lean` (RED)**

Append to `CombinatorCalculusPlayground/Step.lean`:

```lean
-- ## Normal forms
-- A term is in normal form when no step applies. (This is a property of the
-- reduction relation, so it lives here; it was born in Census/Eval.lean and
-- moved once confluence needed it.)
def NormalForm (t : Term) : Prop := ¬ ∃ u, t ⟶ u

-- A normal form goes nowhere: any path out of it has length zero.
theorem NormalForm.steps_eq {t u : Term} (hn : NormalForm t) (h : t ⟶* u) :
    u = t := sorry

-- ## Congruence
-- Multi-step reduction passes through both sides of an application.
-- (Named congL/congR, not appL/appR, to avoid clashing with Step's
-- constructors under `open`.)
theorem Steps.congL {t t' u : Term} (h : t ⟶* t') : app t u ⟶* app t' u := sorry

theorem Steps.congR {t u u' : Term} (h : u ⟶* u') : app t u ⟶* app t u' := sorry

-- Reduce the left side fully, then the right side.
theorem Steps.congApp {t t' u u' : Term} (h1 : t ⟶* t') (h2 : u ⟶* u') :
    app t u ⟶* app t' u' := sorry
```

And in `CombinatorCalculusPlayground/Census/Eval.lean`, DELETE these two lines (the def and its doc comment line directly above it — currently in the `## Completeness` block):

```lean
def NormalForm (t : Term) : Prop := ¬ ∃ u, t ⟶ u
```

(Keep the `## Completeness` comment block itself and `stepOnce_none_normal` — they now refer to the `NormalForm` imported from Step.lean. Adjust the comment text if it says the definition is "here".)

Run: `lake build`
Expected: builds with exactly four `declaration uses 'sorry'` warnings, no errors. (If Eval.lean errors on the deletion, the import chain is broken — Eval imports Step, so the name must resolve; fix before proceeding.)

- [ ] **Step 2: Prove them (GREEN)**

Candidate proofs (iterate freely; statements are the contract):

```lean
theorem NormalForm.steps_eq {t u : Term} (hn : NormalForm t) (h : t ⟶* u) :
    u = t := by
  cases h with
  | refl => rfl
  | tail s _ => exact absurd ⟨_, s⟩ hn

theorem Steps.congL {t t' u : Term} (h : t ⟶* t') : app t u ⟶* app t' u := by
  induction h with
  | refl => exact Steps.refl _
  | tail s _ ih => exact Steps.tail (Step.appL s) ih

theorem Steps.congR {t u u' : Term} (h : u ⟶* u') : app t u ⟶* app t u' := by
  induction h with
  | refl => exact Steps.refl _
  | tail s _ ih => exact Steps.tail (Step.appR s) ih

theorem Steps.congApp {t t' u u' : Term} (h1 : t ⟶* t') (h2 : u ⟶* u') :
    app t u ⟶* app t' u' :=
  Steps.trans (Steps.congL h1) (Steps.congR h2)
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: Steps congruence lemmas; move NormalForm to Step.lean"
```

---

### Task 2: The parallel-reduction relation `Par`

**Files:**
- Create: `CombinatorCalculusPlayground/Confluence.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Confluence`)

**Interfaces:**
- Consumes: `Term`, `app2`, `app3`, `Step`, `Steps`, `Steps.congApp` (Task 1), `Steps.trans`, `Steps.single`.
- Produces: `Par : Term → Term → Prop` with constructors `S`, `K`, `app`, `K_red`, `S_red` (exact shapes below); `Par.rfl : ∀ (t : Term), Par t t`; `Par.of_step : t ⟶ u → Par t u`; `Par.to_steps : Par t u → t ⟶* u`.

- [ ] **Step 1: Create the file with `Par` and the three theorem statements (`sorry`) (RED)**

Create `CombinatorCalculusPlayground/Confluence.lean`:

```lean
--! # Confluence of SK reduction
-- The prize: t ⟶* u and t ⟶* v always rejoin. Proved by the parallel-
-- reduction method (Tait–Martin-Löf, as streamlined by Takahashi):
--
--   Step ⊆ Par ⊆ Steps,   and Par has the diamond property.
--
-- `Par` lets any SUBSET of a term's redexes fire simultaneously — including
-- none of them (so Par is reflexive) and ones nested inside each other.
-- Single steps are too rigid for a diamond (two overlapping steps may need
-- MANY steps each to rejoin); Par is exactly loose enough.
import CombinatorCalculusPlayground.Step

open Term

-- Parallel reduction. Constructors S and K say atoms stand still; `app`
-- reduces both sides at once; K_red and S_red fire a redex WHILE the
-- surviving pieces keep par-reducing inside.
inductive Par : Term → Term → Prop
  | S : Par S S
  | K : Par K K
  | app {t t' u u' : Term} :
      Par t t' → Par u u' → Par (app t u) (app t' u')
  | K_red {x x' : Term} (y : Term) :
      Par x x' → Par (app2 K x y) x'
  | S_red {f f' g g' x x' : Term} :
      Par f f' → Par g g' → Par x x' →
      Par (app3 S f g x) (app (app f' x') (app g' x'))

-- Par is reflexive: fire the empty set of redexes.
theorem Par.rfl : ∀ (t : Term), Par t t := sorry

-- One step is a special case of a parallel step (fire exactly one redex).
theorem Par.of_step {t u : Term} (h : t ⟶ u) : Par t u := sorry

-- A parallel step is many single steps (fire the redexes one at a time).
theorem Par.to_steps {t u : Term} (h : Par t u) : t ⟶* u := sorry
```

Add `import CombinatorCalculusPlayground.Confluence` to `CombinatorCalculusPlayground.lean` (after the Step import, before the Census imports).

Run: `lake build`
Expected: builds with exactly three `sorry` warnings.

- [ ] **Step 2: Prove all three (GREEN)**

Candidate proofs:

```lean
theorem Par.rfl : ∀ (t : Term), Par t t := by
  intro t
  induction t with
  | S => exact Par.S
  | K => exact Par.K
  | app t u iht ihu => exact Par.app iht ihu

theorem Par.of_step {t u : Term} (h : t ⟶ u) : Par t u := by
  induction h with
  | K_red x y => exact Par.K_red y (Par.rfl x)
  | S_red f g x => exact Par.S_red (Par.rfl f) (Par.rfl g) (Par.rfl x)
  | appL _ ih => exact Par.app ih (Par.rfl _)
  | appR _ ih => exact Par.app (Par.rfl _) ih

theorem Par.to_steps {t u : Term} (h : Par t u) : t ⟶* u := by
  induction h with
  | S => exact Steps.refl _
  | K => exact Steps.refl _
  | app _ _ iht ihu => exact Steps.congApp iht ihu
  | K_red y _ ih =>
    -- app2 K x y ⟶ x ⟶* x'
    exact Steps.tail (Step.K_red ..) ih
  | S_red _ _ _ ihf ihg ihx =>
    -- app3 S f g x ⟶ (f x)(g x) ⟶* (f' x')(g' x')
    exact Steps.tail (Step.S_red ..) (Steps.congApp (Steps.congApp ihf ihx) (Steps.congApp ihg ihx))
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: parallel reduction Par with Step ⊆ Par ⊆ Steps"
```

---

### Task 3: The complete development `dev`

**Files:**
- Modify: `CombinatorCalculusPlayground/Confluence.lean` (append)

**Interfaces:**
- Consumes: `Term`, `app2`, `app3`, `I` (from Term.lean).
- Produces: `dev : Term → Term` — fires EVERY redex in the term simultaneously, innermost results fed to outermost redexes. Match-arm order: K-redex, S-redex, descent, atom (mirrors `stepOnce`).

- [ ] **Step 1: Write the failing `#guard` tests (RED)**

Append to `Confluence.lean`:

```lean
-- Atoms and non-redexes are fixed points of dev.
#guard dev S = S
#guard dev K = K
#guard dev (app S K) = app S K
#guard dev I = I
-- A K-redex fires, and dev keeps working inside the kept argument:
-- dev (K (K S K) t) = dev (K S K) = S.  (t = S here, discarded.)
#guard dev (app2 K (app2 K S K) S) = S
-- An S-redex fires with developed pieces distributed:
-- dev (S K K S) = (dev K) (dev S) applied pairwise = (K S)(K S).
#guard dev (app I S) = app (app K S) (app K S)
-- Descent when the head is not a redex: both sides develop independently.
#guard dev (app (app2 K S K) (app2 K K S)) = app S K
-- dev fires nested redexes in ONE pass that Step needs two for:
-- (K S K) is a redex inside the S-redex's argument position... but dev of
-- the S-redex develops f, g, x BEFORE distributing:
-- dev (S K (K S) (K S K)) = (K (dev (K S K))) ((K S) (dev (K S K)))
--                         = (K S) ((K S) S)   [dev (K S K) = S]
#guard dev (app3 S K (app K S) (app2 K S K))
       = app (app K S) (app (app K S) S)
```

Run: `lake build`
Expected: FAIL with `unknown identifier 'dev'`.

- [ ] **Step 2: Implement (GREEN)**

Insert above the `#guard` block:

```lean
-- ## The complete development
-- `dev t` fires EVERY redex in t simultaneously — the maximal parallel step.
-- Takahashi's insight: any parallel step from t can be "completed" to dev t
-- (the triangle property below), which makes the diamond property a
-- two-line corollary instead of a painful double induction.
-- Match arms mirror stepOnce: redexes first, then structural descent.
def dev : Term → Term
  | .app (.app .K x) _ => dev x
  | .app (.app (.app .S f) g) x =>
      .app (.app (dev f) (dev x)) (.app (dev g) (dev x))
  | .app t u => .app (dev t) (dev u)
  | t => t
```

Run: `lake build`
Expected: `Build completed successfully`, zero warnings. If a `#guard` fails, hand-trace it against the match arms before touching either — the guards were derived by hand and one may be wrong; verify and fix whichever side is actually in error, and note it in your report.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: complete development dev — the maximal parallel step"
```

---

### Task 4: The triangle property (the summit of this stage)

**Files:**
- Modify: `CombinatorCalculusPlayground/Confluence.lean` (append)

**Interfaces:**
- Consumes: `Par` (Task 2), `dev` (Task 3).
- Produces: `Par.triangle : Par t u → Par u (dev t)`.

**Escape hatch (spec):** 3 genuinely different documented attempts, then record the statement in `CONJECTURES.md` (Task 6 handles the file), remove broken code, commit green, report DONE_WITH_CONCERNS. Do not weaken the statement.

- [ ] **Step 1: State with `sorry` (RED)**

Append to `Confluence.lean`:

```lean
-- ## The triangle property
-- Wherever a parallel step from t lands, one more parallel step reaches
-- dev t. Picture t at the top, u anywhere below, dev t at the bottom:
-- every u closes the triangle. Diamond then falls out: two arms u, v both
-- rejoin at dev t.
theorem Par.triangle : ∀ {t u : Term}, Par t u → Par u (dev t) := sorry
```

Run: `lake build` — expect only the `sorry` warning.

- [ ] **Step 2: Prove it (GREEN)**

Strategy notes (this is the one real fight in the stage — budget accordingly):

- Induct on the `Par t u` derivation, NOT on `t`. The atom cases are `Par.S`/`Par.K` (dev of an atom is itself). The `K_red`/`S_red` cases are direct from the IHs, since `dev` of a redex develops exactly the surviving pieces.
- The `app` case is the crux: `Par (app t u) (app t' u')` with IHs `Par t' (dev t)`, `Par u' (dev u)`; the goal is `Par (app t' u') (dev (app t u))`, and `dev (app t u)` depends on which match arm `app t u` hits. Case-split on `t` (e.g. `match t with` / nested `cases`) to mirror dev's three arms:
  - `t = app K x` (K-redex): then `Par t t'` forces (by `cases` inversion on the sub-derivation) either `t' = app K x''` shape via `Par.app` (whose left component forces `= K` by inversion on `Par K _`) or a `K_red` firing inside `t`... careful: `t = app K x` is NOT itself a full K-redex (that's `app (app K x) y = app t u`); the redex is the OUTER term. So in the app case, invert the LEFT sub-derivation `Par t t'` when `t` has redex-head shape.
  - Concretely: goal `Par (app t' u') (dev x)` when `t = app K x` — inversion of `Par (app K x) t'` gives `t' = app K x'` with `Par x x'` (the `Par.app` case; its left forces `K` since `Par K w → w = K` by cases) — there is no other constructor matching `app K x` on the left. Then `Par (app (app K x') u') (dev x)` wait — the goal is `Par (app t' u') (dev (app t u)) = Par (app (app K x') u') (dev x)`: fire `Par.K_red` with the IH-derived `Par x' (dev x)`.
  - The S-redex arm is the same shape one level deeper (invert twice; `Par (app (app S f) g) t'` decomposes into nested `Par.app`s whose innermost left forces `S`).
  - The plain-descent arm closes with `Par.app` of the two IHs.
- Helper inversion lemmas make this readable — prove these first if the inline `cases` chains get deep:

```lean
theorem Par.K_inv {w : Term} (h : Par K w) : w = K := by cases h; rfl
theorem Par.S_inv {w : Term} (h : Par S w) : w = S := by cases h; rfl
```

- Two viable skeletons: (a) `induction h with ... | app hl hr ihl ihr => ...` then inside the app case `rw [show dev (app t u) = ...]` via `match`-splitting on `t`'s shape with `dev`'s equation lemmas (`simp only [dev]` after establishing the shape); (b) `fun_induction dev t generalizing u` won't fit directly (the induction must follow the Par derivation) — don't start there, but `dev.eq_def`/`simp [dev]` for arm-specific rewriting is fine.
- The K_red/S_red derivation cases: e.g. `K_red y hx` has `t = app2 K x y`, `u = x'`; `dev (app2 K x y) = dev x` by the first match arm; goal `Par x' (dev x)` is exactly the IH. S_red likewise lands on `Par.app`/constructor assembly of the three IHs — note `dev (app3 S f g x) = app (app (dev f) (dev x)) (app (dev g) (dev x))`, so assemble with `Par.app (Par.app ihf ihx) (Par.app ihg ihx)`.

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: prove the triangle property — every Par step rejoins at dev"
```

---

### Task 5: Diamond, strip, and confluence

**Files:**
- Modify: `CombinatorCalculusPlayground/Confluence.lean` (append)

**Interfaces:**
- Consumes: `Par`, `Par.triangle`, `Par.of_step`, `Par.to_steps`, `Steps`, `Steps.trans`, `NormalForm`, `NormalForm.steps_eq` (Task 1).
- Produces: `Par.diamond : Par t u → Par t v → ∃ w, Par u w ∧ Par v w`; `Pars : Term → Term → Prop` (constructors `refl`, `tail` mirroring `Steps`); `Pars.strip : Par t u → Pars t v → ∃ w, Pars u w ∧ Par v w`; `Pars.diamond : Pars t u → Pars t v → ∃ w, Pars u w ∧ Pars v w`; `Steps.to_pars : t ⟶* u → Pars t u`; `Pars.to_steps : Pars t u → t ⟶* u`; `confluence : t ⟶* u → t ⟶* v → ∃ w, (u ⟶* w) ∧ (v ⟶* w)`; `nf_unique : t ⟶* u → t ⟶* v → NormalForm u → NormalForm v → u = v`.

- [ ] **Step 1: State everything with `sorry` (RED)**

Append to `Confluence.lean`:

```lean
-- ## Diamond, and up the ladder to confluence
-- Triangle → diamond: both arms rejoin at dev t. No induction needed.
theorem Par.diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w := sorry

-- Multi-step parallel reduction, mirroring Steps.
inductive Pars : Term → Term → Prop
  | refl (t : Term) : Pars t t
  | tail {t u v : Term} : Par t u → Pars u v → Pars t v

-- The strip lemma: one Par step against many, rejoined with the shapes
-- swapped (many against one). This is the induction that lifts the
-- diamond from Par to Pars one "strip" at a time.
theorem Pars.strip {t u v : Term} (hu : Par t u) (hv : Pars t v) :
    ∃ w, Pars u w ∧ Par v w := sorry

theorem Pars.diamond {t u v : Term} (hu : Pars t u) (hv : Pars t v) :
    ∃ w, Pars u w ∧ Pars v w := sorry

-- The sandwich Step ⊆ Par ⊆ Steps makes the closures coincide.
theorem Steps.to_pars {t u : Term} (h : t ⟶* u) : Pars t u := sorry

theorem Pars.to_steps {t u : Term} (h : Pars t u) : t ⟶* u := sorry

-- ## Church–Rosser
theorem confluence {t u v : Term} (h1 : t ⟶* u) (h2 : t ⟶* v) :
    ∃ w, (u ⟶* w) ∧ (v ⟶* w) := sorry

-- The payoff for the census: "the" normal form is well-defined.
theorem nf_unique {t u v : Term} (h1 : t ⟶* u) (h2 : t ⟶* v)
    (hu : NormalForm u) (hv : NormalForm v) : u = v := sorry
```

Run: `lake build` — expect exactly seven `sorry` warnings.

- [ ] **Step 2: Prove them in order (GREEN)**

Candidate proofs:

```lean
theorem Par.diamond {t u v : Term} (hu : Par t u) (hv : Par t v) :
    ∃ w, Par u w ∧ Par v w :=
  ⟨dev t, hu.triangle, hv.triangle⟩

theorem Pars.strip {t u v : Term} (hu : Par t u) (hv : Pars t v) :
    ∃ w, Pars u w ∧ Par v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, Pars.refl u, hu⟩
  | tail hp _ ih =>
    -- t —hp→ t₁ —…→ v, and t —hu→ u. Diamond hu/hp gives w₁;
    -- recurse on the tail from t₁ against Par t₁ w₁.
    obtain ⟨w₁, huw₁, hpw₁⟩ := Par.diamond hu hp
    obtain ⟨w, hww, hvw⟩ := ih hpw₁
    exact ⟨w, Pars.tail huw₁ hww, hvw⟩

theorem Pars.diamond {t u v : Term} (hu : Pars t u) (hv : Pars t v) :
    ∃ w, Pars u w ∧ Pars v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, Pars.refl v⟩
  | tail hp _ ih =>
    obtain ⟨w₁, hw₁, hvw₁⟩ := Pars.strip hp hv
    obtain ⟨w, huw, hw₁w⟩ := ih hw₁
    exact ⟨w, huw, Pars.tail hvw₁ hw₁w⟩

theorem Steps.to_pars {t u : Term} (h : t ⟶* u) : Pars t u := by
  induction h with
  | refl => exact Pars.refl _
  | tail s _ ih => exact Pars.tail (Par.of_step s) ih

theorem Pars.to_steps {t u : Term} (h : Pars t u) : t ⟶* u := by
  induction h with
  | refl => exact Steps.refl _
  | tail hp _ ih => exact Steps.trans (Par.to_steps hp) ih

theorem confluence {t u v : Term} (h1 : t ⟶* u) (h2 : t ⟶* v) :
    ∃ w, (u ⟶* w) ∧ (v ⟶* w) := by
  obtain ⟨w, hw1, hw2⟩ := Pars.diamond (Steps.to_pars h1) (Steps.to_pars h2)
  exact ⟨w, hw1.to_steps, hw2.to_steps⟩

theorem nf_unique {t u v : Term} (h1 : t ⟶* u) (h2 : t ⟶* v)
    (hu : NormalForm u) (hv : NormalForm v) : u = v := by
  obtain ⟨w, hw1, hw2⟩ := confluence h1 h2
  rw [← hu.steps_eq hw1, ← hv.steps_eq hw2]
```

Careful in `Pars.strip`: the `generalizing u` and which hypothesis feeds `ih` are the usual stumbling points. If `induction hv generalizing u` misbehaves, swap to inducting on the SECOND argument of the strip (many-side) with the one-side fixed — the candidate above already does the standard orientation; read the goal states.

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: Church-Rosser for SK reduction with unique normal forms"
```

---

### Task 6: `normalize_normal` + standing-artifact updates

**Files:**
- Modify: `CombinatorCalculusPlayground/Census/Eval.lean` (append theorem)
- Modify: `CONJECTURES.md` (status/notes updates)
- Modify: `LAB_NOTEBOOK.md` (new dated entry)

**Interfaces:**
- Consumes: `normalize`, `stepOnce_none_normal`, `NormalForm` (now from Step.lean), `nf_unique` (Task 5), `normalize_sound`.
- Produces: `normalize_normal : normalize fuel t = some (u, k) → NormalForm u`; updated artifacts.

- [ ] **Step 1: State `normalize_normal` with `sorry` (RED)**

Append to `CombinatorCalculusPlayground/Census/Eval.lean`:

```lean
-- The other half of the certificate: a successful normalize run ends at a
-- genuine normal form (it only ever returns terms stepOnce said `none` on).
-- With normalize_sound and nf_unique (Confluence.lean), the census value of
-- a terminating term is THE normal form, full stop.
theorem normalize_normal :
    ∀ (fuel : Nat) {t u : Term} {k : Nat},
      normalize fuel t = some (u, k) → NormalForm u := sorry
```

Run: `lake build` — expect only the `sorry` warning.

- [ ] **Step 2: Prove it (GREEN)**

Candidate (mirror `normalize_sound`'s `fun_induction` shape, which is proven precedent in this file):

```lean
theorem normalize_normal :
    ∀ (fuel : Nat) {t u : Term} {k : Nat},
      normalize fuel t = some (u, k) → NormalForm u := by
  intro fuel t
  fun_induction normalize fuel t with
  | _ =>
    intro u k h
    first
      | -- success arm: returned (t, 0) because stepOnce t = none
        (injection h with h'; injection h' with h1 _; subst h1
         exact stepOnce_none_normal (by assumption))
      | -- recursive arm: the result comes from the recursive call; use ih
        (simp_all)
      | -- dead arms: none = some _, absurd
        (simp_all)
```

As with Stage 0's proofs, expect to replace the `first`-combinator sketch with explicit named cases after reading `fun_induction`'s actual goals — the success case uses `stepOnce_none_normal`, the recursive case is exactly the IH applied to the inner equation, fuel-out and propagated-none cases are absurd. (Stage 0 lab note: the `first | ...` catch-alls failed twice before; go to named cases early.)

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

- [ ] **Step 3: Update `CONJECTURES.md`**

Add to the methodology header paragraph (after the sentence about exhausted verdicts), exactly this claim and no stronger:

```markdown
As of Stage 1, SK reduction is proven confluent (`confluence`,
`Confluence.lean`) with unique normal forms (`nf_unique`), and
`normalize` is certified on both ends (`normalize_sound`,
`normalize_normal`): when the census reports a normal form, that term IS
the unique normal form of its input. (The classifier's step-counting and
cycle bookkeeping remain unverified census tooling.)
```

Do NOT change any conjecture's status — confluence proves none of C1/C2/C3.

- [ ] **Step 4: Add the `LAB_NOTEBOOK.md` entry**

Append a dated entry (use the actual date of execution; structure below, content from your actual experience — real friction, not boilerplate):

```markdown
## <date> — Stage 1: Confluence

- Church–Rosser for SK reduction proved via Par + complete development
  (Takahashi triangle). <N> theorems, all sorry-free; zero deps held.
- Proof friction: [honest notes per theorem — which candidate scripts
  survived contact with the compiler, which needed named-case rewrites,
  how the Par.triangle app-case inversions actually went]
- The sandwich (Step ⊆ Par ⊆ Steps) and the census payoff
  (normalize_normal + nf_unique) landed as planned / with deviations: [say which].
- Next per the DAG: Stage 2 (conservation laws) and Stage 3 (taxonomy)
  both remain unblocked.
```

- [ ] **Step 5: Build and commit**

Run: `lake build`
Expected: `Build completed successfully`, zero warnings.

```bash
git add -A
git commit -m "feat: normalize_normal certificate; Stage 1 artifact updates"
```

---

## Self-review notes

- Spec coverage (Stage 1 section): `theorem confluence : t ⟶* u → t ⟶* v → ∃ w, u ⟶* w ∧ v ⟶* w` ✓ (Task 5, statement matches spec's success criterion with explicit binders); corollary uniqueness of normal forms ✓ (`nf_unique`, Task 5); parallel-reduction method ✓ (Tasks 2–4); hand-rolled/zero deps ✓ (no new imports anywhere).
- Final-review carryover: `normalize_normal` ✓ (Task 6, was "cheap future-proofing" recommendation); epistemics-precision constraint carried into Global Constraints and Task 6's CONJECTURES wording ("remain unverified census tooling").
- Type consistency: `Par` constructor shapes in Task 2 match their uses in Task 4 strategy notes and Task 5 proofs (`Par.K_red y hx` arity: implicit `x x'`, explicit `y`, one hypothesis; `Par.S_red` three hypotheses). `Pars` constructors mirror `Steps` exactly and are used with those names in Task 5. `NormalForm.steps_eq` direction (`u = t`) matches its use in `nf_unique` (`rw [← ...]`). `Steps.congL/congR/congApp` names consistent across Tasks 1, 2, 5.
- Placeholder scan: no TBDs; every proof step has a candidate script or (Task 4) an explicit strategy section — Task 4's is intentionally strategy-not-script since the exact inversion bookkeeping is compiler-driven; the statement contract is exact.
- NormalForm move (Task 1) is the only cross-file refactor; Eval.lean's `stepOnce_none_normal` keeps compiling because Eval imports Step. Main.lean and Enumerate.lean never reference NormalForm (verified against Stage 0 sources).
