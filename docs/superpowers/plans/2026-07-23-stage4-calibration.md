# Stage 4: Calibration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Calibrate the Stage 3 definitions with one positive and one negative result: combinatory completeness of {S,K} via bracket abstraction, and a machine-checked refutation of first-order iota hosting SK — locating Barker's one-combinator universality precisely as a λ-calculus phenomenon outside first-order rewriting.

**Architecture:** Simulation algebra (identity, composition, monotonicity) appends to `Universality/Defs.lean`. `Bracket.lean` is a standalone variables-and-abstraction world (`TermV`, naive bracket, `bracket_beta`) — the positive calibration. `Iota.lean` gives the first-order iota system with Stage 0-style executable machinery and CENSUS-FIRST empirical probes of the plan's central prediction (iota reduction strictly grows terms by +8 leaves per step). `Universality/Calibration.lean` then proves the growth law, exhibits an explicit 5-step SK reduction cycle (Ω = (SII)(SII)), and derives `no_sim_SK_iota`: no pinned Simulation of SK into first-order iota exists — sizes cannot strictly increase around a loop.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.28.0`), Lake, zero external dependencies.

## Global Constraints

- Toolchain: `leanprover/lean4:v4.28.0`. Zero dependencies.
- **No `sorry` on main.** 3 documented failed attempts → statement to `CONJECTURES.md`, code removed (spec escape hatch).
- **No `partial def`.** Plain `decide` is allowed (kernel-checked); `native_decide` is not.
- Every commit must `lake build` clean with zero warnings.
- Comments state precisely what is machine-checked. This stage's honesty burden: the refutation targets the FIRST-ORDER reading of iota (`RS.Iota` as defined); Barker's λ-level universality is external, untouched, and every mention must say so.
- **Census-first discipline:** Task 4's empirical probes run BEFORE Task 5's proofs. If a probe contradicts the growth prediction, STOP and report — Task 5's plan would be wrong.
- Spec deviation, pre-authorized here: the spec's "universality of iota under the taxonomy" deliverable becomes a refutation + external registration (the finding forced it); the spec's Waldmann-kill deliverable takes the spec's own Risks-section downgrade (cite, don't formalize). Both must be registered in the ledger exactly as such.

## Lean TDD adaptation (house rules)

- Theorems: `:= sorry` (RED, count matches) → proof (GREEN, zero warnings). Defs with embedded proof fields land whole. NEVER commit with sorry.
- Known instance-level friction: `induction` on `RS.Steps` at a CONCRETE instance fails (mkElimApp motive bug) — use the `.rec` pattern from RS.lean's `SK_steps_iff`, with the why-comment. Task 5's `iota_steps_le` hits this.
- Named cases; no `first |` catch-alls; qualify constructors inside namespaces.

---

### Task 1: Simulation algebra

**Files:**
- Modify: `CombinatorCalculusPlayground/Universality/Defs.lean` (append, inside/after the `Simulation` namespace)

**Interfaces:**
- Consumes: `Simulation` (fields enc/dec/dec_enc/fwd/bwd), `Simulation.fwd_steps`, `RS.Steps.single`, `UniversalReach`.
- Produces: `Simulation.id (A : RS) : Simulation A A`; `Simulation.comp {A B C : RS} (S1 : Simulation A B) (S2 : Simulation B C) : Simulation A C`; `UniversalReach.of_sim {R B C : RS} (h : UniversalReach R B) (S : Simulation B C) : UniversalReach R C`.

- [ ] **Step 1: Append the two defs whole and the theorem with `sorry` (RED: exactly one sorry warning)**

```lean
-- ## Simulation algebra
-- Simulations compose, so universality is transitive along hosts — the
-- lattice's transport layer.

/-- Every system simulates itself. -/
def Simulation.id (A : RS) : Simulation A A where
  enc := fun a => a
  dec := fun a => some a
  dec_enc := fun _ => rfl
  fwd := fun s => RS.Steps.single s
  bwd := fun h => h

/-- A inside B and B inside C gives A inside C. -/
def Simulation.comp {A B C : RS} (S1 : Simulation A B) (S2 : Simulation B C) :
    Simulation A C where
  enc := fun a => S2.enc (S1.enc a)
  dec := fun c => (S2.dec c).bind S1.dec
  dec_enc := fun a => by simp [S2.dec_enc, S1.dec_enc]
  fwd := fun s => S2.fwd_steps (S1.fwd s)
  bwd := fun h => S1.bwd (S2.bwd h)

/-- Universality transports along a host-to-host simulation. -/
theorem UniversalReach.of_sim {R B C : RS}
    (h : UniversalReach R B) (S : Simulation B C) : UniversalReach R C := sorry
```

Run: `lake build` — the two defs must elaborate (their proof fields are inline); exactly one sorry warning.

- [ ] **Step 2: Prove (GREEN)**

```lean
theorem UniversalReach.of_sim {R B C : RS}
    (h : UniversalReach R B) (S : Simulation B C) : UniversalReach R C := by
  obtain ⟨S1⟩ := h
  exact ⟨S1.comp S⟩
```

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: simulation algebra — identity, composition, transport"
```

---

### Task 2: `Bracket.lean` — terms with variables

**Files:**
- Create: `CombinatorCalculusPlayground/Bracket.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Bracket` after Confluence, before SFragment)

**Interfaces:**
- Consumes: nothing project-side (standalone syntax world).
- Produces: `TermV` (constructors `.S`, `.K`, `.var : Nat → TermV`, `.app`); `TermV.app2`, `TermV.app3`; `StepV` (K_red, S_red, appL, appR — variables inert); `StepsV` (refl, tail); `StepsV.trans`, `StepsV.congL`, `StepsV.congR`, `StepsV.congApp`; `subst (x : Nat) (u : TermV) : TermV → TermV`; `occurs (x : Nat) : TermV → Bool`.

- [ ] **Step 1: Create the file — definitions whole, `#guard`s for the executables, four lemmas with `sorry` (RED: exactly four sorry warnings)**

```lean
--! # Terms with variables
-- Combinatory completeness needs something to be complete FOR: terms
-- built from variables and application. The variables live in a separate
-- syntax (TermV) so the core Term stays pure; nothing here touches the
-- census or the RS layer. Reduction is the same two rules — variables
-- are inert (no rule mentions them).

inductive TermV : Type
  | S : TermV
  | K : TermV
  | var : Nat → TermV
  | app : TermV → TermV → TermV
deriving Repr, DecidableEq

namespace TermV

def app2 (f a b : TermV) : TermV := .app (.app f a) b
def app3 (f a b c : TermV) : TermV := .app (.app (.app f a) b) c

inductive StepV : TermV → TermV → Prop
  | K_red (x y : TermV) : StepV (app2 .K x y) x
  | S_red (f g x : TermV) :
      StepV (app3 .S f g x) (.app (.app f x) (.app g x))
  | appL {t t' u : TermV} : StepV t t' → StepV (.app t u) (.app t' u)
  | appR {t u u' : TermV} : StepV u u' → StepV (.app t u) (.app t u')

inductive StepsV : TermV → TermV → Prop
  | refl (t : TermV) : StepsV t t
  | tail {t u v : TermV} : StepV t u → StepsV u v → StepsV t v

theorem StepsV.trans {t u v : TermV} (h1 : StepsV t u) (h2 : StepsV u v) :
    StepsV t v := sorry

theorem StepsV.congL {t t' u : TermV} (h : StepsV t t') :
    StepsV (.app t u) (.app t' u) := sorry

theorem StepsV.congR {t u u' : TermV} (h : StepsV u u') :
    StepsV (.app t u) (.app t u') := sorry

theorem StepsV.congApp {t t' u u' : TermV} (h1 : StepsV t t') (h2 : StepsV u u') :
    StepsV (.app t u) (.app t' u') := sorry

/-- Substitute u for variable x. -/
def subst (x : Nat) (u : TermV) : TermV → TermV
  | .var y => if y = x then u else .var y
  | .S => .S
  | .K => .K
  | .app a b => .app (subst x u a) (subst x u b)

/-- Does variable x occur in t? -/
def occurs (x : Nat) : TermV → Bool
  | .var y => y == x
  | .app a b => occurs x a || occurs x b
  | _ => false

#guard subst 0 .S (.app (.var 0) (.var 1)) = .app .S (.var 1)
#guard subst 0 .S (.var 1) = .var 1
#guard occurs 0 (.app .K (.var 0)) = true
#guard occurs 1 (.app .K (.var 0)) = false
#guard occurs 0 (app2 .S .K .K) = false

end TermV
```

Add the root import. Run: `lake build` — exactly four sorry warnings, guards pass.

- [ ] **Step 2: Prove the four lemmas (GREEN)**

They are line-for-line mirrors of `Steps.trans`/`Steps.congL`/`Steps.congR`/`Steps.congApp` in Step.lean — same inductions, `StepV.appL`/`StepV.appR` in place of `Step.appL`/`Step.appR`, `StepsV.congApp := StepsV.trans (congL h1) (congR h2)`. Read Step.lean for the exact shapes.

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: TermV — terms with variables, inert-variable reduction, subst"
```

---

### Task 3: Naive bracket abstraction and combinatory completeness

**Files:**
- Modify: `CombinatorCalculusPlayground/Bracket.lean` (append inside `namespace TermV`)

**Interfaces:**
- Consumes: everything from Task 2.
- Produces: `bracket (x : Nat) : TermV → TermV`; `bracket_beta (x : Nat) (t u : TermV) : StepsV (.app (bracket x t) u) (subst x u t)`; `occurs_bracket (x y : Nat) (t : TermV) : occurs y (bracket x t) = (occurs y t && !(y == x))`; `ClosedV (t : TermV) : Prop := ∀ y, occurs y t = false`; `bracket_closed`; `combinatory_completeness`.

- [ ] **Step 1: Definitions + guards, theorems with `sorry` (RED: exactly four sorry warnings)**

Append inside `namespace TermV`:

```lean
-- ## Bracket abstraction
-- The NAIVE algorithm — no occurs-check optimization. Terms come out
-- bigger, proofs come out smaller; for calibration the proofs win (YAGNI).
--   [x]x       = S K K            (the I combinator, on the spot)
--   [x](var y) = K (var y)        (y ≠ x)
--   [x](a b)   = S ([x]a) ([x]b)
--   [x]S = K S,  [x]K = K K
def bracket (x : Nat) : TermV → TermV
  | .var y => if y = x then app2 .S .K .K else .app .K (.var y)
  | .app a b => app2 .S (bracket x a) (bracket x b)
  | .S => .app .K .S
  | .K => .app .K .K

#guard bracket 0 (.var 0) = TermV.app2 .S .K .K
#guard bracket 0 (.var 1) = .app .K (.var 1)
#guard bracket 0 (.app (.var 0) (.var 0))
       = TermV.app2 .S (TermV.app2 .S .K .K) (TermV.app2 .S .K .K)

-- ## Combinatory completeness of {S, K}
-- THE theorem of this file: applying the abstraction is substitution.
theorem bracket_beta (x : Nat) (t u : TermV) :
    StepsV (.app (bracket x t) u) (subst x u t) := sorry

-- The abstraction really binds: x is gone, other variables survive.
theorem occurs_bracket (x y : Nat) (t : TermV) :
    occurs y (bracket x t) = (occurs y t && !(y == x)) := sorry

/-- No variables at all. -/
def ClosedV (t : TermV) : Prop := ∀ y, occurs y t = false

theorem bracket_closed {x : Nat} {t : TermV}
    (h : ∀ y, occurs y t = true → y = x) : ClosedV (bracket x t) := sorry

/-- Packaging: any single-variable term is realized by a CLOSED combinator.
(Multi-variable completeness is this theorem iterated — deliberately not
formalized; one clean statement beats a fold nobody consumes. YAGNI.) -/
theorem combinatory_completeness (x : Nat) (t : TermV)
    (h : ∀ y, occurs y t = true → y = x) :
    ∃ F : TermV, ClosedV F ∧ ∀ u, StepsV (.app F u) (subst x u t) := sorry
```

Run: `lake build` — exactly four sorry warnings, guards pass.

- [ ] **Step 2: Prove, in order (GREEN)**

Candidates:

```lean
theorem bracket_beta (x : Nat) (t u : TermV) :
    StepsV (.app (bracket x t) u) (subst x u t) := by
  induction t with
  | S =>
    -- (K S) u → S
    exact StepsV.tail (StepV.K_red .S u) (StepsV.refl _)
  | K =>
    exact StepsV.tail (StepV.K_red .K u) (StepsV.refl _)
  | var y =>
    by_cases hy : y = x
    · -- (S K K) u → (K u) (K u) → u ; subst gives u via if_pos
      simp [bracket, subst, hy]
      exact StepsV.tail (StepV.S_red .K .K u)
        (StepsV.tail (StepV.K_red u (.app .K u)) (StepsV.refl u))
    · -- (K (var y)) u → var y ; subst gives var y via if_neg
      simp [bracket, subst, hy]
      exact StepsV.tail (StepV.K_red (.var y) u) (StepsV.refl _)
  | app a b iha ihb =>
    -- (S [x]a [x]b) u → ([x]a u) ([x]b u) →* (subst a)(subst b)
    exact StepsV.tail (StepV.S_red (bracket x a) (bracket x b) u)
      (StepsV.congApp (iha) (ihb))
```

(The `simp [bracket, subst, hy]` calls align the goal with the chain — expect
bookkeeping iteration; if `simp` rewrites too much, use `rw [bracket]`-style
targeted unfolding or `show` the concrete goal. The chains themselves are
fixed.)

```lean
theorem occurs_bracket (x y : Nat) (t : TermV) :
    occurs y (bracket x t) = (occurs y t && !(y == x)) := by
  induction t with
  | S => simp [bracket, occurs]
  | K => simp [bracket, occurs]
  | var z =>
    by_cases hz : z = x
    · subst hz; simp [bracket, occurs]
      -- LHS: occurs y (S K K) = false; RHS: (z == y)-vs-beq bookkeeping
      -- reduces to false && / y == x cancellation. omega/simp on Nat beq.
      sorry_free_by_cases -- placeholder note: expect by_cases y = z + simp [Nat.beq]
    · simp [bracket, occurs, hz]
      -- (z == y) = (z == y) && !(y == x) when z ≠ x: case on y = z.
      sorry_free_by_cases
  | app a b iha ihb =>
    simp [bracket, occurs, iha, ihb]
    -- Boolean distribution: (p && c) || (q && c) = (p || q) && c
    cases occurs y a <;> cases occurs y b <;> cases (y == x) <;> rfl
```

IMPORTANT: `sorry_free_by_cases` above is NOT Lean — it marks the two spots
where Nat `==`/`=` bookkeeping needs case analysis the plan can't predict
exactly. Close them with `by_cases hyz : y = z` + `simp [hyz]`/`omega`-style
reasoning, or `cases Nat.decEq y z` — whatever the goal states demand. The
statement is the contract; no sorry may remain.

```lean
theorem bracket_closed {x : Nat} {t : TermV}
    (h : ∀ y, occurs y t = true → y = x) : ClosedV (bracket x t) := by
  intro y
  rw [occurs_bracket]
  by_cases hy : occurs y t = true
  · have := h y hy
    subst this
    simp
  · simp [Bool.not_eq_true] at hy
    simp [hy]

theorem combinatory_completeness (x : Nat) (t : TermV)
    (h : ∀ y, occurs y t = true → y = x) :
    ∃ F : TermV, ClosedV F ∧ ∀ u, StepsV (.app F u) (subst x u t) :=
  ⟨bracket x t, bracket_closed h, fun u => bracket_beta x t u⟩
```

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: combinatory completeness of {S,K} via naive bracket abstraction"
```

---

### Task 4: `Iota.lean` — the first-order iota system, census-first

**Files:**
- Create: `CombinatorCalculusPlayground/Iota.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Iota` after RS, before Universality imports)

**Interfaces:**
- Consumes: `RS` (RS.lean).
- Produces: `IotaTerm` (`.iota`, `.app`); `IotaTerm.Kiota : IotaTerm` (= ι(ι(ιι))); `IotaTerm.Siota : IotaTerm` (= ι Kiota); `IotaTerm.IotaStep` (iota_red, appL, appR); `IotaTerm.leafCount : IotaTerm → Nat`; `IotaTerm.stepOnce : IotaTerm → Option IotaTerm`; `IotaTerm.stepOnce_sound`; `IotaTerm.trace : Nat → IotaTerm → List IotaTerm`; `RS.Iota : RS`.

- [ ] **Step 1: Create the file — definitions + probes, one theorem with `sorry` (RED: one sorry warning; ALL probes must pass)**

```lean
--! # The iota combinator, first-order
-- Barker's ι is classically λx. x S K — famously a ONE-combinator basis
-- for the λ-calculus. Its first-order rewrite reading is the single rule
--     ι x  →  (x Sι) Kι
-- with Sι, Kι the fixed iota-terms below (the images of S and K).
-- EPISTEMIC STATUS: iota's universality is a λ-CALCULUS (higher-order,
-- erasing) fact — external, Barker 2001-era folklore — and is NOT
-- contradicted by anything in this repository. What THIS stage settles is
-- whether the first-order reading hosts SK under the pinned Simulation
-- (Universality/Calibration.lean: it cannot — the rule strictly grows
-- terms, and SK has reduction cycles).
import CombinatorCalculusPlayground.RS

inductive IotaTerm : Type
  | iota : IotaTerm
  | app : IotaTerm → IotaTerm → IotaTerm
deriving Repr, DecidableEq

namespace IotaTerm

/-- The image of K: ι(ι(ιι)). Behaviorally K in the λ-reading. -/
def Kiota : IotaTerm := .app .iota (.app .iota (.app .iota .iota))

/-- The image of S: ι Kiota. Behaviorally S in the λ-reading. -/
def Siota : IotaTerm := .app .iota Kiota

inductive IotaStep : IotaTerm → IotaTerm → Prop
  | iota_red (x : IotaTerm) :
      IotaStep (.app .iota x) (.app (.app x Siota) Kiota)
  | appL {t t' u : IotaTerm} : IotaStep t t' → IotaStep (.app t u) (.app t' u)
  | appR {t u u' : IotaTerm} : IotaStep u u' → IotaStep (.app t u) (.app t u')

def leafCount : IotaTerm → Nat
  | .iota => 1
  | .app t u => leafCount t + leafCount u

#guard leafCount Kiota = 4
#guard leafCount Siota = 5

-- Executable leftmost-outermost reducer, mirroring Census/Eval.lean.
def stepOnce : IotaTerm → Option IotaTerm
  | .app .iota x => some (.app (.app x Siota) Kiota)
  | .app t u =>
    match stepOnce t with
    | some t' => some (.app t' u)
    | none =>
      match stepOnce u with
      | some u' => some (.app t u')
      | none => none
  | _ => none

theorem stepOnce_sound : ∀ {t u : IotaTerm}, stepOnce t = some u → IotaStep t u := sorry

def trace (fuel : Nat) (t : IotaTerm) : List IotaTerm :=
  match stepOnce t, fuel with
  | none, _ => [t]
  | some _, 0 => [t]
  | some t', f + 1 => t :: trace f t'

-- ## CENSUS-FIRST PROBES (read before proving anything in Task 5)
-- The plan's central prediction: every iota_red strictly GROWS leaf count
-- (1 + |x| becomes |x| + 9), so first-order iota can never erase, and the
-- λ-level "Kι a b reduces to a" behavior is unreachable as first-order
-- reachability. These guards check that prediction empirically BEFORE any
-- proof effort. IF ANY PROBE FAILS: STOP — do not "fix" it; report
-- DONE_WITH_CONCERNS with the failing trace. The Task 5 plan would be
-- wrong and the stage must re-plan.

-- Sizes strictly increase along an observed trajectory of Kι ι ι.
#guard (let tr := trace 60 (.app (.app Kiota .iota) .iota)
        (tr.zip tr.tail).all fun (a, b) => leafCount a < leafCount b)
-- In particular Kι ι ι never reaches its first argument ι.
#guard (let tr := trace 60 (.app (.app Kiota .iota) .iota)
        tr.all (· != IotaTerm.iota))
-- And Sι ι ι ι never reaches (ι ι)(ι ι) — the S-behavior target.
#guard (let tr := trace 60 (.app (.app (.app Siota .iota) .iota) .iota)
        tr.all (· != IotaTerm.app (.app .iota .iota) (.app .iota .iota)))
-- The trajectory genuinely runs (never normalizes within fuel): 61 entries.
#guard (trace 60 (.app (.app Kiota .iota) .iota)).length = 61

end IotaTerm

/-- First-order iota as a rewriting system. -/
def RS.Iota : RS := ⟨IotaTerm, IotaTerm.IotaStep⟩
```

Add the root import. Run: `lake build` — exactly one sorry warning; every guard passes. If a PROBE guard fails, follow the STOP instruction above verbatim.

- [ ] **Step 2: Prove `stepOnce_sound` (GREEN)**

Mirror `Census/Eval.lean`'s `stepOnce_sound`: `fun_induction stepOnce t` with named cases — iota-redex arm via `IotaStep.iota_red`, descent arms via `IotaStep.appL`/`appR` + IHs from the nested matches, dead arms absurd. Read the Eval.lean proof for the working case pattern.

Run: `lake build` — zero warnings.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: first-order iota system with census-first growth probes"
```

---

### Task 5: `Universality/Calibration.lean` — the growth law, the SK cycle, the refutation

**Files:**
- Create: `CombinatorCalculusPlayground/Universality/Calibration.lean`
- Modify: `CombinatorCalculusPlayground.lean` (add `import CombinatorCalculusPlayground.Universality.Calibration` after Taxonomy)

**Interfaces:**
- Consumes: `IotaTerm` machinery (Task 4), `RS.Iota`; `Simulation` (+ `fwd_steps`, `enc_injective`), `UniversalReach`; `RS.SK`, `RS.SK_steps_iff`; `Term`, `Step`, `Steps` (⟶*), `I`, `app2`, `app3` (Term/Step.lean).
- Produces: `iota_step_lt {w w' : IotaTerm} (h : IotaTerm.IotaStep w w') : IotaTerm.leafCount w < IotaTerm.leafCount w'`; `iota_steps_le {w w' : IotaTerm} (h : RS.Iota.Steps w w') : w = w' ∨ IotaTerm.leafCount w < IotaTerm.leafCount w'`; `Wdup : Term` (= app2 S I I), `omegaSK : Term` (= app Wdup Wdup), `Mcycle : Term` (= app (app I Wdup) (app I Wdup)); `omega_to_M : omegaSK ⟶* Mcycle`; `M_to_omega : Mcycle ⟶* omegaSK`; `omega_ne_M : omegaSK ≠ Mcycle`; `no_sim_SK_iota : ¬ Nonempty (Simulation RS.SK RS.Iota)`; `iota_not_universal_for_SK : ¬ UniversalReach RS.SK RS.Iota`.

**Escape hatch (spec):** 3 documented attempts per theorem → CONJECTURES registration + removal, DONE_WITH_CONCERNS.

- [ ] **Step 1: Create the file, all statements `sorry` (RED: exactly seven sorry warnings — the three defs land whole)**

```lean
--! # Calibration: the definitions have teeth
-- Positive: {S,K} is combinatorially complete (Bracket.lean). Negative —
-- the surprise of this stage: the first-order reading of Barker's ι
-- CANNOT host SK under the pinned Simulation. The argument is a
-- conservation law meeting a cycle: every iota step strictly grows leaf
-- count (+8), while SK reduces (SII)(SII) around a genuine 5-step loop;
-- an injective encoding would need sizes to strictly increase around a
-- circle. Barker's one-combinator universality is thereby LOCATED, not
-- contradicted: it is a λ-calculus (erasing, higher-order) phenomenon,
-- invisible to first-order reachability — exactly the kind of boundary
-- this taxonomy exists to draw.
import CombinatorCalculusPlayground.Universality.Defs
import CombinatorCalculusPlayground.Iota

open Term

-- ## The iota conservation law (compare SFragment: pure S never SHRINKS;
-- first-order iota strictly GROWS — an even stronger conservation).
theorem iota_step_lt {w w' : IotaTerm} (h : IotaTerm.IotaStep w w') :
    IotaTerm.leafCount w < IotaTerm.leafCount w' := sorry

theorem iota_steps_le {w w' : IotaTerm} (h : RS.Iota.Steps w w') :
    w = w' ∨ IotaTerm.leafCount w < IotaTerm.leafCount w' := sorry

-- ## An SK reduction cycle, fully explicit
-- Wdup x would reduce to x x; omegaSK = Wdup Wdup is the classic loop.
def Wdup : Term := app2 S I I
def omegaSK : Term := Term.app Wdup Wdup
def Mcycle : Term := Term.app (Term.app I Wdup) (Term.app I Wdup)

theorem omega_to_M : omegaSK ⟶* Mcycle := sorry

theorem M_to_omega : Mcycle ⟶* omegaSK := sorry

theorem omega_ne_M : omegaSK ≠ Mcycle := sorry

-- ## The refutation
theorem no_sim_SK_iota : ¬ Nonempty (Simulation RS.SK RS.Iota) := sorry

theorem iota_not_universal_for_SK : ¬ UniversalReach RS.SK RS.Iota := sorry
```

Add the root import. Run: `lake build` — exactly seven sorry warnings.

- [ ] **Step 2: Prove, in this order (GREEN)**

Candidates:

```lean
theorem iota_step_lt {w w' : IotaTerm} (h : IotaTerm.IotaStep w w') :
    IotaTerm.leafCount w < IotaTerm.leafCount w' := by
  induction h with
  | iota_red x =>
    -- 1 + |x|  <  |x| + |Sι| + |Kι|  =  |x| + 9
    simp [IotaTerm.leafCount, IotaTerm.Siota, IotaTerm.Kiota]
    omega
  | appL _ ih => simp [IotaTerm.leafCount]; omega
  | appR _ ih => simp [IotaTerm.leafCount]; omega
```

`iota_steps_le` — CAUTION: this inducts on `RS.Iota.Steps`, a CONCRETE
instance, so `induction` will hit the mkElimApp motive bug. Use the `.rec`
pattern from RS.lean (`SK_steps_iff`), with the why-comment:

```lean
theorem iota_steps_le {w w' : IotaTerm} (h : RS.Iota.Steps w w') :
    w = w' ∨ IotaTerm.leafCount w < IotaTerm.leafCount w' := by
  -- Raw recursor: `induction` fails on RS.Steps at a concrete instance
  -- (mkElimApp motive error) — same workaround as RS.SK_steps_iff.
  refine h.rec (fun a => Or.inl rfl) (fun s _ ih => Or.inr ?_)
  -- one strict step s, then either equality (use s's strict bound) or
  -- strictness composing with the tail's bound
  rcases ih with heq | hlt
  · exact heq ▸ iota_step_lt s
  · exact Nat.lt_trans (iota_step_lt s) hlt
```

(If the `refine h.rec` form fights the motive, spell the motive explicitly:
`h.rec (motive := fun a b _ => a = b ∨ IotaTerm.leafCount a < IotaTerm.leafCount b) ...` — the two minor premises are as above. Iterate; the statement is the contract.)

The cycle — five explicit steps. Note `omegaSK` is definitionally
`app3 S I I Wdup` (unfold `Wdup`/`app2`/`app3` to see it), so `Step.S_red`
applies directly; similarly `app I Wdup` is definitionally `app3 S K K Wdup`:

```lean
theorem omega_to_M : omegaSK ⟶* Mcycle :=
  Steps.tail (Step.S_red I I Wdup) (Steps.refl _)

theorem M_to_omega : Mcycle ⟶* omegaSK :=
  -- (I W)(I W) → ((KW)(KW))(I W) → W (I W) → W ((KW)(KW)) → W W
  Steps.tail (Step.appL (Step.S_red K K Wdup))
    (Steps.tail (Step.appL (Step.K_red Wdup (Term.app K Wdup)))
      (Steps.tail (Step.appR (Step.S_red K K Wdup))
        (Steps.tail (Step.appR (Step.K_red Wdup (Term.app K Wdup)))
          (Steps.refl _))))

theorem omega_ne_M : omegaSK ≠ Mcycle := by decide
```

(`decide` is kernel-checked structural disequality on a derived
DecidableEq — legal; `native_decide` remains banned. If `decide` times out
— it should not on terms this small — `simp [omegaSK, Mcycle, Wdup, I]` +
`nofun`/injection chains is the fallback.)

```lean
theorem no_sim_SK_iota : ¬ Nonempty (Simulation RS.SK RS.Iota) := by
  rintro ⟨Sim⟩
  have h1 : RS.Iota.Steps (Sim.enc omegaSK) (Sim.enc Mcycle) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr omega_to_M)
  have h2 : RS.Iota.Steps (Sim.enc Mcycle) (Sim.enc omegaSK) :=
    Sim.fwd_steps (RS.SK_steps_iff.mpr M_to_omega)
  rcases iota_steps_le h1 with heq1 | hlt1
  · exact omega_ne_M (Sim.enc_injective heq1)
  · rcases iota_steps_le h2 with heq2 | hlt2
    · exact omega_ne_M (Sim.enc_injective heq2.symm)
    · exact absurd (Nat.lt_trans hlt1 hlt2) (Nat.lt_irrefl _)

theorem iota_not_universal_for_SK : ¬ UniversalReach RS.SK RS.Iota :=
  no_sim_SK_iota
```

Run: `lake build` — zero warnings. Then the axiom audit (scratch file,
delete after): `#print axioms no_sim_SK_iota`, `#print axioms
combinatory_completeness`, `#print axioms bracket_beta` — record outputs.

- [ ] **Step 3: Commit**

```bash
git add -A
git commit -m "feat: first-order iota cannot host SK — growth law meets the SK cycle"
```

---

### Task 6: Ledger + artifacts

**Files:**
- Modify: `CONJECTURES.md` (ledger updates, new conjecture C4, methodology line)
- Modify: `LAB_NOTEBOOK.md` (dated entry)

**Interfaces:**
- Consumes: all Stage 4 names (verify each against the tree by grep before writing): `combinatory_completeness`, `bracket_beta`, `Simulation.comp`, `UniversalReach.of_sim`, `iota_step_lt`, `no_sim_SK_iota`, `iota_not_universal_for_SK`, `RS.Iota`.
- Produces: the updated status register (spec Stage 4 success-criterion accounting, including the two pre-authorized deviations).

- [ ] **Step 1: Update the Definitions ledger in `CONJECTURES.md`**

Add a new table row/section (adapt names only if the tree differs — verify first):

```markdown
### Stage 4 calibration results

- **Positive:** {S,K} is combinatorially complete
  (`combinatory_completeness`, `Bracket.lean`): every single-variable term
  over {S,K,·} is realized by a closed combinator, via naive bracket
  abstraction (`bracket_beta`). This is the classic sense in which S and K
  suffice; the Tag→SK Reach cell below remains open (encoding a reference
  machine is Stage 5-adjacent work).
- **Negative (machine-checked):** `UniversalReach RS.SK RS.Iota` is
  **REFUTED** (`no_sim_SK_iota`, `Universality/Calibration.lean`): every
  first-order iota step strictly grows leaf count (`iota_step_lt`), SK has
  an explicit 5-step reduction cycle (Ω = (SII)(SII)), and no injective
  encoding survives both. IMPORTANT SCOPE: this refutes the FIRST-ORDER
  reading of ι (`RS.Iota` as defined). Barker's one-combinator
  universality is a λ-calculus (higher-order, erasing) result — external,
  NOT contradicted, and not expressible as a first-order RS in this
  framework. The taxonomy just drew that boundary precisely.
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
system whose rule is non-erasing (every rule variable occurs in the
reduct) cannot host SK under `Simulation`. (Non-erasure alone gives ≤,
not <; the generalization needs care where the rule preserves size.
Compare pure S — non-erasing but size-PRESERVING steps exist, so this
argument does NOT apply to S; C2's cycle question stays genuinely open.)
```

Also update the existing ledger table: the SK row's Reach cell may note "combinatory completeness proven at TermV level (`combinatory_completeness`); Tag→SK still open"; add an Iota row with the REFUTED entry pointing at the section above.

- [ ] **Step 2: Methodology line**

After the Stage 3 methodology paragraph:

```markdown
As of Stage 4, the taxonomy is calibrated in both directions: {S,K}
combinatory completeness is machine-checked (`Bracket.lean`), and the
first-order reading of the one-combinator iota basis is machine-checked
NOT to host SK (`Universality/Calibration.lean`) — with Barker's λ-level
iota universality explicitly registered as external and out of
first-order scope. Simulations compose (`Simulation.comp`), so
universality transports along hosts (`UniversalReach.of_sim`).
```

- [ ] **Step 3: `LAB_NOTEBOOK.md` entry**

Dated entry (actual execution date), honest voice: the headline is that
pre-planning analysis predicted the iota refutation BEFORE implementation
(size argument), the census-first probes (Task 4) validated it empirically
before proof effort, and the proofs then landed — record which candidates
survived, what the `.rec` motive needed in `iota_steps_le`, the
`bracket_beta` simp-bookkeeping experience, the axiom-audit outputs, and
one line on how this stage's outcome differs from what the Stage 3 atlas
originally imagined ("iota calibration target" → refutation).

- [ ] **Step 4: Build and commit**

Run: `lake build` — zero warnings.

```bash
git add -A
git commit -m "feat: Stage 4 calibration ledger — completeness proven, first-order iota refuted"
```

---

## Self-review notes

- Spec coverage (Stage 4 section): bracket abstraction / combinatory completeness ✓ (Tasks 2–3); one-combinator basis "under the taxonomy" → refutation with external Barker registration (Tasks 4–5 + ledger; pre-authorized deviation in Global Constraints); Waldmann formal-kill → spec's own Risks-downgrade, registered (Task 6); λI stretch: explicitly registered not-attempted (Task 6). Success criteria: "`universal SK`" realized as `combinatory_completeness` (TermV level, honestly framed) — Tag→SK registered open; "`universal iota`" realized as its refutation — the S-column/status chart updated (Task 6).
- Census-first discipline: Task 4's probes gate Task 5, with an explicit STOP instruction; this is the plan's own falsifiability clause for the size analysis (leafCount Kiota = 4, Siota = 5, growth +8 — checked by #guards before any proof).
- Type consistency: `IotaTerm.leafCount`/`IotaStep`/`Kiota`/`Siota` names consistent Tasks 4–5; `Wdup`/`omegaSK`/`Mcycle` defined and consumed in Task 5 only; `Simulation.comp`/`UniversalReach.of_sim` (Task 1) cited in Task 6's methodology text; `StepsV.congApp` (Task 2) consumed by `bracket_beta` (Task 3); `RS.SK_steps_iff` direction (`mpr` : ⟶* → RS.Steps) matches its Stage 3 statement.
- Placeholder scan: the two `sorry_free_by_cases` markers in Task 3 are explicitly flagged as NOT-Lean with closure instructions — they mark compiler-driven bookkeeping, not missing content; statements are exact. No TBDs.
- Sorry counts per task stated for RED gates: T1=1, T2=4, T3=4, T4=1, T5=7, T6=0.
- Known risk sites, named: Task 4 probes (falsifiability gate), Task 5's `iota_steps_le` (.rec at concrete instance), Task 3's Nat-beq bookkeeping.
- Import DAG: Bracket standalone; Iota imports RS; Calibration imports Defs+Iota; no cycles. Root order: …Confluence, Bracket, SFragment, RS, Iota, Universality.Defs, Universality.Taxonomy, Universality.Calibration, Census.*.
