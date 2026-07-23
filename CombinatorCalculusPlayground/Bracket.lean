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
    StepsV t v := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact tail s (ih h2)

theorem StepsV.congL {t t' u : TermV} (h : StepsV t t') :
    StepsV (.app t u) (.app t' u) := by
  induction h with
  | refl => exact StepsV.refl _
  | tail s _ ih => exact StepsV.tail (StepV.appL s) ih

theorem StepsV.congR {t u u' : TermV} (h : StepsV u u') :
    StepsV (.app t u) (.app t u') := by
  induction h with
  | refl => exact StepsV.refl _
  | tail s _ ih => exact StepsV.tail (StepV.appR s) ih

theorem StepsV.congApp {t t' u u' : TermV} (h1 : StepsV t t') (h2 : StepsV u u') :
    StepsV (.app t u) (.app t' u') :=
  StepsV.trans (StepsV.congL h1) (StepsV.congR h2)

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

-- The abstraction really binds: x is gone, other variables survive.
theorem occurs_bracket (x y : Nat) (t : TermV) :
    occurs y (bracket x t) = (occurs y t && !(y == x)) := by
  induction t with
  | S => simp [bracket, occurs]
  | K => simp [bracket, occurs]
  | var z =>
    simp only [bracket]
    by_cases hz : z = x <;> simp only [hz, if_true, if_false, occurs, app2] <;> grind
  | app a b iha ihb =>
    simp only [bracket, occurs, app2, iha, ihb]
    -- Boolean distribution: (p && c) || (q && c) = (p || q) && c
    cases occurs y a <;> cases occurs y b <;> cases (y == x) <;> rfl

/-- No variables at all. -/
def ClosedV (t : TermV) : Prop := ∀ y, occurs y t = false

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

/-- Packaging: any single-variable term is realized by a CLOSED combinator.
(Multi-variable completeness is this theorem iterated — deliberately not
formalized; one clean statement beats a fold nobody consumes. YAGNI.) -/
theorem combinatory_completeness (x : Nat) (t : TermV)
    (h : ∀ y, occurs y t = true → y = x) :
    ∃ F : TermV, ClosedV F ∧ ∀ u, StepsV (.app F u) (subst x u t) :=
  ⟨bracket x t, bracket_closed h, fun u => bracket_beta x t u⟩

end TermV
