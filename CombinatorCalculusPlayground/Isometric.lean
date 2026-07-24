--! # The isometric fragment and the head-weight measure
-- THE CLAIM THIS FILE EXISTS TO CHECK AND THEN PROVE: any cycle in
-- pure-S reduction would have to preserve leaf count at every step
-- (Stage 2: sizes are monotone, and around a loop they return), and a
-- size-preserving K-free step is exactly an S-redex whose third argument
-- is the atom S — the ISOMETRIC fragment. The head-weight measure below
-- strictly DECREASES on every isometric step, so no trajectory can loop:
-- conjecture C2 becomes a theorem (`no_pure_S_cycle`).
--
-- τ has a natural reading: each leaf weighs 2^(number of left-edges on
-- its root path) — material in head position weighs exponentially more,
-- and isometric steps push weight rightward. The head burns fuel.
--
-- EPISTEMIC STATUS while this file is under construction: the τ-decrease
-- arithmetic was derived on paper and is probed empirically in
-- Reachability.lean BEFORE the theorems below are attempted. The
-- paper-level idea (polynomial interpretations proving termination) is
-- STANDARD term-rewriting technology; its application to C2 may well be
-- known — the machine-checked resolution is the contribution claimed.
import CombinatorCalculusPlayground.SFragment

open Term

/-- Head weight: leaves in head (left) position count exponentially. -/
def tau : Term → Nat
  | .S => 1
  | .K => 1
  | .app a b => 2 * tau a + tau b

-- Hand-checked values (S S S S is the classic isometric redex):
#guard tau S = 1
#guard tau (app S S) = 3
#guard tau (app (app S S) S) = 7
#guard tau (app3 S S S S) = 15
-- ...and its reduct (S S)(S S) weighs 9: the promised drop of exactly 6.
#guard tau (app (app S S) (app S S)) = 9

-- ## The decrease lemma
theorem tau_pos : ∀ (t : Term), 1 ≤ tau t := by
  intro t
  induction t with
  | S => simp [tau]
  | K => simp [tau]
  | app a b iha ihb => simp [tau]; omega

-- In a K-free term, one leaf means THE atom.
theorem KFree.leafCount_eq_one {x : Term} (hk : KFree x)
    (h : leafCount x = 1) : x = Term.S := by
  cases hk with
  | S => rfl
  | app hl hr =>
    -- an application has ≥ 2 leaves: contradiction
    rename_i l r
    have h1 := leafCount_pos l
    have h2 := leafCount_pos r
    simp [leafCount] at h
    omega

-- The heart of the slice: a size-preserving K-free step strictly drops τ.
-- (Size preservation forces the S-redex's third argument to be atomic —
-- Stage 2's arithmetic — and then the drop at the redex is exactly 6,
-- carried through congruence by τ's positive coefficients.)
theorem tau_lt_of_isometric_step : ∀ {t u : Term}, KFree t → (t ⟶ u) →
    leafCount t = leafCount u → tau u < tau t := by
  intro t u hk h
  induction h with
  | K_red x y =>
    -- K-free t cannot contain the firing K: the Stage 2 vacuity pattern.
    intro _
    cases hk with | app hl _ =>
    cases hl with | app hK _ =>
    cases hK
  | S_red f g x =>
    intro hsize
    -- Size equality forces leafCount x = 1, hence x = S.
    have hkx : KFree x := by
      cases hk with | app _ hx => exact hx
    have hx1 : leafCount x = 1 := by
      simp [leafCount, app3] at hsize
      omega
    have hxS : x = Term.S := hkx.leafCount_eq_one hx1
    subst hxS
    -- τ(S f g S) = 4τf + 2τg + 9  >  4τf + 2τg + 3 = τ((f S)(g S))
    simp [tau, app3]
    omega
  | appL s ih =>
    intro hsize
    cases hk with | app hl hr =>
    -- whole-size equality gives subterm-size equality by plain arithmetic
    simp only [leafCount] at hsize
    have := ih hl (by omega)
    simp only [tau]
    omega
  | appR s ih =>
    intro hsize
    cases hk with | app hl hr =>
    simp only [leafCount] at hsize
    have := ih hr (by omega)
    simp only [tau]
    omega
