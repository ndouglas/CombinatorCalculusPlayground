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
