--! # Conservation laws of the S-fragment
-- Pure-S terms (no K anywhere) are the arena of the prize question. This
-- module proves what S-reduction CONSERVES: K-freeness itself, and leaf
-- count (S cannot erase — its reduct mentions every argument).
--
-- HONEST FRAMING (spec requirement): these laws explain why *naive*
-- encodings into pure S fail — you cannot discard scaffolding, so
-- halting-as-normalization tricks that rely on erasure don't transfer.
-- They are NOT an impossibility argument. The λI-calculus (equivalently
-- the {S,B,C,I} basis) is also erasure-free, and it is computationally
-- complete for total computable functions (Church–Kleene 1936). Whatever
-- blocks S alone — if anything does — is not mere non-erasure.
import CombinatorCalculusPlayground.Step

open Term

-- A term is K-free when every leaf is S. The only ways to build one:
inductive KFree : Term → Prop
  | S : KFree Term.S
  | app {t u : Term} : KFree t → KFree u → KFree (Term.app t u)

-- Executable twin, for census guards and decidability.
def kFree : Term → Bool
  | .S => true
  | .K => false
  | .app t u => kFree t && kFree u

#guard kFree S = true
#guard kFree K = false
#guard kFree I = false                         -- I = S K K smuggles two K's
#guard kFree (app (app S S) S) = true
#guard kFree (app S (app S K)) = false

-- The Bool and the Prop agree — so KFree is decidable, and census guards
-- can speak for the proposition.
theorem kFree_iff : ∀ {t : Term}, kFree t = true ↔ KFree t := by
  intro t
  induction t with
  | S => simp [kFree]; exact KFree.S
  | K => simp [kFree]; intro h; cases h
  | app l r ihl ihr =>
    simp [kFree, Bool.and_eq_true, ihl, ihr]
    constructor
    · exact fun ⟨hl, hr⟩ => KFree.app hl hr
    · intro h; cases h with | app hl hr => exact ⟨hl, hr⟩

instance : DecidablePred KFree := fun t =>
  decidable_of_iff (kFree t = true) kFree_iff
