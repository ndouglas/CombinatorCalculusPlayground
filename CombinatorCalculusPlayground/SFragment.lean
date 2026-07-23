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
-- complete for total computable functions (Church 1941; Barendregt §9.5). Whatever
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

-- ## Closure under reduction
-- The S-fragment is a world unto itself: reduction can never manufacture
-- a K. (The K-redex case is vacuous — a K-free term cannot contain the
-- K that would fire.)
theorem KFree.of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) : KFree u := by
  induction h with
  | K_red x y =>
    -- t = app (app K x) y and KFree t: invert twice to expose KFree K.
    cases hk with | app hl _ =>
    cases hl with | app hK _ =>
    cases hK
  | S_red f g x =>
    -- t = app (app (app S f) g) x: harvest KFree f, g, x, reassemble.
    cases hk with | app hl hx =>
    cases hl with | app hl2 hg =>
    cases hl2 with | app _ hf =>
    exact KFree.app (KFree.app hf hx) (KFree.app hg hx)
  | appL _ ih =>
    cases hk with | app hl hr => exact KFree.app (ih hl) hr
  | appR _ ih =>
    cases hk with | app hl hr => exact KFree.app hl (ih hr)

theorem KFree.of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) : KFree u := by
  induction h with
  | refl => exact hk
  | tail s _ ih => exact ih (hk.of_step s)

-- ## No erasure
-- The heart of the conservation story. An S-step S f g x → (f x)(g x)
-- keeps one copy of f and g and DUPLICATES x; nothing is discarded.
-- Leaf count: |f|+|g|+|x|+1 becomes |f|+|g|+2|x|, a gain of |x|-1 ≥ 0.
-- (K-steps erase — which is exactly why they're excluded by KFree.)

-- Every term has at least one leaf.
theorem leafCount_pos : ∀ (t : Term), 1 ≤ leafCount t := by
  intro t
  induction t with
  | S => simp [leafCount]
  | K => simp [leafCount]
  | app l r ihl ihr => simp [leafCount]; omega

theorem leafCount_le_of_step {t u : Term} (hk : KFree t) (h : t ⟶ u) :
    leafCount t ≤ leafCount u := by
  induction h with
  | K_red x y =>
    cases hk with | app hl _ => cases hl with | app hK _ => cases hK
  | S_red f g x =>
    -- |S f g x| = |f|+|g|+|x|+1 ≤ |f|+|x|+(|g|+|x|) = |(f x)(g x)|
    have := leafCount_pos x
    simp [leafCount, app3]
    omega
  | appL _ ih =>
    cases hk with | app hl _ =>
    simp [leafCount]
    exact ih hl
  | appR _ ih =>
    cases hk with | app _ hr =>
    simp [leafCount]
    exact ih hr

theorem leafCount_le_of_steps {t u : Term} (hk : KFree t) (h : t ⟶* u) :
    leafCount t ≤ leafCount u := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail s rest ih =>
    exact Nat.le_trans (leafCount_le_of_step hk s) (ih (hk.of_step s))

-- A proven constraint on census conjecture C2: if a K-free term sits on
-- a reduction cycle, every term on that cycle has the SAME leaf count.
-- Any hunt for S-cycles can restrict to size-preserving steps.
theorem cycle_leafCount_eq {t u : Term} (hk : KFree t)
    (h1 : t ⟶* u) (h2 : u ⟶* t) : leafCount t = leafCount u :=
  Nat.le_antisymm
    (leafCount_le_of_steps hk h1)
    (leafCount_le_of_steps (hk.of_steps h1) h2)
