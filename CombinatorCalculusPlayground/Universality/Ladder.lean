--! # The relaxation ladder, rung one: {S, I}
-- The design spec's Stage 5 has TWO components. One is the north star
-- (decidability of reachability — closed in Stage 6). The other is:
--
--   "Bracketing program (the relaxation ladder): classify universality of bases
--    between {S} and {S,K} — e.g., {S,I}, {S,B}, {S,C} — each rung a publishable
--    partial result that narrows where universality is lost."
--
-- Sixteen stages engaged with the first component and never mentioned the
-- second. This module opens it.
--
-- WHY {S,I} IS THE RIGHT FIRST RUNG, and it is not because it is easiest: it is
-- where the program's ONLY negative mechanism dies. Every refutation in this
-- tree routes through `RS.Acyclic.of_strict_measure` — pure S, first-order ι, and
-- all one-combinator one-rule systems (C4) fall to a host being ACYCLIC. `{S,I}`
-- has a cycle, so that mechanism provably cannot touch it.
--
-- The resulting boundary is sharp. Pure S is acyclic (`no_pure_S_cycle`, C2).
-- Adding `I` — which erases nothing and duplicates nothing — makes it cyclic.
-- So **the acyclicity boundary sits exactly at the first rung of the ladder**,
-- and the program's negative tooling reaches no further than {S}.
import CombinatorCalculusPlayground.Universality.Taxonomy

-- ## The basis {S, I}, with I primitive
-- Note this is NOT `Term`'s `I = S K K`. Here `I` is a combinator in its own
-- right, so the system is genuinely erasure-free: neither rule discards an
-- argument. That matters — it makes {S,I} a λI-style basis, and the cycle below
-- shows erasure-freeness is not what keeps pure S acyclic.

inductive SITerm : Type
  | S : SITerm
  | I : SITerm
  | app : SITerm → SITerm → SITerm
deriving Repr, DecidableEq

inductive SIStep : SITerm → SITerm → Prop
  | S_red (f g x : SITerm) :
      SIStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | I_red (x : SITerm) : SIStep (.app .I x) x
  | appL {t t' u : SITerm} : SIStep t t' → SIStep (.app t u) (.app t' u)
  | appR {t u u' : SITerm} : SIStep u u' → SIStep (.app t u) (.app t u')

def RS.SI : RS := ⟨SITerm, SIStep⟩

def SITerm.leafCount : SITerm → Nat
  | .S => 1
  | .I => 1
  | .app a b => a.leafCount + b.leafCount

-- ## The cycle
-- Ω = (S I I)(S I I), the classic. `S I I` has spine 2 so it is not itself a
-- redex; applying it to itself supplies the third argument and fires.

def Wsi : SITerm := .app (.app .S .I) .I
def omegaSI : SITerm := .app Wsi Wsi
def omegaSI_mid1 : SITerm := .app (.app .I Wsi) (.app .I Wsi)
def omegaSI_mid2 : SITerm := .app Wsi (.app .I Wsi)

#guard SITerm.leafCount omegaSI = 6
#guard omegaSI ≠ omegaSI_mid1

/-- `Ω → (I Ω')(I Ω')` — the S-redex fires, duplicating `S I I`. -/
theorem omegaSI_step1 : RS.SI.step omegaSI omegaSI_mid1 :=
  SIStep.S_red .I .I Wsi

/-- ...and two I-reductions close the loop, returning to Ω exactly. -/
theorem omegaSI_back : RS.SI.Steps omegaSI_mid1 omegaSI :=
  RS.Steps.tail (SIStep.appL (SIStep.I_red Wsi))
    (RS.Steps.tail (SIStep.appR (SIStep.I_red Wsi)) (RS.Steps.refl _))

/-- **{S,I} has a proper reduction cycle** — three steps, through two distinct
intermediates. This is the concrete content of the rung. -/
theorem omegaSI_cycle : RS.SI.step omegaSI omegaSI_mid1 ∧ RS.SI.Steps omegaSI_mid1 omegaSI :=
  ⟨omegaSI_step1, omegaSI_back⟩

-- ## The consequence: the program's negative mechanism cannot reach {S,I}

/-- {S,I} is NOT acyclic, so `PathEncoding.refute_of_acyclic` — the single
mechanism behind every refutation in this tree — has an unsatisfiable hypothesis
here. -/
theorem SI_not_acyclic : ¬ RS.Acyclic RS.SI :=
  fun h => h omegaSI_step1 omegaSI_back

/-- Stronger and more useful: NO strictly-increasing measure exists on {S,I}, so
the C4 engine (`RS.Acyclic.of_strict_measure`) provably cannot be applied — not
merely "we have not found a measure", but "there is none". -/
theorem SI_no_strict_measure :
    ¬ ∃ mu : SITerm → Nat, ∀ (b b' : SITerm), RS.SI.step b b' → mu b < mu b' := by
  rintro ⟨mu, hmono⟩
  exact SI_not_acyclic (RS.Acyclic.of_strict_measure mu (fun h => hmono _ _ h))

/-- The same for a strictly DECREASING measure: a cycle rules out monotone
measures in both directions, so no termination argument of that shape works
either. -/
theorem SI_no_decreasing_measure :
    ¬ ∃ mu : SITerm → Nat, ∀ (b b' : SITerm), RS.SI.step b b' → mu b' < mu b := by
  rintro ⟨mu, hmono⟩
  -- walk the measure down around the cycle and back to where it started
  have hdrop : mu omegaSI_mid1 < mu omegaSI := hmono _ _ omegaSI_step1
  -- Raw recursor: `induction` hits the mkElimApp motive error on `RS.Steps` at a
  -- concrete instance, as in `iota_steps_le` and `RS.Discrete2_steps_eq`.
  have hpath : ∀ {a b : SITerm}, RS.SI.Steps a b → mu b ≤ mu a := by
    intro a b h
    exact h.rec (fun _ => Nat.le_refl _)
      (fun s _ ih => Nat.le_trans ih (Nat.le_of_lt (hmono _ _ s)))
  have := hpath omegaSI_back
  omega

-- ## Where the boundary sits
-- Pure S is acyclic — `no_pure_S_cycle` (C2, Isometric.lean), proved via the
-- head-weight measure τ, for every K-free term and every strategy. Adding `I`
-- destroys that, as above. Two things follow, and the second is the point of
-- the rung:
--
--   * erasure-freeness is NOT what keeps pure S acyclic. {S,I} erases nothing
--     either, and it cycles. Whatever τ is measuring is specific to S-only
--     reduction, not a consequence of non-erasure.
--   * the acyclicity boundary is exactly the first rung. The program's entire
--     negative apparatus applies to {S}, to first-order ι, and to every
--     one-combinator one-rule system (C4) — and stops dead at {S,I}. So the
--     answer to "where is universality lost?" cannot be approached from the
--     negative side beyond rung zero, and the ladder's higher rungs need
--     positive constructions or new mechanisms.
--
-- ## Rungs two and three, scoped not attempted
-- `{S,B}` (B x y z → x (y z)) and `{S,C}` (C x y z → x z y) both have a rule
-- that STRICTLY DECREASES leaf count by 1, mixed with S's rule which changes
-- leaf count by |x| - 1 ≥ 0. So `leafCount` is non-monotone in both directions on
-- each of them, and neither the growth refutation nor a naive shrink argument
-- applies. A combined measure in the style of C2's τ would be needed — the same
-- shape of work that resolved C2, which took a full slice.
--
-- Whether either has a cycle is open here. One natural attempt at Ω fails for
-- `{S,B}`: `S B B (SBB) → (B (SBB))(B (SBB))`, and that reduct is a NORMAL FORM,
-- because `B` applied to fewer than three arguments is stuck and `S B B` has
-- spine 2. So the obvious self-application terminates, which is weak evidence
-- that `{S,B}` may be acyclic and therefore refutable by the existing mechanism
-- — the opposite verdict from rung one, and the reason rung two is worth doing
-- next.
