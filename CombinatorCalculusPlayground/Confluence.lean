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
theorem Par.rfl : ∀ (t : Term), Par t t := by
  intro t
  induction t with
  | S => exact Par.S
  | K => exact Par.K
  | app t u iht ihu => exact Par.app iht ihu

-- One step is a special case of a parallel step (fire exactly one redex).
theorem Par.of_step {t u : Term} (h : t ⟶ u) : Par t u := by
  induction h with
  | K_red x y => exact Par.K_red y (Par.rfl x)
  | S_red f g x => exact Par.S_red (Par.rfl f) (Par.rfl g) (Par.rfl x)
  | appL _ ih => exact Par.app ih (Par.rfl _)
  | appR _ ih => exact Par.app (Par.rfl _) ih

-- A parallel step is many single steps (fire the redexes one at a time).
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
