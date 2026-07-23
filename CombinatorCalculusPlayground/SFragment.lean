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

-- ## The shape of a K-free normal form
-- A K-free term is a tree of S's; it is normal exactly when no S has
-- three arguments — i.e. every head spine has length ≤ 2. SNF captures
-- that shape structurally: an S, an S with one normal argument, or an S
-- with two. This is the S-fragment's answer to "what do values look
-- like?", and a stepping stone toward Waldmann-style normalization
-- analysis in later stages.
inductive SNF : Term → Prop
  | S : SNF Term.S
  | app1 {t : Term} : SNF t → SNF (Term.app Term.S t)
  | app2 {t u : Term} : SNF t → SNF u → SNF (Term.app (Term.app Term.S t) u)

-- A step inside either side of an application lifts to the whole —
-- so a normal application has normal sides (contrapositive).
theorem NormalForm.of_appL {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm t :=
  fun ⟨t', s⟩ => h ⟨Term.app t' u, Step.appL s⟩

theorem NormalForm.of_appR {t u : Term} (h : NormalForm (Term.app t u)) :
    NormalForm u :=
  fun ⟨u', s⟩ => h ⟨Term.app t u', Step.appR s⟩

theorem SNF.kFree {t : Term} (h : SNF t) : KFree t := by
  induction h with
  | S => exact KFree.S
  | app1 _ ih => exact KFree.app KFree.S ih
  | app2 _ _ ih1 ih2 => exact KFree.app (KFree.app KFree.S ih1) ih2

-- The heart of the characterization: none of the three SNF shapes can
-- step. Head spines of length ≤ 2 starve both redex rules (K_red needs a
-- K head, S_red needs a spine of 3), and the inner steps that appL/appR
-- would lift are killed by the induction hypotheses.
theorem SNF.normal {t : Term} (h : SNF t) : NormalForm t := by
  induction h with
  | S =>
    -- An atom has no step: no Step constructor's LHS is atomic.
    intro ⟨u, s⟩
    cases s
  | app1 _ ih =>
    -- t = app S t', with ih : NormalForm t'. K_red/S_red can't match
    -- (head is S with spine 1), leaving appL (a step out of the atom S —
    -- impossible) and appR (a step out of t' — contradicts ih).
    intro ⟨u, s⟩
    cases s with
    | appL sS => cases sS
    | appR sR => exact ih ⟨_, sR⟩
  | app2 _ _ iht ihu =>
    -- t = app (app S t') u'. S_red needs spine 3, this has 2; K_red needs
    -- head K. appR steps inside u' (contradicts ihu); appL steps inside
    -- app S t', which recurses one level as in the app1 case.
    intro ⟨u, s⟩
    cases s with
    | appL sL =>
      cases sL with
      | appL sS => cases sS
      | appR sR => exact iht ⟨_, sR⟩
    | appR sR => exact ihu ⟨_, sR⟩

-- Conversely: a K-free normal term must wear one of the three shapes.
-- Structural induction on the term; the left component's own SNF shape
-- decides which constructor applies — and the one forbidden shape
-- (spine already 2 on the left) would make the whole term an S-redex.
theorem SNF.of_normal {t : Term} (hk : KFree t) (hn : NormalForm t) : SNF t := by
  induction t with
  | S => exact SNF.S
  | K => cases hk
  | app l r ihl ihr =>
    cases hk with | app hkl hkr =>
    have hl : SNF l := ihl hkl hn.of_appL
    have hr : SNF r := ihr hkr hn.of_appR
    -- Which shape is l? SNF gives exactly three possibilities.
    cases hl with
    | S => exact SNF.app1 hr
    | app1 hl' => exact SNF.app2 hl' hr
    | app2 hl' hr' =>
      -- l = app (app S a) b, so app l r = S a b r — an S-redex,
      -- contradicting hn.
      exact absurd ⟨_, Step.S_red ..⟩ hn

-- The characterization, both directions bundled.
theorem SNF_iff {t : Term} : SNF t ↔ KFree t ∧ NormalForm t :=
  ⟨fun h => ⟨h.kFree, h.normal⟩, fun ⟨hk, hn⟩ => SNF.of_normal hk hn⟩
