--! # Confluence of K-reduction, and unique K-normal forms
-- Stage 45 found the mechanism for the adequacy blocker: read a host term only after its DOOMED
-- subterms have been discarded, i.e. after contracting K-redexes. That makes "the K-normal form of
-- `t`" a thing the abstraction depends on, and the abstraction is only well defined if that phrase
-- denotes. Hence this file. It is the small self-contained lemma Stage 45's ranking named.
--
-- The architecture is Confluence.lean's, restricted to the K rule, because that file already
-- establishes the pattern in this development: parallel reduction between `KStep` and `KSteps`,
-- a complete development `kdev`, Takahashi's triangle, then diamond → strip → confluence. The
-- K-only version is strictly simpler — there is no S_red case anywhere, and `kdev` has one redex
-- arm instead of two.
--
-- Note what is NOT claimed: this says nothing about the fuel-based `kNorm` in AdequacyProbe.lean,
-- which remains unverified census tooling. The results here are about the RELATION, which is what
-- a relational abstraction (`RS.bwd_of_abstraction_rel`) actually needs.
import CombinatorCalculusPlayground.Confluence

open Term

/-- K-reduction: the `K` rule and congruence, with S-redexes deliberately excluded. Contracting an
S-redex is what advances an encoded machine, so an abstraction must not do it. -/
inductive KStep : Term → Term → Prop
  | K_red (x y : Term) : KStep (app2 K x y) x
  | appL {t t' u : Term} : KStep t t' → KStep (app t u) (app t' u)
  | appR {t u u' : Term} : KStep u u' → KStep (app t u) (app t u')

inductive KSteps : Term → Term → Prop
  | refl (t : Term) : KSteps t t
  | tail {t u v : Term} : KStep t u → KSteps u v → KSteps t v

theorem KSteps.single {t u : Term} (h : KStep t u) : KSteps t u := .tail h (.refl u)

theorem KSteps.trans {t u v : Term} (h1 : KSteps t u) (h2 : KSteps u v) : KSteps t v := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact .tail s (ih h2)

/-- Every K-step is an SK-step, so everything proved here sits inside the ambient system. -/
theorem KStep.toStep : ∀ {t u : Term}, KStep t u → t ⟶ u := by
  intro t u h
  induction h with
  | K_red x y => exact Step.K_red x y
  | appL _ ih => exact Step.appL ih
  | appR _ ih => exact Step.appR ih

theorem KSteps.toSteps : ∀ {t u : Term}, KSteps t u → t ⟶* u := by
  intro t u h
  induction h with
  | refl => exact Steps.refl _
  | tail s _ ih => exact Steps.tail s.toStep ih

/-- Parallel K-reduction: atoms stand still, `app` reduces both sides at once, and `K_red` fires a
redex while the surviving piece keeps reducing inside. -/
inductive KPar : Term → Term → Prop
  | S : KPar S S
  | K : KPar K K
  | app {t t' u u' : Term} : KPar t t' → KPar u u' → KPar (app t u) (app t' u')
  | K_red {x x' : Term} (y : Term) : KPar x x' → KPar (app2 K x y) x'

theorem KPar.rfl : ∀ (t : Term), KPar t t := by
  intro t
  induction t with
  | S => exact KPar.S
  | K => exact KPar.K
  | app t u iht ihu => exact KPar.app iht ihu

theorem KPar.of_kstep : ∀ {t u : Term}, KStep t u → KPar t u := by
  intro t u h
  induction h with
  | K_red x y => exact KPar.K_red y (KPar.rfl x)
  | appL _ ih => exact KPar.app ih (KPar.rfl _)
  | appR _ ih => exact KPar.app (KPar.rfl _) ih

theorem KSteps.congL : ∀ {t t' u : Term}, KSteps t t' → KSteps (app t u) (app t' u) := by
  intro t t' u h
  induction h with
  | refl => exact KSteps.refl _
  | tail s _ ih => exact KSteps.tail (KStep.appL s) ih

theorem KSteps.congR : ∀ {t u u' : Term}, KSteps u u' → KSteps (app t u) (app t u') := by
  intro t u u' h
  induction h with
  | refl => exact KSteps.refl _
  | tail s _ ih => exact KSteps.tail (KStep.appR s) ih

theorem KPar.to_ksteps : ∀ {t u : Term}, KPar t u → KSteps t u := by
  intro t u h
  induction h with
  | S => exact KSteps.refl _
  | K => exact KSteps.refl _
  | app _ _ iha ihb => exact KSteps.trans iha.congL ihb.congR
  | K_red y _ ih => exact KSteps.tail (KStep.K_red ..) ih

/-- The complete K-development: fire every K-redex at once. -/
def kdev : Term → Term
  | .app (.app .K x) _ => kdev x
  | .app t u => .app (kdev t) (kdev u)
  | t => t

#guard kdev S = S
#guard kdev K = K
#guard kdev (app S K) = app S K
-- An S-redex is left completely alone, which is the whole point.
#guard kdev I = I
#guard kdev (app I S) = app I S
-- Nested K-redexes fire in one pass: K (K S K) S → K S K → S.
#guard kdev (app2 K (app2 K S K) S) = S
-- ...and a redex in a DOOMED position simply vanishes with it.
#guard kdev (app2 K S (app2 K K S)) = S

theorem KPar.K_inv {w : Term} (h : KPar Term.K w) : w = Term.K := by cases h; rfl

/-- Takahashi's triangle, for K-reduction: wherever a parallel K-step lands, one more parallel
K-step reaches `kdev t`. -/
theorem KPar.triangle : ∀ {t u : Term}, KPar t u → KPar u (kdev t) := by
  intro t u h
  induction h with
  | S => exact KPar.S
  | K => exact KPar.K
  | K_red y hx ih => simpa only [app2, kdev] using ih
  | @app a a' b b' hl _ ihl ihr =>
      -- mirror `kdev`'s match arms on `a`'s shape
      cases a with
      | S => exact KPar.app ihl ihr
      | K => exact KPar.app ihl ihr
      | app c d =>
        cases c with
        | S => exact KPar.app ihl ihr
        | app _ _ => exact KPar.app ihl ihr
        | K =>
          -- `app (app K d) b` is a K-redex. `hl` lives one level down, where `K_red`'s
          -- left-hand side is too deep to match, so inversion leaves only `app`.
          cases hl with
          | app hK hd =>
            obtain rfl := KPar.K_inv hK
            simp only [kdev] at ihl ⊢
            cases ihl with
            | app _ hd' => exact KPar.K_red b' hd'

theorem KPar.to_kdev (t : Term) : KPar t (kdev t) := (KPar.rfl t).triangle

theorem KPar.diamond {t u v : Term} (hu : KPar t u) (hv : KPar t v) :
    ∃ w, KPar u w ∧ KPar v w :=
  ⟨kdev t, hu.triangle, hv.triangle⟩

inductive KPars : Term → Term → Prop
  | refl (t : Term) : KPars t t
  | tail {t u v : Term} : KPar t u → KPars u v → KPars t v

theorem KPars.strip {t u v : Term} (hu : KPar t u) (hv : KPars t v) :
    ∃ w, KPars u w ∧ KPar v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, KPars.refl u, hu⟩
  | tail hp _ ih =>
      obtain ⟨w₁, huw₁, hpw₁⟩ := KPar.diamond hu hp
      obtain ⟨w, hww, hvw⟩ := ih hpw₁
      exact ⟨w, KPars.tail huw₁ hww, hvw⟩

theorem KPars.diamond {t u v : Term} (hu : KPars t u) (hv : KPars t v) :
    ∃ w, KPars u w ∧ KPars v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, KPars.refl v⟩
  | tail hp _ ih =>
      obtain ⟨w₁, hw₁, hvw₁⟩ := KPars.strip hp hv
      obtain ⟨w, huw, hw₁w⟩ := ih hw₁
      exact ⟨w, huw, KPars.tail hvw₁ hw₁w⟩

theorem KSteps.to_kpars : ∀ {t u : Term}, KSteps t u → KPars t u := by
  intro t u h
  induction h with
  | refl => exact KPars.refl _
  | tail s _ ih => exact KPars.tail (KPar.of_kstep s) ih

theorem KPars.to_ksteps : ∀ {t u : Term}, KPars t u → KSteps t u := by
  intro t u h
  induction h with
  | refl => exact KSteps.refl _
  | tail hp _ ih => exact KSteps.trans hp.to_ksteps ih

/-- **K-reduction is confluent.** -/
theorem kconfluence {t u v : Term} (h1 : KSteps t u) (h2 : KSteps t v) :
    ∃ w, KSteps u w ∧ KSteps v w := by
  obtain ⟨w, hw1, hw2⟩ := KPars.diamond h1.to_kpars h2.to_kpars
  exact ⟨w, hw1.to_ksteps, hw2.to_ksteps⟩

def KNormalForm (t : Term) : Prop := ¬ ∃ u, KStep t u

theorem KNormalForm.ksteps_eq {t u : Term} (hn : KNormalForm t) (h : KSteps t u) : t = u := by
  cases h with
  | refl => rfl
  | tail s _ => exact absurd ⟨_, s⟩ hn

/-- **"The" K-normal form is well defined** — which is what makes an abstraction that reads a term
after discarding its doomed subterms a function of the term at all. -/
theorem knf_unique {t u v : Term} (h1 : KSteps t u) (h2 : KSteps t v)
    (hu : KNormalForm u) (hv : KNormalForm v) : u = v := by
  obtain ⟨w, hw1, hw2⟩ := kconfluence h1 h2
  exact (hu.ksteps_eq hw1).trans (hv.ksteps_eq hw2).symm

-- ## The payoff for adequacy
-- `IsKNF t w` says `w` is the K-normal form of `t`. `knf_unique` makes it single-valued, and the
-- corollary below is exactly the K-step case of Stage 45's stutter-or-advance obligation: a host
-- step that merely discards a doomed subterm leaves the abstraction alone, because it does not move
-- the K-normal form.

def IsKNF (t w : Term) : Prop := KSteps t w ∧ KNormalForm w

theorem IsKNF.unique {t w w' : Term} (h : IsKNF t w) (h' : IsKNF t w') : w = w' :=
  knf_unique h.1 h'.1 h.2 h'.2

/-- **A K-step does not move the K-normal form.** So an abstraction reading the K-normal form
STUTTERS on every K-step — no case analysis on the encoding required. -/
theorem IsKNF.of_kstep {t t' w : Term} (hs : KStep t t') (h : IsKNF t w) : IsKNF t' w := by
  obtain ⟨w', h1, h2⟩ := kconfluence (KSteps.single hs) h.1
  have heq : w = w' := h.2.ksteps_eq h2
  subst heq
  exact ⟨h1, h.2⟩

-- Anchors, so none of the above is vacuous: `S` is K-normal, `K S S` reduces to it, and an
-- S-redex is K-normal too — which is the property that keeps the machine's steps out of reach.
theorem kNormalForm_S : KNormalForm Term.S := by rintro ⟨u, hu⟩; cases hu
theorem kNormalForm_I : KNormalForm I := by
  rintro ⟨u, hu⟩
  cases hu with
  | appL h => cases h with
    | appL h => cases h
    | appR h => cases h
  | appR h => cases h

example : IsKNF (app2 Term.K Term.S Term.S) Term.S :=
  ⟨KSteps.single (KStep.K_red _ _), kNormalForm_S⟩

/-- The countdown encoding is already K-normal, so its abstraction reads it unchanged — the
`habs` side of Stage 45's mechanism, now at the level of the relation. -/
theorem isKNF_self {t : Term} (h : KNormalForm t) : IsKNF t t := ⟨KSteps.refl t, h⟩

-- ## The other half of `Step`
-- The abstraction must react differently to the two kinds of host step: a K-step is invisible to it
-- (`IsKNF.of_kstep`) while an S-step is what advances the encoded machine. So the split has to be
-- exhaustive, and that is a theorem rather than an observation.

/-- S-reduction: the `S` rule and congruence. -/
inductive SStep : Term → Term → Prop
  | S_red (f g x : Term) : SStep (app3 S f g x) (app (app f x) (app g x))
  | appL {t t' u : Term} : SStep t t' → SStep (app t u) (app t' u)
  | appR {t u u' : Term} : SStep u u' → SStep (app t u) (app t u')

theorem SStep.toStep : ∀ {t u : Term}, SStep t u → t ⟶ u := by
  intro t u h
  induction h with
  | S_red f g x => exact Step.S_red f g x
  | appL _ ih => exact Step.appL ih
  | appR _ ih => exact Step.appR ih

/-- **Every SK step is a K-step or an S-step.** -/
theorem Step.kOrS : ∀ {t u : Term}, (t ⟶ u) → KStep t u ∨ SStep t u := by
  intro t u h
  induction h with
  | K_red x y => exact Or.inl (KStep.K_red x y)
  | S_red f g x => exact Or.inr (SStep.S_red f g x)
  | appL _ ih => exact ih.imp KStep.appL SStep.appL
  | appR _ ih => exact ih.imp KStep.appR SStep.appR

-- ## What the S-step case cannot be
-- The tempting one-layer commutation statement is
--
--     SStep b b' → SStep (kdev b) (kdev b') ∨ kdev b = kdev b'
--
-- and it is FALSE. The reason is worth recording, because it is the shape of the real obligation.
-- When the fired redex is `S K g x`, its reduct `(K x)(g x)` is ITSELF a K-redex, so `kdev` fires
-- that too and lands a step further along than one S-step from `kdev b` can reach. Concretely with
-- `g = x = S`:

theorem sStep_SKSS : SStep (app3 S K S S) (app (app K S) (app S S)) := SStep.S_red K S S

#guard kdev (app3 S K S S) = app3 S K S S          -- not a K-redex, so kdev leaves it alone
#guard kdev (app (app K S) (app S S)) = S         -- ...but its S-reduct IS one, and collapses

/-- So `kdev b` and `kdev b'` are neither equal nor one S-step apart: the reduct's K-collapse gets
there first. The correct statement interposes K-reduction AFTER the S-step, which is why the
remaining obligation is a commutation square and not an equation. -/
theorem naive_kdev_commutation_fails :
    kdev (app3 S K S S) ≠ kdev (app (app K S) (app S S))
      ∧ ¬ SStep (kdev (app3 S K S S)) (kdev (app (app K S) (app S S))) := by
  refine ⟨by decide, ?_⟩
  intro h
  -- `kdev` has left both sides where the guards above put them, so this asks for
  -- `SStep (S K S S) S`, and an S-reduct is always an application
  simp only [show kdev (app3 S K S S) = app3 S K S S from by decide,
    show kdev (app (app K S) (app S S)) = S from by decide] at h
  cases h

-- ## The commutation square
-- Stage 47 refuted the equation; this is the square that replaces it. Read it as: an S-step and a
-- K-step out of the same term can be closed, with K-reduction on the S-side and AT MOST one S-step
-- on the K-side. Both weakenings are forced, and by different cases:
--   * the K-side may need ZERO S-steps, because the S-redex may sit in the argument a `K` discards;
--   * the S-side may need TWO K-steps, because the S-step duplicates its third argument and a
--     K-redex inside it gets copied along with it.

theorem sk_local_square : ∀ {b c : Term}, KStep b c → ∀ {b' : Term}, SStep b b' →
    ∃ c', KSteps b' c' ∧ (SStep c c' ∨ c = c') := by
  intro b c hk
  induction hk with
  | K_red x y =>
      intro b' hs
      cases hs with
      | appL hl =>
          cases hl with
          | appL h => cases h                       -- no S-step out of the bare `K`
          | appR hx => exact ⟨_, KSteps.single (KStep.K_red _ y), Or.inl hx⟩
      | appR hy =>
          -- the S-step happened in the argument `K` discards, so it simply vanishes
          exact ⟨x, KSteps.single (KStep.K_red x _), Or.inr rfl⟩
  | @appL t t' u hkt ih =>
      intro b' hs
      cases hs with
      | S_red f g =>
          -- `u` IS the S-redex's third argument; the K-step is inside `f` or `g`
          cases hkt with
          | appL hkl =>
              cases hkl with
              | appL h => cases h                   -- no K-step out of the bare `S`
              | appR hf =>
                  exact ⟨_, KSteps.congL (KSteps.congL (KSteps.single hf)),
                    Or.inl (SStep.S_red _ g u)⟩
          | appR hg =>
              exact ⟨_, KSteps.congR (KSteps.congL (KSteps.single hg)),
                Or.inl (SStep.S_red f _ u)⟩
      | appL hst =>
          obtain ⟨e, he1, he2⟩ := ih hst
          exact ⟨Term.app e u, KSteps.congL he1, he2.imp SStep.appL (fun h => by rw [h])⟩
      | appR hsu =>
          exact ⟨Term.app t' _, KSteps.single (KStep.appL hkt), Or.inl (SStep.appR hsu)⟩
  | @appR t u u' hku ih =>
      intro b' hs
      cases hs with
      | S_red f g =>
          -- the K-step is inside the argument the S-step DUPLICATED, so the S-side needs two
          exact ⟨_, KSteps.trans (KSteps.congL (KSteps.congR (KSteps.single hku)))
            (KSteps.congR (KSteps.congR (KSteps.single hku))), Or.inl (SStep.S_red f g u')⟩
      | appL hst =>
          exact ⟨Term.app _ u', KSteps.single (KStep.appR hku), Or.inl (SStep.appL hst)⟩
      | appR hsu =>
          obtain ⟨e, he1, he2⟩ := ih hsu
          exact ⟨Term.app t e, KSteps.congR he1, he2.imp SStep.appR (fun h => by rw [h])⟩

/-- **The square, lifted to whole K-reductions.** An S-step out of `b` and a K-reduction from `b` to
`c` close up: `b'` K-reduces to some `c'` that is `c` itself or one S-step past it. -/
theorem sk_square : ∀ {b c : Term}, KSteps b c → ∀ {b' : Term}, SStep b b' →
    ∃ c', KSteps b' c' ∧ (SStep c c' ∨ c = c') := by
  intro b c h
  induction h with
  | refl => intro b' hs; exact ⟨b', KSteps.refl _, Or.inl hs⟩
  | @tail b d c hkd hrest ih =>
      intro b' hs
      obtain ⟨e, he1, he2⟩ := sk_local_square hkd hs
      rcases he2 with hse | rfl
      · obtain ⟨c', hc1, hc2⟩ := ih hse
        exact ⟨c', KSteps.trans he1 hc1, hc2⟩
      · exact ⟨c, KSteps.trans he1 hrest, Or.inr rfl⟩

/-- `S K K` is underapplied, hence S-normal — the fact that lets an `I` layer be observed rather
than stepped. -/
theorem sNormalForm_I : ¬ ∃ u, SStep I u := by
  rintro ⟨u, hu⟩
  cases hu with
  | appL h =>
      cases h with
      | appL h' => cases h'
      | appR h' => cases h'
  | appR h => cases h
