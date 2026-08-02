--! # Confluence for {S,C} — the SK proof, transported (Stage 119)
-- The one big SK theorem that never crossed to rung 3, needed by the decidability program
-- (unique normal forms make bounded search meaningful) and by any future normalization argument.
-- The proof is Takahashi's, mirroring Confluence.lean arm for arm: parallel reduction, the
-- complete development, the triangle property, diamond, strip. The one structural difference
-- from SK: both {S,C} rules are 3-ary and NON-ERASING, so the C-case of the development keeps
-- all three pieces developing (where K discarded one), and the 2-argument head shapes
-- (`S f g`, `C x y`) are plain — both redex inversions live at depth three.
import CombinatorCalculusPlayground.Universality.RungTermination

/-- Parallel reduction for `{S,C}`: fire any set of redexes simultaneously. -/
inductive SCPar : SCTerm → SCTerm → Prop
  | S : SCPar .S .S
  | C : SCPar .C .C
  | app {t t' u u' : SCTerm} :
      SCPar t t' → SCPar u u' → SCPar (.app t u) (.app t' u')
  | S_red {f f' g g' x x' : SCTerm} :
      SCPar f f' → SCPar g g' → SCPar x x' →
      SCPar (.app (.app (.app .S f) g) x) (.app (.app f' x') (.app g' x'))
  | C_red {x x' y y' z z' : SCTerm} :
      SCPar x x' → SCPar y y' → SCPar z z' →
      SCPar (.app (.app (.app .C x) y) z) (.app (.app x' z') y')

theorem SCPar.rfl : ∀ t : SCTerm, SCPar t t := by
  intro t
  induction t with
  | S => exact SCPar.S
  | C => exact SCPar.C
  | app t u iht ihu => exact SCPar.app iht ihu

theorem SCPar.of_step {t u : SCTerm} (h : SCStep t u) : SCPar t u := by
  induction h with
  | S_red f g x => exact SCPar.S_red (SCPar.rfl f) (SCPar.rfl g) (SCPar.rfl x)
  | C_red x y z => exact SCPar.C_red (SCPar.rfl x) (SCPar.rfl y) (SCPar.rfl z)
  | appL _ ih => exact SCPar.app ih (SCPar.rfl _)
  | appR _ ih => exact SCPar.app (SCPar.rfl _) ih

/-- Right congruence for paths (the left version is `scSteps_appL`). -/
theorem scSteps_appR (f : SCTerm) {x x' : SCTerm} (h : RS.SC.Steps x x') :
    RS.SC.Steps (.app f x) (.app f x') := by
  refine h.rec (motive := fun a b _ =>
      RS.SC.Steps (SCTerm.app f a) (SCTerm.app f b)) ?_ ?_
  · intro a
    exact @RS.Steps.refl RS.SC _
  · intro a b c s rest ih
    exact RS.Steps.tail (SCStep.appR s) ih

/-- Both-sides congruence for paths. -/
theorem scSteps_congApp {t t' u u' : SCTerm}
    (h1 : RS.SC.Steps t t') (h2 : RS.SC.Steps u u') :
    RS.SC.Steps (.app t u) (.app t' u') :=
  RS.Steps.trans (scSteps_appL u h1) (scSteps_appR t' h2)

theorem SCPar.to_steps {t u : SCTerm} (h : SCPar t u) : RS.SC.Steps t u := by
  induction h with
  | S => exact @RS.Steps.refl RS.SC _
  | C => exact @RS.Steps.refl RS.SC _
  | app _ _ iht ihu => exact scSteps_congApp iht ihu
  | S_red _ _ _ ihf ihg ihx =>
      exact RS.Steps.tail (SCStep.S_red ..)
        (scSteps_congApp (scSteps_congApp ihf ihx) (scSteps_congApp ihg ihx))
  | C_red _ _ _ ihx ihy ihz =>
      exact RS.Steps.tail (SCStep.C_red ..)
        (scSteps_congApp (scSteps_congApp ihx ihz) ihy)

/-- The complete development: fire EVERY redex at once. -/
def scDev : SCTerm → SCTerm
  | .app (.app (.app .S f) g) x =>
      .app (.app (scDev f) (scDev x)) (.app (scDev g) (scDev x))
  | .app (.app (.app .C x) y) z =>
      .app (.app (scDev x) (scDev z)) (scDev y)
  | .app t u => .app (scDev t) (scDev u)
  | t => t

theorem SCPar.S_inv {w : SCTerm} (h : SCPar .S w) : w = .S := by cases h; rfl
theorem SCPar.C_inv {w : SCTerm} (h : SCPar .C w) : w = .C := by cases h; rfl

/-- The triangle: every parallel step from `t` rejoins at `scDev t` in one more. -/
theorem SCPar.triangle : ∀ {t u : SCTerm}, SCPar t u → SCPar u (scDev t) := by
  intro t u h
  induction h with
  | S => exact SCPar.S
  | C => exact SCPar.C
  | S_red hf hg hx ihf ihg ihx =>
      simpa only [scDev] using SCPar.app (SCPar.app ihf ihx) (SCPar.app ihg ihx)
  | C_red hx hy hz ihx ihy ihz =>
      simpa only [scDev] using SCPar.app (SCPar.app ihx ihz) ihy
  | @app a a' b b' hl hr ihl ihr =>
      cases a with
      | S => exact SCPar.app ihl ihr
      | C => exact SCPar.app ihl ihr
      | app c d =>
        cases c with
        | S => exact SCPar.app ihl ihr
        | C => exact SCPar.app ihl ihr
        | app e f =>
          cases e with
          | app _ _ => exact SCPar.app ihl ihr
          | S =>
              cases hl with
              | app hw hd =>
                cases hw with
                | app hS hf =>
                  obtain rfl := SCPar.S_inv hS
                  simp only [scDev] at ihl ⊢
                  cases ihl with
                  | app h1 h2 =>
                    cases h1 with
                    | app _ hf' => exact SCPar.S_red hf' h2 ihr
          | C =>
              cases hl with
              | app hw hd =>
                cases hw with
                | app hC hx =>
                  obtain rfl := SCPar.C_inv hC
                  simp only [scDev] at ihl ⊢
                  cases ihl with
                  | app h1 h2 =>
                    cases h1 with
                    | app _ hx' => exact SCPar.C_red hx' h2 ihr

theorem SCPar.to_dev (t : SCTerm) : SCPar t (scDev t) := (SCPar.rfl t).triangle

/-- Triangle → diamond, with no induction. -/
theorem SCPar.diamond {t u v : SCTerm} (hu : SCPar t u) (hv : SCPar t v) :
    ∃ w, SCPar u w ∧ SCPar v w :=
  ⟨scDev t, hu.triangle, hv.triangle⟩

/-- Multi-step parallel reduction. -/
inductive SCPars : SCTerm → SCTerm → Prop
  | refl (t : SCTerm) : SCPars t t
  | tail {t u v : SCTerm} : SCPar t u → SCPars u v → SCPars t v

theorem SCPars.strip {t u v : SCTerm} (hu : SCPar t u) (hv : SCPars t v) :
    ∃ w, SCPars u w ∧ SCPar v w := by
  induction hv generalizing u with
  | refl => exact ⟨u, SCPars.refl u, hu⟩
  | tail hp _ ih =>
      obtain ⟨w₁, huw₁, hpw₁⟩ := SCPar.diamond hu hp
      obtain ⟨w, hww, hvw⟩ := ih hpw₁
      exact ⟨w, SCPars.tail huw₁ hww, hvw⟩

theorem SCPars.diamond {t u v : SCTerm} (hu : SCPars t u) (hv : SCPars t v) :
    ∃ w, SCPars u w ∧ SCPars v w := by
  induction hu generalizing v with
  | refl => exact ⟨v, hv, SCPars.refl v⟩
  | tail hp _ ih =>
      obtain ⟨w₁, hw₁, hvw₁⟩ := SCPars.strip hp hv
      obtain ⟨w, huw, hw₁w⟩ := ih hw₁
      exact ⟨w, huw, SCPars.tail hvw₁ hw₁w⟩

theorem scSteps_to_pars {t u : SCTerm} (h : RS.SC.Steps t u) : SCPars t u := by
  refine h.rec (motive := fun a b _ => SCPars a b) ?_ ?_
  · intro a
    exact SCPars.refl a
  · intro a b c s rest ih
    exact SCPars.tail (SCPar.of_step s) ih

theorem SCPars.to_steps {t u : SCTerm} (h : SCPars t u) : RS.SC.Steps t u := by
  induction h with
  | refl => exact @RS.Steps.refl RS.SC _
  | tail hp _ ih => exact RS.Steps.trans hp.to_steps ih

/-- **Church–Rosser for `{S,C}`.** -/
theorem SC_confluence {t u v : SCTerm}
    (h1 : RS.SC.Steps t u) (h2 : RS.SC.Steps t v) :
    ∃ w, RS.SC.Steps u w ∧ RS.SC.Steps v w := by
  obtain ⟨w, hw1, hw2⟩ := SCPars.diamond (scSteps_to_pars h1) (scSteps_to_pars h2)
  exact ⟨w, hw1.to_steps, hw2.to_steps⟩

/-- Normal forms are unique in `{S,C}`. -/
theorem sc_nf_unique {t u v : SCTerm}
    (h1 : RS.SC.Steps t u) (h2 : RS.SC.Steps t v)
    (hu : RS.NormalForm RS.SC u) (hv : RS.NormalForm RS.SC v) : u = v := by
  obtain ⟨w, hw1, hw2⟩ := SC_confluence h1 h2
  rw [hu.steps_eq hw1, hv.steps_eq hw2]

-- ## Stage 120: the normal forms of {S,C} — spine-width ≤ 2, everywhere
-- The analogue of Goal 1's `SNF_iff`: a `{S,C}` term is normal exactly when every spine carries
-- at most two arguments (neither combinator has enough arguments to fire anywhere). With
-- `sc_nf_unique`, "the" normal form of a normalizing term is now a well-defined object.

/-- Spine-width-≤-2 shapes: a leaf, or a leaf applied to one or two normal arguments. -/
inductive SCNF : SCTerm → Prop
  | leafS : SCNF .S
  | leafC : SCNF .C
  | one {k a : SCTerm} : (k = .S ∨ k = .C) → SCNF a → SCNF (.app k a)
  | two {k a b : SCTerm} : (k = .S ∨ k = .C) → SCNF a → SCNF b →
      SCNF (.app (.app k a) b)

/-- `SCNF` terms have no steps. -/
theorem SCNF.no_step : ∀ {t : SCTerm}, SCNF t → ¬ ∃ u, SCStep t u := by
  intro t h
  induction h with
  | leafS =>
      rintro ⟨u, hs⟩
      obtain ⟨a, b, hab⟩ := scStep_source_isApp hs
      exact SCTerm.noConfusion hab
  | leafC =>
      rintro ⟨u, hs⟩
      obtain ⟨a, b, hab⟩ := scStep_source_isApp hs
      exact SCTerm.noConfusion hab
  | one hk ha iha =>
      rintro ⟨u, hs⟩
      rcases scStep_cases hs with hroot | ⟨F, X, F', j1, j2, hst⟩ | ⟨F, X, X', j1, j2, hst⟩
      · rcases scRootStep_inv hroot with ⟨p, q, r, hb, _⟩ | ⟨p, q, r, hb, _⟩
        · injection hb with h1 h2
          rcases hk with rfl | rfl
          · exact SCTerm.noConfusion h1
          · exact SCTerm.noConfusion h1
        · injection hb with h1 h2
          rcases hk with rfl | rfl
          · exact SCTerm.noConfusion h1
          · exact SCTerm.noConfusion h1
      · injection j1 with j3 j4
        obtain ⟨a', b', hab⟩ := scStep_source_isApp hst
        rw [← j3] at hab
        rcases hk with rfl | rfl
        · exact SCTerm.noConfusion hab
        · exact SCTerm.noConfusion hab
      · injection j1 with j3 j4
        exact iha ⟨X', by rw [j4]; exact hst⟩
  | two hk ha hb iha ihb =>
      rintro ⟨u, hs⟩
      rcases scStep_cases hs with hroot | ⟨F, X, F', j1, j2, hst⟩ | ⟨F, X, X', j1, j2, hst⟩
      · rcases scRootStep_inv hroot with ⟨p, q, r, hb2, _⟩ | ⟨p, q, r, hb2, _⟩
        · injection hb2 with h1 h2
          injection h1 with h3 h4
          rcases hk with rfl | rfl
          · exact SCTerm.noConfusion h3
          · exact SCTerm.noConfusion h3
        · injection hb2 with h1 h2
          injection h1 with h3 h4
          rcases hk with rfl | rfl
          · exact SCTerm.noConfusion h3
          · exact SCTerm.noConfusion h3
      · injection j1 with j3 j4
        rcases scStep_cases (show SCStep (SCTerm.app _ _) F' from by rw [j3]; exact hst) with
          hroot2 | ⟨F₂, X₂, F₂', l1, l2, hst2⟩ | ⟨F₂, X₂, X₂', l1, l2, hst2⟩
        · rcases scRootStep_inv hroot2 with ⟨p, q, r, hb2, _⟩ | ⟨p, q, r, hb2, _⟩
          · injection hb2 with h1 h2
            rcases hk with rfl | rfl
            · exact SCTerm.noConfusion h1
            · exact SCTerm.noConfusion h1
          · injection hb2 with h1 h2
            rcases hk with rfl | rfl
            · exact SCTerm.noConfusion h1
            · exact SCTerm.noConfusion h1
        · injection l1 with l3 l4
          obtain ⟨a', b', hab⟩ := scStep_source_isApp hst2
          rw [← l3] at hab
          rcases hk with rfl | rfl
          · exact SCTerm.noConfusion hab
          · exact SCTerm.noConfusion hab
        · injection l1 with l3 l4
          exact iha ⟨X₂', by rw [l4]; exact hst2⟩
      · injection j1 with j3 j4
        exact ihb ⟨X', by rw [j4]; exact hst⟩

/-- Steplessness implies the shape. -/
theorem SCNF.of_no_step : ∀ {t : SCTerm}, (¬ ∃ u, SCStep t u) → SCNF t := by
  intro t
  induction t with
  | S =>
      intro _
      exact SCNF.leafS
  | C =>
      intro _
      exact SCNF.leafC
  | app f x ihf ihx =>
      intro h
      have hf : ¬ ∃ u, SCStep f u := fun ⟨u, hu⟩ => h ⟨.app u x, SCStep.appL hu⟩
      have hx : ¬ ∃ u, SCStep x u := fun ⟨u, hu⟩ => h ⟨.app f u, SCStep.appR hu⟩
      have hxn := ihx hx
      cases ihf hf with
      | leafS => exact SCNF.one (Or.inl rfl) hxn
      | leafC => exact SCNF.one (Or.inr rfl) hxn
      | one hk ha => exact SCNF.two hk ha hxn
      | two hk ha hb =>
          rcases hk with rfl | rfl
          · exact absurd ⟨_, SCStep.S_red _ _ x⟩ h
          · exact absurd ⟨_, SCStep.C_red _ _ x⟩ h

/-- **The normal forms of `{S,C}` are exactly the spine-width-≤-2 shapes** — the rung-3
analogue of `SNF_iff`. -/
theorem SCNF_iff (t : SCTerm) : SCNF t ↔ ¬ ∃ u, SCStep t u :=
  ⟨SCNF.no_step, SCNF.of_no_step⟩
