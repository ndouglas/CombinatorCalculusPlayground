--! # The ranked route, typechecked at last
-- Stage 80. "Rungs 2/3 via match-bounds" has sat in the ranking since Stage 44 — thirty-five
-- stages — and was never typechecked. Match-bounds are TERMINATION certificates: they prove a
-- rewriting system terminating (or relatively terminating), and acyclicity follows from
-- termination. But `{S,B}` and `{S,C}` each CONTAIN pure S — the B-free (resp. C-free) fragment
-- steps identically — and C1(a) proved pure S has a term with no normal form. Transporting that
-- witness shows the full rung systems are not even weakly normalizing, so NO termination
-- certificate of any kind — match-bounds included — can exist for them. The route as recorded is
-- not hard; it is TYPE-INCORRECT.
--
-- What survives: a certificate for LOOP-FREENESS of a non-terminating system. That is the corrected
-- open problem — relative/transformed match-bounds whose termination is equivalent to the absence
-- of cycles, or the unbounded well-founded measure Stage 44 already named. Sharper, and now with
-- the impossibility half machine-checked.
import CombinatorCalculusPlayground.Universality.Ladder
import CombinatorCalculusPlayground.Recurrence

open Term

/-- The FULL rung-two system, as a rewriting system (the fragments each had one; the whole did not). -/
def RS.SB : RS := ⟨SBTerm, SBStep⟩

/-- The full rung-three system. -/
def RS.SC : RS := ⟨SCTerm, SCStep⟩

-- ## The B-free embedding of pure S into {S,B}

/-- `S ↦ S`, `app ↦ app`; `K ↦ B` is junk that K-free terms never exercise — and keeps the map
injective on constructors, which is what the inversions below use. -/
def sbOfTerm : Term → SBTerm
  | Term.S => .S
  | Term.K => .B
  | Term.app a b => .app (sbOfTerm a) (sbOfTerm b)

theorem sbOfTerm_eq_S {t : Term} (h : sbOfTerm t = .S) : t = Term.S := by
  cases t with
  | S => rfl
  | K => exact SBTerm.noConfusion h
  | app a b => exact SBTerm.noConfusion h

theorem sbOfTerm_eq_B {t : Term} (h : sbOfTerm t = .B) : t = Term.K := by
  cases t with
  | S => exact SBTerm.noConfusion h
  | K => rfl
  | app a b => exact SBTerm.noConfusion h

theorem sbOfTerm_eq_app {t : Term} {X Y : SBTerm} (h : sbOfTerm t = .app X Y) :
    ∃ a b, t = Term.app a b ∧ sbOfTerm a = X ∧ sbOfTerm b = Y := by
  cases t with
  | S => exact SBTerm.noConfusion h
  | K => exact SBTerm.noConfusion h
  | app a b =>
      injection h with h1 h2
      exact ⟨a, b, rfl, h1, h2⟩

/-- Forward: a K-free step is an {S,B} step on the image. -/
theorem sbOfTerm_step {t u : Term} (hk : KFree t) (h : t ⟶ u) :
    SBStep (sbOfTerm t) (sbOfTerm u) := by
  induction h with
  | K_red x y =>
      cases hk with
      | app h1 _ =>
          cases h1 with
          | app h2 _ => cases h2
  | S_red f g x => exact SBStep.S_red _ _ _
  | appL h ih =>
      cases hk with
      | app h1 h2 => exact SBStep.appL (ih h1)
  | appR h ih =>
      cases hk with
      | app h1 h2 => exact SBStep.appR (ih h2)

/-- Backward: an {S,B} step out of the image of a K-free term is the image of a step — `B_red`
would need a `B`, and the image of a K-free term has none. -/
theorem sbOfTerm_step_back {t : Term} (hk : KFree t) {a u' : SBTerm}
    (ha : sbOfTerm t = a) (h : SBStep a u') :
    ∃ u, u' = sbOfTerm u ∧ (t ⟶ u) := by
  induction h generalizing t with
  | S_red f g x =>
      obtain ⟨t3, x', rfl, h3, hx⟩ := sbOfTerm_eq_app ha
      obtain ⟨t2, g', rfl, h2, hg⟩ := sbOfTerm_eq_app h3
      obtain ⟨t1, f', rfl, h1, hf⟩ := sbOfTerm_eq_app h2
      rw [sbOfTerm_eq_S h1]
      exact ⟨Term.app (Term.app f' x') (Term.app g' x'),
        by rw [← hf, ← hg, ← hx]; rfl, Step.S_red f' g' x'⟩
  | B_red x y z =>
      obtain ⟨t3, z', rfl, h3, _⟩ := sbOfTerm_eq_app ha
      obtain ⟨t2, y', rfl, h2, _⟩ := sbOfTerm_eq_app h3
      obtain ⟨t1, x', rfl, h1, _⟩ := sbOfTerm_eq_app h2
      rw [sbOfTerm_eq_B h1] at hk
      cases hk with
      | app h4 _ =>
          cases h4 with
          | app h5 _ =>
              cases h5 with
              | app h6 _ => cases h6
  | appL hs ih =>
      obtain ⟨a', b', rfl, h1, h2⟩ := sbOfTerm_eq_app ha
      cases hk with
      | app hka hkb =>
          obtain ⟨u1, hu1, hstep⟩ := ih hka h1
          exact ⟨Term.app u1 b', by rw [hu1, ← h2]; rfl, Step.appL hstep⟩
  | appR hs ih =>
      obtain ⟨a', b', rfl, h1, h2⟩ := sbOfTerm_eq_app ha
      cases hk with
      | app hka hkb =>
          obtain ⟨u1, hu1, hstep⟩ := ih hkb h2
          exact ⟨Term.app a' u1, by rw [hu1, ← h1]; rfl, Step.appR hstep⟩

/-- Backward, for whole paths — the image of a K-free term can only ever walk inside the image. -/
theorem sb_steps_back : ∀ {a b : SBTerm}, RS.SB.Steps a b → ∀ {t : Term}, KFree t →
    sbOfTerm t = a → ∃ u, b = sbOfTerm u ∧ (t ⟶* u) ∧ KFree u := by
  intro a b h
  exact h.rec
    (motive := fun a b _ => ∀ {t : Term}, KFree t → sbOfTerm t = a →
      ∃ u, b = sbOfTerm u ∧ (t ⟶* u) ∧ KFree u)
    (fun a {t} hk ha => ⟨t, ha.symm, Steps.refl t, hk⟩)
    (fun {a c b} s _ ih {t} hk ha => by
      obtain ⟨u1, hc, hs⟩ := sbOfTerm_step_back hk ha s
      obtain ⟨u, hb, hp, hku⟩ := ih (hk.of_step hs) hc.symm
      exact ⟨u, hb, Steps.tail hs hp, hku⟩)

/-- **Rung two's full system is not even weakly normalizing** — C1(a)'s divergent pure-S term
diverges here too. So no termination certificate, match-bounds included, can exist for `{S,B}`. -/
theorem SB_not_normalizing : ∃ t : SBTerm, ¬ RS.SB.Normalizes t := by
  obtain ⟨t₀, hk, hno⟩ := c1a
  refine ⟨sbOfTerm t₀, ?_⟩
  rintro ⟨n', hpath, hnf⟩
  obtain ⟨n, rfl, hp, hkn⟩ := sb_steps_back hpath hk rfl
  exact hno ⟨n, hp, fun ⟨u, hu⟩ => hnf ⟨_, sbOfTerm_step hkn hu⟩⟩

-- ## The same, for rung three

def scOfTerm : Term → SCTerm
  | Term.S => .S
  | Term.K => .C
  | Term.app a b => .app (scOfTerm a) (scOfTerm b)

theorem scOfTerm_eq_S {t : Term} (h : scOfTerm t = .S) : t = Term.S := by
  cases t with
  | S => rfl
  | K => exact SCTerm.noConfusion h
  | app a b => exact SCTerm.noConfusion h

theorem scOfTerm_eq_C {t : Term} (h : scOfTerm t = .C) : t = Term.K := by
  cases t with
  | S => exact SCTerm.noConfusion h
  | K => rfl
  | app a b => exact SCTerm.noConfusion h

theorem scOfTerm_eq_app {t : Term} {X Y : SCTerm} (h : scOfTerm t = .app X Y) :
    ∃ a b, t = Term.app a b ∧ scOfTerm a = X ∧ scOfTerm b = Y := by
  cases t with
  | S => exact SCTerm.noConfusion h
  | K => exact SCTerm.noConfusion h
  | app a b =>
      injection h with h1 h2
      exact ⟨a, b, rfl, h1, h2⟩

theorem scOfTerm_step {t u : Term} (hk : KFree t) (h : t ⟶ u) :
    SCStep (scOfTerm t) (scOfTerm u) := by
  induction h with
  | K_red x y =>
      cases hk with
      | app h1 _ =>
          cases h1 with
          | app h2 _ => cases h2
  | S_red f g x => exact SCStep.S_red _ _ _
  | appL h ih =>
      cases hk with
      | app h1 h2 => exact SCStep.appL (ih h1)
  | appR h ih =>
      cases hk with
      | app h1 h2 => exact SCStep.appR (ih h2)

theorem scOfTerm_step_back {t : Term} (hk : KFree t) {a u' : SCTerm}
    (ha : scOfTerm t = a) (h : SCStep a u') :
    ∃ u, u' = scOfTerm u ∧ (t ⟶ u) := by
  induction h generalizing t with
  | S_red f g x =>
      obtain ⟨t3, x', rfl, h3, hx⟩ := scOfTerm_eq_app ha
      obtain ⟨t2, g', rfl, h2, hg⟩ := scOfTerm_eq_app h3
      obtain ⟨t1, f', rfl, h1, hf⟩ := scOfTerm_eq_app h2
      rw [scOfTerm_eq_S h1]
      exact ⟨Term.app (Term.app f' x') (Term.app g' x'),
        by rw [← hf, ← hg, ← hx]; rfl, Step.S_red f' g' x'⟩
  | C_red x y z =>
      obtain ⟨t3, z', rfl, h3, _⟩ := scOfTerm_eq_app ha
      obtain ⟨t2, y', rfl, h2, _⟩ := scOfTerm_eq_app h3
      obtain ⟨t1, x', rfl, h1, _⟩ := scOfTerm_eq_app h2
      rw [scOfTerm_eq_C h1] at hk
      cases hk with
      | app h4 _ =>
          cases h4 with
          | app h5 _ =>
              cases h5 with
              | app h6 _ => cases h6
  | appL hs ih =>
      obtain ⟨a', b', rfl, h1, h2⟩ := scOfTerm_eq_app ha
      cases hk with
      | app hka hkb =>
          obtain ⟨u1, hu1, hstep⟩ := ih hka h1
          exact ⟨Term.app u1 b', by rw [hu1, ← h2]; rfl, Step.appL hstep⟩
  | appR hs ih =>
      obtain ⟨a', b', rfl, h1, h2⟩ := scOfTerm_eq_app ha
      cases hk with
      | app hka hkb =>
          obtain ⟨u1, hu1, hstep⟩ := ih hkb h2
          exact ⟨Term.app a' u1, by rw [hu1, ← h1]; rfl, Step.appR hstep⟩

theorem sc_steps_back : ∀ {a b : SCTerm}, RS.SC.Steps a b → ∀ {t : Term}, KFree t →
    scOfTerm t = a → ∃ u, b = scOfTerm u ∧ (t ⟶* u) ∧ KFree u := by
  intro a b h
  exact h.rec
    (motive := fun a b _ => ∀ {t : Term}, KFree t → scOfTerm t = a →
      ∃ u, b = scOfTerm u ∧ (t ⟶* u) ∧ KFree u)
    (fun a {t} hk ha => ⟨t, ha.symm, Steps.refl t, hk⟩)
    (fun {a c b} s _ ih {t} hk ha => by
      obtain ⟨u1, hc, hs⟩ := scOfTerm_step_back hk ha s
      obtain ⟨u, hb, hp, hku⟩ := ih (hk.of_step hs) hc.symm
      exact ⟨u, hb, Steps.tail hs hp, hku⟩)

/-- **Rung three's full system is not weakly normalizing either.** -/
theorem SC_not_normalizing : ∃ t : SCTerm, ¬ RS.SC.Normalizes t := by
  obtain ⟨t₀, hk, hno⟩ := c1a
  refine ⟨scOfTerm t₀, ?_⟩
  rintro ⟨n', hpath, hnf⟩
  obtain ⟨n, rfl, hp, hkn⟩ := sc_steps_back hpath hk rfl
  exact hno ⟨n, hp, fun ⟨u, hu⟩ => hnf ⟨_, scOfTerm_step hkn hu⟩⟩

-- ## What this settles about the ranked route
-- Acyclicity-via-termination is CLOSED for both rungs: the systems have divergent terms, so no
-- termination proof — by match-bounds, by any measure, by any method — exists to imply it. The
-- corrected open problem, now stated with its impossibility half machine-checked: certify
-- LOOP-FREENESS of a non-terminating system. The two live shapes remain the ones Stage 44 named —
-- a relative/transformed match-bound whose termination is EQUIVALENT to the absence of {S,B}-cycles
-- (unbuilt, and the transformation is the research content), or an unbounded well-founded measure
-- (unfound). The ledger's necessary conditions (a cycle needs a B-duplicating S-step on a τ-heavy,
-- ≥3-leaf argument) are constraints any such certificate may consume.
