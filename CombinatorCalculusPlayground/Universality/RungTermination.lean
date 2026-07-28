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
import CombinatorCalculusPlayground.Universality.Calibration
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

-- ## Stage 81: cycle localization — a minimal cycle passes through a ROOT redex
-- The design probe's survivor. All prior necessary conditions on rung-2 cycles came from measures;
-- this one comes from projection: a cycle whose steps all happen inside arguments projects to a
-- strictly smaller cycle on one argument, so a minimal cycle must fire a redex AT THE ROOT. The
-- corrected open problem shrinks again: to prove `{S,B}` acyclic it now SUFFICES to rule out cycles
-- through root redexes (`sb_acyclic_of_no_root_cycle`) — terms of the very specific shapes
-- `S f g x` and `B x y z` that reduce back to themselves.

/-- A step at the root — no congruence. -/
inductive SBRootStep : SBTerm → SBTerm → Prop
  | S_red (f g x : SBTerm) :
      SBRootStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | B_red (x y z : SBTerm) :
      SBRootStep (.app (.app (.app .B x) y) z) (.app x (.app y z))

/-- A nonempty reduction. -/
def SBPlus (a b : SBTerm) : Prop := ∃ c, SBStep a c ∧ RS.SB.Steps c b

theorem sbLeaf_pos : ∀ t : SBTerm, 1 ≤ t.leafCount := by
  intro t
  induction t with
  | S => exact Nat.le_refl 1
  | B => exact Nat.le_refl 1
  | app a b iha ihb =>
      show 1 ≤ a.leafCount + b.leafCount
      omega

/-- Every step is a root step or a projection into one side. -/
theorem sbStep_cases {t w : SBTerm} (h : SBStep t w) :
    SBRootStep t w
    ∨ (∃ f x f', t = .app f x ∧ w = .app f' x ∧ SBStep f f')
    ∨ (∃ f x x', t = .app f x ∧ w = .app f x' ∧ SBStep x x') := by
  cases h with
  | S_red f g x => exact Or.inl (SBRootStep.S_red f g x)
  | B_red x y z => exact Or.inl (SBRootStep.B_red x y z)
  | appL h => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩)
  | appR h => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, h⟩)

/-- Path dichotomy: a path contains a root step, or is trivial, or projects into the two sides —
with at least one side's projection nonempty when the path is. -/
theorem sb_path_facts : ∀ {t u : SBTerm}, RS.SB.Steps t u →
    (∃ a b, SBRootStep a b ∧ RS.SB.Steps t a ∧ RS.SB.Steps b u)
    ∨ t = u
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SB.Steps f f' ∧ RS.SB.Steps x x'
        ∧ (SBPlus f f' ∨ SBPlus x x')) := by
  intro t u h
  exact h.rec
    (motive := fun t u _ =>
      (∃ a b, SBRootStep a b ∧ RS.SB.Steps t a ∧ RS.SB.Steps b u)
      ∨ t = u
      ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SB.Steps f f' ∧ RS.SB.Steps x x'
          ∧ (SBPlus f f' ∨ SBPlus x x')))
    (fun a => Or.inr (Or.inl rfl))
    (fun {a c b} s rest ih => by
      rcases sbStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
      · exact Or.inl ⟨a, c, hroot, @RS.Steps.refl RS.SB a, rest⟩
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SB _ _ hs,
            @RS.Steps.refl RS.SB x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SB f'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px,
            Or.inl ⟨f', hs, pf⟩⟩)
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SB f,
            @RS.Steps.single RS.SB _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SB x'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px,
            Or.inr ⟨x', hs, px⟩⟩))

/-- The same, for NONEMPTY paths: the trivial disjunct disappears. -/
theorem sb_plus_facts {t u : SBTerm} (h : SBPlus t u) :
    (∃ a b, SBRootStep a b ∧ RS.SB.Steps t a ∧ RS.SB.Steps b u)
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SB.Steps f f' ∧ RS.SB.Steps x x'
        ∧ (SBPlus f f' ∨ SBPlus x x')) := by
  obtain ⟨c, s, rest⟩ := h
  rcases sbStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
  · exact Or.inl ⟨t, c, hroot, @RS.Steps.refl RS.SB t, rest⟩
  · subst heq
    rcases sb_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SB _ _ hs,
        @RS.Steps.refl RS.SB x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SB f'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px, Or.inl ⟨f', hs, pf⟩⟩
  · subst heq
    rcases sb_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SB f,
        @RS.Steps.single RS.SB _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SB x'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px, Or.inr ⟨x', hs, px⟩⟩

/-- **Cycle localization.** Any cycle yields a cycle through a root redex — strong induction on
size, projecting rootless cycles into a strictly smaller argument. -/
theorem sb_cycle_root_aux : ∀ (n : Nat) (t v : SBTerm), t.leafCount ≤ n →
    SBStep t v → RS.SB.Steps v t →
    ∃ a b, SBRootStep a b ∧ RS.SB.Steps b a := by
  intro n
  induction n with
  | zero =>
      intro t v hle _ _
      exact absurd hle (by have := sbLeaf_pos t; omega)
  | succ n ih =>
      intro t v hle hs hback
      rcases sb_plus_facts ⟨v, hs, hback⟩ with
        ⟨a, b, hr, h1, h2⟩ | ⟨f, x, f', x', heq1, heq2, pf, px, hne⟩
      · exact ⟨a, b, hr, RS.Steps.trans h2 h1⟩
      · subst heq1
        injection heq2 with h1 h2
        subst h1; subst h2
        have hsz : f.leafCount + x.leafCount ≤ n + 1 := hle
        rcases hne with ⟨fm, hsf, hpf⟩ | ⟨xm, hsx, hpx⟩
        · exact ih f fm (by have := sbLeaf_pos x; omega) hsf hpf
        · exact ih x xm (by have := sbLeaf_pos f; omega) hsx hpx

/-- The packaging: any cycle witness produces a root-cycle witness. -/
theorem sb_cycle_needs_root {t v : SBTerm} (hs : SBStep t v) (hback : RS.SB.Steps v t) :
    ∃ a b, SBRootStep a b ∧ RS.SB.Steps b a :=
  sb_cycle_root_aux t.leafCount t v (Nat.le_refl _) hs hback

/-- **The reduction of rung 2**: to prove `{S,B}` acyclic, it suffices to rule out cycles through
root redexes — terms `S f g x` and `B x y z` whose contraction reduces back to them. -/
theorem sb_acyclic_of_no_root_cycle
    (h : ∀ a b, SBRootStep a b → ¬ RS.SB.Steps b a) : RS.Acyclic RS.SB := by
  intro t v hs hback
  obtain ⟨a, b, hr, hcyc⟩ := sb_cycle_needs_root hs hback
  exact h a b hr hcyc

-- ### The same, for rung three — parity maintained

/-- A step at the root — no congruence. -/
inductive SCRootStep : SCTerm → SCTerm → Prop
  | S_red (f g x : SCTerm) :
      SCRootStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | C_red (x y z : SCTerm) :
      SCRootStep (.app (.app (.app .C x) y) z) (.app (.app x z) y)

/-- A nonempty reduction. -/
def SCPlus (a b : SCTerm) : Prop := ∃ c, SCStep a c ∧ RS.SC.Steps c b

theorem scLeaf_pos : ∀ t : SCTerm, 1 ≤ t.leafCount := by
  intro t
  induction t with
  | S => exact Nat.le_refl 1
  | C => exact Nat.le_refl 1
  | app a b iha ihb =>
      show 1 ≤ a.leafCount + b.leafCount
      omega

/-- Every step is a root step or a projection into one side. -/
theorem scStep_cases {t w : SCTerm} (h : SCStep t w) :
    SCRootStep t w
    ∨ (∃ f x f', t = .app f x ∧ w = .app f' x ∧ SCStep f f')
    ∨ (∃ f x x', t = .app f x ∧ w = .app f x' ∧ SCStep x x') := by
  cases h with
  | S_red f g x => exact Or.inl (SCRootStep.S_red f g x)
  | C_red x y z => exact Or.inl (SCRootStep.C_red x y z)
  | appL h => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩)
  | appR h => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, h⟩)

/-- Path dichotomy: a path contains a root step, or is trivial, or projects into the two sides —
with at least one side's projection nonempty when the path is. -/
theorem sc_path_facts : ∀ {t u : SCTerm}, RS.SC.Steps t u →
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps t a ∧ RS.SC.Steps b u)
    ∨ t = u
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps x x'
        ∧ (SCPlus f f' ∨ SCPlus x x')) := by
  intro t u h
  exact h.rec
    (motive := fun t u _ =>
      (∃ a b, SCRootStep a b ∧ RS.SC.Steps t a ∧ RS.SC.Steps b u)
      ∨ t = u
      ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps x x'
          ∧ (SCPlus f f' ∨ SCPlus x x')))
    (fun a => Or.inr (Or.inl rfl))
    (fun {a c b} s rest ih => by
      rcases scStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
      · exact Or.inl ⟨a, c, hroot, @RS.Steps.refl RS.SC a, rest⟩
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SC _ _ hs,
            @RS.Steps.refl RS.SC x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SC f'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px,
            Or.inl ⟨f', hs, pf⟩⟩)
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SC f,
            @RS.Steps.single RS.SC _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SC x'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px,
            Or.inr ⟨x', hs, px⟩⟩))

/-- The same, for NONEMPTY paths: the trivial disjunct disappears. -/
theorem sc_plus_facts {t u : SCTerm} (h : SCPlus t u) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps t a ∧ RS.SC.Steps b u)
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps x x'
        ∧ (SCPlus f f' ∨ SCPlus x x')) := by
  obtain ⟨c, s, rest⟩ := h
  rcases scStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
  · exact Or.inl ⟨t, c, hroot, @RS.Steps.refl RS.SC t, rest⟩
  · subst heq
    rcases sc_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SC _ _ hs,
        @RS.Steps.refl RS.SC x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SC f'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px, Or.inl ⟨f', hs, pf⟩⟩
  · subst heq
    rcases sc_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SC f,
        @RS.Steps.single RS.SC _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SC x'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px, Or.inr ⟨x', hs, px⟩⟩

/-- **Cycle localization.** Any cycle yields a cycle through a root redex — strong induction on
size, projecting rootless cycles into a strictly smaller argument. -/
theorem sc_cycle_root_aux : ∀ (n : Nat) (t v : SCTerm), t.leafCount ≤ n →
    SCStep t v → RS.SC.Steps v t →
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps b a := by
  intro n
  induction n with
  | zero =>
      intro t v hle _ _
      exact absurd hle (by have := scLeaf_pos t; omega)
  | succ n ih =>
      intro t v hle hs hback
      rcases sc_plus_facts ⟨v, hs, hback⟩ with
        ⟨a, b, hr, h1, h2⟩ | ⟨f, x, f', x', heq1, heq2, pf, px, hne⟩
      · exact ⟨a, b, hr, RS.Steps.trans h2 h1⟩
      · subst heq1
        injection heq2 with h1 h2
        subst h1; subst h2
        have hsz : f.leafCount + x.leafCount ≤ n + 1 := hle
        rcases hne with ⟨fm, hsf, hpf⟩ | ⟨xm, hsx, hpx⟩
        · exact ih f fm (by have := scLeaf_pos x; omega) hsf hpf
        · exact ih x xm (by have := scLeaf_pos f; omega) hsx hpx

/-- The packaging: any cycle witness produces a root-cycle witness. -/
theorem sc_cycle_needs_root {t v : SCTerm} (hs : SCStep t v) (hback : RS.SC.Steps v t) :
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps b a :=
  sc_cycle_root_aux t.leafCount t v (Nat.le_refl _) hs hback

/-- **The reduction of rung 3**, at parity: `{S,C}` is acyclic if no root redex cycles. -/
theorem sc_acyclic_of_no_root_cycle
    (h : ∀ a b, SCRootStep a b → ¬ RS.SC.Steps b a) : RS.Acyclic RS.SC := by
  intro t v hs hback
  obtain ⟨a, b, hr, hcyc⟩ := sc_cycle_needs_root hs hback
  exact h a b hr hcyc

-- ## Stage 82: what a root cycle's return path must do
-- Stage 81 reduced the rungs to root-redex cycles. Applying its own path dichotomy to the RETURN
-- path splits each root cycle into two shapes: the return contains ANOTHER root step, or it
-- projects into the redex's two sides — and the projections are remarkable: `g x ⟶* x` (a term
-- COLLAPSING to its own argument) and `f x ⟶* S f g` (self-embedding under application). The
-- degenerate branch dies on size. Collapse-to-argument appears in BOTH rules' dichotomies, making
-- it the single sub-target that would force every root cycle's return path to carry root steps of
-- its own.

/-- A root S-cycle's return path either carries a root step, or projects:
`f x ⟶* S f g` and `g x ⟶* x`. -/
theorem sb_root_S_return {f g x : SBTerm}
    (hback : RS.SB.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ a b, SBRootStep a b ∧ RS.SB.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SB.Steps b (.app (.app (.app .S f) g) x))
    ∨ (RS.SB.Steps (.app f x) (.app (.app .S f) g) ∧ RS.SB.Steps (.app g x) x) := by
  rcases sb_path_facts hback with h | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
  · exact Or.inl h
  · exfalso
    injection heq with h1 h2
    have hc := congrArg SBTerm.leafCount h2
    have hg := sbLeaf_pos g
    exact absurd hc (by
      show ¬(g.leafCount + x.leafCount = x.leafCount)
      omega)
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    exact Or.inr ⟨pf, px⟩

/-- A root B-cycle's return path either carries a root step, or projects:
`x ⟶* B x y` (self-embedding) and `y z ⟶* z` (collapse to argument). -/
theorem sb_root_B_return {x y z : SBTerm}
    (hback : RS.SB.Steps (.app x (.app y z)) (.app (.app (.app .B x) y) z)) :
    (∃ a b, SBRootStep a b ∧ RS.SB.Steps (.app x (.app y z)) a
      ∧ RS.SB.Steps b (.app (.app (.app .B x) y) z))
    ∨ (RS.SB.Steps x (.app (.app .B x) y) ∧ RS.SB.Steps (.app y z) z) := by
  rcases sb_path_facts hback with h | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
  · exact Or.inl h
  · exfalso
    injection heq with h1 h2
    have hc := congrArg SBTerm.leafCount h1
    have hy := sbLeaf_pos y
    exact absurd hc (by
      show ¬(x.leafCount = (1 + x.leafCount) + y.leafCount)
      omega)
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    exact Or.inr ⟨pf, px⟩

/-- Rung three's mirrors, at parity: the root S-case is identical... -/
theorem sc_root_S_return {f g x : SCTerm}
    (hback : RS.SC.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SC.Steps b (.app (.app (.app .S f) g) x))
    ∨ (RS.SC.Steps (.app f x) (.app (.app .S f) g) ∧ RS.SC.Steps (.app g x) x) := by
  rcases sc_path_facts hback with h | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
  · exact Or.inl h
  · exfalso
    injection heq with h1 h2
    have hc := congrArg SCTerm.leafCount h2
    have hg := scLeaf_pos g
    exact absurd hc (by
      show ¬(g.leafCount + x.leafCount = x.leafCount)
      omega)
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    exact Or.inr ⟨pf, px⟩

/-- ...and the root C-case projects to `x z ⟶* C x y` and `y ⟶* z`, its degenerate branch dying on
`x = C x` rather than on the argument slot. -/
theorem sc_root_C_return {x y z : SCTerm}
    (hback : RS.SC.Steps (.app (.app x z) y) (.app (.app (.app .C x) y) z)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app x z) y) a
      ∧ RS.SC.Steps b (.app (.app (.app .C x) y) z))
    ∨ (RS.SC.Steps (.app x z) (.app (.app .C x) y) ∧ RS.SC.Steps y z) := by
  rcases sc_path_facts hback with h | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
  · exact Or.inl h
  · exfalso
    injection heq with h1 h2
    injection h1 with h3 h4
    have hc := congrArg SCTerm.leafCount h3
    exact absurd hc (by
      show ¬(x.leafCount = 1 + x.leafCount)
      omega)
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    exact Or.inr ⟨pf, px⟩

-- ## Where the rungs stand after the dichotomies
-- Every root cycle's return path either carries a root step of its own — the regress the next probe
-- should formalize — or performs one of two exotic reductions:
--   * COLLAPSE TO ARGUMENT: `u v ⟶* v`, appearing in BOTH rules' projection branches. `{S,B}` and
--     `{S,C}` are non-erasing except for the fired combinator leaf itself, so a collapse must
--     destroy all of `u` one combinator-fire at a time while rebuilding `v` exactly — the next
--     named sub-target, and a plausible theorem;
--   * SELF-EMBEDDING UNDER APPLICATION: `f x ⟶* S f g`, `x ⟶* B x y` — the open-term cousin of
--     the ground self-embedding machinery from Stages 39–42.
-- Ruling out collapse would force every root cycle to contain an inner root step; whether that
-- regress terminates is then the whole of the rungs.

-- ## Stage 83: RUNG 2 IS CLOSED — {S,B} is acyclic
--
-- The no-collapse probe found something stronger than no-collapse. Both rules of `{S,B}` BURY THE
-- LAST ARGUMENT DEEPER RIGHT: `S f g x → (f x)(g x)` and `B x y z → x (y z)` each push the
-- rightmost subterm one application deeper on the right spine. So the RIGHT-SPINE DEPTH
--
--     ρ(app a b) = ρ(b) + 1,   ρ(leaf) = 0
--
-- never decreases along any step, and strictly increases at every root step. Alone that proves
-- nothing — a cycle could avoid the right spine — which is why every measure hunt since Stage 20
-- missed it: ρ is not a counting measure (the ledger's refutations do not cover it), and without
-- strictness on some step OF EVERY CYCLE it is useless. Stage 81's localization supplies exactly
-- that missing strictness: every cycle yields a cycle through a ROOT step. Composed: ρ(a) < ρ(b)
-- and ρ(b) ≤ ρ(a). Rung 2 falls in four lemmas.
--
-- Why rung 3 does NOT fall to the same argument, exactly as the ledger predicted ("structurally
-- unlike"): `C x y z → x z y` moves `z` OFF the right spine — Δρ = ρ(y) − ρ(z), either sign — so ρ
-- is not monotone for `{S,C}`, and any `{S,C}` cycle must contain a right-spine C-reduction whose
-- `y` is right-shallower than its `z`. That is rung 3's new constraint, inherited free.

/-- The right-spine depth. -/
def rightDepth : SBTerm → Nat
  | .app _ b => rightDepth b + 1
  | _ => 0

/-- Every `{S,B}` step weakly increases the right-spine depth: both rules bury the last argument
deeper, left-side steps do not touch the spine, right-side steps are monotone by induction. -/
theorem sbStep_rightDepth_le {t u : SBTerm} (h : SBStep t u) :
    rightDepth t ≤ rightDepth u := by
  induction h with
  | S_red f g x =>
      show rightDepth x + 1 ≤ (rightDepth x + 1) + 1
      omega
  | B_red x y z =>
      show rightDepth z + 1 ≤ (rightDepth z + 1) + 1
      omega
  | @appL t t' u _ _ =>
      show rightDepth u + 1 ≤ rightDepth u + 1
      exact Nat.le_refl _
  | @appR t u u' _ ih =>
      show rightDepth u + 1 ≤ rightDepth u' + 1
      omega

/-- ...and every ROOT step strictly increases it. -/
theorem sbRoot_rightDepth_lt {t u : SBTerm} (h : SBRootStep t u) :
    rightDepth t < rightDepth u := by
  cases h with
  | S_red f g x =>
      show rightDepth x + 1 < (rightDepth x + 1) + 1
      omega
  | B_red x y z =>
      show rightDepth z + 1 < (rightDepth z + 1) + 1
      omega

theorem sbSteps_rightDepth_le : ∀ {t u : SBTerm}, RS.SB.Steps t u →
    rightDepth t ≤ rightDepth u := by
  intro t u h
  exact h.rec (fun _ => Nat.le_refl _)
    (fun s _ ih => Nat.le_trans (sbStep_rightDepth_le s) ih)

/-- **RUNG 2: `{S,B}` IS ACYCLIC.** A cycle yields a root-cycle (Stage 81); the root step strictly
raises the right-spine depth; the return path cannot lower it. -/
theorem SB_acyclic : RS.Acyclic RS.SB := by
  intro t v hs hback
  obtain ⟨a, b, hr, hcyc⟩ := sb_cycle_needs_root hs hback
  have h1 := sbRoot_rightDepth_lt hr
  have h2 := sbSteps_rightDepth_le hcyc
  omega

/-- **The rung's purpose, delivered: `{S,B}` cannot host SK** — by the program's one refutation
mechanism, now applicable because the rung is closed. The ladder gains its first full rung beyond
`{S}` and ι. -/
theorem no_pathEncoding_SK_SB : ¬ Nonempty (PathEncoding RS.SK RS.SB) :=
  PathEncoding.refute_of_acyclic SB_acyclic
    (RS.SK_steps_iff.mpr omega_to_M) (RS.SK_steps_iff.mpr M_to_omega)
    omega_ne_M

-- Anchors: the fragments' acyclicity results are all subsumed, and no-collapse — the question that
-- started the stage — is a corollary rather than a target.
theorem sb_no_collapse {u v : SBTerm} (h : RS.SB.Steps (.app u v) v) : False := by
  have := sbSteps_rightDepth_le h
  have : rightDepth v + 1 ≤ rightDepth v := this
  omega

-- ## Stage 84: rung 3 through the ρ-lens — the tame fragment is acyclic
-- `C x y z → x z y` moves `z` off the right spine, so ρ is not monotone for `{S,C}` and rung 3
-- does not fall to Stage 83's argument — the measure hunt on paper confirms the ledger's
-- "structurally unlike" from every direction (sums, maxima, and exponentials of right-depths all
-- break on one rule or the other). What IS true: if C only ever fires when it STRICTLY DEEPENS the
-- right spine (`ρ(z) < ρ(y)`), both root rules are ρ-strict and the Stage 83 argument goes through
-- verbatim. So the strictly-tame fragment is acyclic, and — in the ledger's standard phrasing —
-- **every `{S,C}` cycle must fire a C-reduction with `ρ(y) ≤ ρ(z)`**: a flattening C. Rung 3's
-- fourth necessary condition, and its first positional one.

def rightDepthC : SCTerm → Nat
  | .app _ b => rightDepthC b + 1
  | _ => 0

/-- The strictly-tame fragment: `C` may fire only when the argument it swaps inward is
right-deeper than the one it swaps outward. -/
inductive SCTameStep : SCTerm → SCTerm → Prop
  | S_red (f g x : SCTerm) :
      SCTameStep (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | C_red (x y z : SCTerm) : rightDepthC z < rightDepthC y →
      SCTameStep (.app (.app (.app .C x) y) z) (.app (.app x z) y)
  | appL {t t' u : SCTerm} : SCTameStep t t' → SCTameStep (.app t u) (.app t' u)
  | appR {t u u' : SCTerm} : SCTameStep u u' → SCTameStep (.app t u) (.app t u')

def RS.SCTame : RS := ⟨SCTerm, SCTameStep⟩

inductive SCTameRoot : SCTerm → SCTerm → Prop
  | S_red (f g x : SCTerm) :
      SCTameRoot (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x))
  | C_red (x y z : SCTerm) : rightDepthC z < rightDepthC y →
      SCTameRoot (.app (.app (.app .C x) y) z) (.app (.app x z) y)

theorem scTameStep_rightDepth_le {t u : SCTerm} (h : SCTameStep t u) :
    rightDepthC t ≤ rightDepthC u := by
  induction h with
  | S_red f g x =>
      show rightDepthC x + 1 ≤ (rightDepthC x + 1) + 1
      omega
  | C_red x y z hc =>
      show rightDepthC z + 1 ≤ rightDepthC y + 1
      omega
  | @appL t t' u _ _ =>
      show rightDepthC u + 1 ≤ rightDepthC u + 1
      exact Nat.le_refl _
  | @appR t u u' _ ih =>
      show rightDepthC u + 1 ≤ rightDepthC u' + 1
      omega

theorem scTameRoot_rightDepth_lt {t u : SCTerm} (h : SCTameRoot t u) :
    rightDepthC t < rightDepthC u := by
  cases h with
  | S_red f g x =>
      show rightDepthC x + 1 < (rightDepthC x + 1) + 1
      omega
  | C_red x y z hc =>
      show rightDepthC z + 1 < rightDepthC y + 1
      omega

theorem scTameSteps_rightDepth_le : ∀ {t u : SCTerm}, RS.SCTame.Steps t u →
    rightDepthC t ≤ rightDepthC u := by
  intro t u h
  exact h.rec (fun _ => Nat.le_refl _)
    (fun s _ ih => Nat.le_trans (scTameStep_rightDepth_le s) ih)

-- The localization engine, for the tame relation (the condition is local, so it survives
-- projection — exactly why whole-term-Δρ fragments would NOT have worked here).

theorem scTameStep_cases {t w : SCTerm} (h : SCTameStep t w) :
    SCTameRoot t w
    ∨ (∃ f x f', t = .app f x ∧ w = .app f' x ∧ SCTameStep f f')
    ∨ (∃ f x x', t = .app f x ∧ w = .app f x' ∧ SCTameStep x x') := by
  cases h with
  | S_red f g x => exact Or.inl (SCTameRoot.S_red f g x)
  | C_red x y z hc => exact Or.inl (SCTameRoot.C_red x y z hc)
  | appL h => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, h⟩)
  | appR h => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, h⟩)

def SCTamePlus (a b : SCTerm) : Prop := ∃ c, SCTameStep a c ∧ RS.SCTame.Steps c b

theorem scTame_path_facts : ∀ {t u : SCTerm}, RS.SCTame.Steps t u →
    (∃ a b, SCTameRoot a b ∧ RS.SCTame.Steps t a ∧ RS.SCTame.Steps b u)
    ∨ t = u
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SCTame.Steps f f' ∧ RS.SCTame.Steps x x'
        ∧ (SCTamePlus f f' ∨ SCTamePlus x x')) := by
  intro t u h
  exact h.rec
    (motive := fun t u _ =>
      (∃ a b, SCTameRoot a b ∧ RS.SCTame.Steps t a ∧ RS.SCTame.Steps b u)
      ∨ t = u
      ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SCTame.Steps f f' ∧ RS.SCTame.Steps x x'
          ∧ (SCTamePlus f f' ∨ SCTamePlus x x')))
    (fun a => Or.inr (Or.inl rfl))
    (fun {a c b} s rest ih => by
      rcases scTameStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
      · exact Or.inl ⟨a, c, hroot, @RS.Steps.refl RS.SCTame a, rest⟩
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SCTame _ _ hs,
            @RS.Steps.refl RS.SCTame x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SCTame f'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px,
            Or.inl ⟨f', hs, pf⟩⟩)
      · subst heq
        rcases ih with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
        · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
        · exact Or.inr (Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SCTame f,
            @RS.Steps.single RS.SCTame _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SCTame x'⟩⟩)
        · injection heqc with hg hy
          subst hg; subst hy
          exact Or.inr (Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px,
            Or.inr ⟨x', hs, px⟩⟩))

theorem scTame_plus_facts {t u : SCTerm} (h : SCTamePlus t u) :
    (∃ a b, SCTameRoot a b ∧ RS.SCTame.Steps t a ∧ RS.SCTame.Steps b u)
    ∨ (∃ f x f' x', t = .app f x ∧ u = .app f' x' ∧ RS.SCTame.Steps f f' ∧ RS.SCTame.Steps x x'
        ∧ (SCTamePlus f f' ∨ SCTamePlus x x')) := by
  obtain ⟨c, s, rest⟩ := h
  rcases scTameStep_cases s with hroot | ⟨f, x, f', heq, rfl, hs⟩ | ⟨f, x, x', heq, rfl, hs⟩
  · exact Or.inl ⟨t, c, hroot, @RS.Steps.refl RS.SCTame t, rest⟩
  · subst heq
    rcases scTame_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f', x, rfl, heq2 ▸ rfl, @RS.Steps.single RS.SCTame _ _ hs,
        @RS.Steps.refl RS.SCTame x, Or.inl ⟨f', hs, @RS.Steps.refl RS.SCTame f'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, RS.Steps.tail hs pf, px, Or.inl ⟨f', hs, pf⟩⟩
  · subst heq
    rcases scTame_path_facts rest with ⟨p, q, hr, h1, h2⟩ | heq2 | ⟨g, y, g', y', heqc, hequ, pf, px, _⟩
    · exact Or.inl ⟨p, q, hr, RS.Steps.tail s h1, h2⟩
    · exact Or.inr ⟨f, x, f, x', rfl, heq2 ▸ rfl, @RS.Steps.refl RS.SCTame f,
        @RS.Steps.single RS.SCTame _ _ hs, Or.inr ⟨x', hs, @RS.Steps.refl RS.SCTame x'⟩⟩
    · injection heqc with hg hy
      subst hg; subst hy
      exact Or.inr ⟨f, x, g', y', rfl, hequ, pf, RS.Steps.tail hs px, Or.inr ⟨x', hs, px⟩⟩

theorem scTame_cycle_root_aux : ∀ (n : Nat) (t v : SCTerm), t.leafCount ≤ n →
    SCTameStep t v → RS.SCTame.Steps v t →
    ∃ a b, SCTameRoot a b ∧ RS.SCTame.Steps b a := by
  intro n
  induction n with
  | zero =>
      intro t v hle _ _
      exact absurd hle (by have := scLeaf_pos t; omega)
  | succ n ih =>
      intro t v hle hs hback
      rcases scTame_plus_facts ⟨v, hs, hback⟩ with
        ⟨a, b, hr, h1, h2⟩ | ⟨f, x, f', x', heq1, heq2, pf, px, hne⟩
      · exact ⟨a, b, hr, RS.Steps.trans h2 h1⟩
      · subst heq1
        injection heq2 with h1 h2
        subst h1; subst h2
        have hsz : f.leafCount + x.leafCount ≤ n + 1 := hle
        rcases hne with ⟨fm, hsf, hpf⟩ | ⟨xm, hsx, hpx⟩
        · exact ih f fm (by have := scLeaf_pos x; omega) hsf hpf
        · exact ih x xm (by have := scLeaf_pos f; omega) hsx hpx

/-- **The strictly-tame fragment of `{S,C}` is ACYCLIC**: both its root rules strictly deepen the
right spine, and localization forces every cycle through a root. -/
theorem scTame_acyclic : RS.Acyclic RS.SCTame := by
  intro t v hs hback
  obtain ⟨a, b, hr, hcyc⟩ :=
    scTame_cycle_root_aux t.leafCount t v (Nat.le_refl _) hs hback
  have h1 := scTameRoot_rightDepth_lt hr
  have h2 := scTameSteps_rightDepth_le hcyc
  omega

/-- **Any `{S,C}` cycle must fire a FLATTENING `C`** — one whose swapped-in argument is not
right-deeper than the one it displaces (`ρ(y) ≤ ρ(z)`). Rung three's fourth necessary condition,
and its first positional one. -/
theorem scCycle_needs_flat_C {t : SCTerm}
    (hcyc : ∃ u, SCTameStep t u ∧ RS.SCTame.Steps u t) : False := by
  obtain ⟨u, h1, h2⟩ := hcyc
  exact scTame_acyclic h1 h2

-- ## Stage 85: the braid fails, and what lies under both measures
-- The ranked τ×ρ braid does not exist, for a reason now witnessed rather than suspected: the
-- cycle-necessary FLAT C-steps are τ-unconstrained — the ledger's own `scHeavy` is flat AND
-- τ-raising (guards below) — and S-fires, the τ-family's bad steps, always RAISE ρ. Each family's
-- blind spot is invisible to the other, so no lexicographic composite of the two closes rung 3.
--
-- What the failure exposes is the structure beneath both measures: the RIGHT-SPINE SEQUENCE —
-- the list of left-children along the right spine. ρ is its length; τ weights its elements. The
-- two root rules act on it with completely different signatures:
--
--     S f g x :  (S f g) :: σ(x)   ⟶   (f x) :: g :: σ(x)     — head refined, TAIL PRESERVED
--     C x y z :  (C x y) :: σ(z)   ⟶   (x z) :: σ(y)          — the ENTIRE TAIL REPLACED
--
-- Both are `rfl`. Any measure that closes rung 3 must handle C's tail replacement, which no
-- function of ρ alone (Stage 84's sweep) and no τ-composite (this stage) can. The spine sequence
-- itself — a word over terms, rewritten by the two signatures above — is the recorded route.

/-- The right-spine sequence: left-children along the right spine, root first. -/
def scSpine : SCTerm → List SCTerm
  | .app a b => a :: scSpine b
  | _ => []

/-- ρ is its length. -/
theorem rightDepthC_eq_spine_length : ∀ t : SCTerm, rightDepthC t = (scSpine t).length := by
  intro t
  induction t with
  | S => rfl
  | C => rfl
  | app a b _ ihb =>
      show rightDepthC b + 1 = (scSpine b).length + 1
      omega

/-- An S-root step refines the spine head into two elements and PRESERVES the tail. -/
theorem scSpine_S_root (f g x : SCTerm) :
    scSpine (.app (.app (.app .S f) g) x) = (.app (.app .S f) g) :: scSpine x ∧
    scSpine (.app (.app f x) (.app g x)) = (.app f x) :: g :: scSpine x :=
  ⟨rfl, rfl⟩

/-- A C-root step REPLACES the entire spine tail: `σ(z)` out, `σ(y)` in. -/
theorem scSpine_C_root (x y z : SCTerm) :
    scSpine (.app (.app (.app .C x) y) z) = (.app (.app .C x) y) :: scSpine z ∧
    scSpine (.app (.app x z) y) = (.app x z) :: scSpine y :=
  ⟨rfl, rfl⟩

-- ### The independence witnesses, build-enforced
-- `scHeavy = C S S (S S S S)` — the ledger's own τ-asymmetry witness — is FLAT (its C fires with
-- ρ(y) = 0 ≤ 1 = ρ(z)), and it RAISES τ. So the flat C-steps that every cycle must contain
-- (`scCycle_needs_flat_C`) are exactly the ones τ cannot punish: the braid's precise obstruction.
#guard rightDepthC .S ≤ rightDepthC (.app (.app (.app .S .S) .S) .S)
#guard tauSC (.app (.app .S (.app (.app (.app .S .S) .S) .S)) .S)
  > tauSC (.app (.app (.app .C .S) .S) (.app (.app (.app .S .S) .S) .S))
-- And S-root fires always raise ρ — the τ-family's bad steps are ρ-good, closing the other
-- direction of the pincer's independence.
example (f g x : SCTerm) :
    rightDepthC (.app (.app (.app .S f) g) x)
      < rightDepthC (.app (.app f x) (.app g x)) := by
  show rightDepthC x + 1 < (rightDepthC x + 1) + 1
  omega

-- ## Stage 87: the frozen left — no {S,C} term reduces to itself under a leaf
-- The spine calculus's first theorem, from an invariant both measure families overlooked: every
-- `{S,C}` step RESULT is an application, and both root rules produce APP-HEADED LEFT components
-- (`(f x)(g x)` and `(x z) y` alike — contrast `{S,B}`, where `B x y z → x (y z)` can expose a
-- leaf left). So after any root step the left component is an application forever, leaves are
-- unreachable by nonempty paths, and terms of shape `app ℓ x` (a leaf applied to `x`) are
-- unreachable from any path containing a root step. The path dichotomy then forces a size descent:
--
--     **no term reduces to itself applied under a leaf: `¬(x ⟶* ℓ x)`** —
--
-- unconditional, and exactly the shape the second-level root-cycle analysis produces.

/-- Every step lands on an application. -/
theorem scStep_result_isApp {t u : SCTerm} (h : SCStep t u) : ∃ a b, u = .app a b := by
  cases h with
  | S_red f g x => exact ⟨_, _, rfl⟩
  | C_red x y z => exact ⟨_, _, rfl⟩
  | appL h => exact ⟨_, _, rfl⟩
  | appR h => exact ⟨_, _, rfl⟩

/-- Leaves are unreachable: a path ending at a non-application is empty. -/
theorem sc_steps_to_leaf : ∀ {t u : SCTerm}, RS.SC.Steps t u →
    (∀ a b, u ≠ SCTerm.app a b) → t = u := by
  intro t u h
  exact h.rec (motive := fun t u _ => (∀ a b, u ≠ SCTerm.app a b) → t = u)
    (fun _ _ => rfl)
    (fun {a c b} s _ ih hu => by
      have hc := ih hu
      subst hc
      obtain ⟨p, q, hpq⟩ := scStep_result_isApp s
      exact absurd hpq (hu p q))

/-- Both root rules produce an app-headed left component. -/
theorem scRootStep_left_app {t u : SCTerm} (h : SCRootStep t u) :
    ∃ a b c, u = .app (.app a b) c := by
  cases h with
  | S_red f g x => exact ⟨_, _, _, rfl⟩
  | C_red x y z => exact ⟨_, _, _, rfl⟩

/-- ...and app-headedness of the left component is invariant from then on. -/
theorem scStep_leftApp {t u : SCTerm} (h : SCStep t u)
    (hp : ∃ a b c, t = .app (.app a b) c) : ∃ a b c, u = .app (.app a b) c := by
  cases h with
  | S_red f g x => exact ⟨_, _, _, rfl⟩
  | C_red x y z => exact ⟨_, _, _, rfl⟩
  | @appL t t' u h' =>
      obtain ⟨p, q, hpq⟩ := scStep_result_isApp h'
      exact ⟨p, q, u, by rw [hpq]⟩
  | @appR t u u' h' =>
      obtain ⟨a, b, c, habc⟩ := hp
      injection habc with h1 _
      exact ⟨a, b, u', by rw [h1]⟩

theorem scSteps_leftApp : ∀ {t u : SCTerm}, RS.SC.Steps t u →
    (∃ a b c, t = .app (.app a b) c) → ∃ a b c, u = .app (.app a b) c := by
  intro t u h
  refine h.rec (motive := fun t u _ =>
      (∃ a b c, t = SCTerm.app (SCTerm.app a b) c) →
        ∃ a b c, u = SCTerm.app (SCTerm.app a b) c) ?_ ?_
  · intro _ hp
    exact hp
  · intro a b c s h' ih hp
    exact ih (scStep_leftApp s hp)

/-- **No `{S,C}` term reduces to itself applied under a leaf.** A root step anywhere on the path
freezes the left component as an application, which `app ℓ x` is not; the rootless alternative
forces `x = app ℓ x₁` with `x₁ ⟶* app ℓ x₁`, a strict size descent. -/
theorem sc_no_leaf_self_embed_aux (ℓ : SCTerm) (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b) :
    ∀ (n : Nat) (x : SCTerm), x.leafCount ≤ n → ¬ RS.SC.Steps x (SCTerm.app ℓ x) := by
  intro n
  induction n with
  | zero =>
      intro x hle _
      exact absurd hle (by have := scLeaf_pos x; omega)
  | succ n ih =>
      intro x hle h
      rcases sc_path_facts h with ⟨a, b, hr, h1, h2⟩ | heq | ⟨f, x₁, F', X', heq1, heq2, pf, px, _⟩
      · obtain ⟨p, q, r, hb⟩ := scRootStep_left_app hr
        obtain ⟨a', b', c', habc⟩ := scSteps_leftApp h2 ⟨p, q, r, hb⟩
        injection habc with h1' _
        exact absurd h1' (hℓ a' b')
      · have hc := congrArg SCTerm.leafCount heq
        have hp := scLeaf_pos ℓ
        exact absurd hc (by
          show ¬(x.leafCount = ℓ.leafCount + x.leafCount)
          omega)
      · injection heq2 with hF' hX'
        subst hX'
        rw [← hF'] at pf
        have hf : f = ℓ := sc_steps_to_leaf pf hℓ
        rw [hf] at heq1
        subst heq1
        have hx1 : x₁.leafCount ≤ n := by
          have := scLeaf_pos ℓ
          have hsz : ℓ.leafCount + x₁.leafCount ≤ n + 1 := hle
          omega
        exact ih x₁ hx1 px

/-- The packaged form, and its two instances. -/
theorem sc_no_leaf_self_embed {ℓ x : SCTerm} (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b) :
    ¬ RS.SC.Steps x (SCTerm.app ℓ x) :=
  sc_no_leaf_self_embed_aux ℓ hℓ x.leafCount x (Nat.le_refl _)

example (x : SCTerm) : ¬ RS.SC.Steps x (SCTerm.app SCTerm.C x) :=
  sc_no_leaf_self_embed (fun _ _ h => SCTerm.noConfusion h)

example (x : SCTerm) : ¬ RS.SC.Steps x (SCTerm.app SCTerm.S x) :=
  sc_no_leaf_self_embed (fun _ _ h => SCTerm.noConfusion h)

-- ## Stage 88: the second fire — every root cycle's return path reaches another root redex
-- Stage 82's dichotomies left each root cycle two escapes: the return path carries a root step of
-- its own, or it projects into the redex's components, with the LEFT projection performing a
-- self-embedding — `f x ⟶* (S f) g` and `x z ⟶* (C x) y`, both of shape `f x ⟶* (ℓ f) g` for a
-- leaf `ℓ`. Running the path dichotomy on THAT path, its trivial branch dies on size and its
-- projection branch is exactly `f ⟶* ℓ f` — the frozen-left theorem. So the self-embedding itself
-- needs a root step, and lifting through left congruence: **every root cycle's return path
-- reaches a second root redex, at the root or immediately left of it** — rung 3's sixth necessary
-- condition, and its first POSITIONAL one in tree terms: cycles cannot avoid the top-left spine.

/-- The left self-embedding `f x ⟶* (ℓ f) g` (`ℓ` a leaf) cannot happen rootlessly: the trivial
branch dies on size, the projection branch on the frozen left. -/
theorem sc_left_self_embed_needs_root {ℓ f x g : SCTerm} (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b)
    (h : RS.SC.Steps (.app f x) (.app (.app ℓ f) g)) :
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app f x) a ∧ RS.SC.Steps b (.app (.app ℓ f) g) := by
  rcases sc_path_facts h with hroot | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
  · exact hroot
  · exfalso
    injection heq with h1 h2
    have hc := congrArg SCTerm.leafCount h1
    have hp := scLeaf_pos ℓ
    exact absurd hc (by
      show ¬(f.leafCount = ℓ.leafCount + f.leafCount)
      omega)
  · exfalso
    injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    exact sc_no_leaf_self_embed hℓ pf

/-- Second-level dichotomy for a root S-cycle: the return carries a root step, or its left
projection `f x ⟶* (S f) g` does. -/
theorem sc_root_S_return2 {f g x : SCTerm}
    (hback : RS.SC.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SC.Steps b (.app (.app (.app .S f) g) x))
    ∨ ((∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app f x) a ∧ RS.SC.Steps b (.app (.app .S f) g))
        ∧ RS.SC.Steps (.app g x) x) := by
  rcases sc_root_S_return hback with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨sc_left_self_embed_needs_root (fun _ _ hab => SCTerm.noConfusion hab) h1, h2⟩

/-- ...and for a root C-cycle: the return carries a root step, or its left projection
`x z ⟶* (C x) y` does. -/
theorem sc_root_C_return2 {x y z : SCTerm}
    (hback : RS.SC.Steps (.app (.app x z) y) (.app (.app (.app .C x) y) z)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app x z) y) a
      ∧ RS.SC.Steps b (.app (.app (.app .C x) y) z))
    ∨ ((∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app x z) a ∧ RS.SC.Steps b (.app (.app .C x) y))
        ∧ RS.SC.Steps y z) := by
  rcases sc_root_C_return hback with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨sc_left_self_embed_needs_root (fun _ _ hab => SCTerm.noConfusion hab) h1, h2⟩

/-- Left congruence, lifted to paths. -/
theorem scSteps_appL {f f' : SCTerm} (x : SCTerm) (h : RS.SC.Steps f f') :
    RS.SC.Steps (SCTerm.app f x) (SCTerm.app f' x) := by
  refine h.rec (motive := fun a b _ => RS.SC.Steps (SCTerm.app a x) (SCTerm.app b x)) ?_ ?_
  · intro a
    exact @RS.Steps.refl RS.SC (SCTerm.app a x)
  · intro a b c s h' ih
    exact RS.Steps.tail (SCStep.appL s) ih

/-- **THE SIXTH CONDITION: every root cycle's return path reaches a second root redex** — at the
root, or immediately left of it. -/
theorem scRootCycle_second_redex {t u : SCTerm} (hr : SCRootStep t u) (hback : RS.SC.Steps u t) :
    ∃ a b, SCRootStep a b ∧ (RS.SC.Steps u a ∨ ∃ c, RS.SC.Steps u (SCTerm.app a c)) := by
  cases hr with
  | S_red f g x =>
      rcases sc_root_S_return2 hback with ⟨a, b, hr', h1, _⟩ | ⟨⟨a, b, hr', h1, _⟩, _⟩
      · exact ⟨a, b, hr', Or.inl h1⟩
      · exact ⟨a, b, hr', Or.inr ⟨.app g x, scSteps_appL _ h1⟩⟩
  | C_red x y z =>
      rcases sc_root_C_return2 hback with ⟨a, b, hr', h1, _⟩ | ⟨⟨a, b, hr', h1, _⟩, _⟩
      · exact ⟨a, b, hr', Or.inl h1⟩
      · exact ⟨a, b, hr', Or.inr ⟨y, scSteps_appL _ h1⟩⟩

/-- Composed with localization: every `{S,C}` cycle produces a root cycle whose return path
reaches a second root redex. -/
theorem scCycle_second_redex {t v : SCTerm} (hs : SCStep t v) (hback : RS.SC.Steps v t) :
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps b a ∧
      ∃ p q, SCRootStep p q ∧ (RS.SC.Steps b p ∨ ∃ c, RS.SC.Steps b (SCTerm.app p c)) := by
  obtain ⟨a, b, hr, hcyc⟩ := sc_cycle_needs_root hs hback
  obtain ⟨p, q, hr', hreach⟩ := scRootCycle_second_redex hr hcyc
  exact ⟨a, b, hr, hcyc, p, q, hr', hreach⟩

-- ## Stage 89: collapse under the shape lens — the last escape narrows
-- Stage 82 named COLLAPSE TO ARGUMENT (`u v ⟶* v`) the load-bearing escape; the shape lens now
-- takes two bites out of it. First: leaves are NORMAL (every step source is an application), so a
-- leaf-headed term `ℓ v` is left-rigid — everything it reaches is `ℓ w` with `v ⟶* w` — and
-- leaf-headed collapse dies by size descent, unconditionally. Second: for arbitrary `u`, the path
-- dichotomy on a collapse has its trivial branch dead on size and its projection branch forcing
-- `v = F' X'` with `v ⟶* X'` — the SAME collapse shape one level down `v`'s right spine. The
-- descent bottoms out only in the root branch: **every collapse fires a root redex, launched from
-- a right-nested subterm of the collapsing term**. Plugged into Stage 88's S-side survivor (whose
-- extra datum `g x ⟶* x` is exactly a collapse): a root S-cycle either returns through a
-- whole-term root step, or BOTH its projections carry root fires of their own.

/-- Every step SOURCE is an application: leaves are normal. -/
theorem scStep_source_isApp {t u : SCTerm} (h : SCStep t u) : ∃ a b, t = .app a b := by
  cases h with
  | S_red f g x => exact ⟨_, _, rfl⟩
  | C_red x y z => exact ⟨_, _, rfl⟩
  | appL h => exact ⟨_, _, rfl⟩
  | appR h => exact ⟨_, _, rfl⟩

/-- Root sources are app-app-headed. -/
theorem scRootStep_source {t u : SCTerm} (h : SCRootStep t u) :
    ∃ p q r, t = .app (.app p q) r := by
  cases h with
  | S_red f g x => exact ⟨_, _, _, rfl⟩
  | C_red x y z => exact ⟨_, _, _, rfl⟩

/-- Left-leaf rigidity: from `ℓ v` (`ℓ` a leaf) only the right side can ever move. -/
theorem scSteps_from_leafLeft {ℓ : SCTerm} (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b) :
    ∀ {t u : SCTerm}, RS.SC.Steps t u → ∀ v, t = SCTerm.app ℓ v →
      ∃ w, u = SCTerm.app ℓ w ∧ RS.SC.Steps v w := by
  intro t u h
  refine h.rec (motive := fun t u _ => ∀ v, t = SCTerm.app ℓ v →
      ∃ w, u = SCTerm.app ℓ w ∧ RS.SC.Steps v w) ?_ ?_
  · intro a v heq
    exact ⟨v, heq, @RS.Steps.refl RS.SC v⟩
  · intro a b c s rest ih v heq
    subst heq
    rcases scStep_cases s with hroot | ⟨f, x, f', heq1, heq2, hs⟩ | ⟨f, x, x', heq1, heq2, hs⟩
    · obtain ⟨p, q, r, heqs⟩ := scRootStep_source hroot
      injection heqs with h1 h2
      exact absurd h1 (hℓ p q)
    · injection heq1 with h1 h2
      subst h1; subst h2
      obtain ⟨p, q, hpq⟩ := scStep_source_isApp hs
      exact absurd hpq (hℓ p q)
    · injection heq1 with h1 h2
      subst h1; subst h2
      obtain ⟨w, hb, hw⟩ := ih x' heq2
      exact ⟨w, hb, RS.Steps.tail hs hw⟩

/-- Leaf-headed collapse is dead: `ℓ v` never reduces to `v`. -/
theorem sc_no_leaf_collapse_aux (ℓ : SCTerm) (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b) :
    ∀ (n : Nat) (v : SCTerm), v.leafCount ≤ n → ¬ RS.SC.Steps (SCTerm.app ℓ v) v := by
  intro n
  induction n with
  | zero =>
      intro v hle _
      exact absurd hle (by have := scLeaf_pos v; omega)
  | succ n ih =>
      intro v hle h
      obtain ⟨w, hv, hvw⟩ := scSteps_from_leafLeft hℓ h v rfl
      rw [hv] at hvw
      have hw : w.leafCount ≤ n := by
        have hc : v.leafCount = ℓ.leafCount + w.leafCount := by rw [hv]; rfl
        have := scLeaf_pos ℓ
        omega
      exact ih w hw hvw

/-- The packaged form. -/
theorem sc_no_leaf_collapse {ℓ v : SCTerm} (hℓ : ∀ a b, ℓ ≠ SCTerm.app a b) :
    ¬ RS.SC.Steps (SCTerm.app ℓ v) v :=
  sc_no_leaf_collapse_aux ℓ hℓ v.leafCount v (Nat.le_refl _)

example (v : SCTerm) : ¬ RS.SC.Steps (SCTerm.app SCTerm.S v) v :=
  sc_no_leaf_collapse (fun _ _ h => SCTerm.noConfusion h)

example (v : SCTerm) : ¬ RS.SC.Steps (SCTerm.app SCTerm.C v) v :=
  sc_no_leaf_collapse (fun _ _ h => SCTerm.noConfusion h)

/-- Right-nested subterms: the term itself, its right child, that one's right child, ... -/
inductive SCRightNested : SCTerm → SCTerm → Prop
  | refl (t : SCTerm) : SCRightNested t t
  | tail {x a b : SCTerm} : SCRightNested x b → SCRightNested x (.app a b)

/-- **Collapse cannot be rootless**: a collapse-to-argument fires a root redex, launched from a
right-nested subterm of the collapsing term. The projection branch forces the same collapse shape
one level down the right spine; the descent bottoms out only in the root branch. -/
theorem sc_collapse_needs_root_aux : ∀ (n : Nat) (u v : SCTerm), v.leafCount ≤ n →
    RS.SC.Steps (SCTerm.app u v) v →
    ∃ w a b, SCRightNested w (SCTerm.app u v) ∧ SCRootStep a b ∧ RS.SC.Steps w a := by
  intro n
  induction n with
  | zero =>
      intro u v hle _
      exact absurd hle (by have := scLeaf_pos v; omega)
  | succ n ih =>
      intro u v hle h
      rcases sc_path_facts h with ⟨a, b, hr, h1, h2⟩ | heq | ⟨F, X, F', X', heq1, heq2, pf, px, _⟩
      · exact ⟨_, a, b, SCRightNested.refl _, hr, h1⟩
      · have hc := congrArg SCTerm.leafCount heq
        have := scLeaf_pos u
        exact absurd hc (by
          show ¬(u.leafCount + v.leafCount = v.leafCount)
          omega)
      · injection heq1 with h1 h2
        subst h1; subst h2
        rw [heq2] at px
        have hx : X'.leafCount ≤ n := by
          have hc : v.leafCount = F'.leafCount + X'.leafCount := by rw [heq2]; rfl
          have := scLeaf_pos F'
          omega
        obtain ⟨w, a, b, hnest, hr, hreach⟩ := ih F' X' hx px
        rw [← heq2] at hnest
        exact ⟨w, a, b, SCRightNested.tail hnest, hr, hreach⟩

/-- The packaged form. -/
theorem sc_collapse_needs_root {u v : SCTerm} (h : RS.SC.Steps (SCTerm.app u v) v) :
    ∃ w a b, SCRightNested w (SCTerm.app u v) ∧ SCRootStep a b ∧ RS.SC.Steps w a :=
  sc_collapse_needs_root_aux v.leafCount u v (Nat.le_refl _) h

/-- Plugged into Stage 88's S-side survivor: a root S-cycle either returns through a whole-term
root step, or BOTH its projections carry root fires — the left self-embedding's (Stage 88) and
the right collapse's (this stage). -/
theorem sc_root_S_return3 {f g x : SCTerm}
    (hback : RS.SC.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SC.Steps b (.app (.app (.app .S f) g) x))
    ∨ ((∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app f x) a ∧ RS.SC.Steps b (.app (.app .S f) g))
        ∧ (∃ w a b, SCRightNested w (.app g x) ∧ SCRootStep a b ∧ RS.SC.Steps w a)) := by
  rcases sc_root_S_return2 hback with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, sc_collapse_needs_root h2⟩

-- ## Stage 90: the leaf-argument kill — cycle anatomy at rung 3
-- Stages 88 and 89 supplied the two halves of a contradiction: root sources are APP-APP-HEADED
-- (`scRootStep_source`), and leaf-headed terms are LEFT-RIGID (`scSteps_from_leafLeft`) — so a
-- leaf-headed term can NEVER reach a root redex. Stage 88's second-level sandwich lives inside
-- the left projections `f x ⟶* (S f) g` and `x z ⟶* (C x) y`, whose sources are leaf-headed
-- exactly when the redex's HEAD ARGUMENT is a leaf. For those cycles the projection escape is
-- absurd and the return must carry a whole-term root step. Folding in Stage 89's collapse fire,
-- each rule gets its sharpest cycle statement yet — the ANATOMY: a root cycle returns through a
-- whole-term root step, or its head argument is an application and the projections carry root
-- fires of their own.

/-- Every term is a leaf or an application. -/
theorem sc_leaf_or_app (t : SCTerm) :
    (∀ a b, t ≠ SCTerm.app a b) ∨ ∃ a b, t = SCTerm.app a b := by
  cases t with
  | S => exact Or.inl (fun _ _ h => SCTerm.noConfusion h)
  | C => exact Or.inl (fun _ _ h => SCTerm.noConfusion h)
  | app a b => exact Or.inr ⟨a, b, rfl⟩

/-- A leaf-headed term never reaches a root redex: rigidity keeps its left a leaf, but root
sources are app-app-headed. -/
theorem sc_leafLeft_no_root_reach {ℓ v a b : SCTerm} (hℓ : ∀ p q, ℓ ≠ SCTerm.app p q)
    (hr : SCRootStep a b) (h : RS.SC.Steps (SCTerm.app ℓ v) a) : False := by
  obtain ⟨w, ha, _⟩ := scSteps_from_leafLeft hℓ h v rfl
  obtain ⟨p, q, r, hs⟩ := scRootStep_source hr
  rw [ha] at hs
  injection hs with h1 h2
  exact absurd h1 (hℓ p q)

/-- A root S-cycle with a LEAF `f` must return through a whole-term root step. -/
theorem sc_root_S_return_leaf {f g x : SCTerm} (hf : ∀ a b, f ≠ SCTerm.app a b)
    (hback : RS.SC.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SC.Steps b (.app (.app (.app .S f) g) x) := by
  rcases sc_root_S_return2 hback with h | ⟨⟨a, b, hr, h1, _⟩, _⟩
  · exact h
  · exact (sc_leafLeft_no_root_reach hf hr h1).elim

/-- A root C-cycle with a LEAF `x` must return through a whole-term root step. -/
theorem sc_root_C_return_leaf {x y z : SCTerm} (hx : ∀ a b, x ≠ SCTerm.app a b)
    (hback : RS.SC.Steps (.app (.app x z) y) (.app (.app (.app .C x) y) z)) :
    ∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app x z) y) a
      ∧ RS.SC.Steps b (.app (.app (.app .C x) y) z) := by
  rcases sc_root_C_return2 hback with h | ⟨⟨a, b, hr, h1, _⟩, _⟩
  · exact h
  · exact (sc_leafLeft_no_root_reach hx hr h1).elim

/-- **S-CYCLE ANATOMY**: a root S-cycle returns through a whole-term root step, or `f` is an
application and BOTH projections carry root fires. -/
theorem sc_root_S_anatomy {f g x : SCTerm}
    (hback : RS.SC.Steps (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app f x) (.app g x)) a
      ∧ RS.SC.Steps b (.app (.app (.app .S f) g) x))
    ∨ ((∃ f₁ f₂, f = SCTerm.app f₁ f₂)
        ∧ (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app f x) a ∧ RS.SC.Steps b (.app (.app .S f) g))
        ∧ (∃ w a b, SCRightNested w (.app g x) ∧ SCRootStep a b ∧ RS.SC.Steps w a)) := by
  rcases sc_root_S_return3 hback with h | ⟨⟨a, b, hr, h1, h2⟩, hcol⟩
  · exact Or.inl h
  · rcases sc_leaf_or_app f with hf | hf
    · exact (sc_leafLeft_no_root_reach hf hr h1).elim
    · exact Or.inr ⟨hf, ⟨a, b, hr, h1, h2⟩, hcol⟩

/-- **C-CYCLE ANATOMY**: a root C-cycle returns through a whole-term root step, or `x` is an
application, the left projection carries a root fire, and `y ⟶* z`. -/
theorem sc_root_C_anatomy {x y z : SCTerm}
    (hback : RS.SC.Steps (.app (.app x z) y) (.app (.app (.app .C x) y) z)) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app (.app x z) y) a
      ∧ RS.SC.Steps b (.app (.app (.app .C x) y) z))
    ∨ ((∃ x₁ x₂, x = SCTerm.app x₁ x₂)
        ∧ (∃ a b, SCRootStep a b ∧ RS.SC.Steps (.app x z) a ∧ RS.SC.Steps b (.app (.app .C x) y))
        ∧ RS.SC.Steps y z) := by
  rcases sc_root_C_return2 hback with h | ⟨⟨a, b, hr, h1, h2⟩, hyz⟩
  · exact Or.inl h
  · rcases sc_leaf_or_app x with hx | hx
    · exact (sc_leafLeft_no_root_reach hx hr h1).elim
    · exact Or.inr ⟨hx, ⟨a, b, hr, h1, h2⟩, hyz⟩

-- ## Stage 91: rotate or descend — the anatomy as a single invariant
-- Stage 90's anatomies read, per rule, as a dichotomy. This stage makes it one theorem. The
-- rotation half: a whole-term root fire on the return path closes a root cycle THROUGH THAT FIRE
-- (`b ⟶* t → u ⟶* a` and root steps are steps), sitting on the same cycle. The descent half is
-- uniform across the rules once seen from the redex: for both `S f g x` and `C x y z` the left
-- projection runs from `app h r` (HEAD argument applied to LAST argument) to the fired term's
-- left component, so one statement covers both. Every root cycle rotates or descends; composed
-- with localization, every `{S,C}` cycle carries a root cycle that does.

/-- Root steps are steps. -/
theorem scRootStep_step {t u : SCTerm} (h : SCRootStep t u) : SCStep t u := by
  cases h with
  | S_red f g x => exact SCStep.S_red f g x
  | C_red x y z => exact SCStep.C_red x y z

/-- The rotation: a root fire on a root cycle's return path closes a root cycle of its own. -/
theorem scRootCycle_of_return_fire {t u a b : SCTerm} (hr : SCRootStep t u)
    (h1 : RS.SC.Steps u a) (h2 : RS.SC.Steps b t) : RS.SC.Steps b a :=
  RS.Steps.trans h2 (RS.Steps.tail (scRootStep_step hr) h1)

/-- **ROTATE OR DESCEND**: a root cycle contains another root cycle on itself (through its
return's whole-term root fire), or its head argument is an application and the redex's
`app head last` projection fires a root redex on a strictly smaller term. -/
theorem scRootCycle_rotate_or_descend {t u : SCTerm} (hr : SCRootStep t u)
    (hback : RS.SC.Steps u t) :
    (∃ a b, SCRootStep a b ∧ RS.SC.Steps b a ∧ RS.SC.Steps u a ∧ RS.SC.Steps b t)
    ∨ (∃ K h m r, (K = SCTerm.S ∨ K = SCTerm.C)
        ∧ t = SCTerm.app (SCTerm.app (SCTerm.app K h) m) r
        ∧ (∃ h₁ h₂, h = SCTerm.app h₁ h₂)
        ∧ (∃ a b, SCRootStep a b ∧ RS.SC.Steps (SCTerm.app h r) a
            ∧ RS.SC.Steps b (SCTerm.app (SCTerm.app K h) m))) := by
  cases hr with
  | S_red f g x =>
      rcases sc_root_S_anatomy hback with ⟨a, b, hr', h1, h2⟩ | ⟨happ, hfire, _⟩
      · exact Or.inl ⟨a, b, hr', scRootCycle_of_return_fire (SCRootStep.S_red f g x) h1 h2,
          h1, h2⟩
      · exact Or.inr ⟨SCTerm.S, f, g, x, Or.inl rfl, rfl, happ, hfire⟩
  | C_red x y z =>
      rcases sc_root_C_anatomy hback with ⟨a, b, hr', h1, h2⟩ | ⟨happ, hfire, _⟩
      · exact Or.inl ⟨a, b, hr', scRootCycle_of_return_fire (SCRootStep.C_red x y z) h1 h2,
          h1, h2⟩
      · exact Or.inr ⟨SCTerm.C, x, y, z, Or.inr rfl, rfl, happ, hfire⟩

/-- Composed with localization: every `{S,C}` cycle carries a root cycle that rotates or
descends. -/
theorem scCycle_rotate_or_descend {t v : SCTerm} (hs : SCStep t v) (hback : RS.SC.Steps v t) :
    ∃ p q, SCRootStep p q ∧ RS.SC.Steps q p ∧
      ((∃ a b, SCRootStep a b ∧ RS.SC.Steps b a ∧ RS.SC.Steps q a ∧ RS.SC.Steps b p)
        ∨ (∃ K h m r, (K = SCTerm.S ∨ K = SCTerm.C)
            ∧ p = SCTerm.app (SCTerm.app (SCTerm.app K h) m) r
            ∧ (∃ h₁ h₂, h = SCTerm.app h₁ h₂)
            ∧ (∃ a b, SCRootStep a b ∧ RS.SC.Steps (SCTerm.app h r) a
                ∧ RS.SC.Steps b (SCTerm.app (SCTerm.app K h) m)))) := by
  obtain ⟨p, q, hr, hcyc⟩ := sc_cycle_needs_root hs hback
  exact ⟨p, q, hr, hcyc, scRootCycle_rotate_or_descend hr hcyc⟩

-- ## Stage 92: length-indexed paths — the well-foundedness scaffold
-- Stage 91's invariant is missing one ingredient: a reason rotation cannot recur forever. On a
-- finite cycle it cannot — finitely many fires — but `Steps` is lengthless, so that sentence was
-- unstatable. `RS.StepsN` (in RS.lean) now counts; the pieces here bridge it to `Acyclic` and
-- restate the rotation with lengths. The headline is the CONSERVATION fact the scaffold exists
-- for: rotation is a length-preserving basepoint shift — the original root cycle and its rotated
-- companion have the SAME total length `k + l + 2`. A descent argument now has its measure: any
-- future cycle surgery that strictly shortens feeds `RS.no_cycle_of_descent` and closes rung 3.

/-- No nonempty `StepsN` cycles means acyclic, generically. -/
theorem RS.acyclic_of_no_stepsN_cycle {A : RS}
    (h : ∀ n t, 1 ≤ n → ¬ A.StepsN n t t) : RS.Acyclic A := by
  intro t v hs hback
  obtain ⟨k, hk⟩ := hback.toStepsN
  exact h (k + 1) t (by omega) (RS.StepsN.tail hs hk)

/-- The descent engine, at `Acyclic`: strictly-shortening cycle surgery proves acyclicity. -/
theorem RS.acyclic_of_cycle_descent {A : RS}
    (h : ∀ n t, 1 ≤ n → A.StepsN n t t → ∃ m u, 1 ≤ m ∧ m < n ∧ A.StepsN m u u) :
    RS.Acyclic A :=
  RS.acyclic_of_no_stepsN_cycle (RS.no_cycle_of_descent h)

/-- Every `{S,C}` cycle yields a length-indexed nonempty cycle. -/
theorem sc_cycle_stepsN {t v : SCTerm} (hs : SCStep t v) (hback : RS.SC.Steps v t) :
    ∃ n, 1 ≤ n ∧ RS.SC.StepsN n t t := by
  obtain ⟨k, hk⟩ := hback.toStepsN
  exact ⟨k + 1, by omega, RS.StepsN.tail hs hk⟩

/-- **Rotation preserves length**: a root cycle `t → u ⟶ᵏ a → b ⟶ˡ t` and its rotation at the
return's fire are cycles of the SAME total length `k + l + 2`. Rotation never grows the cycle —
the measure a future descent argument will spend. -/
theorem scRootCycle_rotate_same_length {t u a b : SCTerm} {k l : Nat} (hr : SCRootStep t u)
    (hr' : SCRootStep a b) (h1 : RS.SC.StepsN k u a) (h2 : RS.SC.StepsN l b t) :
    RS.SC.StepsN (k + l + 2) t t ∧ RS.SC.StepsN (k + l + 2) b b := by
  have ct : RS.SC.StepsN (k + (l + 1) + 1) t t :=
    RS.StepsN.tail (scRootStep_step hr)
      (RS.StepsN.trans h1 (RS.StepsN.tail (scRootStep_step hr') h2))
  have cb : RS.SC.StepsN (l + (k + (0 + 1) + 1)) b b :=
    RS.StepsN.trans h2
      (RS.StepsN.tail (scRootStep_step hr)
        (RS.StepsN.trans h1 (RS.StepsN.tail (scRootStep_step hr') (@RS.StepsN.refl RS.SC b))))
  constructor
  · have he : k + (l + 1) + 1 = k + l + 2 := by omega
    exact he ▸ ct
  · have he : l + (k + (0 + 1) + 1) = k + l + 2 := by omega
    exact he ▸ cb

-- ## Stage 93: minimal cycles are root cycles — localization spends no length
-- The scaffold's first purchase. Stage 81's localization descends through projections to find a
-- root cycle, but its output forgets how long the found cycle is; against the descent engine that
-- is a wasted asset. This stage redoes the dichotomy and the localization in `StepsN` form: a
-- cycle of length `n` yields a root cycle of TOTAL length ≤ n — and on a MINIMAL cycle the
-- inequality is forced to equality, so minimal cycles may be assumed root cycles outright. Two
-- small teeth for the atlas come along: no step is a self-loop, so minimal cycles have length ≥ 2.

/-- No step is a self-loop. -/
theorem scStep_irrefl_aux : ∀ (n : Nat) (t : SCTerm), t.leafCount ≤ n → ¬ SCStep t t := by
  intro n
  induction n with
  | zero =>
      intro t hle _
      exact absurd hle (by have := scLeaf_pos t; omega)
  | succ n ih =>
      intro t hle h
      rcases scStep_cases h with hroot | ⟨f, x, f', heq1, heq2, hs⟩ | ⟨f, x, x', heq1, heq2, hs⟩
      · cases hroot
      · subst heq1
        injection heq2 with h1 h2
        subst h1
        have hf : f.leafCount ≤ n := by
          have := scLeaf_pos x
          have hs2 : f.leafCount + x.leafCount ≤ n + 1 := hle
          omega
        exact ih f hf hs
      · subst heq1
        injection heq2 with h1 h2
        subst h2
        have hx : x.leafCount ≤ n := by
          have := scLeaf_pos f
          have hs2 : f.leafCount + x.leafCount ≤ n + 1 := hle
          omega
        exact ih x hx hs

theorem scStep_irrefl (t : SCTerm) : ¬ SCStep t t :=
  scStep_irrefl_aux t.leafCount t (Nat.le_refl _)

/-- Zero-length paths go nowhere. -/
theorem RS.stepsN_zero_eq {A : RS} {a b : A.Carrier} (h : A.StepsN 0 a b) : a = b := by
  cases h
  rfl

/-- One-length paths are steps. -/
theorem RS.stepsN_one_step {A : RS} {a b : A.Carrier} (h : A.StepsN 1 a b) : A.step a b := by
  cases h with
  | tail s rest => exact (RS.stepsN_zero_eq rest) ▸ s

/-- Cycles of length one do not exist. -/
theorem sc_no_one_cycle {t : SCTerm} (h : RS.SC.StepsN 1 t t) : False :=
  scStep_irrefl t (RS.stepsN_one_step h)

/-- Every nonempty `{S,C}` cycle has length at least 2. -/
theorem sc_cycle_length_ge_two {n : Nat} {t : SCTerm} (h1 : 1 ≤ n)
    (hcyc : RS.SC.StepsN n t t) : 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn : n = 1 := by omega
    subst hn
    exact (sc_no_one_cycle hcyc).elim
  · exact h2

/-- The path dichotomy, with lengths: a root sandwich accounting for every step, the empty path,
or a projection whose component lengths SUM to the whole. -/
theorem sc_stepsN_facts : ∀ {n : Nat} {t u : SCTerm}, RS.SC.StepsN n t u →
    (∃ k₁ k₂ a b, SCRootStep a b ∧ RS.SC.StepsN k₁ t a ∧ RS.SC.StepsN k₂ b u ∧ k₁ + 1 + k₂ = n)
    ∨ (n = 0 ∧ t = u)
    ∨ (∃ nf nx f x f' x', t = SCTerm.app f x ∧ u = SCTerm.app f' x' ∧ RS.SC.StepsN nf f f'
        ∧ RS.SC.StepsN nx x x' ∧ nf + nx = n) := by
  intro n t u h
  refine h.rec (motive := fun n t u _ =>
      (∃ k₁ k₂ a b, SCRootStep a b ∧ RS.SC.StepsN k₁ t a ∧ RS.SC.StepsN k₂ b u ∧ k₁ + 1 + k₂ = n)
      ∨ (n = 0 ∧ t = u)
      ∨ (∃ nf nx f x f' x', t = SCTerm.app f x ∧ u = SCTerm.app f' x' ∧ RS.SC.StepsN nf f f'
          ∧ RS.SC.StepsN nx x x' ∧ nf + nx = n)) ?_ ?_
  · intro a
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · intro m a b c s rest ih
    rcases scStep_cases s with hroot | ⟨f, x, f', heq1, heq2, hs⟩ | ⟨f, x, x', heq1, heq2, hs⟩
    · exact Or.inl ⟨0, m, a, b, hroot, @RS.StepsN.refl RS.SC a, rest, by omega⟩
    · subst heq1; subst heq2
      rcases ih with ⟨k₁, k₂, p, q, hr, h1, h2, hsum⟩ | ⟨hm0, heqbc⟩
        | ⟨nf, nx, g, y, g', y', heqb, heqc, pf2, px2, hsum⟩
      · exact Or.inl ⟨k₁ + 1, k₂, p, q, hr, RS.StepsN.tail s h1, h2, by omega⟩
      · exact Or.inr (Or.inr ⟨1, 0, f, x, f', x, rfl, heqbc.symm,
          RS.StepsN.tail hs (@RS.StepsN.refl RS.SC f'), @RS.StepsN.refl RS.SC x, by omega⟩)
      · injection heqb with hg hy
        subst hg; subst hy
        exact Or.inr (Or.inr ⟨nf + 1, nx, f, x, g', y', rfl, heqc,
          RS.StepsN.tail hs pf2, px2, by omega⟩)
    · subst heq1; subst heq2
      rcases ih with ⟨k₁, k₂, p, q, hr, h1, h2, hsum⟩ | ⟨hm0, heqbc⟩
        | ⟨nf, nx, g, y, g', y', heqb, heqc, pf2, px2, hsum⟩
      · exact Or.inl ⟨k₁ + 1, k₂, p, q, hr, RS.StepsN.tail s h1, h2, by omega⟩
      · exact Or.inr (Or.inr ⟨0, 1, f, x, f, x', rfl, heqbc.symm,
          @RS.StepsN.refl RS.SC f, RS.StepsN.tail hs (@RS.StepsN.refl RS.SC x'), by omega⟩)
      · injection heqb with hg hy
        subst hg; subst hy
        exact Or.inr (Or.inr ⟨nf, nx + 1, f, x, g', y', rfl, heqc,
          pf2, RS.StepsN.tail hs px2, by omega⟩)

/-- Localization with lengths: a cycle of length `n` yields a root cycle of total length ≤ `n`. -/
theorem sc_cycle_root_length_aux : ∀ (size : Nat), ∀ (n : Nat) (t : SCTerm),
    t.leafCount ≤ size → 1 ≤ n → RS.SC.StepsN n t t →
    ∃ a b k, SCRootStep a b ∧ RS.SC.StepsN k b a ∧ k + 1 ≤ n := by
  intro size
  induction size with
  | zero =>
      intro n t hle _ _
      exact absurd hle (by have := scLeaf_pos t; omega)
  | succ size ih =>
      intro n t hle h1 hcyc
      rcases sc_stepsN_facts hcyc with ⟨k₁, k₂, a, b, hr, hta, hbt, hsum⟩ | ⟨hn0, _⟩
        | ⟨nf, nx, f, x, f', x', heq1, heq2, pf, px, hsum⟩
      · exact ⟨a, b, k₂ + k₁, hr, RS.StepsN.trans hbt hta, by omega⟩
      · subst hn0
        exact absurd h1 (Nat.not_succ_le_zero 0)
      · subst heq1
        injection heq2 with hf hx
        subst hf; subst hx
        have hsize : f.leafCount + x.leafCount ≤ size + 1 := hle
        rcases Nat.lt_or_ge 0 nf with hnf | hnf
        · obtain ⟨a, b, k, hr, hret, hk⟩ :=
            ih nf f (by have := scLeaf_pos x; omega) (by omega) pf
          exact ⟨a, b, k, hr, hret, by omega⟩
        · obtain ⟨a, b, k, hr, hret, hk⟩ :=
            ih nx x (by have := scLeaf_pos f; omega) (by omega) px
          exact ⟨a, b, k, hr, hret, by omega⟩

/-- The packaged form. -/
theorem sc_cycle_needs_root_length {n : Nat} {t : SCTerm} (h1 : 1 ≤ n)
    (hcyc : RS.SC.StepsN n t t) :
    ∃ a b k, SCRootStep a b ∧ RS.SC.StepsN k b a ∧ k + 1 ≤ n :=
  sc_cycle_root_length_aux t.leafCount n t (Nat.le_refl _) h1 hcyc

/-- **MINIMAL CYCLES ARE ROOT CYCLES**: if `n` is the least nonempty cycle length, some root
cycle has EXACTLY that length — localization spends no length on a minimal cycle, so any descent
argument may assume its minimal cycle fires at the root. -/
theorem sc_minimal_cycle_is_root {n : Nat} {t : SCTerm} (h1 : 1 ≤ n)
    (hcyc : RS.SC.StepsN n t t)
    (hmin : ∀ m u, 1 ≤ m → RS.SC.StepsN m u u → n ≤ m) :
    ∃ a b k, SCRootStep a b ∧ RS.SC.StepsN k b a ∧ k + 1 = n := by
  obtain ⟨a, b, k, hr, hret, hle⟩ := sc_cycle_needs_root_length h1 hcyc
  have hcyc' : RS.SC.StepsN (k + 1) a a := RS.StepsN.tail (scRootStep_step hr) hret
  have := hmin (k + 1) a (by omega) hcyc'
  exact ⟨a, b, k, hr, hret, by omega⟩

-- ## Stage 94: no two-cycles — the first kill from descend-vs-minimality
-- Stage 93's localization makes short cycles very concrete: a 2-cycle yields a root cycle of
-- length ≤ 2, i.e. a root fire followed by AT MOST ONE step straight back. Working the return
-- step against the fired shape kills every branch: most die on size (a term absorbing itself
-- under an application) or occurs-check; the one live-looking branch — an `appL` return over a
-- root C-fire — needs the step `x ⟶ C x`, which the frozen left forbids. So `{S,C}` has no
-- cycles of length 2, and with Stage 93's no-self-loops the minimal cycle length rises to 3.

/-- Root steps, as equations. -/
theorem scRootStep_inv {s t : SCTerm} (h : SCRootStep s t) :
    (∃ f g x, s = SCTerm.app (SCTerm.app (SCTerm.app SCTerm.S f) g) x
      ∧ t = SCTerm.app (SCTerm.app f x) (SCTerm.app g x))
    ∨ (∃ x y z, s = SCTerm.app (SCTerm.app (SCTerm.app SCTerm.C x) y) z
      ∧ t = SCTerm.app (SCTerm.app x z) y) := by
  cases h with
  | S_red f g x => exact Or.inl ⟨f, g, x, rfl, rfl⟩
  | C_red x y z => exact Or.inr ⟨x, y, z, rfl, rfl⟩

private theorem sc_ne_absorb_left {s r : SCTerm} (h : s = SCTerm.app s r) : False := by
  have hc := congrArg SCTerm.leafCount h
  have := scLeaf_pos r
  exact absurd hc (by
    show ¬(s.leafCount = s.leafCount + r.leafCount)
    omega)

private theorem sc_ne_absorb_right {s r : SCTerm} (h : s = SCTerm.app r s) : False := by
  have hc := congrArg SCTerm.leafCount h
  have := scLeaf_pos r
  exact absurd hc (by
    show ¬(s.leafCount = r.leafCount + s.leafCount)
    omega)

/-- A root fire is never undone in one step. -/
theorem sc_no_root_two_cycle {a b : SCTerm} (hr : SCRootStep a b) (hs : SCStep b a) : False := by
  cases hr with
  | S_red f g x =>
      rcases scStep_cases hs with hroot
        | ⟨F, X, F', heq1, heq2, hstep⟩ | ⟨F, X, X', heq1, heq2, hstep⟩
      · rcases scRootStep_inv hroot with ⟨p, q, r, hb, ha⟩ | ⟨p, q, r, hb, ha⟩
        · injection hb with hb1 hb2
          injection hb1 with hb3 hb4
          injection ha with ha1 ha2
          rw [← hb4] at ha2
          exact sc_ne_absorb_left ha2
        · injection hb with hb1 hb2
          injection ha with ha1 ha2
          injection ha1 with ha3 ha4
          rw [← ha4] at hb2
          exact sc_ne_absorb_left hb2.symm
      · injection heq1 with hF hX
        injection heq2 with hF' hX2
        rw [← hX2] at hX
        exact sc_ne_absorb_right hX.symm
      · injection heq1 with hF hX
        injection heq2 with hF2 hX'
        rw [← hF] at hF2
        injection hF2 with hSf hg
        exact sc_ne_absorb_right hSf.symm
  | C_red x y z =>
      rcases scStep_cases hs with hroot
        | ⟨F, X, F', heq1, heq2, hstep⟩ | ⟨F, X, X', heq1, heq2, hstep⟩
      · rcases scRootStep_inv hroot with ⟨p, q, r, hb, ha⟩ | ⟨p, q, r, hb, ha⟩
        · injection hb with hb1 hb2
          injection hb1 with hb3 hb4
          injection ha with ha1 ha2
          rw [← hb4] at ha2
          exact sc_ne_absorb_left ha2
        · injection hb with hb1 hb2
          injection hb1 with hb3 hb4
          injection ha with ha1 ha2
          injection ha1 with ha3 ha4
          rw [← ha3] at hb3
          have hc := congrArg SCTerm.leafCount hb3
          exact absurd hc (by
            show ¬(x.leafCount = 1 + (1 + x.leafCount))
            omega)
      · -- the live-looking branch: an appL return forces y = z and the step `x z ⟶ (C x) z`
        injection heq1 with hF hX
        injection heq2 with hF' hX2
        rw [← hX2] at hX
        rw [hX] at hF'
        rw [← hF, ← hF'] at hstep
        rcases scStep_cases hstep with hroot2
          | ⟨P, Q, P', k1, k2, hst2⟩ | ⟨P, Q, Q', k1, k2, hst2⟩
        · rcases scRootStep_inv hroot2 with ⟨p, q, r, h1, h2⟩ | ⟨p, q, r, h1, h2⟩
          · injection h1 with i1 i2
            injection h2 with j1 j2
            rw [← i2] at j2
            exact sc_ne_absorb_right j2
          · injection h1 with i1 i2
            injection h2 with j1 j2
            injection j1 with jC jx
            rw [← jC] at i1
            rw [← j2] at i1
            have hxz : x = z := jx.trans i2.symm
            rw [hxz] at i1
            exact sc_ne_absorb_right i1
        · injection k1 with i1 i2
          injection k2 with j1 j2
          rw [← i1] at hst2
          rw [← j1] at hst2
          exact sc_no_leaf_self_embed (fun _ _ h => SCTerm.noConfusion h)
            (@RS.Steps.single RS.SC _ _ hst2)
        · injection k1 with i1 i2
          injection k2 with j1 j2
          rw [← i1] at j1
          exact sc_ne_absorb_right j1.symm
      · injection heq1 with hF hX
        injection heq2 with hF2 hX'
        rw [← hF] at hF2
        injection hF2 with hCx hy
        exact sc_ne_absorb_right hCx.symm

/-- No `{S,C}` cycle has length 2. -/
theorem sc_no_two_cycle {t : SCTerm} (h : RS.SC.StepsN 2 t t) : False := by
  obtain ⟨a, b, k, hr, hret, hk⟩ := sc_cycle_needs_root_length (by omega) h
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have heq : b = a := RS.stepsN_zero_eq hret
    subst heq
    exact scStep_irrefl b (scRootStep_step hr)
  · exact sc_no_root_two_cycle hr (RS.stepsN_one_step hret)

/-- **Minimal cycle length is at least 3.** -/
theorem sc_cycle_length_ge_three {n : Nat} {t : SCTerm} (h1 : 1 ≤ n)
    (hcyc : RS.SC.StepsN n t t) : 3 ≤ n := by
  have h2 := sc_cycle_length_ge_two h1 hcyc
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn : n = 2 := by omega
    subst hn
    exact (sc_no_two_cycle hcyc).elim
  · exact h3

-- ## Stage 95: budgets — the return dichotomies with lengths, and collapse costs two
-- The general form of Stage 94's constraint. First an unconditional new fact: NO SINGLE STEP
-- collapses `u v` to `v` — the root and appL cases die on absorption, and the appR case demands
-- the same collapse one size smaller — so collapse costs at least two steps. Then the Stage 82
-- return dichotomies in `StepsN` form, with exact budget accounting and the side conditions the
-- shapes force: both left projections are nonempty (absorption), and the S-side's right
-- projection is a collapse, so it costs ≥ 2. Corollary: an S-rooted root cycle whose return
-- carries no whole-term root fire has return length ≥ 3, cycle length ≥ 4.

/-- No single step collapses an application onto its own argument. -/
theorem sc_no_step_collapse_aux : ∀ (n : Nat) (v u : SCTerm), v.leafCount ≤ n →
    ¬ SCStep (SCTerm.app u v) v := by
  intro n
  induction n with
  | zero =>
      intro v u hle _
      exact absurd hle (by have := scLeaf_pos v; omega)
  | succ n ih =>
      intro v u hle h
      rcases scStep_cases h with hroot
        | ⟨F, X, F', heq1, heq2, hstep⟩ | ⟨F, X, X', heq1, heq2, hstep⟩
      · rcases scRootStep_inv hroot with ⟨p, q, r, hb, ha⟩ | ⟨p, q, r, hb, ha⟩
        · injection hb with hb1 hb2
          rw [← hb2] at ha
          have hc := congrArg SCTerm.leafCount ha
          have hp := scLeaf_pos p
          have hq := scLeaf_pos q
          exact absurd hc (by
            show ¬(v.leafCount = (p.leafCount + v.leafCount) + (q.leafCount + v.leafCount))
            omega)
        · injection hb with hb1 hb2
          rw [← hb2] at ha
          have hc := congrArg SCTerm.leafCount ha
          have hp := scLeaf_pos p
          have hq := scLeaf_pos q
          exact absurd hc (by
            show ¬(v.leafCount = (p.leafCount + v.leafCount) + q.leafCount)
            omega)
      · injection heq1 with h1 h2
        rw [← h2] at heq2
        exact sc_ne_absorb_right heq2
      · injection heq1 with h1 h2
        rw [← h1] at heq2
        rw [← h2] at hstep
        rw [heq2] at hstep
        have hx : X'.leafCount ≤ n := by
          have hc : v.leafCount = u.leafCount + X'.leafCount := by rw [heq2]; rfl
          have := scLeaf_pos u
          omega
        exact ih X' u hx hstep

theorem sc_no_step_collapse {u v : SCTerm} (h : SCStep (SCTerm.app u v) v) : False :=
  sc_no_step_collapse_aux v.leafCount v u (Nat.le_refl _) h

/-- **Collapse costs at least two steps.** -/
theorem sc_collapse_length_ge_two {n : Nat} {u v : SCTerm}
    (h : RS.SC.StepsN n (SCTerm.app u v) v) : 2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · have heq := RS.stepsN_zero_eq h
      exact (sc_ne_absorb_right heq.symm).elim
    · exact (sc_no_step_collapse (RS.stepsN_one_step h)).elim
  · exact h2

/-- The S-return dichotomy with budgets: a root sandwich accounting for every step, or a
projection with `kL + kR = n`, a nonempty self-embedding and a ≥ 2 collapse. -/
theorem sc_root_S_return_length {f g x : SCTerm} {n : Nat}
    (hback : RS.SC.StepsN n (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x)) :
    (∃ k₁ k₂ a b, SCRootStep a b
      ∧ RS.SC.StepsN k₁ (.app (.app f x) (.app g x)) a
      ∧ RS.SC.StepsN k₂ b (.app (.app (.app .S f) g) x) ∧ k₁ + 1 + k₂ = n)
    ∨ (∃ kL kR, RS.SC.StepsN kL (.app f x) (.app (.app .S f) g)
        ∧ RS.SC.StepsN kR (.app g x) x ∧ kL + kR = n ∧ 1 ≤ kL ∧ 2 ≤ kR) := by
  rcases sc_stepsN_facts hback with h | ⟨hn0, heq⟩
    | ⟨nf, nx, F, X, F', X', heq1, heq2, pf, px, hsum⟩
  · exact Or.inl h
  · injection heq with h1 h2
    exact (sc_ne_absorb_right h2.symm).elim
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    have hkL : 1 ≤ nf := by
      rcases Nat.lt_or_ge 0 nf with h' | h'
      · omega
      · have h0 : nf = 0 := by omega
        subst h0
        have heq := RS.stepsN_zero_eq pf
        injection heq with e1 e2
        exact (sc_ne_absorb_right e1).elim
    have hkR : 2 ≤ nx := sc_collapse_length_ge_two px
    exact Or.inr ⟨nf, nx, pf, px, hsum, hkL, hkR⟩

/-- The C-return dichotomy with budgets: the left self-embedding is nonempty; the right
projection `y ⟶* z` may be free. -/
theorem sc_root_C_return_length {x y z : SCTerm} {n : Nat}
    (hback : RS.SC.StepsN n (.app (.app x z) y) (.app (.app (.app .C x) y) z)) :
    (∃ k₁ k₂ a b, SCRootStep a b
      ∧ RS.SC.StepsN k₁ (.app (.app x z) y) a
      ∧ RS.SC.StepsN k₂ b (.app (.app (.app .C x) y) z) ∧ k₁ + 1 + k₂ = n)
    ∨ (∃ kL kR, RS.SC.StepsN kL (.app x z) (.app (.app .C x) y)
        ∧ RS.SC.StepsN kR y z ∧ kL + kR = n ∧ 1 ≤ kL) := by
  rcases sc_stepsN_facts hback with h | ⟨hn0, heq⟩
    | ⟨nf, nx, F, X, F', X', heq1, heq2, pf, px, hsum⟩
  · exact Or.inl h
  · injection heq with h1 h2
    injection h1 with h3 h4
    exact (sc_ne_absorb_right h3).elim
  · injection heq1 with hF hX
    injection heq2 with hF' hX'
    subst hF; subst hX; subst hF'; subst hX'
    have hkL : 1 ≤ nf := by
      rcases Nat.lt_or_ge 0 nf with h' | h'
      · omega
      · have h0 : nf = 0 := by omega
        subst h0
        have heq := RS.stepsN_zero_eq pf
        injection heq with e1 e2
        exact (sc_ne_absorb_right e1).elim
    exact Or.inr ⟨nf, nx, pf, px, hsum, hkL⟩

/-- An S-rooted root cycle whose return carries no whole-term root fire has return length ≥ 3
(cycle length ≥ 4): the self-embedding costs ≥ 1 and the collapse costs ≥ 2. -/
theorem sc_root_S_projection_length {f g x : SCTerm} {k : Nat}
    (hback : RS.SC.StepsN k (.app (.app f x) (.app g x)) (.app (.app (.app .S f) g) x))
    (hnoroot : ¬ ∃ k₁ k₂ a b, SCRootStep a b
      ∧ RS.SC.StepsN k₁ (.app (.app f x) (.app g x)) a
      ∧ RS.SC.StepsN k₂ b (.app (.app (.app .S f) g) x) ∧ k₁ + 1 + k₂ = k) :
    3 ≤ k := by
  rcases sc_root_S_return_length hback with h | ⟨kL, kR, _, _, hsum, hkL, hkR⟩
  · exact absurd h hnoroot
  · omega
