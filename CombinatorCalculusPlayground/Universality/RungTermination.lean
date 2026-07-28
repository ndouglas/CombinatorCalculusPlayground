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
