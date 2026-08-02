--! # Bounded reachability for {S,C} is decidable (Stage 121)
-- The decidability program's first executable brick: a VERIFIED one-step successor function,
-- its soundness and completeness against `SCStep`, and the bounded-reachability closure with a
-- full correctness iff — so `∃ k ≤ n, StepsN k t u` is `Decidable`. The full-reachability
-- question remains exactly the bounded-intermediate question: these tools decide any region a
-- future intermediate bound pins down.
import CombinatorCalculusPlayground.Universality.SCConfluence

/-- Root-redex successors (zero or one). -/
def scSuccRoot : SCTerm → List SCTerm
  | .app (.app (.app .S f) g) x => [.app (.app f x) (.app g x)]
  | .app (.app (.app .C x) y) z => [.app (.app x z) y]
  | _ => []

/-- All one-step successors. -/
def scSucc : SCTerm → List SCTerm
  | .S => []
  | .C => []
  | .app f x =>
      scSuccRoot (.app f x)
        ++ (scSucc f).map (fun f' => .app f' x)
        ++ (scSucc x).map (fun x' => .app f x')

theorem scSuccRoot_sound : ∀ {t u : SCTerm}, u ∈ scSuccRoot t → SCStep t u := by
  intro t u h
  match t, h with
  | .app (.app (.app .S f) g) x, h =>
      cases h with
      | head => exact SCStep.S_red f g x
      | tail _ h' => cases h'
  | .app (.app (.app .C x) y) z, h =>
      cases h with
      | head => exact SCStep.C_red x y z
      | tail _ h' => cases h'

theorem scSucc_sound : ∀ {t u : SCTerm}, u ∈ scSucc t → SCStep t u := by
  intro t
  induction t with
  | S => intro u h; exact absurd h (by simp [scSucc])
  | C => intro u h; exact absurd h (by simp [scSucc])
  | app f x ihf ihx =>
      intro u h
      simp only [scSucc, List.mem_append, List.mem_map] at h
      rcases h with (h | ⟨f', hf', rfl⟩) | ⟨x', hx', rfl⟩
      · exact scSuccRoot_sound h
      · exact SCStep.appL (ihf hf')
      · exact SCStep.appR (ihx hx')

theorem scSucc_complete : ∀ {t u : SCTerm}, SCStep t u → u ∈ scSucc t := by
  intro t u h
  induction h with
  | S_red f g x =>
      simp [scSucc, scSuccRoot]
  | C_red x y z =>
      simp [scSucc, scSuccRoot]
  | @appL a a' b h ih =>
      simp only [scSucc, List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨a', ih, rfl⟩)
  | @appR a b b' h ih =>
      simp only [scSucc, List.mem_append, List.mem_map]
      exact Or.inr ⟨b', ih, rfl⟩

/-- Peel the LAST step off a length-indexed path, generically. -/
theorem RS.stepsN_last {A : RS} : ∀ {k : Nat} {t u : A.Carrier},
    A.StepsN (k + 1) t u → ∃ v, A.StepsN k t v ∧ A.step v u := by
  intro k
  induction k with
  | zero =>
      intro t u h
      cases h with
      | tail s rest =>
          have := RS.stepsN_zero_eq rest
          exact ⟨t, RS.StepsN.refl t, this ▸ s⟩
  | succ k ih =>
      intro t u h
      cases h with
      | tail s rest =>
          obtain ⟨v, hv, hs⟩ := ih rest
          exact ⟨v, RS.StepsN.tail s hv, hs⟩

/-- Everything reachable within `n` steps. -/
def scReachFrom (t : SCTerm) : Nat → List SCTerm
  | 0 => [t]
  | n + 1 => scReachFrom t n ++ (scReachFrom t n).flatMap scSucc

theorem scReachFrom_start (t : SCTerm) : ∀ n, t ∈ scReachFrom t n
  | 0 => by simp [scReachFrom]
  | n + 1 => by
      simp only [scReachFrom, List.mem_append]
      exact Or.inl (scReachFrom_start t n)

theorem scReachFrom_sound : ∀ (n : Nat) {t u : SCTerm}, u ∈ scReachFrom t n →
    ∃ k, k ≤ n ∧ RS.SC.StepsN k t u := by
  intro n
  induction n with
  | zero =>
      intro t u h
      simp only [scReachFrom, List.mem_singleton] at h
      exact ⟨0, Nat.le_refl _, h ▸ @RS.StepsN.refl RS.SC t⟩
  | succ n ih =>
      intro t u h
      simp only [scReachFrom, List.mem_append, List.mem_flatMap] at h
      rcases h with h | ⟨v, hv, hu⟩
      · obtain ⟨k, hk, hs⟩ := ih h
        exact ⟨k, Nat.le_succ_of_le hk, hs⟩
      · obtain ⟨k, hk, hs⟩ := ih hv
        exact ⟨k + 1, Nat.succ_le_succ hk,
          RS.StepsN.trans hs (RS.StepsN.tail (scSucc_sound hu) (@RS.StepsN.refl RS.SC u))⟩

theorem scReachFrom_complete : ∀ (n : Nat) {t u : SCTerm} (k : Nat),
    k ≤ n → RS.SC.StepsN k t u → u ∈ scReachFrom t n := by
  intro n
  induction n with
  | zero =>
      intro t u k hk hs
      have h0 : k = 0 := Nat.le_zero.mp hk
      subst h0
      have := RS.stepsN_zero_eq hs
      subst this
      exact scReachFrom_start t 0
  | succ n ih =>
      intro t u k hk hs
      cases k with
      | zero =>
          have := RS.stepsN_zero_eq hs
          subst this
          exact scReachFrom_start t (n + 1)
      | succ k =>
          obtain ⟨v, hv, hstep⟩ := RS.stepsN_last hs
          have hvmem := ih k (Nat.le_of_succ_le_succ hk) hv
          simp only [scReachFrom, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨v, hvmem, scSucc_complete hstep⟩

/-- The correctness iff, packaged. -/
theorem scReachFrom_iff (n : Nat) (t u : SCTerm) :
    u ∈ scReachFrom t n ↔ ∃ k, k ≤ n ∧ RS.SC.StepsN k t u :=
  ⟨scReachFrom_sound n, fun ⟨k, hk, hs⟩ => scReachFrom_complete n k hk hs⟩

/-- **Bounded reachability in `{S,C}` is decidable.** -/
def scReachWithin_decidable (n : Nat) (t u : SCTerm) :
    Decidable (∃ k, k ≤ n ∧ RS.SC.StepsN k t u) :=
  decidable_of_iff _ (scReachFrom_iff n t u)

-- ## Stage 122: S-count conservation, and the pairing deadlock
-- Two yields. FORMAL: C-fires preserve the S-count exactly (they kill only their own C), so in
-- the C-fragment (S-count, leaf-count) evolve as (constant, −1 per step) — sharpening Stage
-- 117's conservation to a two-component invariant. ON PAPER (ledger): the member calculus now
-- PROVES the arrival-order pairing impossibility by deadlock — for `s` to head the final term,
-- both `a` and `b` must cross behind `s`, but a crossing's configuration `[C, machine, Y, s]`
-- forces the other variable to already be behind `s` (it cannot hide in the machine slot: vars
-- in argument position are bare, and var-headed members freeze wrong on unpacking) — so no
-- crossing can be first. Formalizing the deadlock needs the member-position calculus as a Lean
-- structure; the supporting laws land now.

/-- Count the `S` leaves. -/
def SCTerm.countS : SCTerm → Nat
  | .S => 1
  | .C => 0
  | .app f x => f.countS + x.countS

/-- C-fires preserve the S-count exactly. -/
theorem scStepC_countS {t u : SCTerm} (h : SCStepC t u) :
    u.countS = t.countS := by
  induction h with
  | C_red x y z =>
      show (x.countS + z.countS) + y.countS = ((0 + x.countS) + y.countS) + z.countS
      omega
  | appL h ih =>
      show _ + _ = _ + _
      omega
  | appR h ih =>
      show _ + _ = _ + _
      omega

/-- The C-fragment's two-component invariant: S-count constant, leaf count down one per step. -/
theorem scStepsC_invariant : ∀ {n : Nat} {t u : SCTerm}, RS.SCC.StepsN n t u →
    u.countS = t.countS ∧ n + u.leafCount = t.leafCount := by
  intro n t u h
  exact ⟨by
    refine h.rec (motive := fun n t u _ =>
        SCTerm.countS u = SCTerm.countS t) ?_ ?_
    · intro a
      rfl
    · intro m a b c s rest ih
      rw [ih, scStepC_countS s],
    scStepsC_conservation h⟩

-- ## Stage 132: the mountain — bounded intermediates has a floor
-- The frontier question for full `{S,C}` decidability is whether every reachability fact has a
-- path whose intermediates are bounded by some computable function of the endpoint sizes.
-- Probing computationally (minimax-bottleneck search over all starts to 8 leaves): mountains
-- EXIST, and they grow fast — at 6 leaves the forced excess is one leaf, at 8 leaves every
-- path to some 3-to-8-leaf targets passes through THIRTY-ONE. Machine-checked below: the
-- minimal mountain. `S (C S) S (S S) ⟶* S (S (S S)) (S S)` (six leaves each), yet the source's
-- ONLY step goes to seven leaves — so the identity bound (max of the endpoints) is refuted,
-- and any bounding function `f` for the frontier must satisfy `f(6,6) ≥ 7` and (bounded
-- evidence) `f(8,8) ≥ 31`. The generic `StepsLe` predicate states the question precisely.

/-- Paths whose every term (endpoints included) stays within a size bound. -/
inductive RS.StepsLe (A : RS) (size : A.Carrier → Nat) (c : Nat) :
    A.Carrier → A.Carrier → Prop
  | refl (a : A.Carrier) : size a ≤ c → RS.StepsLe A size c a a
  | tail {a b d : A.Carrier} : A.step a b → size a ≤ c →
      RS.StepsLe A size c b d → RS.StepsLe A size c a d

theorem RS.StepsLe.head_le {A : RS} {size : A.Carrier → Nat} {c : Nat}
    {a b : A.Carrier} (h : RS.StepsLe A size c a b) : size a ≤ c := by
  cases h with
  | refl _ h => exact h
  | tail _ h _ => exact h

theorem RS.StepsLe.toSteps {A : RS} {size : A.Carrier → Nat} {c : Nat}
    {a b : A.Carrier} (h : RS.StepsLe A size c a b) : A.Steps a b := by
  induction h with
  | refl _ _ => exact RS.Steps.refl _
  | tail s _ _ ih => exact RS.Steps.tail s ih

theorem RS.StepsLe.weaken {A : RS} {size : A.Carrier → Nat} {c c' : Nat}
    {a b : A.Carrier} (hcc : c ≤ c') (h : RS.StepsLe A size c a b) :
    RS.StepsLe A size c' a b := by
  induction h with
  | refl a ha => exact RS.StepsLe.refl a (Nat.le_trans ha hcc)
  | tail s ha _ ih => exact RS.StepsLe.tail s (Nat.le_trans ha hcc) ih

/-- Every path is bounded by SOMETHING — the frontier question is whether that something can
be a function of the endpoint sizes alone. -/
theorem RS.Steps.exists_le {A : RS} (size : A.Carrier → Nat) {a b : A.Carrier}
    (h : A.Steps a b) : ∃ c, RS.StepsLe A size c a b := by
  induction h with
  | refl a => exact ⟨size a, RS.StepsLe.refl a (Nat.le_refl _)⟩
  | tail s _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨max (size _) c,
        RS.StepsLe.tail s (Nat.le_max_left _ _) (hc.weaken (Nat.le_max_right _ _))⟩

/-- Generic first-step inversion for bounded paths between distinct endpoints. -/
theorem RS.StepsLe.first {A : RS} {size : A.Carrier → Nat} {c : Nat}
    {a b : A.Carrier} (h : RS.StepsLe A size c a b) (hne : a ≠ b) :
    ∃ v, A.step a v ∧ size v ≤ c := by
  cases h with
  | refl _ _ => exact absurd rfl hne
  | tail s _ rest => exact ⟨_, s, rest.head_le⟩

/-- The minimal mountain's base camp: `S (C S) S (S S)`, six leaves. -/
def scMtT : SCTerm := .app (.app (.app .S (.app .C .S)) .S) (.app .S .S)

/-- The forced peak: seven leaves. -/
def scMtV : SCTerm := .app (.app (.app .C .S) (.app .S .S)) (.app .S (.app .S .S))

/-- The far side: `S (S (S S)) (S S)`, six leaves. -/
def scMtU : SCTerm := .app (.app .S (.app .S (.app .S .S))) (.app .S .S)

#guard scMtT.leafCount = 6
#guard scMtV.leafCount = 7
#guard scMtU.leafCount = 6
#guard scSucc scMtT = [scMtV]

/-- The crossing: two fires, over the peak. -/
theorem scMt_steps : RS.SC.Steps scMtT scMtU :=
  RS.Steps.tail (SCStep.S_red (.app .C .S) .S (.app .S .S))
    (RS.Steps.tail (SCStep.C_red .S (.app .S .S) (.app .S (.app .S .S)))
      (RS.Steps.refl _))

theorem scMt_ne : scMtT ≠ scMtU := by
  intro h
  injection h with h1 _
  injection h1 with h2 _
  exact SCTerm.noConfusion h2

/-- The base camp has exactly one exit, and it climbs. -/
theorem scMt_forced {v : SCTerm} (h : SCStep scMtT v) : v.leafCount = 7 := by
  have hm := scSucc_complete h
  rw [show scSucc scMtT = [scMtV] from rfl] at hm
  simp at hm
  rw [hm]
  rfl

/-- **The identity bound fails**: there is no path from `scMtT` to `scMtU` staying within the
maximum of the endpoint sizes — every path must exceed it. Any bounding function for the
`{S,C}` decidability frontier must allow intermediates strictly above both endpoints. -/
theorem sc_no_max_bound :
    ¬ (∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (max t.leafCount u.leafCount) t u) := by
  intro hall
  have h := hall scMtT scMtU scMt_steps
  have h6 : RS.StepsLe RS.SC SCTerm.leafCount 6 scMtT scMtU := h
  obtain ⟨v, hs, hle⟩ := RS.StepsLe.first h6 scMt_ne
  have h7 := scMt_forced hs
  omega
