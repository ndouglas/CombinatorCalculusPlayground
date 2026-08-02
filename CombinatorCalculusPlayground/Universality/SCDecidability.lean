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
