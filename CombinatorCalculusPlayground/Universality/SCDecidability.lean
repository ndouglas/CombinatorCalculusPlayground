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

-- ## Stage 133: the pigeonhole and the capped engine
-- Toward the frontier's backbone theorem — "a computable intermediate bound implies
-- decidability". Two bricks: the constructive list pigeonhole (a duplicate-free list of
-- elements drawn from `L` is no longer than `L`), and the capped reachability engine
-- (saturate the successor relation inside a leaf-count cap, duplicate-free by construction).
-- Deep probe data behind the ranking (recorded in the ledger): the 8-leaf champion's
-- bottleneck-optimal crossing is 71 steps long with a 31-leaf peak — real computation happens
-- between small endpoints, so if a bound `f` exists it is not gentle, and the backbone theorem
-- is what makes "f exists" equivalent to decidability rather than a heuristic.

-- (Core's `List.erase` lemmas ride `Classical.choice` — the TENTH leak, and the first found
-- inside the core library rather than in a tactic. Hand-rolled removal keeps the budget.)
/-- Remove the first occurrence. Choice-free twin of `List.erase`. -/
def listRemove {α : Type} [DecidableEq α] : List α → α → List α
  | [], _ => []
  | b :: l, a => if b = a then l else b :: listRemove l a

theorem listRemove_length {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a : α), a ∈ l → (listRemove l a).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons b l ih =>
      intro a ha
      by_cases h : b = a
      · show (if b = a then l else b :: listRemove l a).length + 1 = _
        rw [if_pos h]
        rfl
      · show (if b = a then l else b :: listRemove l a).length + 1 = _
        rw [if_neg h]
        have hal : a ∈ l := by
          rcases List.mem_cons.mp ha with he | hm
          · exact absurd he.symm h
          · exact hm
        have := ih a hal
        show ((listRemove l a).length + 1) + 1 = l.length + 1
        omega

theorem listRemove_mem {α : Type} [DecidableEq α] :
    ∀ (l : List α) (a x : α), x ∈ l → x ≠ a → x ∈ listRemove l a := by
  intro l
  induction l with
  | nil => intro a x hx _; exact absurd hx List.not_mem_nil
  | cons b l ih =>
      intro a x hx hne
      by_cases h : b = a
      · show x ∈ if b = a then l else b :: listRemove l a
        rw [if_pos h]
        rcases List.mem_cons.mp hx with he | hm
        · exact absurd (he.trans h) hne
        · exact hm
      · show x ∈ if b = a then l else b :: listRemove l a
        rw [if_neg h]
        rcases List.mem_cons.mp hx with he | hm
        · rw [he]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (ih a x hm hne)

/-- Constructive pigeonhole: a duplicate-free list drawn from `L` is no longer than `L`. -/
theorem List.nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ a, a ∈ xs → a ∈ ys) → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil => intro ys _ _; exact Nat.zero_le _
  | cons x xs ih =>
      intro ys hnd hsub
      have hx : x ∈ ys := hsub x (List.mem_cons_self)
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hsub' : ∀ a, a ∈ xs → a ∈ listRemove ys x := by
        intro a ha
        have hne : a ≠ x := fun he => hxnot (he ▸ ha)
        exact listRemove_mem ys x a (hsub a (List.mem_cons_of_mem x ha)) hne
      have hlen := ih (listRemove ys x) hnd' hsub'
      have hrem := listRemove_length ys x hx
      show xs.length + 1 ≤ ys.length
      omega

/-- Insert without duplicating. -/
def scInsert (ts : List SCTerm) (u : SCTerm) : List SCTerm :=
  if u ∈ ts then ts else u :: ts

theorem scInsert_mem {ts : List SCTerm} {u v : SCTerm} :
    v ∈ scInsert ts u ↔ v = u ∨ v ∈ ts := by
  unfold scInsert
  by_cases h : u ∈ ts
  · rw [if_pos h]
    constructor
    · intro hv; exact Or.inr hv
    · rintro (rfl | hv)
      · exact h
      · exact hv
  · rw [if_neg h]
    exact List.mem_cons

theorem scInsert_nodup {ts : List SCTerm} {u : SCTerm} (h : ts.Nodup) :
    (scInsert ts u).Nodup := by
  unfold scInsert
  by_cases hm : u ∈ ts
  · rw [if_pos hm]; exact h
  · rw [if_neg hm]; exact List.nodup_cons.mpr ⟨hm, h⟩

theorem scInsert_sub {ts : List SCTerm} {u : SCTerm} : ∀ v ∈ ts, v ∈ scInsert ts u := by
  intro v hv
  exact scInsert_mem.mpr (Or.inr hv)

/-- One saturation round: fold all capped successors in. -/
def scRoundCapped (c : Nat) (ts : List SCTerm) : List SCTerm :=
  ((ts.flatMap scSucc).filter (fun u => u.leafCount ≤ c)).foldl scInsert ts

theorem scFoldInsert_base : ∀ (ns ts : List SCTerm) (v : SCTerm), v ∈ ts →
    v ∈ ns.foldl scInsert ts := by
  intro ns
  induction ns with
  | nil => intro ts v hv; exact hv
  | cons n ns ih =>
      intro ts v hv
      exact ih _ v (scInsert_sub v hv)

theorem scFoldInsert_mem : ∀ (ns ts : List SCTerm) (v : SCTerm),
    v ∈ ns.foldl scInsert ts ↔ v ∈ ts ∨ v ∈ ns := by
  intro ns
  induction ns with
  | nil =>
      intro ts v
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h (List.not_mem_nil)
  | cons n ns ih =>
      intro ts v
      show v ∈ ns.foldl scInsert (scInsert ts n) ↔ _
      rw [ih]
      rw [scInsert_mem]
      constructor
      · rintro ((rfl | h) | h)
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem n h)
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr h

theorem scFoldInsert_nodup : ∀ (ns ts : List SCTerm), ts.Nodup →
    (ns.foldl scInsert ts).Nodup := by
  intro ns
  induction ns with
  | nil => intro ts h; exact h
  | cons n ns ih => intro ts h; exact ih _ (scInsert_nodup h)

/-- Membership in a saturation round: the old states plus every capped successor. -/
theorem scRoundCapped_mem {c : Nat} {ts : List SCTerm} {v : SCTerm} :
    v ∈ scRoundCapped c ts
      ↔ v ∈ ts ∨ (∃ w ∈ ts, SCStep w v ∧ v.leafCount ≤ c) := by
  unfold scRoundCapped
  rw [scFoldInsert_mem]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have h' := List.mem_filter.mp h
      obtain ⟨w, hw, hsucc⟩ := List.mem_flatMap.mp h'.1
      exact ⟨w, hw, scSucc_sound hsucc, by simpa using h'.2⟩
  · rintro (h | ⟨w, hw, hstep, hcap⟩)
    · exact Or.inl h
    · right
      refine List.mem_filter.mpr ⟨?_, by simpa⟩
      exact List.mem_flatMap.mpr ⟨w, hw, scSucc_complete hstep⟩

theorem scRoundCapped_nodup {c : Nat} {ts : List SCTerm} (h : ts.Nodup) :
    (scRoundCapped c ts).Nodup :=
  scFoldInsert_nodup _ _ h

theorem scRoundCapped_sub {c : Nat} {ts : List SCTerm} : ∀ v ∈ ts, v ∈ scRoundCapped c ts :=
  fun _ hv => scRoundCapped_mem.mpr (Or.inl hv)

/-- The capped reachability engine: `n` saturation rounds from `t`. -/
def scReachCapped (c : Nat) (t : SCTerm) : Nat → List SCTerm
  | 0 => [t]
  | n + 1 => scRoundCapped c (scReachCapped c t n)

theorem scReachCapped_nodup (c : Nat) (t : SCTerm) : ∀ n, (scReachCapped c t n).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => scRoundCapped_nodup (scReachCapped_nodup c t n)

theorem scReachCapped_mono {c : Nat} {t : SCTerm} {n : Nat} :
    ∀ v ∈ scReachCapped c t n, v ∈ scReachCapped c t (n + 1) :=
  fun v hv => scRoundCapped_sub v hv

/-- Soundness: everything the engine finds is genuinely reachable. -/
theorem scReachCapped_sound {c : Nat} {t : SCTerm} :
    ∀ {n : Nat} {v : SCTerm}, v ∈ scReachCapped c t n → RS.SC.Steps t v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have : v = t := by
        rcases List.mem_cons.mp hv with h | h
        · exact h
        · exact absurd h (List.not_mem_nil)
      rw [this]
      exact @RS.Steps.refl RS.SC t
  | succ n ih =>
      intro v hv
      rcases scRoundCapped_mem.mp hv with h | ⟨w, hw, hstep, _⟩
      · exact ih h
      · exact RS.Steps.trans (ih hw) (RS.Steps.tail hstep (@RS.Steps.refl RS.SC v))

/-- Completeness: a capped path from anything the engine has found lands in the engine's
cone at some fuel. -/
theorem scReachCapped_complete {c : Nat} {t : SCTerm} :
    ∀ {v u : SCTerm}, RS.StepsLe RS.SC SCTerm.leafCount c v u →
    ∀ n, v ∈ scReachCapped c t n → ∃ m, u ∈ scReachCapped c t m := by
  intro v u h
  refine h.rec (motive := fun (v u : SCTerm) _ =>
      ∀ n, v ∈ scReachCapped c t n → ∃ m, u ∈ scReachCapped c t m) ?_ ?_
  · intro a _ n hn
    exact ⟨n, hn⟩
  · intro a b d s _ rest ih n hn
    refine ih (n + 1) ?_
    exact scRoundCapped_mem.mpr
      (Or.inr ⟨a, hn, s, RS.StepsLe.head_le rest⟩)

/-- Every capped path from `t` is seen by the engine at some fuel. -/
theorem scReachCapped_complete_start {c : Nat} {t u : SCTerm}
    (h : RS.StepsLe RS.SC SCTerm.leafCount c t u) :
    ∃ m, u ∈ scReachCapped c t m :=
  scReachCapped_complete h 0 List.mem_cons_self

-- ## Stage 134: the backbone — a computable intermediate bound implies decidability
-- The frontier question becomes a THEOREM about itself: if some function of the endpoint
-- sizes bounds the intermediates of witnessing paths, then `{S,C}` reachability is decidable
-- outright. Enumerate the capped universe (mirroring the Census enumerator's budget pattern),
-- saturate the capped engine inside it by pigeonhole, and decide by list membership.

/-- All `{S,C}` terms with exactly `n` leaves, given budget `d ≥ n` (the budget makes the
recursion structural, exactly as in the Census `enum`). -/
def scEnum : Nat → Nat → List SCTerm
  | _, 0 => []
  | _, 1 => [.S, .C]
  | 0, _ => []
  | d + 1, n + 2 =>
    (List.range (n + 1)).flatMap fun i =>
      (scEnum d (i + 1)).flatMap fun l =>
        (scEnum d (n + 1 - i)).map fun r => SCTerm.app l r

theorem scEnum_succ (d n : Nat) :
    scEnum (d + 1) (n + 2) =
      (List.range (n + 1)).flatMap fun i =>
        (scEnum d (i + 1)).flatMap fun l =>
          (scEnum d (n + 1 - i)).map fun r => SCTerm.app l r := rfl

theorem scEnum_complete : ∀ (t : SCTerm) (d : Nat), t.leafCount ≤ d →
    t ∈ scEnum d t.leafCount := by
  intro t
  induction t with
  | S =>
      intro d hd
      have hd1 : 1 ≤ d := hd
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      show SCTerm.S ∈ [SCTerm.S, SCTerm.C]
      exact List.mem_cons_self
  | C =>
      intro d hd
      have hd1 : 1 ≤ d := hd
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      show SCTerm.C ∈ [SCTerm.S, SCTerm.C]
      exact List.mem_cons_of_mem _ List.mem_cons_self
  | app l r ihl ihr =>
      intro d hd
      have hl1 := scLeaf_pos l
      have hr1 := scLeaf_pos r
      have hsum : (SCTerm.app l r).leafCount = l.leafCount + r.leafCount := rfl
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 :=
        ⟨d - 1, (Nat.succ_pred_eq_of_pos (by rw [hsum] at hd; omega)).symm⟩
      obtain ⟨m, hm⟩ : ∃ m, l.leafCount + r.leafCount = m + 2 :=
        ⟨l.leafCount + r.leafCount - 2, by omega⟩
      rw [hsum, hm, scEnum_succ]
      refine List.mem_flatMap.mpr ⟨l.leafCount - 1, List.mem_range.mpr ?_, ?_⟩
      · omega
      refine List.mem_flatMap.mpr ⟨l, ?_, ?_⟩
      · have h1 : l.leafCount - 1 + 1 = l.leafCount := by omega
        rw [h1]
        exact ihl d' (by rw [hsum] at hd; omega)
      refine List.mem_map.mpr ⟨r, ?_, rfl⟩
      · have h2 : m + 1 - (l.leafCount - 1) = r.leafCount := by omega
        rw [h2]
        exact ihr d' (by rw [hsum] at hd; omega)

/-- The capped universe: every term with at most `c` leaves. -/
def scEnumLe (c : Nat) : List SCTerm :=
  (List.range c).flatMap fun n => scEnum c (n + 1)

theorem scEnumLe_complete {c : Nat} {t : SCTerm} (h : t.leafCount ≤ c) :
    t ∈ scEnumLe c := by
  have h1 := scLeaf_pos t
  refine List.mem_flatMap.mpr ⟨t.leafCount - 1, List.mem_range.mpr (by omega), ?_⟩
  have h2 : t.leafCount - 1 + 1 = t.leafCount := by omega
  rw [h2]
  exact scEnum_complete t c h

/-- Everything the engine holds is capped (given a capped start). -/
theorem scReachCapped_capped {c : Nat} {t : SCTerm} (ht : t.leafCount ≤ c) :
    ∀ {n : Nat} {v : SCTerm}, v ∈ scReachCapped c t n → v.leafCount ≤ c := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hvt : v = t := by
        rcases List.mem_cons.mp hv with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      rw [hvt]
      exact ht
  | succ n ih =>
      intro v hv
      rcases scRoundCapped_mem.mp hv with h | ⟨_, _, _, hcap⟩
      · exact ih h
      · exact hcap

/-- Append a step at the end of a bounded path. -/
theorem RS.StepsLe.snoc {A : RS} {size : A.Carrier → Nat} {c : Nat} {a b d : A.Carrier}
    (h : RS.StepsLe A size c a b) (s : A.step b d) (hd : size d ≤ c) :
    RS.StepsLe A size c a d := by
  induction h with
  | refl _ ha => exact RS.StepsLe.tail s ha (RS.StepsLe.refl _ hd)
  | tail s' ha _ ih => exact RS.StepsLe.tail s' ha (ih s)

/-- Bounded soundness: the engine's members are reached by capped paths. -/
theorem scReachCapped_soundLe {c : Nat} {t : SCTerm} (ht : t.leafCount ≤ c) :
    ∀ {n : Nat} {v : SCTerm}, v ∈ scReachCapped c t n →
    RS.StepsLe RS.SC SCTerm.leafCount c t v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hvt : v = t := by
        rcases List.mem_cons.mp hv with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      rw [hvt]
      exact RS.StepsLe.refl (A := RS.SC) (size := SCTerm.leafCount) (c := c) t ht
  | succ n ih =>
      intro v hv
      rcases scRoundCapped_mem.mp hv with h | ⟨w, hw, hstep, hcap⟩
      · exact ih h
      · exact RS.StepsLe.snoc (ih hw) hstep hcap

theorem scReachCapped_mono_add {c : Nat} {t : SCTerm} (a m : Nat) :
    ∀ v ∈ scReachCapped c t a, v ∈ scReachCapped c t (a + m) := by
  induction m with
  | zero => intro v hv; exact hv
  | succ m ih => intro v hv; exact scReachCapped_mono v (ih v hv)

theorem scReachCapped_mono_le {c : Nat} {t : SCTerm} {a b : Nat} (hab : a ≤ b) :
    ∀ v ∈ scReachCapped c t a, v ∈ scReachCapped c t b := by
  intro v hv
  have h := scReachCapped_mono_add (c := c) (t := t) a (b - a) v hv
  rw [Nat.add_sub_cancel' hab] at h
  exact h

/-- If a round adds nothing by count, it added nothing by membership. -/
theorem scReachCapped_stable_step {c : Nat} {t : SCTerm} {n : Nat}
    (h : (scReachCapped c t (n + 1)).length ≤ (scReachCapped c t n).length) :
    ∀ v ∈ scReachCapped c t (n + 1), v ∈ scReachCapped c t n := by
  intro v hv
  by_cases hin : v ∈ scReachCapped c t n
  · exact hin
  · exfalso
    have hnd : (v :: scReachCapped c t n).Nodup :=
      List.nodup_cons.mpr ⟨hin, scReachCapped_nodup c t n⟩
    have hsub : ∀ a, a ∈ v :: scReachCapped c t n → a ∈ scReachCapped c t (n + 1) := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | h'
      · exact hv
      · exact scReachCapped_mono a h'
    have hle := List.nodup_length_le _ _ hnd hsub
    have hlen : (v :: scReachCapped c t n).length = (scReachCapped c t n).length + 1 := rfl
    omega

/-- Stability propagates: once a round is stable, every later fuel stays inside it. -/
theorem scReachCapped_stable_forever {c : Nat} {t : SCTerm} {n : Nat}
    (h : ∀ v ∈ scReachCapped c t (n + 1), v ∈ scReachCapped c t n) :
    ∀ m v, v ∈ scReachCapped c t (n + m) → v ∈ scReachCapped c t n := by
  intro m
  induction m with
  | zero => intro v hv; exact hv
  | succ m ih =>
      intro v hv
      rcases scRoundCapped_mem.mp hv with h' | ⟨w, hw, hstep, hcap⟩
      · exact ih v h'
      · have hw' := ih w hw
        exact h v (scRoundCapped_mem.mpr (Or.inr ⟨w, hw', hstep, hcap⟩))

/-- A stable round exists within the pigeonhole budget. -/
theorem scReachCapped_exists_stable {c : Nat} {t : SCTerm} (ht : t.leafCount ≤ c) :
    ∃ k, k ≤ (scEnumLe c).length ∧
      ∀ v ∈ scReachCapped c t (k + 1), v ∈ scReachCapped c t k := by
  have hbound : ∀ n, (scReachCapped c t n).length ≤ (scEnumLe c).length := by
    intro n
    exact List.nodup_length_le _ _ (scReachCapped_nodup c t n)
      (fun a ha => scEnumLe_complete (scReachCapped_capped ht ha))
  have key : ∀ (b j : Nat), (scEnumLe c).length ≤ (scReachCapped c t j).length + b →
      ∃ k, j ≤ k ∧ k ≤ j + b ∧
        (scReachCapped c t (k + 1)).length ≤ (scReachCapped c t k).length := by
    intro b
    induction b with
    | zero =>
        intro j hj
        refine ⟨j, Nat.le_refl _, by omega, ?_⟩
        have := hbound (j + 1)
        omega
    | succ b ih =>
        intro j hj
        by_cases hstep : (scReachCapped c t (j + 1)).length ≤ (scReachCapped c t j).length
        · exact ⟨j, Nat.le_refl _, by omega, hstep⟩
        · obtain ⟨k, hk1, hk2, hk3⟩ := ih (j + 1) (by omega)
          exact ⟨k, by omega, by omega, hk3⟩
  obtain ⟨k, _, hk2, hk3⟩ := key (scEnumLe c).length 0 (by omega)
  exact ⟨k, by omega, scReachCapped_stable_step hk3⟩

/-- **Saturation**: fuel `|scEnumLe c|` sees everything any fuel ever sees. -/
theorem scReachCapped_saturates {c : Nat} {t : SCTerm} (ht : t.leafCount ≤ c) :
    ∀ n v, v ∈ scReachCapped c t n → v ∈ scReachCapped c t (scEnumLe c).length := by
  obtain ⟨k, hkle, hstable⟩ := scReachCapped_exists_stable ht
  intro n v hv
  by_cases hn : n ≤ k
  · exact scReachCapped_mono_le (Nat.le_trans hn hkle) v hv
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
    exact scReachCapped_mono_le hkle v (scReachCapped_stable_forever hstable m v hv)

/-- Capped reachability is decidable outright. -/
def scStepsLe_decidable (c : Nat) (t u : SCTerm) (ht : t.leafCount ≤ c) :
    Decidable (RS.StepsLe RS.SC SCTerm.leafCount c t u) :=
  decidable_of_iff (u ∈ scReachCapped c t (scEnumLe c).length) (by
    constructor
    · intro h
      exact scReachCapped_soundLe ht h
    · intro h
      obtain ⟨m, hm⟩ := scReachCapped_complete_start h
      exact scReachCapped_saturates ht m u hm)

/-- **THE BACKBONE**: a computable intermediate bound implies `{S,C}` reachability is
decidable. The frontier question — does such an `f` exist? — is now exactly the distance
between this theorem and undecidability. -/
def sc_decidable_of_bound (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    ∀ t u : SCTerm, Decidable (RS.SC.Steps t u) := fun t u =>
  have ht : t.leafCount ≤ max (f t.leafCount u.leafCount) t.leafCount :=
    Nat.le_max_right _ _
  decidable_of_iff
    (u ∈ scReachCapped (max (f t.leafCount u.leafCount) t.leafCount) t
      (scEnumLe (max (f t.leafCount u.leafCount) t.leafCount)).length) (by
    constructor
    · intro h
      exact RS.StepsLe.toSteps (scReachCapped_soundLe ht h)
    · intro h
      have h1 : RS.StepsLe RS.SC SCTerm.leafCount
          (max (f t.leafCount u.leafCount) t.leafCount) t u :=
        RS.StepsLe.weaken (Nat.le_max_left _ _) (hf t u h)
      obtain ⟨m, hm⟩ := scReachCapped_complete_start h1
      exact scReachCapped_saturates ht m u hm)

-- ## Stage 135: the glider — deterministic unbounded growth from eight leaves
-- Probing the convergence of the two threads (hosting ↔ decidability): forced-march depth —
-- the longest run of unique successors — EXPLODES with size (0, 1, 2, 4, 12, 60+ for sizes
-- 3–8), and the size-8 champion `S (S S S) S (C (S S))` marches deterministically without end
-- (1500 steps traced, no branch ever, linear growth ≈ +5 leaves per 3 steps). The mechanism
-- is a three-fire self-similar loop: with `p = S (C (S S))`, the core `p p p` fires
-- S-C-S back into `S p (p p p)` — itself under a wrapper. Formalized: the glider family and
-- UNBOUNDED GROWTH from a fixed eight-leaf term. The reachable set of an 8-leaf `{S,C}` term
-- can be infinite — the capped engine (Stage 133) is not an optimization but a necessity.

/-- The glider's pump: `S (C (S S))`. -/
def scP : SCTerm := .app .S (.app .C (.app .S .S))

/-- The self-reproducing core: `p p p`. -/
def scCore : SCTerm := .app (.app scP scP) scP

/-- The eight-leaf seed: `S (S S S) S (C (S S))`. -/
def scGliderSeed : SCTerm :=
  .app (.app (.app .S (.app (.app .S .S) .S)) .S) (.app .C (.app .S .S))

/-- The glider at time `k`: the core under `k` wrappers. -/
def scGlide : Nat → SCTerm
  | 0 => scCore
  | k + 1 => .app (.app .S scP) (scGlide k)

#guard scGliderSeed.leafCount = 8
#guard scP.leafCount = 4
#guard scCore.leafCount = 12

/-- The three-fire loop: the core reproduces itself under a wrapper. -/
theorem scCore_pump : RS.SC.Steps scCore (.app (.app .S scP) scCore) :=
  RS.Steps.tail (SCStep.S_red (.app .C (.app .S .S)) scP scP)
    (RS.Steps.tail (SCStep.C_red (.app .S .S) scP (.app scP scP))
      (RS.Steps.tail (SCStep.S_red .S (.app scP scP) scP)
        (RS.Steps.refl _)))

/-- The seed reaches the core in two fires. -/
theorem scGliderSeed_core : RS.SC.Steps scGliderSeed scCore :=
  RS.Steps.tail (SCStep.S_red (.app (.app .S .S) .S) .S (.app .C (.app .S .S)))
    (RS.Steps.tail (SCStep.appL (SCStep.S_red .S .S (.app .C (.app .S .S))))
      (RS.Steps.refl _))

theorem scGlide_step : ∀ k, RS.SC.Steps (scGlide k) (scGlide (k + 1))
  | 0 => scCore_pump
  | k + 1 => scSteps_appR (.app .S scP) (scGlide_step k)

theorem scGlide_reach : ∀ k, RS.SC.Steps scCore (scGlide k)
  | 0 => RS.Steps.refl _
  | k + 1 => RS.Steps.trans (scGlide_reach k) (scGlide_step k)

theorem scGlide_leafCount : ∀ k, (scGlide k).leafCount = 12 + 5 * k
  | 0 => rfl
  | k + 1 => by
      show (1 + scP.leafCount) + (scGlide k).leafCount = 12 + 5 * (k + 1)
      rw [scGlide_leafCount k]
      show (1 + 4) + (12 + 5 * k) = 12 + 5 * (k + 1)
      omega

/-- **The glider**: a fixed eight-leaf `{S,C}` term reaches terms of every size — its
reachable set is infinite, deterministically pumped, and never returns. Non-cyclic
divergence at eight leaves. -/
theorem sc_glider : ∀ n, ∃ u, RS.SC.Steps scGliderSeed u ∧ n ≤ u.leafCount := by
  intro n
  refine ⟨scGlide n, RS.Steps.trans scGliderSeed_core (scGlide_reach n), ?_⟩
  rw [scGlide_leafCount n]
  omega

-- ## Stage 136: glider determinism — the seed has no normal form
-- The 1500-step trace becomes a theorem. The glider's trajectory is exactly five shapes —
-- the seed, one intermediate, and the three phases under any number of wrappers — and each
-- has EXACTLY ONE successor (`scSucc` computes to a singleton, parametrically in the wrapper
-- count). So reduction from the seed is deterministic, the trajectory never ends, and the
-- seed has NO NORMAL FORM — the first machine-checked normal-form-free `{S,C}` term (cycles
-- alone never certify this: a cyclic term may still normalize down another path).

/-- `k` wrappers around a payload. -/
def scWrapN : Nat → SCTerm → SCTerm
  | 0, X => X
  | k + 1, X => .app (.app .S scP) (scWrapN k X)

/-- Phase two: `C (S S) p (p p)`. -/
def scC1 : SCTerm := .app (.app (.app .C (.app .S .S)) scP) (.app scP scP)

/-- Phase three: `S S (p p) p`. -/
def scC2 : SCTerm := .app (.app (.app .S .S) (.app scP scP)) scP

/-- The seed's first reduct: `S S S (C (S S)) (S (C (S S)))`. -/
def scT1 : SCTerm :=
  .app (.app (.app (.app .S .S) .S) (.app .C (.app .S .S))) (.app .S (.app .C (.app .S .S)))

#guard scSucc scGliderSeed = [scT1]
#guard scSucc scT1 = [scCore]
#guard scSucc scCore = [scC1]
#guard scSucc scC1 = [scC2]
#guard scSucc scC2 = [scWrapN 1 scCore]

/-- A wrapper is inert: successors of a wrapped term are the wrapped successors. -/
theorem scSucc_wrap (X : SCTerm) :
    scSucc (.app (.app .S scP) X) = (scSucc X).map (fun x' => .app (.app .S scP) x') := by
  show scSuccRoot (.app (.app .S scP) X)
      ++ ((scSucc (.app .S scP)).map (fun f' => .app f' X)
      ++ (scSucc X).map (fun x' => .app (.app .S scP) x')) = _
  rw [show scSuccRoot (.app (.app .S scP) X) = [] from rfl,
      show scSucc (.app .S scP) = [] from rfl]
  simp

/-- Singleton successors survive wrapping. -/
theorem scSucc_wrapN {X Y : SCTerm} (h : scSucc X = [Y]) :
    ∀ k, scSucc (scWrapN k X) = [scWrapN k Y]
  | 0 => h
  | k + 1 => by
      show scSucc (.app (.app .S scP) (scWrapN k X)) = _
      rw [scSucc_wrap, scSucc_wrapN h k]
      rfl

/-- The glider's complete trajectory. -/
def GliderTraj (u : SCTerm) : Prop :=
  u = scGliderSeed ∨ u = scT1
  ∨ ∃ k, u = scWrapN k scCore ∨ u = scWrapN k scC1 ∨ u = scWrapN k scC2

/-- Every trajectory member has exactly the successor list `[next]` for its known next. -/
theorem gliderTraj_succ {u : SCTerm} (h : GliderTraj u) :
    ∃ v, scSucc u = [v] ∧ GliderTraj v := by
  rcases h with rfl | rfl | ⟨k, rfl | rfl | rfl⟩
  · exact ⟨scT1, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨scCore, rfl, Or.inr (Or.inr ⟨0, Or.inl rfl⟩)⟩
  · exact ⟨scWrapN k scC1, scSucc_wrapN rfl k, Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)⟩
  · exact ⟨scWrapN k scC2, scSucc_wrapN rfl k, Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)⟩
  · refine ⟨scWrapN (k + 1) scCore, ?_, Or.inr (Or.inr ⟨k + 1, Or.inl rfl⟩)⟩
    have h1 : scSucc scC2 = [scWrapN 1 scCore] := rfl
    have h2 := scSucc_wrapN h1 k
    rw [h2]
    show [scWrapN k (.app (.app .S scP) scCore)] = _
    have : ∀ j, scWrapN j (.app (.app .S scP) scCore) = scWrapN (j + 1) scCore := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
          show SCTerm.app (.app .S scP) (scWrapN j (.app (.app .S scP) scCore))
            = SCTerm.app (.app .S scP) (scWrapN (j + 1) scCore)
          rw [ih]
    rw [this k]

/-- Reachability stays on the trajectory. -/
theorem gliderTraj_reach : ∀ {u : SCTerm}, RS.SC.Steps scGliderSeed u → GliderTraj u := by
  intro u h
  refine h.rec (motive := fun (a b : SCTerm) _ => GliderTraj a → GliderTraj b) ?_ ?_ (Or.inl rfl)
  · intro a ha
    exact ha
  · intro a b c s _ ih ha
    obtain ⟨v, hv, htv⟩ := gliderTraj_succ ha
    have hb := scSucc_complete s
    rw [hv] at hb
    have : b = v := by
      rcases List.mem_cons.mp hb with h' | h'
      · exact h'
      · exact absurd h' List.not_mem_nil
    exact ih (this ▸ htv)

/-- **Determinism**: every reduct of the glider seed has exactly one successor. -/
theorem scGlider_deterministic {u v w : SCTerm} (h : RS.SC.Steps scGliderSeed u)
    (h1 : SCStep u v) (h2 : SCStep u w) : v = w := by
  obtain ⟨n, hn, _⟩ := gliderTraj_succ (gliderTraj_reach h)
  have hv := scSucc_complete h1
  have hw := scSucc_complete h2
  rw [hn] at hv hw
  have ev : v = n := by
    rcases List.mem_cons.mp hv with h' | h'
    · exact h'
    · exact absurd h' List.not_mem_nil
  have ew : w = n := by
    rcases List.mem_cons.mp hw with h' | h'
    · exact h'
    · exact absurd h' List.not_mem_nil
  rw [ev, ew]

/-- **The glider seed has NO NORMAL FORM** — the march never ends, and determinism leaves no
side exit. First machine-checked normal-form-free term in `{S,C}`. -/
theorem scGlider_no_normal_form : ¬ RS.SC.Normalizes scGliderSeed := by
  rintro ⟨b, hsteps, hnf⟩
  obtain ⟨v, hv, _⟩ := gliderTraj_succ (gliderTraj_reach hsteps)
  exact hnf ⟨v, scSucc_sound (by rw [hv]; exact List.mem_cons_self)⟩

-- ## Stage 137: fixpoint detection — unreachability certificates by computation
-- The control probe found FUELED mountains (verified by exhaustive BFS with the unique-NF
-- sanity check that also caught a buggy first probe): machines `M` where `M (CC-tower k)`
-- strongly normalizes to a small fixed form while its reachable space peaks linearly in `k`
-- (star: `S (C (S C S)) S` — sizes 10..16, peaks 34..118, NFs 5..7). To make such facts
-- machine-checkable one at a time, the engine gains DETECTION: if one saturation round adds
-- nothing (a decidable check), the engine's cone is complete, and non-membership becomes a
-- full unreachability certificate. Demonstrated by re-certifying the minimal mountain through
-- the engine alone.

/-- Detected fixpoint: one stable round certifies the cone is complete. -/
theorem scReachCapped_detect {c : Nat} {t : SCTerm} {n : Nat}
    (h : ∀ v ∈ scReachCapped c t (n + 1), v ∈ scReachCapped c t n)
    {u : SCTerm} (hu : RS.StepsLe RS.SC SCTerm.leafCount c t u) :
    u ∈ scReachCapped c t n := by
  obtain ⟨m, hm⟩ := scReachCapped_complete_start hu
  by_cases hmn : m ≤ n
  · exact scReachCapped_mono_le hmn u hm
  · obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
    exact scReachCapped_stable_forever h j u hm

/-- The certificate: a stable round plus non-membership excludes every capped path. Both
hypotheses are decidable — `#guard`/`decide` can discharge them for concrete instances. -/
theorem scReachCapped_excludes {c : Nat} {t u : SCTerm} {n : Nat}
    (h : ∀ v ∈ scReachCapped c t (n + 1), v ∈ scReachCapped c t n)
    (hu : u ∉ scReachCapped c t n) :
    ¬ RS.StepsLe RS.SC SCTerm.leafCount c t u :=
  fun hle => hu (scReachCapped_detect h hle)

/-- The minimal mountain, re-certified through the engine alone: no path from `scMtT` to
`scMtU` stays within six leaves — by running the capped engine to its (immediately detected)
fixpoint and checking membership. -/
theorem scMt_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 6 scMtT scMtU :=
  scReachCapped_excludes (n := 0) (by decide) (by decide)

-- ## Stage 139: the converse — decidability implies a computable bound
-- The frontier becomes an EQUIVALENCE. Stage 134 proved bound ⟹ decidable; here the converse:
-- from a decision procedure, a bounding function is assembled — decide each same-size pair,
-- and for the reachable ones search upward for a cap that admits a bounded path (the search
-- terminates because every path is bounded by something, Stage 132's `exists_le`; the searcher
-- is a hand-rolled choice-free `find` — core has no `Nat.find`, and `Acc.rec` eliminates into
-- data without choice). So: `{S,C}` reachability is decidable IFF a computable intermediate
-- bound exists. The open frontier question is now a single well-posed sentence.

/-- The ascent relation for least-witness search. -/
private def scLbp (p : Nat → Prop) (m n : Nat) : Prop :=
  m = n + 1 ∧ ∀ k, k ≤ n → ¬ p k

private theorem scLbp_acc (p : Nat → Prop) (H : ∃ n, p n) : ∀ m, Acc (scLbp p) m := by
  obtain ⟨n, hn⟩ := H
  have key : ∀ j m, n ≤ m + j → Acc (scLbp p) m := by
    intro j
    induction j with
    | zero =>
        intro m hm
        refine Acc.intro m ?_
        intro y hy
        exact absurd hn (hy.2 n (by omega))
    | succ j ih =>
        intro m _
        refine Acc.intro m ?_
        intro y hy
        by_cases hnm : n ≤ m
        · exact absurd hn (hy.2 n hnm)
        · rw [hy.1]
          exact ih (m + 1) (by omega)
  intro m
  by_cases h : n ≤ m
  · exact key 0 m (by omega)
  · exact key (n - m) m (by omega)

/-- Choice-free witness search for decidable predicates: `Acc.rec` eliminates into data. -/
private def scFind (p : Nat → Prop) [DecidablePred p] (H : ∃ n, p n) : {n // p n} :=
  (WellFounded.fix (C := fun m => (∀ k, k < m → ¬ p k) → {n // p n})
    ⟨scLbp_acc p H⟩
    (fun m ih hbelow =>
      if h : p m then ⟨m, h⟩
      else
        have hall : ∀ k, k ≤ m → ¬ p k := by
          intro k hk
          by_cases h' : k < m
          · exact hbelow k h'
          · have hkm : k = m := by omega
            rw [hkm]
            exact h
        ih (m + 1) ⟨rfl, hall⟩ (fun k hk => hall k (by omega)))
    0) (fun k hk => absurd hk (Nat.not_lt_zero k))

instance scStepsLeDecPred (t u : SCTerm) :
    DecidablePred (fun c => RS.StepsLe RS.SC SCTerm.leafCount c t u) := fun c =>
  if h : t.leafCount ≤ c then scStepsLe_decidable c t u h
  else isFalse (fun hle => h (RS.StepsLe.head_le hle))

/-- Some cap admitting a bounded path, computed. -/
private def scAnyCap (t u : SCTerm)
    (H : ∃ c, RS.StepsLe RS.SC SCTerm.leafCount c t u) :
    {c // RS.StepsLe RS.SC SCTerm.leafCount c t u} :=
  scFind _ H

private theorem le_foldr_max : ∀ (l : List Nat) {x : Nat}, x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
      intro x hx
      show x ≤ max a (l.foldr max 0)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- The bounding function assembled from a decision procedure. -/
def scBoundFn (hdec : ∀ t u : SCTerm, Decidable (RS.SC.Steps t u)) (n m : Nat) : Nat :=
  ((scEnum n n).flatMap fun t => (scEnum m m).flatMap fun u =>
    match hdec t u with
    | isTrue h => [(scAnyCap t u (RS.Steps.exists_le _ h)).1]
    | isFalse _ => []).foldr max 0

/-- **The converse backbone**: decidability yields a computable intermediate bound. -/
theorem sc_bound_of_decidable (hdec : ∀ t u : SCTerm, Decidable (RS.SC.Steps t u)) :
    ∃ f : Nat → Nat → Nat, ∀ t u : SCTerm, RS.SC.Steps t u →
      RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u := by
  refine ⟨scBoundFn hdec, ?_⟩
  intro t u h
  refine RS.StepsLe.weaken ?_ (scAnyCap t u (RS.Steps.exists_le _ h)).2
  refine le_foldr_max _ ?_
  refine List.mem_flatMap.mpr ⟨t, scEnum_complete t t.leafCount (Nat.le_refl _), ?_⟩
  refine List.mem_flatMap.mpr ⟨u, scEnum_complete u u.leafCount (Nat.le_refl _), ?_⟩
  cases hdec t u with
  | isFalse h' => exact absurd h h'
  | isTrue h' => exact List.mem_cons_self

/-- **THE FRONTIER, WELL-POSED**: `{S,C}` reachability is decidable if and only if some
computable function of the endpoint sizes bounds the intermediates of witnessing paths. -/
theorem sc_decidable_iff_bound :
    Nonempty (∀ t u : SCTerm, Decidable (RS.SC.Steps t u))
    ↔ ∃ f : Nat → Nat → Nat, ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u := by
  constructor
  · rintro ⟨hdec⟩
    exact sc_bound_of_decidable hdec
  · rintro ⟨f, hf⟩
    exact ⟨sc_decidable_of_bound f hf⟩

-- ## Stage 140: the forced-march toolkit — mountains by chain, paths by list
-- A forced (unique-successor) prefix is shared by EVERY reduction path, so a mountain
-- certificate needs no state-space saturation: check the chain of `scSucc` singletons, check
-- the target is off the chain, and every capped path dies at the chain's peak. Dually, any
-- COMPUTED reduction becomes a `Steps` theorem by checking each step's membership in the
-- verified successor list. Both checks are decidable — mountains and reachability facts of
-- arbitrary concrete size are now one `decide` away, with cost linear in the path, not the
-- state space.

/-- A forced chain: from `t`, each listed term is THE unique successor of the last. -/
def SCForced : SCTerm → List SCTerm → Prop
  | _, [] => True
  | t, v :: rest => scSucc t = [v] ∧ SCForced v rest

/-- A checked chain: each listed term is A successor of the last (existence, not uniqueness). -/
def SCChained : SCTerm → List SCTerm → Prop
  | _, [] => True
  | t, v :: rest => v ∈ scSucc t ∧ SCChained v rest

instance instDecidableSCForced : ∀ (t : SCTerm) (l : List SCTerm), Decidable (SCForced t l)
  | _, [] => isTrue trivial
  | t, v :: rest =>
      have : Decidable (SCForced v rest) := instDecidableSCForced v rest
      inferInstanceAs (Decidable (scSucc t = [v] ∧ SCForced v rest))

instance instDecidableSCChained : ∀ (t : SCTerm) (l : List SCTerm), Decidable (SCChained t l)
  | _, [] => isTrue trivial
  | t, v :: rest =>
      have : Decidable (SCChained v rest) := instDecidableSCChained v rest
      inferInstanceAs (Decidable (v ∈ scSucc t ∧ SCChained v rest))

/-- A checked chain is a reduction: computed paths become `Steps` theorems. -/
theorem scChained_steps : ∀ (l : List SCTerm) (t u : SCTerm), SCChained t l →
    u ∈ t :: l → RS.SC.Steps t u := by
  intro l
  induction l with
  | nil =>
      intro t u _ hu
      have : u = t := by
        rcases List.mem_cons.mp hu with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      rw [this]
      exact @RS.Steps.refl RS.SC t
  | cons v rest ih =>
      intro t u hc hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact @RS.Steps.refl RS.SC u
      · exact RS.Steps.tail (scSucc_sound hc.1) (ih v u hc.2 hu')

/-- Generic inversion for bounded paths between distinct endpoints. -/
theorem RS.StepsLe.cases_ne {A : RS} {size : A.Carrier → Nat} {c : Nat} {a b : A.Carrier}
    (h : RS.StepsLe A size c a b) (hne : a ≠ b) :
    ∃ v, A.step a v ∧ RS.StepsLe A size c v b := by
  cases h with
  | refl _ _ => exact absurd rfl hne
  | tail s _ rest => exact ⟨_, s, rest⟩

/-- Every capped path to a point beyond a forced chain rides the whole chain: all chain
terms obey the cap. -/
theorem scForced_all_le {c : Nat} {u : SCTerm} : ∀ (l : List SCTerm) (t : SCTerm),
    SCForced t l → RS.StepsLe RS.SC SCTerm.leafCount c t u → u ∉ t :: l →
    ∀ x ∈ t :: l, x.leafCount ≤ c := by
  intro l
  induction l with
  | nil =>
      intro t hf h _ x hx
      have : x = t := by
        rcases List.mem_cons.mp hx with h' | h'
        · exact h'
        · exact absurd h' List.not_mem_nil
      rw [this]
      exact RS.StepsLe.head_le h
  | cons v rest ih =>
      intro t hf h hu x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact RS.StepsLe.head_le h
      · have hne : t ≠ u := fun he => hu (he ▸ List.mem_cons_self)
        obtain ⟨b, s, rest'⟩ := RS.StepsLe.cases_ne h hne
        have hb := scSucc_complete s
        rw [hf.1] at hb
        have hbv : b = v := by
          rcases List.mem_cons.mp hb with h' | h'
          · exact h'
          · exact absurd h' List.not_mem_nil
        rw [hbv] at rest'
        exact ih v hf.2 rest' (fun hmem => hu (List.mem_cons_of_mem t hmem)) x hx'

/-- **The mountain maker**: a forced chain with a peak above the cap excludes every capped
path to any point beyond the chain. All hypotheses decide. -/
theorem scForced_mountain {c : Nat} {t u : SCTerm} (l : List SCTerm)
    (hf : SCForced t l) (hpeak : ∃ x ∈ t :: l, c < x.leafCount) (hu : u ∉ t :: l) :
    ¬ RS.StepsLe RS.SC SCTerm.leafCount c t u := by
  intro h
  obtain ⟨x, hx, hcx⟩ := hpeak
  exact absurd (scForced_all_le l t hf h hu x hx) (by omega)

/-- The forced march, computed: follow unique successors for `n` steps (stop at any branch). -/
def scForcedMarch : SCTerm → Nat → List SCTerm
  | _, 0 => []
  | t, n + 1 =>
      match scSucc t with
      | [v] => v :: scForcedMarch v n
      | _ => []

/-- The computed march is always a forced chain — no per-instance check needed. -/
theorem scForcedMarch_forced : ∀ (n : Nat) (t : SCTerm), SCForced t (scForcedMarch t n) := by
  intro n
  induction n with
  | zero => intro t; exact trivial
  | succ n ih =>
      intro t
      unfold scForcedMarch
      rcases h : scSucc t with _ | ⟨v, rest⟩
      · exact trivial
      · rcases rest with _ | ⟨w, rest₂⟩
        · exact ⟨h, ih v⟩
        · exact trivial

/-- An eight-leaf term with a 49-step forced prefix peaking at 44 leaves. -/
def scMt2T : SCTerm := .app (.app (.app (.app .S .S) .C) (.app .S (.app (.app .C .S) .S))) .C

/-- A 32-leaf term reachable seven steps past the branch point — off the forced prefix. -/
def scMt2U : SCTerm :=
  .app (.app (.app (.app (.app (.app (.app (.app (.app .S .C) .S) (.app .C .C)) .C)
    (.app .C .C)) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C
    (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S
    (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C

/-- The full witnessing path: the forced march, then seven checked steps to the target. -/
def scMt2Path : List SCTerm :=
  scForcedMarch scMt2T 49 ++
  [.app (.app (.app (.app (.app .C (.app (.app (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)) .C) .C)) .C) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   .app (.app (.app (.app (.app (.app (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)) .C) .C) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   .app (.app (.app (.app (.app (.app (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C) .C) (.app .C .C)) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   .app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C) .C) .C) (.app .C .C)) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   .app (.app (.app (.app (.app (.app (.app (.app (.app .S (.app (.app .C .S) .S)) .C) .C) .C) (.app .C .C)) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   .app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C .S) .S) .C) (.app .C .C)) .C) (.app .C .C)) (.app .S (.app (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C))) .C))) .C) (.app .C (.app .S (.app (.app .C (.app (.app .C (.app .S (.app (.app .C .S) .S))) .C)) .C)))) .C,
   scMt2U]

#guard scMt2T.leafCount = 8
#guard scMt2U.leafCount = 32
#guard (scForcedMarch scMt2T 49).length = 49

/-- The crossing exists. -/
theorem scMt2_steps : RS.SC.Steps scMt2T scMt2U :=
  scChained_steps scMt2Path scMt2T scMt2U (by decide) (by decide)

/-- **The tall mountain**: no path from `scMt2T` (8 leaves) to `scMt2U` (32 leaves) stays
within 43 leaves — the forced prefix peaks at 44. Certified by the chain, not the state
space. -/
theorem scMt2_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 43 scMt2T scMt2U :=
  scForced_mountain (scForcedMarch scMt2T 49) (scForcedMarch_forced 49 scMt2T)
    (by decide) (by decide)

/-- **The floor theorems**: every valid bounding function clears the mountains. -/
theorem sc_bound_floor_6 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    7 ≤ f 6 6 := by
  by_cases h : 7 ≤ f 6 6
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 6 6) scMtT scMtU :=
      hf scMtT scMtU scMt_steps
    exact scMt_no_capped_path (RS.StepsLe.weaken (by omega) hs)

theorem sc_bound_floor_44 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    44 ≤ f 8 32 := by
  by_cases h : 44 ≤ f 8 32
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 8 32) scMt2T scMt2U :=
      hf scMt2T scMt2U scMt2_steps
    exact scMt2_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 141: the march hierarchy — the glider never stalls, and the floor thickens
-- Tying the toolkit to the glider: on the glider's trajectory the computed march never hits
-- a branch, so `scForcedMarch` yields chains of EVERY length — the forced-march "busy beaver"
-- at eight leaves is infinite. (Family search negative, recorded in the ledger: one-parameter
-- perturbations of the tall-mountain seed break forcing; unbounded-excess mountain FAMILIES
-- remain unfound.)

theorem scGliderTraj_march_length : ∀ (n : Nat) {t : SCTerm}, GliderTraj t →
    (scForcedMarch t n).length = n := by
  intro n
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
      intro t ht
      obtain ⟨v, hv, htv⟩ := gliderTraj_succ ht
      unfold scForcedMarch
      rw [hv]
      show (scForcedMarch v n).length + 1 = n + 1
      rw [ih htv]

/-- **The infinite march**: from the glider seed, the computed forced chain has every
length — deterministic computation without end, measured by the toolkit. -/
theorem scGlider_march_unbounded (n : Nat) :
    (scForcedMarch scGliderSeed n).length = n :=
  scGliderTraj_march_length n (Or.inl rfl)

-- ## Stage 142 (witness): the steep mountain — excess fifteen in thirteen forced steps
-- From the exhaustive n=9 census (13,721 forced-prefix mountains): the most compact steep
-- specimen. Nine leaves, thirteen forced steps to a 25-leaf peak, branching to a ten-leaf
-- target ten checked steps later.

/-- Nine leaves: `S S C (S (S C (C C))) C`. -/
def scMt3T : SCTerm := .app (.app (.app (.app .S .S) .C) (.app .S (.app (.app .S .C) (.app .C .C)))) .C

/-- Ten leaves, reached past the 25-leaf peak. -/
def scMt3U : SCTerm := .app (.app (.app .C (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C) .C

def scMt3Path : List SCTerm :=
  scForcedMarch scMt3T 13 ++
  [.app (.app (.app (.app (.app .C .C) (.app (.app .C .C) .C)) (.app (.app (.app .C .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C)) .C) (.app (.app .C .C) .C),
   .app (.app (.app (.app .C (.app (.app (.app .C .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C)) (.app (.app .C .C) .C)) .C) (.app (.app .C .C) .C),
   .app (.app (.app (.app (.app (.app .C .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C) .C) (.app (.app .C .C) .C)) (.app (.app .C .C) .C),
   .app (.app (.app (.app (.app .C .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C) (.app (.app .C .C) .C)) (.app (.app .C .C) .C),
   .app (.app (.app (.app .C .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) (.app (.app .C .C) .C)) (.app (.app .C .C) .C),
   .app (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) (.app (.app .C .C) .C),
   .app (.app (.app (.app .C .C) .C) (.app (.app .C .C) .C)) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C),
   .app (.app (.app .C (.app (.app .C .C) .C)) .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C),
   .app (.app (.app (.app .C .C) .C) (.app (.app .C (.app .S (.app (.app .S .C) (.app .C .C)))) .C)) .C,
   scMt3U]

#guard scMt3T.leafCount = 9
#guard scMt3U.leafCount = 10

theorem scMt3_steps : RS.SC.Steps scMt3T scMt3U :=
  scChained_steps scMt3Path scMt3T scMt3U (by decide) (by decide)

theorem scMt3_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 24 scMt3T scMt3U :=
  scForced_mountain (scForcedMarch scMt3T 13) (scForcedMarch_forced 13 scMt3T)
    (by decide) (by decide)

theorem sc_bound_floor_25 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    25 ≤ f 9 10 := by
  by_cases h : 25 ≤ f 9 10
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 9 10) scMt3T scMt3U :=
      hf scMt3T scMt3U scMt3_steps
    exact scMt3_no_capped_path (RS.StepsLe.weaken (by omega) hs)
