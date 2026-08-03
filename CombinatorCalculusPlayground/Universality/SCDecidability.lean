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

-- Stage 164 certificates: the register demo's outcomes are normal, distinct, and each
-- still contains its register (see RungTermination's Stage 164 block).
#guard scSucc (.app (.app .S (.app .C .C)) (.app (.app .S .C) .S)) = []
#guard scSucc (.app (.app .C (.app .S (.app .C .C))) (.app .C .C)) = []
#guard ((.app (.app .S (.app .C .C)) (.app (.app .S .C) .S) : SCTerm)
    ≠ (.app (.app .C (.app .S (.app .C .C))) (.app .C .C)))

-- ## Stage 165: the latch — stash, consult, diverge, survive
-- The Stage-163 read-gadget design, found executing in the wild. The machine
-- `scLatch bit = S (C C) (C scDup) (S S bit) scDup`: its FIRST fire stashes a copy of the
-- register `S S bit` inside `(C scDup) reg`; at fire ten the working copy FIRES — the
-- consultation, exposing the bit — and the two runs diverge into DIFFERENT perpetual
-- five-beat pulses, each still carrying the stashed register as a standing subterm (checked
-- below with a decidable subterm test; the register shape `S S bit` is disjoint from all
-- machinery by construction — the third contamination lesson). A set-once LATCH with a
-- reusable source bit: `{S,C}`'s first pinned control primitive.

/-- Decidable subterm test. -/
def scHasSub (t sub : SCTerm) : Bool :=
  t == sub ||
    match t with
    | .app f x => scHasSub f sub || scHasSub x sub
    | _ => false

/-- The latch over a bit. -/
def scLatch (bit : SCTerm) : SCTerm :=
  .app (.app (.app (.app .S (.app .C .C)) (.app .C scDup)) (.app (.app .S .S) bit)) scDup

/-- The mode-C pulse basepoint. -/
def scModeC : SCTerm :=
  .app (.app (.app (.app (.app .C scDup) scDup) scDup) scDup) (.app (.app .S .S) .C)

/-- The mode-B pulse basepoint. -/
def scModeB : SCTerm :=
  .app (.app (.app (.app (.app (.app .C .C) scDup) scDup) scDup) scDup)
    (.app (.app .S .S) (.app .C .C))

#guard scHasSub scModeC (.app (.app .S .S) .C)
#guard scHasSub scModeB (.app (.app .S .S) (.app .C .C))
#guard ¬ scHasSub scDup (.app (.app .S .S) .C)
#guard ¬ scHasSub scDup (.app (.app .S .S) (.app .C .C))

/-- Bit `C` latches into mode C: sixteen fires (the stash is fire one; the consultation —
the register copy firing — is fire ten). -/
theorem scLatch_run_C : RS.SC.Steps (scLatch .C) scModeC :=
  (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app (.app .S .S) .C) (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) .C))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) .C)) (.app (.app .S .S) .C) (.app (.app .S (.app .C .C)) (.app .C .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) .C) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) .C) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (@RS.Steps.refl RS.SC scModeC)))))))))))))))))

/-- Mode C pulses with period five, carrying the register. -/
theorem scModeC_pulse : RS.SC.StepsN 5 scModeC scModeC :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (@RS.StepsN.refl RS.SC scModeC))))))

/-- Bit `C C` latches into mode B: sixteen fires, the same stash-consult skeleton, a
different perpetual pulse. -/
theorem scLatch_run_B : RS.SC.Steps (scLatch (.app .C .C)) scModeB :=
  (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app (.app .S .S) (.app .C .C)) (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) (.app .C .C)))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .C (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S .S) (.app .C .C))) (.app (.app .S .S) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S .S) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))
  (@RS.Steps.refl RS.SC scModeB)))))))))))))))))

/-- Mode B pulses with period five too — but through DIFFERENT states. -/
theorem scModeB_pulse : RS.SC.StepsN 5 scModeB scModeB :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .C .C)))))
  (@RS.StepsN.refl RS.SC scModeB))))))

-- ## Stage 166: the consultation loop — twelve reads, register alive
-- The reset exists, and it was never a separate mechanism: the machine `S C C` over a
-- register and one `scDup` consults the register TWELVE TIMES in its first 51 fires (bit
-- `C`; forced throughout — the certificates below replay the march in the kernel), with the
-- register present at every point. The consultation event is detected structurally: a step
-- rewriting `reg X` to `(S X) (bit X)` — the register firing, exposing its bit. Read in a
-- loop: C8's reset requirement, observed and build-enforced. (Bit `C C` consults fourteen
-- times in 132 leftmost steps — branching mid-run, so it is recorded by probe rather than
-- kernel replay.)

/-- One step is a consultation of the `S S bit` register: somewhere, `reg X ⟶ (S X) (bit X)`. -/
def scIsConsult (bit : SCTerm) : SCTerm → SCTerm → Bool
  | a, b =>
    (match a, b with
     | .app r x, _ =>
         r == .app (.app .S .S) bit && b == .app (.app .S x) (.app bit x)
     | _, _ => false)
    ||
    (match a, b with
     | .app f x, .app f' x' =>
         (x == x' && scIsConsult bit f f') || (f == f' && scIsConsult bit x x')
     | _, _ => false)

/-- Count consultations along a trace. -/
def scCountConsults (bit : SCTerm) : List SCTerm → Nat
  | a :: b :: rest =>
      (if scIsConsult bit a b then 1 else 0) + scCountConsults bit (b :: rest)
  | _ => 0

/-- The consultation loop machine. -/
def scConsultLoop (bit : SCTerm) : SCTerm :=
  .app (.app (.app (.app .S .C) .C) (.app (.app .S .S) bit)) scDup

-- The bit-C run: 52 forced fires, twelve consultations, register alive at the end.
#guard (scForcedMarch (scConsultLoop .C) 52).length = 52
#guard scCountConsults .C (scConsultLoop .C :: scForcedMarch (scConsultLoop .C) 52) = 12
#guard scHasSub ((scForcedMarch (scConsultLoop .C) 52).getLastD (scConsultLoop .C))
    (.app (.app .S .S) .C)

/-- Forced chains are checked chains. -/
theorem scForced_chained : ∀ (l : List SCTerm) (t : SCTerm),
    SCForced t l → SCChained t l := by
  intro l
  induction l with
  | nil => intro t _; exact trivial
  | cons v rest ih =>
      intro t hf
      exact ⟨by rw [hf.1]; exact List.mem_cons_self, ih v hf.2⟩

-- ## Stage 171: two clocks, by design — the composition's foundation stone
-- The lockstep law (Stage 162) binds deterministic single-spine marches; the composition
-- escapes it by ARCHITECTURE: configurations held as members of a pair-holder reduce
-- independently (congruence), so two word-registers tick on independent clocks and
-- reachability — which quantifies over all schedules — sees every combination of their
-- states. Pinned generically and instantiated: one register decrements while the other
-- holds, and vice versa; the four primitives now have a chassis to compose on.

/-- **Two clocks**: member-held configurations reduce independently under a pair-holder. -/
theorem sc_two_clocks {c₁ c₁' c₂ c₂' : SCTerm}
    (h₁ : RS.SC.Steps c₁ c₁') (h₂ : RS.SC.Steps c₂ c₂') :
    RS.SC.Steps (.app (.app .S c₁) c₂) (.app (.app .S c₁') c₂') :=
  scSteps_congApp (scSteps_congApp (@RS.Steps.refl RS.SC .S) h₁) h₂

/-- Register one decrements (one pop) while register two holds — and the mirror image.
The lockstep law is broken by design: independent word-registers exist. -/
theorem sc_independent_registers (c : Bool) (w : List Bool) :
    RS.SC.Steps
      (.app (.app .S (.app (.app (scWord scDup (c :: w)) scDup) scDup))
        (.app (.app (scWord scDup (c :: w)) scDup) scDup))
      (.app (.app .S (.app (.app (scWord scDup w) scDup) scDup))
        (.app (.app (scWord scDup (c :: w)) scDup) scDup))
    ∧
    RS.SC.Steps
      (.app (.app .S (.app (.app (scWord scDup (c :: w)) scDup) scDup))
        (.app (.app (scWord scDup (c :: w)) scDup) scDup))
      (.app (.app .S (.app (.app (scWord scDup (c :: w)) scDup) scDup))
        (.app (.app (scWord scDup w) scDup) scDup)) :=
  ⟨sc_two_clocks (scRun_step scDup c w) (@RS.Steps.refl RS.SC _),
   sc_two_clocks (@RS.Steps.refl RS.SC _) (scRun_step scDup c w)⟩

-- ## Stage 172: the coupled zero-test — the driver reads a word's value class
-- The coupling's kernel. Registers are INERT WORDS (`scWord S w` is normal — stable data),
-- and the zero-test bit is the word's own head shape: the bare marker `S` (empty word,
-- ZERO) versus the one-cell word `C C S` (NONZERO). One template — `reg reg (C C) S` with
-- `reg = S C word` — reads the class: the ZERO run normalizes in eight fires, the NONZERO
-- in eleven (its last fire member-internal), to DISTINCT normal forms each still carrying
-- its intact register. The driver has consulted the register's VALUE CLASS without
-- consuming the register: dec/test/inc all exist on word-registers, the clocks are
-- independent (Stage 171), and this is the branch.

/-- The word-register under its `S C` guard. -/
def scWReg (w : SCTerm) : SCTerm := .app (.app .S .C) w

/-- ZERO: the empty-word register normalizes in eight fires. -/
theorem sc_ztest_zero :
    RS.SC.Steps (.app (.app (.app (scWReg .S) (scWReg .S)) (.app .C .C)) .S)
      (.app (.app .C (.app .S (.app .S (.app (.app .S .C) .S)))) (.app .S (.app (.app .S .C) .S))) :=
  RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .C .S (.app (.app .S .C) .S))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .C) .S) (.app .S (.app (.app .S .C) .S)) (.app .C .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .C .S (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .S (.app .C .C)) (.app .S (.app (.app .S .C) .S))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app .S (.app (.app .S .C) .S)) (.app .S (.app .C .C))))
  (RS.Steps.tail (SCStep.C_red (.app .S (.app .C .C)) (.app .S (.app (.app .S .C) .S)) .S)
  (RS.Steps.tail (SCStep.S_red (.app .C .C) .S (.app .S (.app (.app .S .C) .S)))
  (RS.Steps.tail (SCStep.C_red .C (.app .S (.app (.app .S .C) .S)) (.app .S (.app .S (.app (.app .S .C) .S))))
  (@RS.Steps.refl RS.SC _))))))))

/-- NONZERO: the one-cell-word register normalizes in eleven fires to a DIFFERENT form. -/
theorem sc_ztest_nonzero :
    RS.SC.Steps
      (.app (.app (.app (scWReg (.app (.app .C .C) .S)) (scWReg (.app (.app .C .C) .S))) (.app .C .C)) .S)
      (.app (.app .S (.app (.app .C (.app (.app .S .C) (.app (.app .C .C) .S))) .S)) .S) :=
  RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S)))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .C) (.app (.app .C .C) .S)) (.app (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S))) (.app .C .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) .S) (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S)))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S))) (.app (.app (.app .C .C) .S) (.app .C .C))))
  (RS.Steps.tail (SCStep.C_red (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S))) .S)
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C .S (.app .C .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app .C .C) .S .S))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C .S .S))
  (RS.Steps.tail (SCStep.C_red .S .S (.app (.app (.app .C .C) .S) (.app (.app .S .C) (.app (.app .C .C) .S))))
  (RS.Steps.tail (SCStep.appL (SCStep.appR (SCStep.C_red .C .S (.app (.app .S .C) (.app (.app .C .C) .S)))))
  (@RS.Steps.refl RS.SC _)))))))))))

-- Certificates: both outcomes normal, distinct, each carrying its intact register.
#guard scSucc (.app (.app .C (.app .S (.app .S (.app (.app .S .C) .S)))) (.app .S (.app (.app .S .C) .S))) = []
#guard scSucc (.app (.app .S (.app (.app .C (.app (.app .S .C) (.app (.app .C .C) .S))) .S)) .S) = []
#guard scHasSub (.app (.app .C (.app .S (.app .S (.app (.app .S .C) .S)))) (.app .S (.app (.app .S .C) .S)))
    (scWReg .S)
#guard scHasSub (.app (.app .S (.app (.app .C (.app (.app .S .C) (.app (.app .C .C) .S))) .S)) .S)
    (scWReg (.app (.app .C .C) .S))

-- ## Stage 173: test-and-decrement — the Minsky half-step, provenance-verified
-- From the NONZERO word-register `S C (C C (S S))` (word [b] over the distinctive marker
-- `S S`), the eight-leaf machine `S (C S) (C C) (S C)` reaches, in sixteen fires, a state
-- containing `S C (S S)` — the DECREMENTED, RE-GUARDED register. Marker provenance is the
-- certificate's core: the machinery contains no `S S` anywhere (search pool excluded it;
-- the #guards below re-verify), so the marker inside the decremented register can only have
-- traveled through the pop from the original word. Three machines survive the provenance
-- null (48 passed the naive test — the difference is the six probe lessons at work). The
-- last six fires are member-internal (appR contexts): the decrement completes inside a
-- member, where the write can reach it.

/-- Test-dec, pinned: sixteen fires from the nonzero register to a state carrying the
decremented, re-guarded register. -/
theorem sc_testdec :
    RS.SC.Steps
      (.app (.app (.app (.app .S (.app .C .S)) (.app .C .C)) (.app .S .C)) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))
      (.app (.app .C (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C))) (.app (.app (.app (.app .S .C) (.app .S .S)) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C))))) :=
  RS.Steps.tail (SCStep.appL (SCStep.S_red (.app .C .S) (.app .C .C) (.app .S .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .S (.app .S .C) (.app (.app .C .C) (.app .S .C))))
  (RS.Steps.tail (SCStep.S_red (.app (.app .C .C) (.app .S .C)) (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app .S .S)) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))) (.app (.app (.app .C .C) (.app .S .S)) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))) (.app .S .C))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red .C (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)))
  (RS.Steps.tail (SCStep.C_red (.app .S .C) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .S)) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))))
  (RS.Steps.tail (SCStep.S_red .C (.app (.app (.app .C .C) (.app .S .S)) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.C_red .C (.app .S .S) (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))))))
  (RS.Steps.tail (SCStep.appR (SCStep.C_red (.app (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))) (.app .S .S) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C))))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.S_red .C (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.C_red (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C))) (.app .S .S)))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app .S .S)) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C)) (.app .S .S))))
  (@RS.Steps.refl RS.SC _))))))))))))))))

-- Provenance certificates: the decremented register is present in the goal, and the
-- machinery is S S-free (the marker can only have come through the pop).
#guard scHasSub
    (.app (.app .C (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C))) (.app (.app (.app (.app .S .C) (.app .S .S)) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)))))
    (.app (.app .S .C) (.app .S .S))
#guard ¬ scHasSub (.app (.app (.app .S (.app .C .S)) (.app .C .C)) (.app .S .C)) (.app .S .S)

-- ## Stage 174: the decrement cycles — two pops, one machine
-- The half-step iterates. The same provenance-verified machine takes the TWO-cell register
-- through the intermediate to the doubly-decremented register: twenty-six fires, the first
-- sixteen delivering `reg 1` (mid, `#guard`ed), ten more delivering `reg 0` (goal,
-- `#guard`ed) — same `S S` dye, machinery still dye-free. The Minsky decrement CYCLES; the
-- assembly's remaining item is the zero-branch exit wired to Stage 172's test.

/-- Leg one: two-cell register to a state carrying the once-decremented register. -/
theorem sc_testdec_leg1 :
    RS.SC.Steps
      (.app (.app (.app (.app .S (.app .S .C)) (.app .C .C)) (.app .S .C)) (.app (.app .S .C) (.app (.app .C .C) (.app (.app .C .C) (.app .S .S)))))
      (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C))))) :=
    (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app .S .C) (.app .C .C) (.app .S .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red .C (.app .S .C) (.app (.app .C .C) (.app .S .C))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .C .C) (.app .S .C)) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C))) (.app (.app .S .C) (.app (.app .C .C) (.app (.app .C .C) (.app .S .S)))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red .C (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app (.app .C .C) (.app .S .S))))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .S .C) (.app (.app .C .C) (.app (.app .C .C) (.app .S .S)))) (.app .S .C) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app (.app .C .C) (.app .S .S))) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C)))))
  (RS.Steps.tail (SCStep.C_red (.app (.app .S .C) (.app (.app .C .C) (.app .S .C))) (.app (.app (.app .C .C) (.app (.app .C .C) (.app .S .S))) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C)))) (.app .S .C))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app .S .C)) (.app .S .C)))
  (RS.Steps.tail (SCStep.C_red (.app .S .C) (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C)) (.app (.app (.app .C .C) (.app (.app .C .C) (.app .S .S))) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C)))))
  (RS.Steps.tail (SCStep.S_red .C (.app (.app (.app .C .C) (.app (.app .C .C) (.app .S .S))) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C)))) (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C)))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app .S .S)) (.app (.app .S .C) (.app (.app .C .C) (.app .S .C))))))
  (RS.Steps.tail (SCStep.appR (SCStep.C_red (.app (.app .S .C) (.app (.app .C .C) (.app .S .C))) (.app (.app .C .C) (.app .S .S)) (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.appR (SCStep.C_red .C (.app .S .C) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.C_red (.app (.app .C (.app .S .C)) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C))) (.app (.app .C .C) (.app .S .S))))
  (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app .S .C) (.app .S .C) (.app (.app .C .C) (.app .S .S)))))
  (@RS.Steps.refl RS.SC _)))))))))))))))))

/-- Leg two: onward to a state carrying the doubly-decremented register. -/
theorem sc_testdec_leg2 :
    RS.SC.Steps
      (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C)))))
      (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app .C (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))) (.app (.app (.app .C (.app .S .C)) (.app (.app .C (.app .S .S)) (.app (.app .S .C) (.app .S .S)))) (.app .S .C)))) :=
    (RS.Steps.tail (SCStep.appR (SCStep.appL (SCStep.S_red .C (.app (.app .C .C) (.app .S .S)) (.app .S .C))))
  (RS.Steps.tail (SCStep.appR (SCStep.C_red (.app .S .C) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.S_red .C (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C))) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.C_red .C (.app .S .C) (.app (.app .C (.app .S .C)) (.app .S .C))))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.C_red (.app (.app .C (.app .S .C)) (.app .S .C)) (.app .S .C) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.C_red (.app .S .C) (.app .S .C) (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.S_red .C (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C)) (.app .S .C)))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.appR (SCStep.appL (SCStep.C_red .C (.app .S .S) (.app .S .C)))))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.appR (SCStep.C_red (.app .S .C) (.app .S .S) (.app .S .C))))))
  (RS.Steps.tail (SCStep.appR (SCStep.appR (SCStep.appL (SCStep.appR (SCStep.S_red .C (.app .S .C) (.app .S .S))))))
  (@RS.Steps.refl RS.SC _)))))))))))

/-- **The decrement cycles**: two pops through one machine. -/
theorem sc_testdec_twice :
    RS.SC.Steps
      (.app (.app (.app (.app .S (.app .S .C)) (.app .C .C)) (.app .S .C)) (.app (.app .S .C) (.app (.app .C .C) (.app (.app .C .C) (.app .S .S)))))
      (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app .C (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))) (.app (.app (.app .C (.app .S .C)) (.app (.app .C (.app .S .S)) (.app (.app .S .C) (.app .S .S)))) (.app .S .C)))) :=
  RS.Steps.trans sc_testdec_leg1 sc_testdec_leg2

#guard scHasSub (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app (.app (.app .S .C) (.app (.app .C .C) (.app .S .S))) (.app .S .C)) (.app (.app (.app .C .C) (.app .S .C)) (.app (.app .C (.app .S .C)) (.app .S .C))))) (.app (.app .S .C) (.app (.app .C .C) (.app .S .S)))
#guard scHasSub (.app (.app .C (.app (.app (.app .C .C) (.app .S .C)) (.app .S .C))) (.app (.app .C (.app (.app (.app .C .C) (.app .S .S)) (.app .S .C))) (.app (.app (.app .C (.app .S .C)) (.app (.app .C (.app .S .S)) (.app (.app .S .C) (.app .S .S)))) (.app .S .C)))) (.app (.app .S .C) (.app .S .S))

-- ## Stage 176: the persistent reader — a machine that outlives its own step
-- The persistence problem's first solution, for read-only state. The consultation loop's
-- march is a CONSULTING SPIRAL with exact period seven: the front
-- `Front = S P (C P) (C r)` (register `r = S S C`, `P = C (C r) (C r)`) reproduces itself
-- VERBATIM every seven fires while emitting one accounted junk block `J = C P (C r)` — and
-- two of the seven fires are the register CONSULTING (`S_red S C …`, the r-fire shape).
-- Since the junk rides as trailing members, the period lifts to the whole family by
-- congruence: the reader steps forever, reads twice per period, and its register — present
-- in every generation by construction — is never consumed. Persistence, interaction, and
-- nondestructive reading in one pinned machine.

/-- The reader's register. -/
def scRdrReg : SCTerm := .app (.app .S .S) .C

/-- `P = C (C r) (C r)`. -/
def scRdrP : SCTerm :=
  .app (.app .C (.app .C scRdrReg)) (.app .C scRdrReg)

/-- The junk block emitted each period. -/
def scRdrJ : SCTerm := .app (.app .C scRdrP) (.app .C scRdrReg)

/-- The reader's front: reproduces itself every seven fires. -/
def scRdrFront : SCTerm :=
  .app (.app (.app .S scRdrP) (.app .C scRdrP)) (.app .C scRdrReg)

/-- **The period**: seven fires, front restored verbatim, one junk block emitted — with the
register consulting twice en route (fires one and four are `r`-fires). -/
theorem scReader_period : RS.SC.Steps scRdrFront (.app scRdrFront scRdrJ) :=
  RS.Steps.tail (SCStep.S_red (.app (.app .C (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .C (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .S .S) .C)))) (.app .C (.app (.app .S .S) .C)))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app .C (.app (.app .S .S) .C)) (.app .C (.app (.app .S .S) .C)) (.app .C (.app (.app .S .S) .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) .C) (.app .C (.app (.app .S .S) .C)) (.app .C (.app (.app .S .S) .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app .C (.app (.app .S .S) .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.S_red (.app .C (.app (.app .S .S) .C)) (.app .C (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .S .S) .C))))
  (RS.Steps.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) .C) (.app .C (.app (.app .S .S) .C)) (.app (.app .C (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .S .S) .C)))))
  (RS.Steps.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app (.app .C (.app .C (.app (.app .S .S) .C))) (.app .C (.app (.app .S .S) .C))))))
  (@RS.Steps.refl RS.SC _)))))))

/-- The reader at generation `n`: the front trailing `n` accounted junk blocks. -/
def scReader : Nat → SCTerm
  | 0 => scRdrFront
  | n + 1 => .app (scReader n) scRdrJ

/-- Each generation steps to the next: the period, lifted by congruence over the junk. -/
theorem scReader_step : ∀ n, RS.SC.Steps (scReader n) (scReader (n + 1))
  | 0 => scReader_period
  | n + 1 => scSteps_appL scRdrJ (scReader_step n)

/-- **THE PERSISTENT READER**: the machine reaches every generation — it outlives its own
step, unboundedly, consulting its register twice per period. -/
theorem scReader_unbounded : ∀ n, RS.SC.Steps scRdrFront (scReader n)
  | 0 => @RS.Steps.refl RS.SC _
  | n + 1 => RS.Steps.trans (scReader_unbounded n) (scReader_step n)

-- The period is forced, contains exactly two consultations, and the register is present.
#guard (scForcedMarch scRdrFront 7).length = 7
#guard scCountConsults .C (scRdrFront :: scForcedMarch scRdrFront 7) = 2
#guard scHasSub scRdrFront scRdrReg
#guard scHasSub scRdrJ scRdrReg

-- ## Stage 178: the parametric pulse — persistence with arbitrary cargo
-- The latch's mode pulse never touches its last member: all five fires live in the body,
-- so the pulse persists with ANY cargo riding — pinned generically. Persistence is now
-- known parametric (this), interactive (the reader), and mode-selectable (the latch). The
-- write-obstruction's final form, from the reader's fire anatomy: `{S,C}` machines write
-- FORWARD-ONLY — products land behind the front and the front never reads backward; junk
-- re-enters the fire zone only when the front BURNS DOWN (the biodegradable lesson). A
-- writing reader is therefore a GROW/BURN ALTERNATOR: emit computed junk, burn to re-read
-- it — the boustrophedon, returning with a complete instrument set.

/-- The pulse body. -/
def scPulseBody : SCTerm :=
  .app (.app (.app (.app .C scDup) scDup) scDup) scDup

/-- **The parametric pulse**: five fires, any cargo, exact return. -/
theorem sc_pulse_parametric (X : SCTerm) :
    RS.SC.StepsN 5 (.app scPulseBody X) (.app scPulseBody X) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red scDup scDup scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup scDup))))
  (@RS.StepsN.refl RS.SC (.app scPulseBody X)))))))

-- ## Stage 180: the parking orbit — persistence without growth
-- C8's persistence problem asked for state that outlives the machine's step; the reader
-- (Stage 176) answered with unbounded growth. The orbit answers with NONE: `C A A A A`
-- (A = `scDup`, 21 leaves) sits on a period-5 limit cycle in which every term has EXACTLY
-- ONE successor — once on the orbit there is no way off, ever. The cycle turns entirely in
-- the head, so ANY cargo appended on the right rides it verbatim, forever, by congruence:
-- bounded eternal persistence of arbitrary state. And the orbit can be ENTERED by a read:
-- a 9-leaf head consults an `S S bit` register exactly once (kernel-counted) and parks it —
-- sixteen fires for either bit, landing at phase 0 for bit `C` and phase 4 for bit `C C`.
-- Equal wall-clock, different phase: THE BIT IS STORED IN THE PHASE of an eternal bounded
-- orbit. (Honest note: the two parked orbits are rotation-equal after abstracting the
-- register — the earlier probe's "bit-dependent cycles" compared signatures without
-- rotation. Probe lesson #8: cyclic signatures compare up to rotation.)

/-- Phase 0 of the orbit: `C A A A A` with `A = scDup`. -/
def scOrb : SCTerm := (.app (.app (.app (.app .C scDup) scDup) scDup) scDup)

/-- Phase 1: `A A A A` — the head `C` has routed, the spine is pure duplicator. -/
def scOrb1 : SCTerm := (.app (.app (.app scDup scDup) scDup) scDup)

/-- Phase 2: the duplicator has fired and split. -/
def scOrb2 : SCTerm := (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C .C) scDup)) scDup) scDup)

/-- Phase 3. -/
def scOrb3 : SCTerm := (.app (.app (.app (.app .C (.app (.app .C .C) scDup)) scDup) scDup) scDup)

/-- Phase 4: one fire from home. -/
def scOrb4 : SCTerm := (.app (.app (.app (.app (.app .C .C) scDup) scDup) scDup) scDup)

/-- **The orbit is inescapable**: each of its five terms has exactly one successor, and the
fifth returns to the first — a forced limit cycle, kernel-checked. -/
theorem scOrb_forced : SCForced scOrb [scOrb1, scOrb2, scOrb3, scOrb4, scOrb] := by decide

/-- Five fires, verbatim return. -/
theorem scOrb_cycle : RS.SC.StepsN 5 scOrb scOrb :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scDup scDup scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup scDup)))
  (@RS.StepsN.refl RS.SC scOrb))))))

/-- **The parking theorem**: ANY cargo rides the orbit — five fires return `scOrb · x`
verbatim, for every `x`. Persistence without growth: the state the composition campaign
fought to keep alive survives here at constant size. -/
theorem sc_park (x : SCTerm) : RS.SC.StepsN 5 (.app scOrb x) (.app scOrb x) :=
  scStepsN_appL x scOrb_cycle

/-- Eternal, by clockwork: every multiple of the period returns the parked state. -/
theorem sc_park_forever (x : SCTerm) :
    ∀ n, RS.SC.StepsN (5 * n) (.app scOrb x) (.app scOrb x)
  | 0 => @RS.StepsN.refl RS.SC (.app scOrb x)
  | n + 1 => by
      rw [Nat.mul_succ]
      exact RS.StepsN.trans (sc_park_forever x n) (sc_park x)

/-- The parking meter: a 9-leaf reader head over an `S S bit` register and a duplicator.
It consults the register once and parks it on the orbit. -/
def scParkSeed (bit : SCTerm) : SCTerm :=
  .app (.app (.app (.app .S (.app .C .C)) (.app .C scDup)) (.app (.app .S .S) bit)) scDup

/-- Bit `C` parks at PHASE 0 in sixteen fires. -/
theorem scPark_entry_C :
    RS.SC.StepsN 16 (scParkSeed .C) (.app scOrb (.app (.app .S .S) .C)) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C scDup) (.app (.app .S .S) .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .S .S) .C) (.app (.app .C scDup) (.app (.app .S .S) .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C scDup) (.app (.app .S .S) .C)) (.app (.app .S .S) .C) scDup)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scDup (.app (.app .S .S) .C) scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup (.app (.app .S .S) .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .S .S) .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) .C) scDup scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S .C scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red scDup (.app .C scDup) scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup (.app (.app .C scDup) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C scDup) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C scDup) scDup) scDup scDup))
  (@RS.StepsN.refl RS.SC (.app scOrb (.app (.app .S .S) .C)))))))))))))))))))

/-- Bit `C C` parks at PHASE 4 in the SAME sixteen fires: equal wall-clock, different
phase — the bit is stored in WHERE ON THE CYCLE the machine is. -/
theorem scPark_entry_CC :
    RS.SC.StepsN 16 (scParkSeed (.app .C .C))
      (.app scOrb4 (.app (.app .S .S) (.app .C .C))) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C scDup) (.app (.app .S .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .S .S) (.app .C .C)) (.app (.app .C scDup) (.app (.app .S .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C scDup) (.app (.app .S .S) (.app .C .C))) (.app (.app .S .S) (.app .C .C)) scDup)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scDup (.app (.app .S .S) (.app .C .C)) scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup (.app (.app .S .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .S .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .S .S) (.app .C .C)) scDup scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red scDup (.app (.app .C .C) scDup) scDup))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app .C .C) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) scDup) scDup (.app (.app (.app .C .C) scDup) scDup)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app (.app (.app .C .C) scDup) scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app (.app .C .C) scDup) scDup) scDup scDup))
  (@RS.StepsN.refl RS.SC (.app scOrb4 (.app (.app .S .S) (.app .C .C))))))))))))))))))))

/-- The two landing pads are distinct terms: the phase is observable. -/
theorem sc_phase_distinct : scOrb ≠ scOrb4 := by decide

/-- The bit-`C` entry trace, step by step (for the consultation count). -/
def scParkTraceC : List SCTerm := [(.app (.app (.app (.app .C .C) (.app (.app .S .S) .C)) (.app (.app .C scDup) (.app (.app .S .S) .C))) scDup),
  (.app (.app (.app .C (.app (.app .C scDup) (.app (.app .S .S) .C))) (.app (.app .S .S) .C)) scDup),
  (.app (.app (.app (.app .C scDup) (.app (.app .S .S) .C)) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app scDup scDup) (.app (.app .S .S) .C)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C .C) scDup)) (.app (.app .S .S) .C)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app .C (.app (.app .C .C) scDup)) scDup) (.app (.app .S .S) .C)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .S .S) .C)) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app .C (.app (.app .S .S) .C)) scDup) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .S .S) .C) scDup) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app .S scDup) (.app .C scDup)) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app scDup scDup) (.app (.app .C scDup) scDup)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C .C) scDup)) (.app (.app .C scDup) scDup)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app .C (.app (.app .C .C) scDup)) scDup) (.app (.app .C scDup) scDup)) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C scDup) scDup)) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app .C (.app (.app .C scDup) scDup)) scDup) scDup) (.app (.app .S .S) .C)),
  (.app (.app (.app (.app (.app .C scDup) scDup) scDup) scDup) (.app (.app .S .S) .C))]

/-- The bit-`C C` entry trace. -/
def scParkTraceCC : List SCTerm := [(.app (.app (.app (.app .C .C) (.app (.app .S .S) (.app .C .C))) (.app (.app .C scDup) (.app (.app .S .S) (.app .C .C)))) scDup),
  (.app (.app (.app .C (.app (.app .C scDup) (.app (.app .S .S) (.app .C .C)))) (.app (.app .S .S) (.app .C .C))) scDup),
  (.app (.app (.app (.app .C scDup) (.app (.app .S .S) (.app .C .C))) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app scDup scDup) (.app (.app .S .S) (.app .C .C))) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C .C) scDup)) (.app (.app .S .S) (.app .C .C))) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app .C (.app (.app .C .C) scDup)) scDup) (.app (.app .S .S) (.app .C .C))) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .S .S) (.app .C .C))) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app .C (.app (.app .S .S) (.app .C .C))) scDup) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app .S .S) (.app .C .C)) scDup) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app .S scDup) (.app (.app .C .C) scDup)) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app scDup scDup) (.app (.app (.app .C .C) scDup) scDup)) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app .C .C) scDup)) (.app (.app (.app .C .C) scDup) scDup)) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app .C (.app (.app .C .C) scDup)) scDup) (.app (.app (.app .C .C) scDup) scDup)) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app .C .C) scDup) (.app (.app (.app .C .C) scDup) scDup)) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app .C (.app (.app (.app .C .C) scDup) scDup)) scDup) scDup) (.app (.app .S .S) (.app .C .C))),
  (.app (.app (.app (.app (.app (.app .C .C) scDup) scDup) scDup) scDup) (.app (.app .S .S) (.app .C .C)))]

/-- The traces are genuine reduction paths. -/
theorem scParkTraceC_chained : SCChained (scParkSeed .C) scParkTraceC := by decide

theorem scParkTraceCC_chained :
    SCChained (scParkSeed (.app .C .C)) scParkTraceCC := by decide

-- Each entry path consults its register EXACTLY ONCE, and ends parked on the orbit.
#guard scCountConsults .C (scParkSeed .C :: scParkTraceC) = 1
#guard scCountConsults (.app .C .C) (scParkSeed (.app .C .C) :: scParkTraceCC) = 1
#guard scParkTraceC.getLastD (scParkSeed .C) == .app scOrb (.app (.app .S .S) .C)
#guard scParkTraceCC.getLastD (scParkSeed (.app .C .C))
    == .app scOrb4 (.app (.app .S .S) (.app .C .C))

-- ## Stage 181: the n=10 mountain — the census pays out
-- The exhaustive n=10 census (4,978,688 terms, forced-prefix marches to depth 300) found
-- its best excess at a 10-leaf term whose forced prefix climbs to 186 leaves at step 257
-- and descends to 143 by step 300, one checked step from a 142-leaf off-prefix target.
-- Every path from t to u must traverse the entire forced prefix — including the peak — so
-- every valid intermediate-bound function clears 186 at (10, 142): excess 44, TRIPLE the
-- n=8 mountain's 12 and equal to the n=8 floor's absolute height, from two more leaves.

/-- Ten leaves: the census's best climber. -/
def scMt4T : SCTerm := (.app (.app (.app .S (.app .S .S)) .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- 142 leaves, one checked step past the 300-step forced prefix — off the prefix. -/
def scMt4U : SCTerm := (.app (.app .S (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))))))))))))))))))) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))

/-- The witnessing path: the full forced march, then one checked step. -/
def scMt4Path : List SCTerm := scForcedMarch scMt4T 300 ++ [scMt4U]

section
set_option maxRecDepth 8000

#guard scMt4T.leafCount = 10
#guard scMt4U.leafCount = 142
#guard (scForcedMarch scMt4T 300).length = 300

/-- The crossing exists. -/
theorem scMt4_steps : RS.SC.Steps scMt4T scMt4U :=
  scChained_steps scMt4Path scMt4T scMt4U (by decide) (by decide)

/-- **The n=10 mountain**: no path from `scMt4T` (10 leaves) to `scMt4U` (142 leaves)
stays within 185 leaves — the forced prefix peaks at 186. -/
theorem scMt4_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 185 scMt4T scMt4U :=
  scForced_mountain (scForcedMarch scMt4T 300) (scForcedMarch_forced 300 scMt4T)
    (by decide) (by decide)

/-- **The n=10 floor**: every valid bounding function clears 186 at (10, 142). -/
theorem sc_bound_floor_186 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    186 ≤ f 10 142 := by
  by_cases h : 186 ≤ f 10 142
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 10 142) scMt4T scMt4U :=
      hf scMt4T scMt4U scMt4_steps
    exact scMt4_no_capped_path (RS.StepsLe.weaken (by omega) hs)

end

-- ## Stage 182: the fate machine — the bit decides eternity
-- The bounded reader exists, and it is more than a reader. `scFate bit` (12 leaves) holds
-- an `S S bit` register over a duplicator: with bit `C` it falls in seven fires onto a
-- period-7 cycle (sizes 15–20) that CONSULTS the register once per lap, forever — the
-- consumed register copy is re-minted by the duplicating fire, closing the regeneration
-- loop the parking orbit lacked. With bit `C C` the SAME machine reduces in 36 fires to a
-- normal form. One machine, one bit: runs of every length exist, or a halt exists — the
-- register content decides eternity. (Probe: the bit-`C C` reachable state space is FINITE
-- — 231 states, every schedule — with this NF its unique sink; the eternal/halting contrast
-- below is pinned along explicit paths, schedule-independence recorded here as probe data.)

/-- The fate machine: a 9-leaf head holding an `S S bit` register over `C C`. -/
def scFate (bit : SCTerm) : SCTerm :=
  .app (.app (.app .S (.app .S scDup)) (.app (.app .S .S) bit)) (.app .C .C)

/-- The eternal orbit's phase 0: three register copies abreast. -/
def scFateOrb : SCTerm := (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))

/-- Bit `C`: seven fires from seed to orbit. -/
theorem scFate_entry : RS.SC.StepsN 7 (scFate .C) scFateOrb :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .S .S) .C) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))
  (@RS.StepsN.refl RS.SC scFateOrb))))))))

theorem scFateStep0 : RS.SC.step scFateOrb
    (.app (.app (.app .C (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))
theorem scFateStep1 : RS.SC.step (.app (.app (.app .C (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    (.app (.app (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.C_red (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))
theorem scFateStep2 : RS.SC.step (.app (.app (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    (.app (.app (.app (.app .S (.app .C .C)) (.app .C (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app .C .C)))
theorem scFateStep3 : RS.SC.step (.app (.app (.app (.app .S (.app .C .C)) (.app .C (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.appL (SCStep.S_red (.app .C .C) (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))
theorem scFateStep4 : RS.SC.step (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))))
theorem scFateStep5 : RS.SC.step (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    (.app (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) :=
  SCStep.C_red (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))
theorem scFateStep6 : RS.SC.step (.app (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))
    scFateOrb :=
  SCStep.appL (SCStep.C_red (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))

/-- One lap: seven fires, verbatim return — with a consultation inside. -/
theorem scFate_cycle : RS.SC.StepsN 7 scFateOrb scFateOrb :=
  RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1 (RS.StepsN.tail scFateStep2
  (RS.StepsN.tail scFateStep3 (RS.StepsN.tail scFateStep4 (RS.StepsN.tail scFateStep5
  (RS.StepsN.tail scFateStep6 (@RS.StepsN.refl RS.SC scFateOrb)))))))

/-- Laps compose: every multiple of the period. -/
theorem scFate_forever :
    ∀ n, RS.SC.StepsN (7 * n) scFateOrb scFateOrb
  | 0 => @RS.StepsN.refl RS.SC scFateOrb
  | n + 1 => by
      rw [Nat.mul_succ]
      exact RS.StepsN.trans (scFate_forever n) scFate_cycle

/-- Partial laps: a run of every residue length. -/
theorem scFateOrb_partial : ∀ r, r < 7 → ∃ u, RS.SC.StepsN r scFateOrb u
  | 0, _ => ⟨_, @RS.StepsN.refl RS.SC scFateOrb⟩
  | 1, _ => ⟨_, RS.StepsN.tail scFateStep0 (@RS.StepsN.refl RS.SC _)⟩
  | 2, _ => ⟨_, RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1
      (@RS.StepsN.refl RS.SC _))⟩
  | 3, _ => ⟨_, RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1
      (RS.StepsN.tail scFateStep2 (@RS.StepsN.refl RS.SC _)))⟩
  | 4, _ => ⟨_, RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1
      (RS.StepsN.tail scFateStep2 (RS.StepsN.tail scFateStep3
      (@RS.StepsN.refl RS.SC _))))⟩
  | 5, _ => ⟨_, RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1
      (RS.StepsN.tail scFateStep2 (RS.StepsN.tail scFateStep3
      (RS.StepsN.tail scFateStep4 (@RS.StepsN.refl RS.SC _)))))⟩
  | 6, _ => ⟨_, RS.StepsN.tail scFateStep0 (RS.StepsN.tail scFateStep1
      (RS.StepsN.tail scFateStep2 (RS.StepsN.tail scFateStep3
      (RS.StepsN.tail scFateStep4 (RS.StepsN.tail scFateStep5
      (@RS.StepsN.refl RS.SC _))))))⟩
  | r + 7, h => absurd h (by omega)

/-- **Runs of every length**: bit `C` never has to stop. -/
theorem scFate_runs (n : Nat) : ∃ u, RS.SC.StepsN n scFateOrb u := by
  obtain ⟨u, hu⟩ := scFateOrb_partial (n % 7) (Nat.mod_lt n (by omega))
  refine ⟨u, ?_⟩
  rw [← Nat.div_add_mod n 7]
  exact RS.StepsN.trans (scFate_forever (n / 7)) hu

/-- The bit-`C C` normal form: fifteen leaves, no redex. -/
def scFateNf : SCTerm := (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))

#guard scSucc scFateNf = []

/-- `scFateNf` really is normal. -/
theorem scFateNf_normal : ∀ v, ¬ RS.SC.step scFateNf v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scFateNf = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Bit `C C`: thirty-six fires to the normal form. -/
theorem scFate_halts : RS.SC.StepsN 36 (scFate (.app .C .C)) scFateNf :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .S .S) (.app .C .C)) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C .C) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C .C) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .C) (.app (.app .C .C) (.app .C .C)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C .C) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.S_red .S (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appR (SCStep.S_red .S (.app .C .C) (.app .C .C)))
  (@RS.StepsN.refl RS.SC scFateNf)))))))))))))))))))))))))))))))))))))

/-- **The bit decides eternity**: with bit `C` the machine has runs of EVERY length; with
bit `C C` it reaches a normal form. One 12-leaf term, one register — spin or stop. -/
theorem sc_fate :
    (RS.SC.StepsN 7 (scFate .C) scFateOrb ∧ ∀ n, ∃ u, RS.SC.StepsN n scFateOrb u) ∧
    (∃ u, RS.SC.Steps (scFate (.app .C .C)) u ∧ ∀ v, ¬ RS.SC.step u v) :=
  ⟨⟨scFate_entry, scFate_runs⟩, ⟨scFateNf, RS.StepsN.toSteps scFate_halts, scFateNf_normal⟩⟩

/-- The lap's trace, for the kernel-counted consultation. -/
def scFateLap : List SCTerm := [(.app (.app (.app .C (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app (.app (.app .S .S) .C) (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app (.app .S (.app .C .C)) (.app .C (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C)))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))),
  (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C))) (.app (.app (.app .S .S) .C) (.app .C .C)))]

theorem scFateLap_chained : SCChained scFateOrb scFateLap := by decide

-- One consultation per lap, and the lap closes.
#guard scCountConsults .C (scFateOrb :: scFateLap) = 1
#guard scFateLap.getLastD scFateOrb == scFateOrb

-- ## Stage 183: universal fate — every schedule halts, and 36 is the wall
-- Stage 182 pinned that a halt EXISTS for the bit-`C C` fate machine; this stage pins that
-- nothing else can happen. The certificate is a RANKED CLOSURE: the full reachable state
-- space (231 terms, none above 29 leaves), grouped by height so that every successor of
-- every member sits in a strictly lower group — all kernel-checked. The generic lemma
-- `scRanked_bound` (new toolkit piece, reusable) turns any such certificate into a uniform
-- bound: no reduction from the seed outlives its rank. Here the seed's rank is 36 — and the
-- leftmost path REACHES 36 (`scFate_halts`), so the wall is sharp. Together with the
-- unique-exit theorem (every stuck reachable term IS `scFateNf`, by decide over the space),
-- the fate machine's halt half is now UNIVERSAL: every maximal reduction, under every
-- schedule, ends at `scFateNf` within exactly the leftmost budget. The program's first
-- pinned termination-of-all-paths for a specific term of a non-normalizing calculus.

/-- Rank of a term in a grouped space: index of the first group containing it. -/
def scRankIn (G : List (List SCTerm)) (x : SCTerm) : Nat :=
  G.findIdx (·.contains x)

/-- **The ranked-closure lemma**: if a list is closed under successors and every step
strictly descends a rank, no reduction from a member outlives its rank. -/
theorem scRanked_bound {L : List SCTerm} {rank : SCTerm → Nat}
    (hcl : ∀ x ∈ L, ∀ y ∈ scSucc x, y ∈ L ∧ rank y < rank x)
    {n : Nat} {t u : SCTerm} (h : RS.SC.StepsN n t u) :
    t ∈ L → u ∈ L ∧ n + rank u ≤ rank t := by
  refine h.rec (motive := fun (n : Nat) (a b : SCTerm) _ =>
      a ∈ L → b ∈ L ∧ n + rank b ≤ rank a) ?_ ?_
  · intro a ha
    exact ⟨ha, by omega⟩
  · intro m a b c s rest ih ha
    have hb := hcl _ ha _ (scSucc_complete s)
    have hu := ih hb.1
    exact ⟨hu.1, by have h1 := hb.2; have h2 := hu.2; omega⟩

/-- The bit-`C C` fate machine's complete state space, grouped by height (successors
always in strictly lower groups). 231 states, heights 0–36. -/
def scFateSpace : List (List SCTerm) :=
  [[(.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app scDup (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .S scDup) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app scDup (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app scDup (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app scDup (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app (.app .S scDup) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .S (.app .S scDup)) (.app (.app .S .S) (.app .C .C))) (.app .C .C))]]


/-- Flattened for membership. -/
def scFateStates : List SCTerm := scFateSpace.flatten

section
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

#guard scFateStates.length = 231
#guard scRankIn scFateSpace (scFate (.app .C .C)) = 36
#guard scRankIn scFateSpace scFateNf = 0

/-- The certificate: closed under successors, rank strictly descends. -/
theorem scFateSpace_ranked : ∀ x ∈ scFateStates, ∀ y ∈ scSucc x,
    y ∈ scFateStates ∧ scRankIn scFateSpace y < scRankIn scFateSpace x := by decide

theorem scFateSpace_seed : scFate (.app .C .C) ∈ scFateStates := by decide

/-- Within the space, the only stuck term is the normal form. -/
theorem scFateSpace_nf : ∀ x ∈ scFateStates, scSucc x = [] → x = scFateNf := by decide

end

/-- **The wall**: NO reduction from the bit-`C C` fate machine exceeds 36 steps — every
schedule. And `scFate_halts` reaches 36, so the wall is sharp. -/
theorem sc_fate_all_bounded : ∀ (n : Nat) (u : SCTerm),
    RS.SC.StepsN n (scFate (.app .C .C)) u → n ≤ 36 := by
  intro n u h
  have hb := (scRanked_bound scFateSpace_ranked h scFateSpace_seed).2
  have hk : scRankIn scFateSpace (scFate (.app .C .C)) = 36 := rfl
  omega

/-- **Unique exit**: every stuck term reachable from the bit-`C C` seed IS `scFateNf`. -/
theorem sc_fate_unique_exit : ∀ u, RS.SC.Steps (scFate (.app .C .C)) u →
    (∀ v, ¬ RS.SC.step u v) → u = scFateNf := by
  intro u hs hnf
  obtain ⟨n, hn⟩ := RS.Steps.toStepsN hs
  have hu := (scRanked_bound scFateSpace_ranked hn scFateSpace_seed).1
  have hempty : scSucc u = [] := by
    cases hsu : scSucc u with
    | nil => rfl
    | cons a l => exact absurd (scSucc_sound (hsu ▸ List.mem_cons_self)) (hnf a)
  exact scFateSpace_nf u hu hempty

/-- **Universal fate**: with bit `C C`, every reduction is bounded by 36 and every dead
end is the normal form — the machine halts at `scFateNf` under every schedule. With bit
`C` (Stage 182) runs of every length exist. The register decides, universally. -/
theorem sc_fate_universal :
    (∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n (scFate (.app .C .C)) u → n ≤ 36) ∧
    (∀ u, RS.SC.Steps (scFate (.app .C .C)) u → (∀ v, ¬ RS.SC.step u v) → u = scFateNf) :=
  ⟨sc_fate_all_bounded, sc_fate_unique_exit⟩
