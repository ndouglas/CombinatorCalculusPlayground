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

-- ## Stage 184: the four fates — the fate bit becomes a component
-- Two fate machines under the pair chassis `S c₁ c₂` (the two-clocks holder, Stage 171).
-- The chassis is INERT: `S` with two arguments is no redex, so every step of the pair
-- happens in exactly one member (`scPair_inv`), every pair reduction decomposes into two
-- member reductions (`scPair_decompose`), walls ADD (`scPair_bounded`), and normal members
-- make a normal pair (`scPair_normal`). Instantiated at the fate machine: (C,·) — one
-- spinning member keeps the pair running forever, whatever sits beside it; (CC,CC) — the
-- pair dies at `S scFateNf scFateNf` behind a sharp wall of 72 = 36 + 36, and every stuck
-- reachable term IS that double normal form. Two registers, four futures, all pinned from
-- ONE machine's certificates — the fate bit composes.

/-- `StepsN` under the right argument (mirror of `scStepsN_appL`). -/
theorem scStepsN_appR (f : SCTerm) {x x' : SCTerm} {n : Nat} (h : RS.SC.StepsN n x x') :
    RS.SC.StepsN n (SCTerm.app f x) (SCTerm.app f x') := by
  refine h.rec (motive := fun n a b _ => RS.SC.StepsN n (SCTerm.app f a) (SCTerm.app f b))
    ?_ ?_
  · intro a
    exact @RS.StepsN.refl RS.SC (SCTerm.app f a)
  · intro m a b c s rest ih
    exact RS.StepsN.tail (SCStep.appR s) ih

/-- **Pair inversion**: a step of `S c₁ c₂` is a step of `c₁` or a step of `c₂`. -/
theorem scPair_inv {c₁ c₂ v : SCTerm}
    (h : RS.SC.step (SCTerm.app (SCTerm.app .S c₁) c₂) v) :
    (∃ c₁', RS.SC.step c₁ c₁' ∧ v = .app (.app .S c₁') c₂) ∨
    (∃ c₂', RS.SC.step c₂ c₂' ∧ v = .app (.app .S c₁) c₂') := by
  cases h with
  | appL h' =>
      cases h' with
      | appL h'' => cases h''
      | appR h'' => exact .inl ⟨_, h'', rfl⟩
  | appR h' => exact .inr ⟨_, h', rfl⟩

/-- **Pair decomposition**: every reduction of the pair splits into member reductions. -/
theorem scPair_decompose {n : Nat} {a u : SCTerm} (h : RS.SC.StepsN n a u) :
    ∀ c₁ c₂ : SCTerm, a = SCTerm.app (SCTerm.app .S c₁) c₂ →
      ∃ u₁ u₂ n₁ n₂, u = SCTerm.app (SCTerm.app .S u₁) u₂ ∧ n = n₁ + n₂ ∧
        RS.SC.StepsN n₁ c₁ u₁ ∧ RS.SC.StepsN n₂ c₂ u₂ := by
  refine h.rec (motive := fun n a u _ => ∀ c₁ c₂ : SCTerm,
      a = SCTerm.app (SCTerm.app .S c₁) c₂ →
      ∃ u₁ u₂ n₁ n₂, u = SCTerm.app (SCTerm.app .S u₁) u₂ ∧ n = n₁ + n₂ ∧
        RS.SC.StepsN n₁ c₁ u₁ ∧ RS.SC.StepsN n₂ c₂ u₂) ?_ ?_
  · intro a c₁ c₂ ha
    exact ⟨c₁, c₂, 0, 0, ha, rfl, @RS.StepsN.refl RS.SC c₁, @RS.StepsN.refl RS.SC c₂⟩
  · intro m a b c s rest ih c₁ c₂ ha
    subst ha
    rcases scPair_inv s with ⟨c₁', hs, rfl⟩ | ⟨c₂', hs, rfl⟩
    · obtain ⟨u₁, u₂, n₁, n₂, hu, hn, h1, h2⟩ := ih c₁' c₂ rfl
      exact ⟨u₁, u₂, n₁ + 1, n₂, hu, by omega, RS.StepsN.tail hs h1, h2⟩
    · obtain ⟨u₁, u₂, n₁, n₂, hu, hn, h1, h2⟩ := ih c₁ c₂' rfl
      exact ⟨u₁, u₂, n₁, n₂ + 1, hu, by omega, h1, RS.StepsN.tail hs h2⟩

/-- **Walls add**: member bounds compose to a pair bound. -/
theorem scPair_bounded {c₁ c₂ : SCTerm} {k₁ k₂ : Nat}
    (h₁ : ∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n c₁ u → n ≤ k₁)
    (h₂ : ∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n c₂ u → n ≤ k₂) :
    ∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n (SCTerm.app (SCTerm.app .S c₁) c₂) u → n ≤ k₁ + k₂ := by
  intro n u h
  obtain ⟨u₁, u₂, n₁, n₂, _, hn, hh1, hh2⟩ := scPair_decompose h c₁ c₂ rfl
  have hb1 := h₁ n₁ u₁ hh1
  have hb2 := h₂ n₂ u₂ hh2
  omega

/-- Normal members make a normal pair. -/
theorem scPair_normal {m₁ m₂ : SCTerm} (h₁ : ∀ v, ¬ RS.SC.step m₁ v)
    (h₂ : ∀ v, ¬ RS.SC.step m₂ v) : ∀ v, ¬ RS.SC.step (SCTerm.app (SCTerm.app .S m₁) m₂) v := by
  intro v h
  rcases scPair_inv h with ⟨c', hs, _⟩ | ⟨c', hs, _⟩
  · exact h₁ c' hs
  · exact h₂ c' hs

/-- One spinning member keeps the pair running forever, whatever sits beside it. -/
theorem sc_pair_spin (x : SCTerm) :
    ∀ n, ∃ u, RS.SC.StepsN n (SCTerm.app (SCTerm.app .S scFateOrb) x) u := by
  intro n
  obtain ⟨u, hu⟩ := scFate_runs n
  exact ⟨SCTerm.app (SCTerm.app .S u) x, scStepsN_appL x (scStepsN_appR .S hu)⟩

/-- **The four fates.** Quadrants of `S (scFate a) (scFate b)`:
(C,·): seven member fires reach the orbit and the pair has runs of EVERY length;
(CC,CC): the pair reaches `S scFateNf scFateNf` — a normal form — no schedule exceeds
72 = 36 + 36 fires, and every stuck reachable term is that double normal form. -/
theorem sc_four_fates :
    (∀ b : SCTerm, RS.SC.StepsN 7 (SCTerm.app (SCTerm.app .S (scFate .C)) (scFate b))
        (SCTerm.app (SCTerm.app .S scFateOrb) (scFate b)) ∧
      ∀ n, ∃ u, RS.SC.StepsN n (SCTerm.app (SCTerm.app .S scFateOrb) (scFate b)) u) ∧
    (RS.SC.Steps (SCTerm.app (SCTerm.app .S (scFate (.app .C .C))) (scFate (.app .C .C)))
        (SCTerm.app (SCTerm.app .S scFateNf) scFateNf) ∧
      (∀ v, ¬ RS.SC.step (SCTerm.app (SCTerm.app .S scFateNf) scFateNf) v) ∧
      (∀ (n : Nat) (u : SCTerm),
        RS.SC.StepsN n (SCTerm.app (SCTerm.app .S (scFate (.app .C .C))) (scFate (.app .C .C))) u →
          n ≤ 72) ∧
      (∀ u, RS.SC.Steps (SCTerm.app (SCTerm.app .S (scFate (.app .C .C))) (scFate (.app .C .C))) u →
        (∀ v, ¬ RS.SC.step u v) → u = SCTerm.app (SCTerm.app .S scFateNf) scFateNf)) := by
  refine ⟨fun b => ⟨scStepsN_appL _ (scStepsN_appR .S scFate_entry), sc_pair_spin _⟩,
    ?_, scPair_normal scFateNf_normal scFateNf_normal,
    scPair_bounded sc_fate_all_bounded sc_fate_all_bounded, ?_⟩
  · exact RS.Steps.trans
      (RS.StepsN.toSteps (scStepsN_appL _ (scStepsN_appR .S scFate_halts)))
      (RS.StepsN.toSteps (scStepsN_appR _ scFate_halts))
  · intro u hs hstuck
    obtain ⟨n, hn⟩ := RS.Steps.toStepsN hs
    obtain ⟨u₁, u₂, n₁, n₂, rfl, _, h1, h2⟩ := scPair_decompose hn _ _ rfl
    have hs₁ : ∀ v, ¬ RS.SC.step u₁ v := fun v hv =>
      hstuck _ (SCStep.appL (SCStep.appR hv))
    have hs₂ : ∀ v, ¬ RS.SC.step u₂ v := fun v hv => hstuck _ (SCStep.appR hv)
    rw [sc_fate_unique_exit u₁ (RS.StepsN.toSteps h1) hs₁,
        sc_fate_unique_exit u₂ (RS.StepsN.toSteps h2) hs₂]

-- ## Stage 185: bits are sources — and the relay that houses a fate
-- Conditional eternity asked for a machine whose OUTPUT becomes a fate register. The
-- obstruction is structural and pinned here: every `{S,C}` fire produces a double
-- application, so no reduction ever ends at an atom or at `C C` — THE BITS ARE SOURCES of
-- the reduction order. A fate register's content can never be a computed result; in
-- `{S,C}`, fate is decided by initial conditions. What CAN be computed is housing: the
-- assembler `S S C M` fires once into the pair `S M (C M)` — machine and shadow — and the
-- four-fates calculus applies compositionally. With `M = scFate C` the housed pair is
-- immortal; with `M = scFate (C C)` every schedule dies at `S scFateNf (C scFateNf)`
-- behind a wall of 73 — pinned WITHOUT touching the 53,592-state product space (the probe
-- counted it; the lemmas never see it).

/-- No step produces the atom `C`. -/
theorem scStep_no_atom_C : ∀ t : SCTerm, ¬ RS.SC.step t .C := by
  intro t h
  cases h

/-- No step produces the atom `S`. -/
theorem scStep_no_atom_S : ∀ t : SCTerm, ¬ RS.SC.step t .S := by
  intro t h
  cases h

/-- No step produces the bit `C C`. -/
theorem scStep_no_bit : ∀ t : SCTerm, ¬ RS.SC.step t (.app .C .C) := by
  intro t h
  cases h with
  | appL h' => exact scStep_no_atom_C _ h'
  | appR h' => exact scStep_no_atom_C _ h'

/-- **Bits are sources**: the only term that ever reduces to `C C` is `C C` itself.
The fate register's content is forever an input, never an output. -/
theorem sc_bits_are_sources {t : SCTerm} (h : RS.SC.Steps t (.app .C .C)) :
    t = .app .C .C := by
  suffices h' : ∀ a b : SCTerm, RS.SC.Steps a b →
      b = SCTerm.app .C .C → a = SCTerm.app .C .C from h' _ _ h rfl
  intro a b hab
  refine hab.rec (motive := fun (a b : SCTerm) _ =>
      b = SCTerm.app .C .C → a = SCTerm.app .C .C) ?_ ?_
  · intro a hb
    exact hb
  · intro a b c s rest ih hb
    have hbcc := ih hb
    subst hbcc
    exact absurd s (scStep_no_bit a)

/-- The relay: one `S S` assembler over a payload. -/
def scRelay (M : SCTerm) : SCTerm := .app (.app (.app .S .S) .C) M

/-- The housed pair: machine and shadow. -/
def scHoused (M : SCTerm) : SCTerm := .app (.app .S M) (.app .C M)

/-- The assembly fire. -/
theorem scRelay_fire (M : SCTerm) : RS.SC.step (scRelay M) (scHoused M) :=
  SCStep.S_red .S .C M

/-- **Relay inversion**: a step of `S S C M` is the assembly fire or a payload step. -/
theorem scRelay_inv {M v : SCTerm} (h : RS.SC.step (scRelay M) v) :
    v = scHoused M ∨ (∃ M', RS.SC.step M M' ∧ v = scRelay M') := by
  cases h with
  | S_red f g x => exact .inl rfl
  | appL h' =>
      cases h' with
      | appL h'' => cases h'' with
        | appL h₃ => exact absurd h₃ (fun h => by cases h)
        | appR h₃ => exact absurd h₃ (fun h => by cases h)
      | appR h'' => exact absurd h'' (fun h => by cases h)
  | appR h' => exact .inr ⟨_, h', rfl⟩

/-- **Shadow inversion**: a step of `C m` is a step of `m`. -/
theorem scWrap_inv {m v : SCTerm} (h : RS.SC.step (SCTerm.app .C m) v) :
    ∃ m', RS.SC.step m m' ∧ v = .app .C m' := by
  cases h with
  | appL h' => cases h'
  | appR h' => exact ⟨_, h', rfl⟩

/-- Shadow reductions are payload reductions. -/
theorem scWrap_decompose {n : Nat} {a u : SCTerm} (h : RS.SC.StepsN n a u) :
    ∀ m : SCTerm, a = SCTerm.app .C m →
      ∃ m', u = SCTerm.app .C m' ∧ RS.SC.StepsN n m m' := by
  refine h.rec (motive := fun n a u _ => ∀ m : SCTerm, a = SCTerm.app .C m →
      ∃ m', u = SCTerm.app .C m' ∧ RS.SC.StepsN n m m') ?_ ?_
  · intro a m ha
    exact ⟨m, ha, @RS.StepsN.refl RS.SC m⟩
  · intro k a b c s rest ih m ha
    subst ha
    obtain ⟨m₁, hs, rfl⟩ := scWrap_inv s
    obtain ⟨m', hu, hm⟩ := ih m₁ rfl
    exact ⟨m', hu, RS.StepsN.tail hs hm⟩

/-- Relay reductions: all payload, or payload then assembly then housed-pair. -/
theorem scRelay_decompose {n : Nat} {a u : SCTerm} (h : RS.SC.StepsN n a u) :
    ∀ M : SCTerm, a = scRelay M →
      (∃ M', u = scRelay M' ∧ RS.SC.StepsN n M M') ∨
      (∃ k m M', n = k + 1 + m ∧ RS.SC.StepsN k M M' ∧
        RS.SC.StepsN m (scHoused M') u) := by
  refine h.rec (motive := fun n a u _ => ∀ M : SCTerm, a = scRelay M →
      (∃ M', u = scRelay M' ∧ RS.SC.StepsN n M M') ∨
      (∃ k m M', n = k + 1 + m ∧ RS.SC.StepsN k M M' ∧
        RS.SC.StepsN m (scHoused M') u)) ?_ ?_
  · intro a M ha
    exact .inl ⟨M, ha, @RS.StepsN.refl RS.SC M⟩
  · intro k a b c s rest ih M ha
    subst ha
    rcases scRelay_inv s with rfl | ⟨M₁, hs, rfl⟩
    · exact .inr ⟨0, k, M, by omega, @RS.StepsN.refl RS.SC M, rest⟩
    · rcases ih M₁ rfl with ⟨M', hu, hm⟩ | ⟨k₁, m₁, M', hn, hm, hp⟩
      · exact .inl ⟨M', hu, RS.StepsN.tail hs hm⟩
      · exact .inr ⟨k₁ + 1, m₁, M', by omega, RS.StepsN.tail hs hm, hp⟩

/-- **The housed wall**: the halt-side relay never exceeds 73 fires, any schedule —
pinned compositionally, never touching the 53,592-state product space. -/
theorem sc_relay_wall : ∀ (n : Nat) (u : SCTerm),
    RS.SC.StepsN n (scRelay (scFate (.app .C .C))) u → n ≤ 73 := by
  intro n u h
  rcases scRelay_decompose h _ rfl with ⟨M', _, hm⟩ | ⟨k, m, M', hn, hm, hp⟩
  · exact Nat.le_trans (sc_fate_all_bounded n M' hm) (by omega)
  · have hpair := scPair_decompose hp M' (.app .C M') rfl
    obtain ⟨u₁, u₂, m₁, m₂, _, hm12, h1, h2⟩ := hpair
    have hb1 : k + m₁ ≤ 36 := sc_fate_all_bounded _ u₁ (RS.StepsN.trans hm h1)
    obtain ⟨m₂', _, hm2⟩ := scWrap_decompose h2 M' rfl
    have hb2 : k + m₂ ≤ 36 := sc_fate_all_bounded _ m₂' (RS.StepsN.trans hm hm2)
    omega

/-- **Conditional fate, housed**: the relay with a spinning payload assembles an immortal
pair in eight fires; with a halting payload every schedule dies at machine-and-shadow
normal form behind the 73-fire wall. -/
theorem sc_relay_fates :
    (RS.SC.StepsN 8 (scRelay (scFate .C))
        (SCTerm.app (SCTerm.app .S scFateOrb) (.app .C (scFate .C))) ∧
      ∀ n, ∃ u, RS.SC.StepsN n
        (SCTerm.app (SCTerm.app .S scFateOrb) (.app .C (scFate .C))) u) ∧
    (RS.SC.Steps (scRelay (scFate (.app .C .C)))
        (SCTerm.app (SCTerm.app .S scFateNf) (.app .C scFateNf)) ∧
      (∀ v, ¬ RS.SC.step (SCTerm.app (SCTerm.app .S scFateNf) (.app .C scFateNf)) v) ∧
      ∀ (n : Nat) (u : SCTerm),
        RS.SC.StepsN n (scRelay (scFate (.app .C .C))) u → n ≤ 73) := by
  refine ⟨⟨RS.StepsN.tail (scRelay_fire _) (scStepsN_appL _ (scStepsN_appR .S scFate_entry)),
      sc_pair_spin _⟩, ?_, ?_, sc_relay_wall⟩
  · exact RS.Steps.tail (scRelay_fire _)
      (RS.Steps.trans
        (RS.StepsN.toSteps (scStepsN_appL _ (scStepsN_appR .S scFate_halts)))
        (RS.StepsN.toSteps (scStepsN_appR _ (scStepsN_appR .C scFate_halts))))
  · intro v h
    rcases scPair_inv h with ⟨c', hs, _⟩ | ⟨c', hs, _⟩
    · exact scFateNf_normal c' hs
    · obtain ⟨m', hm, _⟩ := scWrap_inv hs
      exact scFateNf_normal m' hm

-- ## Stage 186: the chassis isolates — a theorem, not a suspicion
-- Bits-are-sources forced hosting to route behavior; the pair chassis was the candidate
-- router. This stage closes the question: it cannot route ANYTHING. Pair reachability is
-- EXACTLY member reachability (`sc_pair_reachable_iff`, an iff): no schedule, however
-- adversarial, lets one member's state influence the other's options. And the housed
-- machine-and-shadow pair decouples instantly (`sc_shadow_drifts`): the shadow replays the
-- machine's reductions on its own clock, any combination of progress reachable. The
-- chassis is a PERFECT ISOLATOR — good for composing certificates (Stages 184–185), a
-- dead end for communication. Hosting needs members that SHARE structure through fires,
-- which is exactly what the one-tag-step / cell-synthesis line builds.

/-- `Steps`-level pair decomposition. -/
theorem scPair_steps_decompose {c₁ c₂ u : SCTerm}
    (h : RS.SC.Steps (SCTerm.app (SCTerm.app .S c₁) c₂) u) :
    ∃ u₁ u₂, u = SCTerm.app (SCTerm.app .S u₁) u₂ ∧
      RS.SC.Steps c₁ u₁ ∧ RS.SC.Steps c₂ u₂ := by
  obtain ⟨n, hn⟩ := RS.Steps.toStepsN h
  obtain ⟨u₁, u₂, n₁, n₂, hu, _, h1, h2⟩ := scPair_decompose hn c₁ c₂ rfl
  exact ⟨u₁, u₂, hu, RS.StepsN.toSteps h1, RS.StepsN.toSteps h2⟩

/-- **The chassis isolates**: pair reachability IS the product of member reachabilities. -/
theorem sc_pair_reachable_iff {c₁ c₂ u : SCTerm} :
    RS.SC.Steps (SCTerm.app (SCTerm.app .S c₁) c₂) u ↔
    ∃ u₁ u₂, u = SCTerm.app (SCTerm.app .S u₁) u₂ ∧
      RS.SC.Steps c₁ u₁ ∧ RS.SC.Steps c₂ u₂ := by
  constructor
  · exact scPair_steps_decompose
  · rintro ⟨u₁, u₂, rfl, h1, h2⟩
    exact sc_two_clocks h1 h2

/-- `Steps`-level shadow decomposition. -/
theorem scWrap_steps_decompose {m u : SCTerm}
    (h : RS.SC.Steps (SCTerm.app .C m) u) :
    ∃ m', u = SCTerm.app .C m' ∧ RS.SC.Steps m m' := by
  obtain ⟨n, hn⟩ := RS.Steps.toStepsN h
  obtain ⟨m', hu, hm⟩ := scWrap_decompose hn m rfl
  exact ⟨m', hu, RS.StepsN.toSteps hm⟩

/-- **The shadow drifts**: the housed pair reaches exactly the machine's reductions in
each slot, independently — every combination of progress, no synchronization. -/
theorem sc_shadow_drifts {M u : SCTerm} :
    RS.SC.Steps (scHoused M) u ↔
    ∃ m₁ m₂, u = SCTerm.app (SCTerm.app .S m₁) (SCTerm.app .C m₂) ∧
      RS.SC.Steps M m₁ ∧ RS.SC.Steps M m₂ := by
  constructor
  · intro h
    obtain ⟨u₁, u₂, rfl, h1, h2⟩ := scPair_steps_decompose h
    obtain ⟨m₂, rfl, hm⟩ := scWrap_steps_decompose h2
    exact ⟨u₁, m₂, rfl, h1, hm⟩
  · rintro ⟨m₁, m₂, rfl, h1, h2⟩
    exact sc_two_clocks h1 (scSteps_appR .C h2)

-- ## Stage 187: the n=12 mountain — excess 57, the ladder steepens
-- The n=12 graft-neighborhood sample (two leaves grafted around the n=10 winner) found a
-- taller mountain immediately: a 12-leaf term whose forced prefix runs the full 400 steps,
-- peaks at 291 leaves at step 338, and hands off to a 234-leaf off-prefix target one
-- checked step later. The floor ladder: f(6,6) ≥ 7, f(8,32) ≥ 44, f(9,10) ≥ 25,
-- f(10,142) ≥ 186, f(12,234) ≥ 291 — excess 12 → 44 → 57 at n = 8 → 10 → 12 (and the
-- random-sample phase is still sweeping). Every rung is one more reason to believe no
-- computable intermediate bound exists.

/-- Twelve leaves: the n=10 winner with a `C S S` graft. -/
def scMt5T : SCTerm := (.app (.app (.app (.app (.app .C .S) .S) (.app .S .S)) .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- 234 leaves, one checked step past the 400-step forced prefix. -/
def scMt5U : SCTerm := (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))

/-- The witnessing path: the full forced march, then one checked step. -/
def scMt5Path : List SCTerm := scForcedMarch scMt5T 400 ++ [scMt5U]

section
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

#guard scMt5T.leafCount = 12
#guard scMt5U.leafCount = 234
#guard (scForcedMarch scMt5T 400).length = 400

/-- The crossing exists. -/
theorem scMt5_steps : RS.SC.Steps scMt5T scMt5U :=
  scChained_steps scMt5Path scMt5T scMt5U (by decide) (by decide)

/-- **The n=12 mountain**: no path from `scMt5T` (12 leaves) to `scMt5U` (234 leaves)
stays within 290 leaves — the forced prefix peaks at 291. -/
theorem scMt5_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 290 scMt5T scMt5U :=
  scForced_mountain (scForcedMarch scMt5T 400) (scForcedMarch_forced 400 scMt5T)
    (by decide) (by decide)

end

/-- **The n=12 floor**: every valid bounding function clears 291 at (12, 234). -/
theorem sc_bound_floor_291 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    291 ≤ f 12 234 := by
  by_cases h : 291 ≤ f 12 234
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 12 234) scMt5T scMt5U :=
      hf scMt5T scMt5U scMt5_steps
    exact scMt5_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 188: metabolic assembly — delivery, execution, housing in seven fires
-- The chassis isolates (Stage 186), so machines can only interact through fires — and
-- here is that interaction, pinned end to end from spare parts. Three dead cells (all
-- `C C` shells) burn by the cell-armed pop; the freed head arm is the `S S` MINTER, which
-- executes on the freed cargo and produces `S B (S S B)` — the inert pair chassis housing
-- the cargo NEXT TO its own freshly minted register. Delivery (pop, six fires) →
-- execution (one minting fire) → housing (the chassis, zero fires, by shape). Cell one's
-- contents consumed cell three's contents: the first pinned producer→consumer handoff.
-- Fully parametric in the cargo; at `B = C` the product is `S C (S S C)` — a bit sitting
-- beside the fate register that would spin on it.

/-- Three cells: minter head, minter arm, cargo arm. -/
def scAssembly (B : SCTerm) : SCTerm :=
  .app (.app (.app (.app .C .C) (.app .S .S)) (.app (.app .C .C) (.app .S .S)))
    (.app (.app .C .C) B)

/-- **Metabolic assembly**: the cells burn, the minter runs on the cargo, and the product
is the housed cargo-plus-register — seven fires, any cargo. -/
theorem sc_metabolic_assembly (B : SCTerm) :
    RS.SC.Steps (scAssembly B)
      (SCTerm.app (SCTerm.app .S B) (.app (.app .S .S) B)) :=
  RS.Steps.trans (sc_cellArm_pop (.app .S .S) (.app .S .S) B)
    (RS.Steps.single (SCStep.S_red .S (.app .S .S) B))

/-- The bit instance: three dead cells assemble a bit housed beside its own register. -/
theorem sc_metabolic_assembly_bit :
    RS.SC.Steps (scAssembly .C)
      (SCTerm.app (SCTerm.app .S .C) (.app (.app .S .S) .C)) :=
  sc_metabolic_assembly .C

-- ## Stage 189: the fate machine assembles itself — dead cells to universal fate
-- `scFate b` is EXACTLY a pop product: head cell `S (S scDup)`, arm cell `S S b`, cargo
-- cell `C C`. Three dead cells, six burning fires, and the machine stands assembled —
-- `sc_fate_assembly` is a one-line instantiation of the Stage 156 pop law. The whole
-- lifecycle is now one pinned pipeline: ASSEMBLY (6 fires, dead cells) → FATE (bit `C`:
-- the eternal consulting orbit; bit `C C`: the normal form) — and the halt side carries a
-- UNIVERSAL wall: the assembled-and-run seed space is 237 states graded by height 0–42,
-- so no schedule from the dead cells exceeds 42 = 6 + 36 fires and every dead end is
-- `scFateNf`. Nested housing rounds out the calculus: assemblies take assemblies as
-- cargo (`sc_assembly_line`). From three inert shells to a machine whose register decides
-- eternity, every fire kernel-checked.

/-- The fate seed: three dead cells holding head, register arm, and cargo. -/
def scFateSeed (b : SCTerm) : SCTerm :=
  .app (.app (.app (.app .C .C) (.app .S (.app .S scDup)))
    (.app (.app .C .C) (.app (.app .S .S) b))) (.app (.app .C .C) (.app .C .C))

/-- **The fate machine assembles itself**: six fires from dead cells. -/
theorem sc_fate_assembly (b : SCTerm) :
    RS.SC.Steps (scFateSeed b) (scFate b) :=
  sc_cellArm_pop (.app .S (.app .S scDup)) (.app (.app .S .S) b) (.app .C .C)

/-- Assembly composes with fate, spin side: the dead cells reach the eternal orbit. -/
theorem sc_fate_assembly_spin :
    RS.SC.Steps (scFateSeed .C) scFateOrb ∧ ∀ n, ∃ u, RS.SC.StepsN n scFateOrb u :=
  ⟨RS.Steps.trans (sc_fate_assembly .C) (RS.StepsN.toSteps scFate_entry), scFate_runs⟩

/-- Assembly composes with fate, halt side: the dead cells reach the normal form. -/
theorem sc_fate_assembly_halt :
    RS.SC.Steps (scFateSeed (.app .C .C)) scFateNf :=
  RS.Steps.trans (sc_fate_assembly (.app .C .C)) (RS.StepsN.toSteps scFate_halts)

/-- The halt-side seed's complete state space, height-graded: 237 states, heights 0–42. -/
def scFateSeedSpace : List (List SCTerm) :=
  [[(.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .C (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .C .C) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .C .C) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .C (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app scDup (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .S scDup) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))),
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C))))),
    (.app (.app scDup (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))),
    (.app (.app scDup (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app .S (.app .C .C)) (.app (.app .C .C) (.app .C .C)))))],
   [(.app (.app (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app scDup (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C))))],
   [(.app (.app (.app .S scDup) (.app .C .C)) (.app (.app (.app .S .S) (.app .C .C)) (.app .C .C)))],
   [(.app (.app (.app .S (.app .S scDup)) (.app (.app .S .S) (.app .C .C))) (.app .C .C))],
   [(.app (.app (.app .C (.app .S (.app .S scDup))) (.app .C .C)) (.app (.app .S .S) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app .C .C)) (.app .S (.app .S scDup))) (.app (.app .S .S) (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app .C .C))) (.app (.app .S .S) (.app .C .C))) (.app .S (.app .S scDup)))],
   [(.app (.app (.app (.app .C .C) (.app (.app .S .S) (.app .C .C))) (.app (.app .C .C) (.app .C .C))) (.app .S (.app .S scDup)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app (.app .S .S) (.app .C .C)))) (.app .S (.app .S scDup))) (.app (.app .C .C) (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app .S (.app .S scDup))) (.app (.app .C .C) (.app (.app .S .S) (.app .C .C)))) (.app (.app .C .C) (.app .C .C)))]]


def scFateSeedStates : List SCTerm := scFateSeedSpace.flatten

section
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

#guard scFateSeedStates.length = 237
#guard scRankIn scFateSeedSpace (scFateSeed (.app .C .C)) = 42

theorem scFateSeedSpace_ranked : ∀ x ∈ scFateSeedStates, ∀ y ∈ scSucc x,
    y ∈ scFateSeedStates ∧ scRankIn scFateSeedSpace y < scRankIn scFateSeedSpace x := by
  decide

theorem scFateSeedSpace_seed : scFateSeed (.app .C .C) ∈ scFateSeedStates := by decide

theorem scFateSeedSpace_nf : ∀ x ∈ scFateSeedStates, scSucc x = [] → x = scFateNf := by
  decide

end

/-- **Universal fate from dead cells**: no schedule from the halt-side seed exceeds
42 = 6 + 36 fires, and every dead end is `scFateNf`. -/
theorem sc_fate_assembly_universal :
    (∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n (scFateSeed (.app .C .C)) u → n ≤ 42) ∧
    (∀ u, RS.SC.Steps (scFateSeed (.app .C .C)) u →
      (∀ v, ¬ RS.SC.step u v) → u = scFateNf) := by
  constructor
  · intro n u h
    have hb := (scRanked_bound scFateSeedSpace_ranked h scFateSeedSpace_seed).2
    have hk : scRankIn scFateSeedSpace (scFateSeed (.app .C .C)) = 42 := rfl
    omega
  · intro u hs hnf
    obtain ⟨n, hn⟩ := RS.Steps.toStepsN hs
    have hu := (scRanked_bound scFateSeedSpace_ranked hn scFateSeedSpace_seed).1
    have hempty : scSucc u = [] := by
      cases hsu : scSucc u with
      | nil => rfl
      | cons a l => exact absurd (scSucc_sound (hsu ▸ List.mem_cons_self)) (hnf a)
    exact scFateSeedSpace_nf u hu hempty

/-- **The assembly line**: assemblies take assemblies as cargo — nested housing. -/
theorem sc_assembly_line (B : SCTerm) :
    RS.SC.Steps (scAssembly (scAssembly B))
      (SCTerm.app
        (SCTerm.app .S (SCTerm.app (SCTerm.app .S B) (.app (.app .S .S) B)))
        (.app (.app .S .S)
          (SCTerm.app (SCTerm.app .S B) (.app (.app .S .S) B)))) :=
  RS.Steps.trans
    (scSteps_appR _ (scSteps_appR (.app .C .C) (sc_metabolic_assembly B)))
    (sc_metabolic_assembly (SCTerm.app (SCTerm.app .S B) (.app (.app .S .S) B)))

-- ## Stage 190: the frame trichotomy — one head, three registers, three futures
-- The fate frame `S (S scDup) r (C C)` is not a two-way switch but a COMPLETE behavior
-- selector. A census of all 3,238 registers up to six leaves sorts into 1,168 halting,
-- 336 cycling, 1,661 growing — and the three futures are already selected by registers of
-- at most three leaves: `C` halts in a FORCED 11-fire line (12 states, every schedule
-- identical), `C S` falls onto a period-8 bounded orbit ridden forever inside nine terms,
-- and `S S S` grows without bound on a period-7 front (`F ⟶⁷ F·J`, five leaves of junk
-- per lap). `scFate b` is this frame at `r = S S b` — definitional equality — so the
-- eternity switch of Stages 182–189 is one slice of a spectrum: HALT, ORBIT, EXPLODE,
-- selected by register shape, each certified in its own currency.

/-- The fate frame, register abstracted. -/
def scFrame (r : SCTerm) : SCTerm :=
  .app (.app (.app .S (.app .S scDup)) r) (.app .C .C)

/-- `scFate` is the frame at `S S bit`. -/
theorem scFate_is_frame (b : SCTerm) : scFate b = scFrame (.app (.app .S .S) b) := rfl

/-- Register `C`: the 7-leaf normal form. -/
def scFrameHaltNf : SCTerm := (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C .C)))

/-- Register `C`: eleven fires to the normal form. -/
theorem sc_frame_halt : RS.SC.StepsN 11 (scFrame .C) scFrameHaltNf :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) .C (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app .C (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C (.app .C .C)) (.app (.app .C .C) (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C (.app .C .C))) (.app .C (.app .C .C)) (.app (.app .C .C) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C (.app .C .C)) (.app (.app .C .C) (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C (.app .C .C))) (.app .C (.app .C .C)) (.app .C (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C (.app .C .C)) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app .C .C)) (.app .C (.app .C .C)) (.app .C (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red (.app .C .C) (.app .C (.app .C .C)) (.app .C (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app .C (.app .C .C)) (.app .C (.app .C .C)))
  (@RS.StepsN.refl RS.SC scFrameHaltNf))))))))))))

#guard scSucc scFrameHaltNf = []

theorem scFrameHaltNf_normal : ∀ v, ¬ RS.SC.step scFrameHaltNf v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scFrameHaltNf = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- The halt leg's complete state space: a single forced line of 12 states. -/
def scFrameHaltSpace : List (List SCTerm) :=
  [[(.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app .C .C) (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app .C (.app .C .C)) (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app .C (.app .C .C))) (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app .C (.app .C .C)))) (.app .C (.app .C .C))) (.app .C (.app .C .C)))],
   [(.app (.app (.app (.app .C .C) (.app .C (.app .C .C))) (.app (.app .C .C) (.app .C (.app .C .C)))) (.app .C (.app .C .C)))],
   [(.app (.app (.app .C (.app (.app .C .C) (.app .C (.app .C .C)))) (.app .C (.app .C .C))) (.app (.app .C .C) (.app .C (.app .C .C))))],
   [(.app (.app (.app (.app .C .C) (.app .C (.app .C .C))) (.app (.app .C .C) (.app .C (.app .C .C)))) (.app (.app .C .C) (.app .C (.app .C .C))))],
   [(.app (.app scDup (.app .C (.app .C .C))) (.app (.app .C .C) (.app .C (.app .C .C))))],
   [(.app (.app (.app .S scDup) (.app .C .C)) (.app .C (.app .C .C)))],
   [(.app (.app (.app .S (.app .S scDup)) .C) (.app .C .C))]]

def scFrameHaltStates : List SCTerm := scFrameHaltSpace.flatten

section
set_option maxHeartbeats 1000000

#guard scFrameHaltStates.length = 12
#guard scRankIn scFrameHaltSpace (scFrame .C) = 11

theorem scFrameHaltSpace_ranked : ∀ x ∈ scFrameHaltStates, ∀ y ∈ scSucc x,
    y ∈ scFrameHaltStates ∧ scRankIn scFrameHaltSpace y < scRankIn scFrameHaltSpace x := by
  decide

end

/-- The halt is universal: no schedule exceeds eleven fires. -/
theorem sc_frame_halt_universal : ∀ (n : Nat) (u : SCTerm),
    RS.SC.StepsN n (scFrame .C) u → n ≤ 11 := by
  intro n u h
  have hb := (scRanked_bound scFrameHaltSpace_ranked h (by decide)).2
  have hk : scRankIn scFrameHaltSpace (scFrame .C) = 11 := rfl
  omega

/-- Register `C S`: the period-8 orbit's phase 0. -/
def scFrameOrb : SCTerm := (.app (.app (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))

/-- Thirteen fires from seed to orbit. -/
theorem sc_frame_cycle_entry : RS.SC.StepsN 13 (scFrame (.app .C .S)) scFrameOrb :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C .S) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .S) (.app .C .C)) (.app .C .C) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .S) (.app .C .C)) (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scFrameOrb))))))))))))))

theorem scFrameStep0 : RS.SC.step scFrameOrb
    (.app (.app (.app .S (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) :=
  SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
theorem scFrameStep1 : RS.SC.step (.app (.app (.app .S (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
    (.app (.app (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) :=
  SCStep.S_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
theorem scFrameStep2 : RS.SC.step (.app (.app (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))))
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) :=
  SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
theorem scFrameStep3 : RS.SC.step (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))))
    (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .S) (.app .C .C))) :=
  SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
theorem scFrameStep4 : RS.SC.step (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .S) (.app .C .C)))
    (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C))) :=
  SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))))
theorem scFrameStep5 : RS.SC.step (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C)))
    (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) :=
  SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C))
theorem scFrameStep6 : RS.SC.step (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
    (.app (.app (.app .C (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) :=
  SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C)))
theorem scFrameStep7 : RS.SC.step (.app (.app (.app .C (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
    scFrameOrb :=
  SCStep.C_red (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))

/-- The orbit's lap, ending back home. -/
def scFrameLap : List SCTerm := [(.app (.app (.app .S (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))),
  (.app (.app (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))),
  (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))),
  (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .S) (.app .C .C))),
  (.app (.app (.app .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C))),
  (.app (.app (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))),
  (.app (.app (.app .C (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))),
  (.app (.app (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))]

/-- One lap: eight fires, verbatim return. -/
theorem scFrame_cycle : RS.SC.StepsN 8 scFrameOrb scFrameOrb :=
  (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (RS.StepsN.tail scFrameStep3 (RS.StepsN.tail scFrameStep4 (RS.StepsN.tail scFrameStep5 (RS.StepsN.tail scFrameStep6 (RS.StepsN.tail scFrameStep7 (@RS.StepsN.refl RS.SC scFrameOrb)))))))))

theorem scFrame_forever : ∀ n, RS.SC.StepsN (8 * n) scFrameOrb scFrameOrb
  | 0 => @RS.StepsN.refl RS.SC scFrameOrb
  | n + 1 => by
      rw [Nat.mul_succ]
      exact RS.StepsN.trans (scFrame_forever n) scFrame_cycle

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem scFrameOrb_partial : ∀ r, r < 8 →
    ∃ u : SCTerm, RS.SC.StepsN r scFrameOrb u ∧ u ∈ scFrameOrb :: scFrameLap
  | 0, _ => ⟨_, @RS.StepsN.refl RS.SC scFrameOrb, by decide⟩
  | 1, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (@RS.StepsN.refl RS.SC _)), by decide⟩
  | 2, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (@RS.StepsN.refl RS.SC _))), by decide⟩
  | 3, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (@RS.StepsN.refl RS.SC _)))), by decide⟩
  | 4, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (RS.StepsN.tail scFrameStep3 (@RS.StepsN.refl RS.SC _))))), by decide⟩
  | 5, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (RS.StepsN.tail scFrameStep3 (RS.StepsN.tail scFrameStep4 (@RS.StepsN.refl RS.SC _)))))), by decide⟩
  | 6, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (RS.StepsN.tail scFrameStep3 (RS.StepsN.tail scFrameStep4 (RS.StepsN.tail scFrameStep5 (@RS.StepsN.refl RS.SC _))))))), by decide⟩
  | 7, _ => ⟨_, (RS.StepsN.tail scFrameStep0 (RS.StepsN.tail scFrameStep1 (RS.StepsN.tail scFrameStep2 (RS.StepsN.tail scFrameStep3 (RS.StepsN.tail scFrameStep4 (RS.StepsN.tail scFrameStep5 (RS.StepsN.tail scFrameStep6 (@RS.StepsN.refl RS.SC _)))))))), by decide⟩
  | r + 8, h => absurd h (by omega)

end

/-- **The bounded eternity**: runs of every length, all inside nine terms. -/
theorem scFrame_runs (n : Nat) :
    ∃ u : SCTerm, RS.SC.StepsN n scFrameOrb u ∧ u ∈ scFrameOrb :: scFrameLap := by
  obtain ⟨u, hu, hmem⟩ := scFrameOrb_partial (n % 8) (Nat.mod_lt n (by omega))
  refine ⟨u, ?_, hmem⟩
  rw [← Nat.div_add_mod n 8]
  exact RS.StepsN.trans (scFrame_forever (n / 8)) hu

/-- Register `S S S`: the growth front (15 leaves). -/
def scGrowFront : SCTerm := (.app (.app (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))) (.app (.app (.app .S .S) .S) (.app .C .C)))

/-- Five leaves of junk per lap. -/
def scGrowJ : SCTerm := (.app (.app (.app .S .S) .S) (.app .C .C))

/-- Nine fires from seed to front. -/
theorem scGrow_entry : RS.SC.StepsN 9 (scFrame (.app (.app .S .S) .S)) scGrowFront :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .S .S) .S) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C))) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C))) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))
  (@RS.StepsN.refl RS.SC scGrowFront))))))))))

/-- The period: seven fires, one junk block. -/
theorem scGrow_period : RS.SC.StepsN 7 scGrowFront (.app scGrowFront scGrowJ) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red .S .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .S (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app .S (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .S (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C))) (.app (.app (.app .S .S) .S) (.app .C .C)) (.app (.app (.app .S .S) .S) (.app .C .C)))
  (@RS.StepsN.refl RS.SC (.app scGrowFront scGrowJ)))))))))

/-- The growing family. -/
def scGrow : Nat → SCTerm
  | 0 => scGrowFront
  | n + 1 => .app (scGrow n) scGrowJ

theorem scGrow_step : ∀ n, RS.SC.StepsN 7 (scGrow n) (scGrow (n + 1))
  | 0 => scGrow_period
  | n + 1 => scStepsN_appL scGrowJ (scGrow_step n)

theorem scGrow_reach : ∀ n, RS.SC.Steps scGrowFront (scGrow n)
  | 0 => @RS.Steps.refl RS.SC scGrowFront
  | n + 1 => RS.Steps.trans (scGrow_reach n) (RS.StepsN.toSteps (scGrow_step n))

theorem scGrow_size : ∀ n, (scGrow n).leafCount = 15 + 5 * n
  | 0 => rfl
  | n + 1 => by
      show (scGrow n).leafCount + scGrowJ.leafCount = 15 + 5 * (n + 1)
      have hj : scGrowJ.leafCount = 5 := rfl
      rw [scGrow_size n, hj]
      omega

/-- **The unbounded eternity**: the `S S S` register outgrows every bound. -/
theorem sc_frame_grow_unbounded (m : Nat) :
    ∃ u, RS.SC.Steps (scFrame (.app (.app .S .S) .S)) u ∧ m < u.leafCount := by
  refine ⟨scGrow m, RS.Steps.trans (RS.StepsN.toSteps scGrow_entry) (scGrow_reach m), ?_⟩
  rw [scGrow_size m]
  omega

/-- **The frame trichotomy**: one 8-leaf head, three registers of at most three leaves,
three futures — a forced 11-fire halt (universal), a period-8 orbit ridden forever inside
nine terms, and unbounded growth. -/
theorem sc_frame_trichotomy :
    (RS.SC.StepsN 11 (scFrame .C) scFrameHaltNf ∧
      (∀ v, ¬ RS.SC.step scFrameHaltNf v) ∧
      ∀ (n : Nat) (u : SCTerm), RS.SC.StepsN n (scFrame .C) u → n ≤ 11) ∧
    (RS.SC.StepsN 13 (scFrame (.app .C .S)) scFrameOrb ∧
      ∀ n, ∃ u : SCTerm, RS.SC.StepsN n scFrameOrb u ∧ u ∈ scFrameOrb :: scFrameLap) ∧
    (∀ m, ∃ u, RS.SC.Steps (scFrame (.app (.app .S .S) .S)) u ∧ m < u.leafCount) :=
  ⟨⟨sc_frame_halt, scFrameHaltNf_normal, sc_frame_halt_universal⟩,
   ⟨sc_frame_cycle_entry, scFrame_runs⟩,
   sc_frame_grow_unbounded⟩

-- ## Stage 191: unary parity, hosted — the first eight rungs
-- The steering probe found no binary parity in the ≤2-leaf symbol envelope, but the
-- unary family delivered: in the fate frame, register `C^k S` HALTS when `k` is even
-- (11 + 2k fires to a normal form) and ORBITS FOREVER when `k` is odd (period 7 + k) —
-- verified through k = 10, pinned here for k = 0..7. An input predicate — the parity of a
-- unary numeral — is decided by ETERNITY: the first hosted predicate of the program. Each
-- odd rung has its own orbit (the traces never merge, so the general law is registered as
-- conjecture C9 rather than proved by descent). New toolkit: `sc_cycle_forever` /
-- `sc_cycle_unbounded` — any kernel-pinned cycle yields runs of unbounded length, once.

/-- The unary numeral registers: `C^k S`. -/
def scParityReg : Nat → SCTerm
  | 0 => .S
  | k + 1 => .app .C (scParityReg k)

/-- Cycles compose to every multiple. -/
theorem sc_cycle_forever {p : Nat} {x : SCTerm} (h : RS.SC.StepsN p x x) :
    ∀ q, RS.SC.StepsN (p * q) x x
  | 0 => @RS.StepsN.refl RS.SC x
  | q + 1 => by
      rw [Nat.mul_succ]
      exact RS.StepsN.trans (sc_cycle_forever h q) h

/-- **Any pinned cycle is an eternity certificate**: runs of unbounded length. -/
theorem sc_cycle_unbounded {p : Nat} {x : SCTerm} (hp : 1 ≤ p)
    (h : RS.SC.StepsN p x x) : ∀ n, ∃ m, n ≤ m ∧ RS.SC.StepsN m x x := fun n =>
  ⟨p * n, Nat.le_mul_of_pos_left n hp, sc_cycle_forever h n⟩


/-- Parity rung k = 0 (even): the normal form. -/
def scParityNf0 : SCTerm := (.app (.app .C (.app (.app .S (.app .C .C)) (.app .S (.app .C .C)))) (.app .S (.app .C .C)))

theorem scParity_halt0 :
    RS.SC.StepsN 11 (scFrame (scParityReg 0)) scParityNf0 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) .S (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app .S (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .S (.app .C .C)) (.app (.app .C .C) (.app .S (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .S (.app .C .C))) (.app .S (.app .C .C)) (.app (.app .C .C) (.app .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .S (.app .C .C)) (.app (.app .C .C) (.app .S (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .S (.app .C .C))) (.app .S (.app .C .C)) (.app .S (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .S (.app .C .C)) (.app .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app .S (.app .C .C)) (.app .S (.app .C .C)) (.app .S (.app .C .C)))
  (RS.StepsN.tail (SCStep.S_red (.app .C .C) (.app .S (.app .C .C)) (.app .S (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app .S (.app .C .C)) (.app (.app .S (.app .C .C)) (.app .S (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityNf0))))))))))))

theorem scParityNf0_normal : ∀ v, ¬ RS.SC.step scParityNf0 v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scParityNf0 = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Parity rung k = 1 (odd): the orbit, period 8. -/
def scParityOrb1 : SCTerm := (.app (.app (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))

theorem scParity_entry1 :
    RS.SC.StepsN 13 (scFrame (scParityReg 1)) scParityOrb1 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C .S) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .S) (.app .C .C)) (.app .C .C) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .S) (.app .C .C)) (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb1))))))))))))))

theorem scParity_cycle1 : RS.SC.StepsN 8 scParityOrb1 scParityOrb1 :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))) (.app (.app .C .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .S) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .S) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb1)))))))))

/-- Parity rung k = 2 (even): the normal form. -/
def scParityNf2 : SCTerm := (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C)))) (.app (.app .C (.app .C .S)) (.app .C .C)))

theorem scParity_halt2 :
    RS.SC.StepsN 15 (scFrame (scParityReg 2)) scParityNf2 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C .S)) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C))) (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C))) (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app (.app .C (.app .C .S)) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.S_red (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app (.app .C (.app .C .S)) (.app .C .C)) (.app (.app .C (.app .C .S)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C .S)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red .S (.app (.app .C (.app .C .S)) (.app .C .C)) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityNf2))))))))))))))))

theorem scParityNf2_normal : ∀ v, ¬ RS.SC.step scParityNf2 v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scParityNf2 = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Parity rung k = 3 (odd): the orbit, period 10. -/
def scParityOrb3 : SCTerm := (.app (.app (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))

theorem scParity_entry3 :
    RS.SC.StepsN 17 (scFrame (scParityReg 3)) scParityOrb3 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C (.app .C .S))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb3))))))))))))))))))

theorem scParity_cycle3 : RS.SC.StepsN 10 scParityOrb3 scParityOrb3 :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C .S))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb3)))))))))))

/-- Parity rung k = 4 (even): the normal form. -/
def scParityNf4 : SCTerm := (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))

theorem scParity_halt4 :
    RS.SC.StepsN 19 (scFrame (scParityReg 4)) scParityNf4 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.S_red (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C .S)) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red .S (.app (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C)) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityNf4))))))))))))))))))))

theorem scParityNf4_normal : ∀ v, ¬ RS.SC.step scParityNf4 v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scParityNf4 = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Parity rung k = 5 (odd): the orbit, period 12. -/
def scParityOrb5 : SCTerm := (.app (.app (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))

theorem scParity_entry5 :
    RS.SC.StepsN 21 (scFrame (scParityReg 5)) scParityOrb5 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb5))))))))))))))))))))))

theorem scParity_cycle5 : RS.SC.StepsN 12 scParityOrb5 scParityOrb5 :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb5)))))))))))))

/-- Parity rung k = 6 (even): the normal form. -/
def scParityNf6 : SCTerm := (.app (.app .C (.app (.app .S (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))

theorem scParity_halt6 :
    RS.SC.StepsN 23 (scFrame (scParityReg 6)) scParityNf6 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.S_red (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C (.app .C .S)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red (.app .C .S) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red .S (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C)) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityNf6))))))))))))))))))))))))

theorem scParityNf6_normal : ∀ v, ¬ RS.SC.step scParityNf6 v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scParityNf6 = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Parity rung k = 7 (odd): the orbit, period 14. -/
def scParityOrb7 : SCTerm := (.app (.app (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))

theorem scParity_entry7 :
    RS.SC.StepsN 25 (scFrame (scParityReg 7)) scParityOrb7 :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb7))))))))))))))))))))))))))

theorem scParity_cycle7 : RS.SC.StepsN 14 scParityOrb7 scParityOrb7 :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S)))))) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C (.app .C .S))))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C (.app .C .S)))) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C (.app .C .S))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C (.app .C .S)) (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)) (.app (.app .C .C) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C)))) (.app (.app .C .C) (.app (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C (.app .C .S))))))) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scParityOrb7)))))))))))))))

/-- **Unary parity, hosted (rungs 0–7)**: in the fate frame, the numeral `C^k S` HALTS
for even `k` and ORBITS FOREVER for odd `k` — the parity of the input decided by the
machine's eternity. -/
theorem sc_parity_hosted :
    (∀ k ∈ [0, 2, 4, 6], ∃ nf : SCTerm, RS.SC.Steps (scFrame (scParityReg k)) nf ∧
      ∀ v, ¬ RS.SC.step nf v) ∧
    (∀ k ∈ [1, 3, 5, 7], ∃ orb : SCTerm, RS.SC.Steps (scFrame (scParityReg k)) orb ∧
      ∀ n, ∃ m, n ≤ m ∧ RS.SC.StepsN m orb orb) := by
  constructor
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨scParityNf0, RS.StepsN.toSteps scParity_halt0, scParityNf0_normal⟩
    · exact ⟨scParityNf2, RS.StepsN.toSteps scParity_halt2, scParityNf2_normal⟩
    · exact ⟨scParityNf4, RS.StepsN.toSteps scParity_halt4, scParityNf4_normal⟩
    · exact ⟨scParityNf6, RS.StepsN.toSteps scParity_halt6, scParityNf6_normal⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨scParityOrb1, RS.StepsN.toSteps scParity_entry1,
        sc_cycle_unbounded (by omega) scParity_cycle1⟩
    · exact ⟨scParityOrb3, RS.StepsN.toSteps scParity_entry3,
        sc_cycle_unbounded (by omega) scParity_cycle3⟩
    · exact ⟨scParityOrb5, RS.StepsN.toSteps scParity_entry5,
        sc_cycle_unbounded (by omega) scParity_cycle5⟩
    · exact ⟨scParityOrb7, RS.StepsN.toSteps scParity_entry7,
        sc_cycle_unbounded (by omega) scParity_cycle7⟩

-- ## Stage 192: C9 proved — the frame parity law, every k
-- The template proof. Anatomy, fully parametric in the register `r` and numeral index:
-- (1) THE PRELUDE — nine fires take `scFrame r` to the triple `M M M`, `M = r · W`,
-- `W = C C`, for EVERY register (the frame's universal opening). (2) THE STRIP — `C` is
-- flip: `C^(m+1) S · y · z ⟶ C^m S · z · y` in one fire, so `k` strips sort the two
-- arguments by the parity of `k`. (3) THE CLOSE — even parity puts `W` in operator
-- position and the machine dies in an inert `C (S W M) M`; odd parity puts `M` there and
-- the machine locks into the cycle `Φ = M N₁ N₂ ⟶ᵏ⁺⁷ Φ` on the `N`-tower `N₀ = M`,
-- `Nᵢ₊₁ = W Nᵢ` (k strips, one duplicating S-fire, six C-fires — the six-fire tail is one
-- parametric chain). Conjecture C9 closes as `sc_frame_parity_law`: for every `k`, the
-- frame on numeral `C^k S` reaches a normal form iff `k` is even, and for odd `k` admits
-- runs of unbounded length. Parity of a unary numeral, decided by eternity, for ALL
-- inputs: the program's first complete hosting theorem.

/-- The frame's cargo. -/
def scW : SCTerm := .app .C .C

/-- The register complex `r · W`. -/
def scMof (r : SCTerm) : SCTerm := .app r scW

/-- The N-tower over a register. -/
def scNof (r : SCTerm) : Nat → SCTerm
  | 0 => scMof r
  | i + 1 => .app scW (scNof r i)

/-- **The prelude, register-generic**: nine fires from the frame to the triple. -/
theorem sc_frame_prelude (r : SCTerm) :
    RS.SC.StepsN 9 (scFrame r) (.app (.app (scMof r) (scMof r)) (scMof r)) :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) r (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (scMof r))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (scMof r)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scMof r) (.app (.app .C .C) (scMof r))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (scMof r)) (scMof r)
    (.app (.app .C .C) (scMof r)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scMof r) (.app (.app .C .C) (scMof r))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (scMof r)) (scMof r) (scMof r))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scMof r) (scMof r)))
  (RS.StepsN.tail (SCStep.C_red (scMof r) (scMof r) (scMof r))
  (@RS.StepsN.refl RS.SC (.app (.app (scMof r) (scMof r)) (scMof r))))))))))))

/-- **The strip**: `C` is flip. -/
theorem scStrip (m : Nat) (y z : SCTerm) :
    RS.SC.step (.app (.app (scParityReg (m + 1)) y) z)
      (.app (.app (scParityReg m) z) y) :=
  SCStep.C_red (scParityReg m) y z

/-- Even strip runs restore the argument order. -/
theorem scStripRun_even : ∀ (j : Nat) (y z : SCTerm),
    RS.SC.StepsN (2 * j) (.app (.app (scParityReg (2 * j)) y) z) (.app (.app .S y) z)
  | 0, _, _ => @RS.StepsN.refl RS.SC _
  | j + 1, y, z => by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by omega]
      exact RS.StepsN.tail (scStrip (2 * j + 1) y z)
        (RS.StepsN.tail (scStrip (2 * j) z y) (scStripRun_even j y z))

/-- Odd strip runs swap the arguments. -/
theorem scStripRun_odd (j : Nat) (y z : SCTerm) :
    RS.SC.StepsN (2 * j + 1) (.app (.app (scParityReg (2 * j + 1)) y) z)
      (.app (.app .S z) y) :=
  RS.StepsN.tail (scStrip (2 * j) y z) (scStripRun_even j z y)

/-- Registers are normal. -/
theorem scParityReg_normal : ∀ k, ∀ v, ¬ RS.SC.step (scParityReg k) v
  | 0, _, h => by cases h
  | k + 1, v, h => by
      obtain ⟨x', hx, _⟩ := scWrap_inv h
      exact scParityReg_normal k x' hx

theorem scW_normal : ∀ v, ¬ RS.SC.step scW v := fun _ h => by
  obtain ⟨x', hx, _⟩ := scWrap_inv h
  cases hx

/-- The register complex is normal. -/
theorem scM_normal : ∀ k, ∀ v, ¬ RS.SC.step (scMof (scParityReg k)) v
  | 0, v, h => by
      cases h with
      | appL h' => cases h'
      | appR h' => exact scW_normal _ h'
  | k + 1, v, h => by
      cases h with
      | appL h' => exact scParityReg_normal (k + 1) _ h'
      | appR h' => exact scW_normal _ h'

/-- Two-argument `C` pairs step only in their members. -/
theorem scCPair_inv {x y v : SCTerm}
    (h : RS.SC.step (SCTerm.app (SCTerm.app .C x) y) v) :
    (∃ x', RS.SC.step x x' ∧ v = .app (.app .C x') y) ∨
    (∃ y', RS.SC.step y y' ∧ v = .app (.app .C x) y') := by
  cases h with
  | appL h' =>
      obtain ⟨x', hx, rfl⟩ := scWrap_inv h'
      exact .inl ⟨x', hx, rfl⟩
  | appR h' => exact .inr ⟨_, h', rfl⟩

/-- The even normal form, parametric. -/
def scParityNfT (k : Nat) : SCTerm :=
  .app (.app .C (.app (.app .S scW) (scMof (scParityReg k)))) (scMof (scParityReg k))

theorem scParityNfT_normal (k : Nat) : ∀ v, ¬ RS.SC.step (scParityNfT k) v := by
  intro v h
  rcases scCPair_inv h with ⟨x', hx, _⟩ | ⟨y', hy, _⟩
  · rcases scPair_inv hx with ⟨a, ha, _⟩ | ⟨b, hb, _⟩
    · exact scW_normal a ha
    · exact scM_normal k b hb
  · exact scM_normal k y' hy

/-- **The even law**: `C^(2j) S` halts in `11 + 4j` fires, every j. -/
theorem sc_parity_even (j : Nat) :
    RS.SC.StepsN (11 + 4 * j) (scFrame (scParityReg (2 * j))) (scParityNfT (2 * j)) := by
  have hM : scMof (scParityReg (2 * j)) = .app (scParityReg (2 * j)) scW := rfl
  have h1 := sc_frame_prelude (scParityReg (2 * j))
  have h2 : RS.SC.StepsN (2 * j)
      (.app (.app (scMof (scParityReg (2 * j))) (scMof (scParityReg (2 * j))))
        (scMof (scParityReg (2 * j))))
      (.app (.app (.app .S scW) (scMof (scParityReg (2 * j))))
        (scMof (scParityReg (2 * j)))) :=
    scStepsN_appL _ (scStripRun_even j scW _)
  have h3 : RS.SC.StepsN (2 * j + 1 + 1)
      (.app (.app (.app .S scW) (scMof (scParityReg (2 * j))))
        (scMof (scParityReg (2 * j)))) (scParityNfT (2 * j)) :=
    RS.StepsN.tail (SCStep.S_red scW _ _)
      (RS.StepsN.tail (SCStep.C_red .C _
        (.app (scMof (scParityReg (2 * j))) (scMof (scParityReg (2 * j)))))
        (scStepsN_appL _ (scStepsN_appR .C (scStripRun_even j scW _))))
  have h := RS.StepsN.trans h1 (RS.StepsN.trans h2 h3)
  rw [show 11 + 4 * j = 9 + (2 * j + (2 * j + 1 + 1)) from by omega]
  exact h

/-- The odd orbit, parametric: `Φ = M N₁ N₂`. -/
def scParityOrbT (k : Nat) : SCTerm :=
  .app (.app (.app (scParityReg k) scW) (scNof (scParityReg k) 1))
    (scNof (scParityReg k) 2)

/-- **The odd cycle**: `Φ ⟶ᵏ⁺⁷ Φ` — k strips, one S-fire, six C-fires. -/
theorem sc_parity_cycle (j : Nat) :
    RS.SC.StepsN (2 * j + 8) (scParityOrbT (2 * j + 1)) (scParityOrbT (2 * j + 1)) := by
  have h1 : RS.SC.StepsN (2 * j + 1)
      (scParityOrbT (2 * j + 1))
      (.app (.app (.app .S (scNof (scParityReg (2 * j + 1)) 1)) scW) (scNof (scParityReg (2 * j + 1)) 2)) :=
    scStepsN_appL _ (scStripRun_odd j scW (scNof (scParityReg (2 * j + 1)) 1))
  have h2 : RS.SC.StepsN 7
      (.app (.app (.app .S (scNof (scParityReg (2 * j + 1)) 1)) scW) (scNof (scParityReg (2 * j + 1)) 2))
      (scParityOrbT (2 * j + 1)) :=
    RS.StepsN.tail (SCStep.S_red (scNof (scParityReg (2 * j + 1)) 1) scW (scNof (scParityReg (2 * j + 1)) 2))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scMof (scParityReg (2 * j + 1))) (scNof (scParityReg (2 * j + 1)) 2)))
    (RS.StepsN.tail (SCStep.C_red (scNof (scParityReg (2 * j + 1)) 2) (scMof (scParityReg (2 * j + 1))) (scNof (scParityReg (2 * j + 1)) 3))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scNof (scParityReg (2 * j + 1)) 1) (scNof (scParityReg (2 * j + 1)) 3)))
    (RS.StepsN.tail (SCStep.C_red (scNof (scParityReg (2 * j + 1)) 3) (scNof (scParityReg (2 * j + 1)) 1) (scMof (scParityReg (2 * j + 1))))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (scNof (scParityReg (2 * j + 1)) 2) (scMof (scParityReg (2 * j + 1)))))
    (RS.StepsN.tail (SCStep.C_red (scMof (scParityReg (2 * j + 1))) (scNof (scParityReg (2 * j + 1)) 2) (scNof (scParityReg (2 * j + 1)) 1))
    (@RS.StepsN.refl RS.SC (scParityOrbT (2 * j + 1)))))))))
  have h := RS.StepsN.trans h1 h2
  rw [show 2 * j + 8 = 2 * j + 1 + 7 from by omega]
  exact h

/-- **The odd entry**: `13 + 4j` fires from the frame to the orbit. -/
theorem sc_parity_entry (j : Nat) :
    RS.SC.StepsN (13 + 4 * j) (scFrame (scParityReg (2 * j + 1)))
      (scParityOrbT (2 * j + 1)) := by
  have h1 := sc_frame_prelude (scParityReg (2 * j + 1))
  have h2 : RS.SC.StepsN (2 * j + 1)
      (.app (.app (scMof (scParityReg (2 * j + 1))) (scMof (scParityReg (2 * j + 1)))) (scMof (scParityReg (2 * j + 1))))
      (.app (.app (.app .S (scMof (scParityReg (2 * j + 1)))) scW) (scMof (scParityReg (2 * j + 1)))) :=
    scStepsN_appL _ (scStripRun_odd j scW (scMof (scParityReg (2 * j + 1))))
  have h3 : RS.SC.StepsN 1
      (.app (.app (.app .S (scMof (scParityReg (2 * j + 1)))) scW) (scMof (scParityReg (2 * j + 1))))
      (.app (.app (scMof (scParityReg (2 * j + 1))) (scMof (scParityReg (2 * j + 1)))) (scNof (scParityReg (2 * j + 1)) 1)) :=
    RS.StepsN.tail (SCStep.S_red (scMof (scParityReg (2 * j + 1))) scW (scMof (scParityReg (2 * j + 1)))) (@RS.StepsN.refl RS.SC _)
  have h4 : RS.SC.StepsN (2 * j + 1)
      (.app (.app (scMof (scParityReg (2 * j + 1))) (scMof (scParityReg (2 * j + 1)))) (scNof (scParityReg (2 * j + 1)) 1))
      (.app (.app (.app .S (scMof (scParityReg (2 * j + 1)))) scW) (scNof (scParityReg (2 * j + 1)) 1)) :=
    scStepsN_appL _ (scStripRun_odd j scW (scMof (scParityReg (2 * j + 1))))
  have h5 : RS.SC.StepsN 1
      (.app (.app (.app .S (scMof (scParityReg (2 * j + 1)))) scW) (scNof (scParityReg (2 * j + 1)) 1)) (scParityOrbT (2 * j + 1)) :=
    RS.StepsN.tail (SCStep.S_red (scMof (scParityReg (2 * j + 1))) scW (scNof (scParityReg (2 * j + 1)) 1)) (@RS.StepsN.refl RS.SC _)
  have h := RS.StepsN.trans h1 (RS.StepsN.trans h2 (RS.StepsN.trans h3
    (RS.StepsN.trans h4 h5)))
  rw [show 13 + 4 * j = 9 + (2 * j + 1 + (1 + (2 * j + 1 + 1))) from by omega]
  exact h

/-- **C9, proved — the frame parity law**: for every `k`, the frame on the unary numeral
`C^k S` reaches a normal form when `k` is even and admits runs of unbounded length when
`k` is odd. Parity, decided by eternity, for all inputs. -/
theorem sc_frame_parity_law :
    (∀ j, RS.SC.Steps (scFrame (scParityReg (2 * j))) (scParityNfT (2 * j)) ∧
      ∀ v, ¬ RS.SC.step (scParityNfT (2 * j)) v) ∧
    (∀ j, RS.SC.Steps (scFrame (scParityReg (2 * j + 1))) (scParityOrbT (2 * j + 1)) ∧
      ∀ n, ∃ m, n ≤ m ∧
        RS.SC.StepsN m (scParityOrbT (2 * j + 1)) (scParityOrbT (2 * j + 1))) :=
  ⟨fun j => ⟨RS.StepsN.toSteps (sc_parity_even j), scParityNfT_normal (2 * j)⟩,
   fun j => ⟨RS.StepsN.toSteps (sc_parity_entry j),
     sc_cycle_unbounded (by omega) (sc_parity_cycle j)⟩⟩

-- ## Stage 193: the wrapper ISA — C reads, `C C` calls
-- C9 showed the `C`-wrapper READS a numeral (parity by flips). This stage pins the other
-- wrapper: `C C` EXECUTES. For EVERY register `r`, thirteen fires take the frame on the
-- wrapped register `W r` to `r X X` with `X = (W r) W` — THE HANDOFF: the machine
-- transfers control to its own register, applied to two copies of its wrapped complex.
-- What happens next is the register's choice of program: executing the dead atom `S`
-- halts in two more fires at a 9-leaf normal form (the shield); executing the duplicator
-- locks into a period-9 orbit forever. The frame is an interpreter and the wrapper is its
-- instruction set — one layer of `C` means read, two mean call.

/-- The executed complex: `(W r) W`. -/
def scXof (r : SCTerm) : SCTerm := .app (.app scW r) scW

/-- **The handoff**: thirteen fires from the frame on `W r` to `r X X`, every register. -/
theorem sc_frame_handoff (r : SCTerm) :
    RS.SC.StepsN 13 (scFrame (.app scW r))
      (.app (.app r (scXof r)) (scXof r)) :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .C .C) r) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C))) (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) r) (.app .C .C))) (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app (.app .C .C) r) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app (.app .C .C) r) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app (.app .C .C) r) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C r (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) r (.app (.app (.app .C .C) r) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) r) (.app .C .C)) r))
  (RS.StepsN.tail (SCStep.C_red r (.app (.app (.app .C .C) r) (.app .C .C)) (.app (.app (.app .C .C) r) (.app .C .C)))
  (@RS.StepsN.refl RS.SC (.app (.app r (scXof r)) (scXof r))))))))))))))))

/-- The shield: executing the dead atom halts — 15 fires to a 9-leaf normal form. -/
def scShieldNf : SCTerm :=
  .app (.app .S (.app (.app .C (.app .C .C)) .S)) (.app (.app .C (.app .C .C)) .S)

theorem sc_frame_shield : RS.SC.StepsN 15 (scFrame (.app scW .S)) scShieldNf :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .C .C) .S) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C))) (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) .S) (.app .C .C))) (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) .S (.app (.app (.app .C .C) .S) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) .S) (.app .C .C)) .S))
  (RS.StepsN.tail (SCStep.C_red .S (.app (.app (.app .C .C) .S) (.app .C .C)) (.app (.app (.app .C .C) .S) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appR (SCStep.C_red .C .S (.app .C .C))))
  (RS.StepsN.tail (SCStep.appR (SCStep.C_red .C .S (.app .C .C)))
  (@RS.StepsN.refl RS.SC scShieldNf))))))))))))))))

theorem scShieldNf_normal : ∀ v, ¬ RS.SC.step scShieldNf v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scShieldNf = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

/-- Executing the duplicator: the period-9 orbit. -/
def scExecOrb : SCTerm := (.app (.app (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))) (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C)))) (.app (.app (.app .C .C) scDup) (.app .C .C)))

theorem sc_exec_entry : RS.SC.StepsN 5 (scFrame (.app scW scDup)) scExecOrb :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .C .C) scDup) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))) (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scExecOrb))))))

theorem sc_exec_cycle : RS.SC.StepsN 9 scExecOrb scExecOrb :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))) (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app (.app .C .C) scDup) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app (.app .C .C) scDup) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app (.app .C .C) scDup) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C scDup (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) scDup (.app (.app (.app .C .C) scDup) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) scDup) (.app .C .C)) scDup))
  (RS.StepsN.tail (SCStep.C_red scDup (.app (.app (.app .C .C) scDup) (.app .C .C)) (.app (.app (.app .C .C) scDup) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) scDup) (.app .C .C))))
  (@RS.StepsN.refl RS.SC scExecOrb))))))))))

/-- **The ISA theorem**: one frame, one wrapper depth apart — the dead register's
execution halts, the duplicator's runs forever. -/
theorem sc_wrapper_isa :
    (RS.SC.StepsN 15 (scFrame (.app scW .S)) scShieldNf ∧
      ∀ v, ¬ RS.SC.step scShieldNf v) ∧
    (RS.SC.StepsN 5 (scFrame (.app scW scDup)) scExecOrb ∧
      ∀ n, ∃ m, n ≤ m ∧ RS.SC.StepsN m scExecOrb scExecOrb) :=
  ⟨⟨sc_frame_shield, scShieldNf_normal⟩,
   ⟨sc_exec_entry, sc_cycle_unbounded (by omega) sc_exec_cycle⟩⟩

-- ## Stage 194: the omega instruction — the frame compiles self-application
-- The wrapper algebra's third instruction, and the deepest: the word `W·C·W` takes the
-- frame to NAKED SELF-APPLICATION. For every register `r`, thirty fires take
-- `scFrame (W (C (W r)))` to `r r r` — no residue, no shell, the register applied to
-- itself twice. The interpreter doesn't just read (C) or call (W): composed, its
-- instructions COMPILE the ω-shape, the seed of all self-referential dynamics. At
-- `r = scDup` the output is verbatim `scDup scDup scDup` — the Stage 151 generation-loop
-- seed — so the compiled program composes straight into a pinned eternal cycle: frame to
-- omega in 30, omega to loop in 3, loop forever in 5s.

/-- The omega word: `W (C (W r))`. -/
def scOmegaWord (r : SCTerm) : SCTerm := .app scW (.app .C (.app scW r))

/-- **The omega instruction**: thirty fires from the frame to `r r r`, every register. -/
theorem sc_frame_omega (r : SCTerm) :
    RS.SC.StepsN 30 (scFrame (scOmegaWord r)) (.app (.app r r) r) :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) r)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app .C (.app (.app .C .C) r))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) r)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) r) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C r (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) r (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) r)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) (.app .C (.app (.app .C .C) r))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) r)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) r)
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) r) r (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C r (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) r))) (.app .C .C)) r r)
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) r)) r))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C r (.app .C (.app (.app .C .C) r))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) r)) r r)
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) r) r r)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C r r))
  (RS.StepsN.tail (SCStep.C_red r r r)
  (@RS.StepsN.refl RS.SC (.app (.app r r) r))))))))))))))))))))))))))))))))

/-- The compiled duplicator enters the generation loop: frame to eternal cycle. -/
theorem sc_omega_to_loop :
    RS.SC.Steps (scFrame (scOmegaWord scDup)) scGenLoop :=
  RS.Steps.trans (RS.StepsN.toSteps (sc_frame_omega scDup)) sc_empty_to_loop

/-- ...and therefore runs of unbounded length. -/
theorem sc_omega_unbounded :
    ∀ n, ∃ m, n ≤ m ∧ RS.SC.StepsN m scGenLoop scGenLoop :=
  sc_cycle_unbounded (by omega) sc_generation_cycle

-- ## Stage 195: the addressed fetch — a numeral decides who runs
-- Composing the three proved instructions closes the hosting loop: for the register
-- `C^m · p` (a numeral APPLIED to a payload), the wrapped frame hands off in thirteen
-- fires, the numeral strips sort `p` against the dead complex `X` by parity, and one
-- S-fire dispatches: EVEN address — the payload takes control (`p X (X X)`); ODD address
-- — the dead complex runs and the payload is parked as cargo (`X X (p X)`). The numeral
-- is an INSTRUCTION POINTER: it decides which term becomes the program. Fetch, decode
-- (by parity), execute — all axiom-free, all parametric, assembled without a single new
-- fire from `sc_frame_handoff` and the strip runs of C9.

/-- **Even dispatch**: address `2j` gives the payload control. -/
theorem sc_dispatch_even (j : Nat) (p : SCTerm) :
    RS.SC.StepsN (14 + 2 * j)
      (scFrame (.app scW (.app (scParityReg (2 * j)) p)))
      (.app (.app p (scXof (.app (scParityReg (2 * j)) p)))
        (.app (scXof (.app (scParityReg (2 * j)) p))
          (scXof (.app (scParityReg (2 * j)) p)))) := by
  have h1 := sc_frame_handoff (.app (scParityReg (2 * j)) p)
  have h2 : RS.SC.StepsN (2 * j)
      (.app (.app (.app (scParityReg (2 * j)) p)
        (scXof (.app (scParityReg (2 * j)) p)))
        (scXof (.app (scParityReg (2 * j)) p)))
      (.app (.app (.app .S p) (scXof (.app (scParityReg (2 * j)) p)))
        (scXof (.app (scParityReg (2 * j)) p))) :=
    scStepsN_appL _ (scStripRun_even j p _)
  have h3 := RS.StepsN.tail
    (SCStep.S_red p (scXof (.app (scParityReg (2 * j)) p))
      (scXof (.app (scParityReg (2 * j)) p)))
    (@RS.StepsN.refl RS.SC
      (.app (.app p (scXof (.app (scParityReg (2 * j)) p)))
        (.app (scXof (.app (scParityReg (2 * j)) p))
          (scXof (.app (scParityReg (2 * j)) p)))))
  have h := RS.StepsN.trans h1 (RS.StepsN.trans h2 h3)
  rw [show 14 + 2 * j = 13 + (2 * j + 1) from by omega]
  exact h

/-- **Odd dispatch**: address `2j + 1` parks the payload and runs the dead complex. -/
theorem sc_dispatch_odd (j : Nat) (p : SCTerm) :
    RS.SC.StepsN (15 + 2 * j)
      (scFrame (.app scW (.app (scParityReg (2 * j + 1)) p)))
      (.app (.app (scXof (.app (scParityReg (2 * j + 1)) p))
          (scXof (.app (scParityReg (2 * j + 1)) p)))
        (.app p (scXof (.app (scParityReg (2 * j + 1)) p)))) := by
  have h1 := sc_frame_handoff (.app (scParityReg (2 * j + 1)) p)
  have h2 : RS.SC.StepsN (2 * j + 1)
      (.app (.app (.app (scParityReg (2 * j + 1)) p)
        (scXof (.app (scParityReg (2 * j + 1)) p)))
        (scXof (.app (scParityReg (2 * j + 1)) p)))
      (.app (.app (.app .S (scXof (.app (scParityReg (2 * j + 1)) p))) p)
        (scXof (.app (scParityReg (2 * j + 1)) p))) :=
    scStepsN_appL _ (scStripRun_odd j p _)
  have h3 := RS.StepsN.tail
    (SCStep.S_red (scXof (.app (scParityReg (2 * j + 1)) p)) p
      (scXof (.app (scParityReg (2 * j + 1)) p)))
    (@RS.StepsN.refl RS.SC _)
  have h := RS.StepsN.trans h1 (RS.StepsN.trans h2 h3)
  rw [show 15 + 2 * j = 13 + (2 * j + 1 + 1) from by omega]
  exact h

/-- **The addressed fetch**: one machine shape; the numeral address decides, by parity,
whether the payload becomes the program or the cargo. -/
theorem sc_addressed_fetch (j : Nat) (p : SCTerm) :
    (∃ u, RS.SC.Steps (scFrame (.app scW (.app (scParityReg (2 * j)) p))) u ∧
      ∃ y, u = .app (.app p y) (.app y y)) ∧
    (∃ u, RS.SC.Steps (scFrame (.app scW (.app (scParityReg (2 * j + 1)) p))) u ∧
      ∃ y, u = .app (.app y y) (.app p y)) :=
  ⟨⟨_, RS.StepsN.toSteps (sc_dispatch_even j p), _, rfl⟩,
   ⟨_, RS.StepsN.toSteps (sc_dispatch_odd j p), _, rfl⟩⟩

-- ## Stage 197: machines beget machines — the gene
-- The sequencer exists, and its engine is a 14-leaf payload best called a GENE:
-- `scGene t = C (cell FH) (cell t)` — one cell holding the frame head, one holding the
-- child's register. Addressed at zero and dispatched, the gene EXPRESSES: nine fires
-- emit the fate-seed `(cell FH)(cell t)(cell t)` with two riders, and six pop fires
-- assemble the child `FH t t` in place — `sc_reproduction`, fully parametric in `t`.
-- At `t = W` the child is verbatim `scFrame scW`: twenty-nine kernel fires take a
-- STANDARD ADDRESSED FRAME to a STANDARD FRAME with stack riders (`sc_machines_beget`).
-- Fetch → express → assemble → re-enter. The riders tell the story too: R1 is an
-- unfinished frame (`FH (W t)`, a head awaiting cargo), R2 the spent executed complexes.
-- Machines beget machines, and the parent chooses the child's register.

/-- The gene: frame head in one cell, the child's register in the other. -/
def scGene (t : SCTerm) : SCTerm :=
  .app (.app .C (.app scW (.app .S (.app .S scDup)))) (.app scW t)

/-- The pop, step-counted (six fires — the Stage 156 law transcribed to `StepsN`). -/
theorem scCellArm_popN (X A B : SCTerm) :
    RS.SC.StepsN 6
      (.app (.app (.app (.app .C .C) X) (.app (.app .C .C) A)) (.app (.app .C .C) B))
      (.app (.app X A) B) :=
  RS.StepsN.tail (SCStep.appL (SCStep.C_red .C X (.app (.app .C .C) A)))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) A) X (.app (.app .C .C) B))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C A (.app (.app .C .C) B)))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) B) A X)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C B X))
  (RS.StepsN.tail (SCStep.C_red X B A)
  (@RS.StepsN.refl RS.SC (.app (.app X A) B)))))))

/-- Rider one: an unfinished frame — the head awaiting its cargo. -/
def scRider1 (t : SCTerm) : SCTerm := .app (.app .S (.app .S scDup)) (.app scW t)

/-- Rider two: the spent executed complexes. -/
def scRider2 (t : SCTerm) : SCTerm :=
  .app (scXof (.app .S (scGene t))) (scXof (.app .S (scGene t)))

/-- **Gene expression**: nine fires from the dispatch product to seed-plus-riders. -/
theorem sc_gene_express (t : SCTerm) :
    RS.SC.StepsN 9
      (.app (.app (scGene t) (scXof (.app .S (scGene t))))
        (.app (scXof (.app .S (scGene t))) (scXof (.app .S (scGene t)))))
      (.app (.app (.app (.app (.app (.app .C .C) (.app .S (.app .S scDup)))
          (.app (.app .C .C) t)) (.app (.app .C .C) t))
        (scRider1 t)) (scRider2 t)) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .S (.app .S scDup))) (.app (.app .C .C) t) (.app (.app (.app .C .C) (.app .S (scGene t))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .S (.app .S scDup)) (.app (.app (.app .C .C) (.app .S (scGene t))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app (.app .C .C) (.app .S (scGene t))) (.app .C .C)) (.app .S (.app .S scDup)) (.app (.app .C .C) t)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .S (scGene t)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) (.app .S (scGene t)) (.app (.app .C .C) t))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .C .C) t) (.app .S (scGene t)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .S (scGene t)) (.app (.app .C .C) t) (.app .S (.app .S scDup))))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (scGene t) (.app .S (.app .S scDup)) (.app (.app .C .C) t)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .S (.app .S scDup))) (.app (.app .C .C) t) (.app (.app .C .C) t))))
  (@RS.StepsN.refl RS.SC _))))))))))

/-- **Reproduction**: twenty-nine fires from the addressed parent to the assembled child
`FH t t` with stack riders — the parent's gene chooses the child's register. -/
theorem sc_reproduction (t : SCTerm) :
    RS.SC.StepsN 29 (scFrame (.app scW (.app .S (scGene t))))
      (.app (.app (.app (.app (.app .S (.app .S scDup)) t) t) (scRider1 t))
        (scRider2 t)) := by
  have h1 := sc_dispatch_even 0 (scGene t)
  have h2 := sc_gene_express t
  have h3 : RS.SC.StepsN 6
      (.app (.app (.app (.app (.app (.app .C .C) (.app .S (.app .S scDup)))
          (.app (.app .C .C) t)) (.app (.app .C .C) t))
        (scRider1 t)) (scRider2 t))
      (.app (.app (.app (.app (.app .S (.app .S scDup)) t) t) (scRider1 t))
        (scRider2 t)) :=
    scStepsN_appL _ (scStepsN_appL _ (scCellArm_popN (.app .S (.app .S scDup)) t t))
  have h := RS.StepsN.trans h1 (RS.StepsN.trans h2 h3)
  rw [show 29 = 14 + 2 * 0 + (9 + 6) from by omega]
  exact h

/-- **Machines beget machines**: at `t = W` the child is verbatim the standard frame —
twenty-nine kernel fires from one addressed machine to another, riders as stack. -/
theorem sc_machines_beget :
    RS.SC.StepsN 29 (scFrame (.app scW (.app .S (scGene scW))))
      (.app (.app (scFrame scW) (scRider1 scW)) (scRider2 scW)) :=
  sc_reproduction scW

-- ## Stage 198: the dynasty — lineage, parametric and iterated
-- The verbatim machine-quine is impossible for single-slot genes (child register = child
-- cargo, but an addressed parent needs register ≠ cargo) and probe-dead over 2,143
-- payloads. The three-cell gene dissolves the obstruction: `scGene2 q` holds the frame
-- head, the cargo `W`, and the child's WHOLE ADDRESSED REGISTER `W (S q)` in separate
-- cells. One C-fire orders the cells, six pop fires assemble — and the child is the
-- addressed parent WITH PAYLOAD `q`: `sc_lineage`, twenty-one fires, fully parametric.
-- Iterating the gene iterates the machine: `sc_dynasty` — for every n, the generation-n
-- ancestor `scParent (scGene2ⁿ q)` reduces to a term carrying the FOUNDER `scParent q`
-- in head position, n rider-stacks deep. Not a quine: a genealogy — each generation a
-- real addressed machine, each begetting the next, kernel-certified to any depth.

/-- The addressed parent: the frame fetching payload `p` at address zero. -/
def scParent (p : SCTerm) : SCTerm := scFrame (.app scW (.app .S p))

/-- The three-cell gene: frame head, cargo, and the child's addressed register. -/
def scGene2 (q : SCTerm) : SCTerm :=
  .app (.app (.app .C (.app scW (.app .S (.app .S scDup)))) (.app scW scW))
    (.app scW (.app scW (.app .S q)))

/-- **The lineage law**: twenty-one fires take the parent of `scGene2 q` to the parent
of `q`, riders as stack. -/
theorem sc_lineage (q : SCTerm) :
    RS.SC.StepsN 21 (scParent (scGene2 q))
      (.app (.app (scParent q) (scXof (.app .S (scGene2 q))))
        (.app (scXof (.app .S (scGene2 q))) (scXof (.app .S (scGene2 q))))) := by
  have h1 := sc_dispatch_even 0 (scGene2 q)
  have h2 : RS.SC.StepsN 7
      (.app (.app (scGene2 q) (scXof (.app .S (scGene2 q))))
        (.app (scXof (.app .S (scGene2 q))) (scXof (.app .S (scGene2 q)))))
      (.app (.app (scParent q) (scXof (.app .S (scGene2 q))))
        (.app (scXof (.app .S (scGene2 q))) (scXof (.app .S (scGene2 q))))) :=
    RS.StepsN.tail
      (SCStep.appL (SCStep.appL (SCStep.C_red (.app scW (.app .S (.app .S scDup)))
        (.app scW scW) (.app scW (.app scW (.app .S q))))))
      (scStepsN_appL _ (scStepsN_appL _
        (scCellArm_popN (.app .S (.app .S scDup)) (.app scW (.app .S q)) scW)))
  have h := RS.StepsN.trans h1 h2
  rw [show 21 = 14 + 2 * 0 + 7 from by omega]
  exact h

/-- Generation-n genes. -/
def scGene2Iter : Nat → SCTerm → SCTerm
  | 0, q => q
  | n + 1, q => scGene2 (scGene2Iter n q)

/-- "Carries in head position": the founder as spine prefix. -/
inductive scUnder (pre : SCTerm) : SCTerm → Prop
  | refl : scUnder pre pre
  | app {t x : SCTerm} : scUnder pre t → scUnder pre (.app t x)

/-- **The dynasty**: every generation-n ancestor reduces to a term carrying the founder
in head position — machines beget machines to any depth. -/
theorem sc_dynasty : ∀ (n : Nat) (q : SCTerm),
    ∃ u, RS.SC.Steps (scParent (scGene2Iter n q)) u ∧ scUnder (scParent q) u
  | 0, q => ⟨scParent q, @RS.Steps.refl RS.SC (scParent q), scUnder.refl⟩
  | n + 1, q => by
      obtain ⟨u, hu, hunder⟩ := sc_dynasty n q
      refine ⟨.app (.app u (scXof (.app .S (scGene2 (scGene2Iter n q)))))
        (.app (scXof (.app .S (scGene2 (scGene2Iter n q))))
          (scXof (.app .S (scGene2 (scGene2Iter n q))))), ?_, ?_⟩
      · exact RS.Steps.trans (RS.StepsN.toSteps (sc_lineage (scGene2Iter n q)))
          (scSteps_appL _ (scSteps_appL _ hu))
      · exact scUnder.app (scUnder.app hunder)

-- ## Stage 199: the branch — the payload's numeral selects the successor
-- Lineage passes payloads verbatim; control flow needs a CHOICE. The branch is the
-- dispatch applied to a numeral-headed payload `C^k · y · z`: the fetch hands off, the
-- payload's own strips sort `y` against `z` by the parity of `k`, and one more S-fire
-- gives control to the selected sub-payload — `y X (z X) (X X)` for even `k`,
-- `z X (y X) (X X)` for odd. Zero new fires: fetch + strip runs + one S_red. Composed
-- with the gene, reproduction becomes CONDITIONAL: a parent whose gene carries
-- `C^k g₁ g₂` begets a child that executes gene one or gene two by the numeral's parity
-- — the machine tree forks, and the numeral is the branch condition.

/-- **Even branch**: `C^(2j) y z` gives `y` control. -/
theorem sc_branch_even (j : Nat) (y z : SCTerm) :
    RS.SC.StepsN (15 + 2 * j)
      (scParent (.app (.app (scParityReg (2 * j)) y) z))
      (.app (.app (.app y (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z))))
          (.app z (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z))))) := by
  have h1 := sc_dispatch_even 0 (.app (.app (scParityReg (2 * j)) y) z)
  have h2 : RS.SC.StepsN (2 * j + 1)
      (.app (.app (.app (.app (scParityReg (2 * j)) y) z)
          (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))))
      (.app (.app (.app y (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z))))
          (.app z (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j)) y) z))))) :=
    scStepsN_appL _ (RS.StepsN.trans (scStepsN_appL _ (scStripRun_even j y z))
      (RS.StepsN.tail (SCStep.S_red y z _) (@RS.StepsN.refl RS.SC _)))
  have h := RS.StepsN.trans h1 h2
  rw [show 15 + 2 * j = 14 + 2 * 0 + (2 * j + 1) from by omega]
  exact h

/-- **Odd branch**: `C^(2j+1) y z` gives `z` control. -/
theorem sc_branch_odd (j : Nat) (y z : SCTerm) :
    RS.SC.StepsN (16 + 2 * j)
      (scParent (.app (.app (scParityReg (2 * j + 1)) y) z))
      (.app (.app (.app z (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z))))
          (.app y (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z))))) := by
  have h1 := sc_dispatch_even 0 (.app (.app (scParityReg (2 * j + 1)) y) z)
  have h2 : RS.SC.StepsN (2 * j + 1 + 1)
      (.app (.app (.app (.app (scParityReg (2 * j + 1)) y) z)
          (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))))
      (.app (.app (.app z (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z))))
          (.app y (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))))
        (.app (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z)))
          (scXof (.app .S (.app (.app (scParityReg (2 * j + 1)) y) z))))) :=
    scStepsN_appL _ (RS.StepsN.trans (scStepsN_appL _ (scStripRun_odd j y z))
      (RS.StepsN.tail (SCStep.S_red z y _) (@RS.StepsN.refl RS.SC _)))
  have h := RS.StepsN.trans h1 h2
  rw [show 16 + 2 * j = 14 + 2 * 0 + (2 * j + 1 + 1) from by omega]
  exact h

/-- **Conditional reproduction**: a parent whose gene carries `C^k g₁ g₂` begets a child
that gives control to gene one or gene two by the numeral's parity — the machine tree
forks on a numeral. -/
theorem sc_conditional_dynasty (j : Nat) (g₁ g₂ : SCTerm) :
    ∃ u, RS.SC.Steps
      (scParent (scGene2 (.app (.app (scParityReg (2 * j)) g₁) g₂))) u ∧
      scUnder (.app g₁ (scXof (.app .S (.app (.app (scParityReg (2 * j)) g₁) g₂)))) u := by
  refine ⟨_, RS.Steps.trans (RS.StepsN.toSteps
    (sc_lineage (.app (.app (scParityReg (2 * j)) g₁) g₂)))
    (scSteps_appL _ (scSteps_appL _ (RS.StepsN.toSteps (sc_branch_even j g₁ g₂)))), ?_⟩
  exact scUnder.app (scUnder.app (scUnder.app (scUnder.app scUnder.refl)))

-- ## Stage 200: the tape — a word, read one symbol per generation
-- The hosting construction the ISA was assembled for. A word over {even, odd} is encoded
-- as NESTED BRANCH-GENES — linear size, one gene per symbol — and the machine reads it
-- symbol by symbol across generations: each generation fetches, branches on the current
-- symbol's numeral, and (on even) the next gene takes control and begets the next
-- machine; on odd, the dead atom takes the head and the machine parks. Twenty-two fires
-- per symbol, kernel-certified for every word and every payload. Three lemmas carry it:
-- the gene fires ANYWHERE (`sc_gene_anywhere` — position independence, seven fires), the
-- body induction (`sc_tapeBody_run`), and the top-level entry via lineage. The founder
-- machine `scParent q` arrives in head position after the whole tape is consumed:
-- `sc_tape_run`. This is a read-once tape driven through an addressed machine — the
-- tag-hosting engine's chassis, running.

/-- The gene is position-independent: applied to ANY two arguments, seven fires beget
the child in place, arguments as riders. -/
theorem sc_gene_anywhere (q a b : SCTerm) :
    RS.SC.StepsN 7 (.app (.app (scGene2 q) a) b) (.app (.app (scParent q) a) b) :=
  RS.StepsN.tail
    (SCStep.appL (SCStep.appL (SCStep.C_red (.app scW (.app .S (.app .S scDup)))
      (.app scW scW) (.app scW (.app scW (.app .S q))))))
    (scStepsN_appL _ (scStepsN_appL _
      (scCellArm_popN (.app .S (.app .S scDup)) (.app scW (.app .S q)) scW)))

/-- The tape body: a word as nested branch-genes over a final payload. -/
def scTapeBody : List Bool → SCTerm → SCTerm
  | [], q => q
  | b :: w, q =>
      .app (.app (scParityReg (cond b 1 0)) (scGene2 (scTapeBody w q))) .S

/-- The tape machine: the addressed gene of the whole word. -/
def scTape (w : List Bool) (q : SCTerm) : SCTerm := scGene2 (scTapeBody w q)

/-- The body induction: an all-even word is consumed generation by generation, and the
founder arrives in head position. -/
theorem sc_tapeBody_run : ∀ (w : List Bool) (q : SCTerm), (∀ b ∈ w, b = false) →
    ∃ u, RS.SC.Steps (scParent (scTapeBody w q)) u ∧ scUnder (scParent q) u
  | [], q, _ => ⟨scParent q, @RS.Steps.refl RS.SC (scParent q), scUnder.refl⟩
  | b :: w, q, hall => by
      have hb : b = false := hall b List.mem_cons_self
      subst hb
      obtain ⟨u, hu, hunder⟩ := sc_tapeBody_run w q
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      have h1 := sc_branch_even 0 (scGene2 (scTapeBody w q)) .S
      have h2 := sc_gene_anywhere (scTapeBody w q)
        (scXof (.app .S (.app (.app (scParityReg 0)
          (scGene2 (scTapeBody w q))) .S)))
        (.app .S (scXof (.app .S (.app (.app (scParityReg 0)
          (scGene2 (scTapeBody w q))) .S))))
      have hsteps := RS.Steps.trans (RS.StepsN.toSteps h1)
          (RS.Steps.trans (scSteps_appL _ (RS.StepsN.toSteps h2))
            (scSteps_appL _ (scSteps_appL _ (scSteps_appL _ hu))))
      exact ⟨_, hsteps, scUnder.app (scUnder.app (scUnder.app hunder))⟩

/-- **The tape runs**: for every all-even word and every payload, the tape machine
consumes the word across generations and delivers the founder in head position. -/
theorem sc_tape_run (w : List Bool) (q : SCTerm) (hall : ∀ b ∈ w, b = false) :
    ∃ u, RS.SC.Steps (scParent (scTape w q)) u ∧ scUnder (scParent q) u := by
  obtain ⟨u, hu, hunder⟩ := sc_tapeBody_run w q hall
  have hsteps := RS.Steps.trans (RS.StepsN.toSteps (sc_lineage (scTapeBody w q)))
      (scSteps_appL _ (scSteps_appL _ hu))
  exact ⟨_, hsteps, scUnder.app (scUnder.app hunder)⟩

/-- **The tape stops**: an odd first symbol parks the machine — the dead atom takes the
head. -/
theorem sc_tape_stop (w : List Bool) (q : SCTerm) :
    ∃ u x y, RS.SC.Steps (scParent (scTape (true :: w) q)) u ∧
      scUnder (.app (.app .S x) y) u := by
  have h1 := sc_lineage (scTapeBody (true :: w) q)
  have h2 := sc_branch_odd 0 (scGene2 (scTapeBody w q)) .S
  have hsteps := RS.Steps.trans (RS.StepsN.toSteps h1)
    (scSteps_appL _ (scSteps_appL _ (RS.StepsN.toSteps h2)))
  exact ⟨_, _, _, hsteps,
    scUnder.app (scUnder.app (scUnder.app scUnder.refl))⟩

-- ## Stage 201: the successor — numerals are writable after all
-- Bits are sources (Stage 185): no fire produces an atom or `C C`. But numerals GROW:
-- `S_red` with middle argument `C` wraps one more `C` around anything — the only
-- mechanism in the calculus that extends a C-chain, and it is a COMPUTED write. Three
-- laws, each a constructor or two: the successor (`S f C · r ⟶ (f r)(C r)` — the
-- incremented numeral minted as an argument, any continuation `f`); the double increment
-- (`S (C C) C · r ⟶² (C² r) r` — parity-preserving, the old numeral kept as cargo); and
-- the routed successor (`S (C y) C · r ⟶² (y (C r)) r` — the continuation RECEIVES the
-- incremented numeral in operator position, ready to branch). Write-back is no longer
-- missing: a generation can compute its child's symbol. The tape (200) reads; the
-- successor writes; the gene copies. Tag hosting's parts list is complete.

/-- **The successor**: one fire mints `C r` beside the continuation. -/
theorem sc_successor (f r : SCTerm) :
    RS.SC.step (.app (.app (.app .S f) .C) r) (.app (.app f r) (.app .C r)) :=
  SCStep.S_red f .C r

/-- **The double increment**: two fires, parity preserved, old numeral kept. -/
theorem sc_double_increment (r : SCTerm) :
    RS.SC.StepsN 2 (.app (.app (.app .S (.app .C .C)) .C) r)
      (.app (.app .C (.app .C r)) r) :=
  RS.StepsN.tail (SCStep.S_red (.app .C .C) .C r)
  (RS.StepsN.tail (SCStep.C_red .C r (.app .C r))
  (@RS.StepsN.refl RS.SC (.app (.app .C (.app .C r)) r)))

/-- **The routed successor**: the continuation receives the incremented numeral in
operator position, the old numeral as cargo. -/
theorem sc_routed_successor (y r : SCTerm) :
    RS.SC.StepsN 2 (.app (.app (.app .S (.app .C y)) .C) r)
      (.app (.app y (.app .C r)) r) :=
  RS.StepsN.tail (SCStep.S_red (.app .C y) .C r)
  (RS.StepsN.tail (SCStep.C_red y r (.app .C r))
  (@RS.StepsN.refl RS.SC (.app (.app y (.app .C r)) r)))

/-- Numeral form: the successor of `C^k S` is `C^(k+1) S`, on the nose. -/
theorem sc_successor_numeral (f : SCTerm) (k : Nat) :
    RS.SC.step (.app (.app (.app .S f) .C) (scParityReg k))
      (.app (.app f (scParityReg k)) (scParityReg (k + 1))) :=
  sc_successor f (scParityReg k)

-- ## Stage 203: the second n=12 mountain — excess 69
-- The random phase of the n=12 census plateaued at a witness the graft neighborhood
-- missed: a 12-leaf term whose fully forced 400-step prefix peaks at 87 leaves (step 143)
-- and descends to 19, one checked step from an 18-leaf off-prefix target. A different
-- kind of mountain from Stage 187's: modest peak, tiny endpoint — excess 69, the
-- program's highest. The ladder gains a second n=12 point: f(12,18) ≥ 87 beside
-- f(12,234) ≥ 291. Excess by n now reads 12, 44, 69 — worse than tripling per two
-- leaves on the best-witness line.

/-- Twelve leaves: the census's excess champion. -/
def scMt6T : SCTerm :=
  .app (.app (.app (.app .C .S) (.app .C .C)) (.app (.app .S .S) .C))
    (.app (.app .C (.app (.app .S .S) .S)) .C)

/-- Eighteen leaves, one checked step past the 400-step forced prefix. -/
def scMt6U : SCTerm :=
  .app (.app (.app (.app (.app (.app .S .S) .S) (.app (.app .S .C) .C)) .C)
    (.app .C (.app (.app .C (.app (.app .S .S) .S)) .C)))
    (.app (.app .C (.app (.app .S .S) .S)) .C)

/-- The witnessing path: the full forced march, then one checked step. -/
def scMt6Path : List SCTerm := scForcedMarch scMt6T 400 ++ [scMt6U]

section
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

#guard scMt6T.leafCount = 12
#guard scMt6U.leafCount = 18
#guard (scForcedMarch scMt6T 400).length = 400

/-- The crossing exists. -/
theorem scMt6_steps : RS.SC.Steps scMt6T scMt6U :=
  scChained_steps scMt6Path scMt6T scMt6U (by decide) (by decide)

/-- **The excess champion**: no path from 12 leaves to 18 leaves stays within 86. -/
theorem scMt6_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 86 scMt6T scMt6U :=
  scForced_mountain (scForcedMarch scMt6T 400) (scForcedMarch_forced 400 scMt6T)
    (by decide) (by decide)

end

/-- **The second n=12 floor**: every valid bounding function clears 87 at (12, 18). -/
theorem sc_bound_floor_87 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    87 ≤ f 12 18 := by
  by_cases h : 87 ≤ f 12 18
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 12 18) scMt6T scMt6U :=
      hf scMt6T scMt6U scMt6_steps
    exact scMt6_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 204: the ISA algebra, complete — the cheap omega and the successor call
-- The exhaustive wrapper-word map (all 30 words of length ≤ 4 over {C, W},
-- placeholder-register emission, leak-checked): EVERY word eventually hands control to
-- the register; the word chooses the arguments and the price. The table's two new
-- instructions, pinned: `C·W` compiles SELF-APPLICATION in seventeen fires — the omega
-- shape at nearly half Stage 194's price, with cargo `W` and legible junk — and `W·C·W·C`
-- compiles THE SUCCESSOR CALL: `r (C r) (C r)` — the register executed on its own
-- incremented self, thirty-one fires, every register. The successor call is the
-- C10-relevant primitive: a register that reads numerals now can be handed its own
-- successor as input. The full map lives in the ledger; the remaining 26 words deliver
-- rearrangements of `r`, its wrappings, and X-complex junk — no third novelty.

/-- **The cheap omega**: `C·W` compiles self-application in seventeen fires. -/
theorem sc_cheap_omega (r : SCTerm) :
    RS.SC.StepsN 17 (scFrame (.app .C (.app scW r)))
      (.app (.app (.app r r) (.app .C .C))
        (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))) :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app .C (.app (.app .C .C) r)) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C .C) r) (.app .C .C) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C r (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)) r (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) r) (.app .C .C) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C r (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) r (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C .C) r)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red r (.app .C .C) r))
  (@RS.StepsN.refl RS.SC (.app (.app (.app r r) (.app .C .C)) (.app (.app .C (.app (.app .C .C) r)) (.app .C .C)))))))))))))))))))))

/-- **The successor call**: `W·C·W·C` hands the register its own successor, twice. -/
theorem sc_successor_call (r : SCTerm) :
    RS.SC.StepsN 31 (scFrame (.app scW (.app .C (.app scW (.app .C r)))))
      (.app (.app r (.app .C r)) (.app .C r)) :=
  (RS.StepsN.tail (SCStep.S_red (.app .S scDup) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))
  (RS.StepsN.tail (SCStep.S_red scDup (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .C .C) (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app .C (.app (.app .C .C) (.app .C r)))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C r))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C r)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C r) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app .C r) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app .C (.app (.app .C .C) (.app .C r)))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C r))) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app .C r))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C r)) (.app .C r) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C r) (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.C_red (.app (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r)))) (.app .C .C)) (.app .C r) (.app .C r))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C r))) (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C (.app (.app .C .C) (.app .C r))) (.app .C r)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C r) (.app .C (.app (.app .C .C) (.app .C r)))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C r))) (.app .C r) (.app .C r))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C r)) (.app .C r) (.app .C r))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C r) (.app .C r)))
  (RS.StepsN.tail (SCStep.C_red (.app .C r) (.app .C r) (.app .C r))
  (RS.StepsN.tail (SCStep.C_red r (.app .C r) (.app .C r))
  (@RS.StepsN.refl RS.SC (.app (.app r (.app .C r)) (.app .C r))))))))))))))))))))))))))))))))))

-- ## Stage 206: the counting chain — bounded odometers exist, and their fuel is pre-built
-- C10 asks for a live counter; this is the sharpest thing below it, pinned. Iterating the
-- routed successor gives THE COUNTING CHAIN: `scChain n y` is a linear-size machine
-- (3 leaves per increment) that delivers `C^n r` — the n-fold successor of ANY numeral —
-- to any continuation `y` in exactly `2n` fires, the intermediate numerals trailing as
-- legible junk. With `r = C^k S` the continuation receives `C^(k+n) S` on the nose
-- (`sc_iterC_numeral`). Counters exist; what C10 asks, precisely, is whether the chain's
-- fuel (the n nested prefabs, consumed one per increment) can ever be REGROWN by the
-- machine itself. Every piece of an odometer is now pinned except the regrowth.

/-- The n-fold increment prefab: `S (C ·) C` nested. -/
def scChain : Nat → SCTerm → SCTerm
  | 0, y => y
  | n + 1, y => .app (.app .S (.app .C (scChain n y))) .C

/-- The n-fold successor. -/
def scIterC : Nat → SCTerm → SCTerm
  | 0, r => r
  | n + 1, r => .app .C (scIterC n r)

/-- On numerals, iterated successor is numeral addition. -/
theorem sc_iterC_numeral : ∀ n k, scIterC n (scParityReg k) = scParityReg (k + n)
  | 0, _ => rfl
  | n + 1, k => by
      show .app .C (scIterC n (scParityReg k)) = scParityReg (k + (n + 1))
      rw [sc_iterC_numeral n k]
      rfl

/-- One chain stage: two fires, one increment. -/
theorem sc_chain_fire (n : Nat) (y r : SCTerm) :
    RS.SC.StepsN 2 (.app (scChain (n + 1) y) r)
      (.app (.app (scChain n y) (.app .C r)) r) :=
  sc_routed_successor (scChain n y) r

/-- **The counting chain**: `2n` fires deliver the n-fold successor to the continuation,
for every start numeral — the intermediate numerals trail as junk. -/
theorem sc_chain_run : ∀ (n : Nat) (y r : SCTerm),
    ∃ u, RS.SC.Steps (.app (scChain n y) r) u ∧ scUnder (.app y (scIterC n r)) u
  | 0, y, r => ⟨SCTerm.app y r, @RS.Steps.refl RS.SC (SCTerm.app y r), scUnder.refl⟩
  | n + 1, y, r => by
      obtain ⟨u, hu, hunder⟩ := sc_chain_run n y (.app .C r)
      have hsteps := RS.Steps.trans (RS.StepsN.toSteps (sc_chain_fire n y r))
        (scSteps_appL r hu)
      refine ⟨.app u r, hsteps, ?_⟩
      have : scIterC (n + 1) r = scIterC n (.app .C r) := by
        clear hsteps hu hunder u
        induction n with
        | zero => rfl
        | succ m ih =>
            show SCTerm.app .C (scIterC (m + 1) r)
              = SCTerm.app .C (scIterC m (SCTerm.app .C r))
            rw [ih]
      rw [this]
      exact scUnder.app hunder

/-- **The bounded odometer**: for every `n` and `k`, a machine of `3n + 3` leaves plus
the numeral delivers `C^(n+k) S` to the continuation. Counting is free; only REGROWING
the counter is (C10-)hard. -/
theorem sc_bounded_odometer (n k : Nat) (y : SCTerm) :
    ∃ u, RS.SC.Steps (.app (scChain n y) (scParityReg k)) u ∧
      scUnder (.app y (scParityReg (k + n))) u := by
  obtain ⟨u, hu, hunder⟩ := sc_chain_run n y (scParityReg k)
  rw [sc_iterC_numeral n k] at hunder
  exact ⟨u, hu, hunder⟩

-- ## Stage 207: the n=14 mountain — excess 86
-- The n=14 graft neighborhood (seeded by both n=12 species) delivered inside 352 tries:
-- a 14-leaf term whose fully forced 500-step prefix peaks at 366 leaves (step 422),
-- with a 280-leaf off-prefix target eight checked steps past the end. Excess 86; the
-- best-witness ladder reads 12 → 44 → 69 → 86 at n = 8 → 10 → 12 → 14, and the floor
-- family gains f(14,280) ≥ 366. The forced-march technology at march-500: cost still
-- linear in the path.

/-- Fourteen leaves: the n=12 champion with a two-leaf graft in the numeral tail. -/
def scMt7T : SCTerm :=
  .app (.app (.app (.app (.app .C .S) .S) (.app .S .S)) .C)
    (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)

/-- 280 leaves, eight checked steps past the 500-step forced prefix. -/
def scMt7U : SCTerm := (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))

/-- The witnessing path: the full forced march, then eight checked steps. -/
def scMt7Path : List SCTerm := scForcedMarch scMt7T 500 ++
  [(.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))),
   (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C .C)) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))]

section
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

#guard scMt7T.leafCount = 14
#guard scMt7U.leafCount = 280
#guard (scForcedMarch scMt7T 500).length = 500

/-- The crossing exists. -/
theorem scMt7_steps : RS.SC.Steps scMt7T scMt7U :=
  scChained_steps scMt7Path scMt7T scMt7U (by decide) (by decide)

/-- **The n=14 mountain**: no path from 14 leaves to 280 leaves stays within 365. -/
theorem scMt7_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 365 scMt7T scMt7U :=
  scForced_mountain (scForcedMarch scMt7T 500) (scForcedMarch_forced 500 scMt7T)
    (by decide) (by decide)

end

/-- **The n=14 floor**: every valid bounding function clears 366 at (14, 280). -/
theorem sc_bound_floor_366 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    366 ≤ f 14 280 := by
  by_cases h : 366 ≤ f 14 280
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 14 280) scMt7T scMt7U :=
      hf scMt7T scMt7U scMt7_steps
    exact scMt7_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 211: the spine dichotomy — every step is a mutation or a call
-- The invariant program's opening theorem. View any term as head-atom plus spine
-- arguments. Then every step does exactly one of two things: (i) MUTATE — the head and
-- the argument list survive, one argument steps in place; or (ii) CALL — the head atom
-- is consumed, the FIRST argument becomes the new program (its head is the new head, its
-- arguments prepend), and the fire's products join the argument list. This is the
-- structural law behind all five walls: nothing returns to head position except by
-- having been argument one — the leftmost branch is the return stack. Head restoration —
-- the heart of C10 — is therefore exactly the question of what a machine can place in
-- its own a₁-chain.

/-- The spine head: the leftmost atom. -/
def scSpineHead : SCTerm → SCTerm
  | .app f _ => scSpineHead f
  | t => t

/-- The spine arguments, left to right. -/
def scSpineArgs : SCTerm → List SCTerm
  | .app f x => scSpineArgs f ++ [x]
  | _ => []

/-- One list element steps in place. -/
inductive scStepAt : List SCTerm → List SCTerm → Prop
  | head {a a' : SCTerm} {l : List SCTerm} :
      RS.SC.step a a' → scStepAt (a :: l) (a' :: l)
  | tail {a : SCTerm} {l l' : List SCTerm} :
      scStepAt l l' → scStepAt (a :: l) (a :: l')

theorem scStepAt_append {l l' m : List SCTerm} (h : scStepAt l l') :
    scStepAt (l ++ m) (l' ++ m) := by
  induction h with
  | head s => exact scStepAt.head s
  | tail _ ih => exact scStepAt.tail ih

theorem scStepAt_last {y y' : SCTerm} (l : List SCTerm) (h : RS.SC.step y y') :
    scStepAt (l ++ [y]) (l ++ [y']) := by
  induction l with
  | nil => exact scStepAt.head h
  | cons a l ih => exact scStepAt.tail ih

/-- **The spine dichotomy**: every step is a mutation (head and argument list survive,
one argument steps) or a call (the first argument becomes the program). -/
theorem sc_spine_dichotomy {t u : SCTerm} (h : RS.SC.step t u) :
    (scSpineHead u = scSpineHead t ∧ scStepAt (scSpineArgs t) (scSpineArgs u)) ∨
    (∃ f g x rest,
      scSpineHead u = scSpineHead f ∧
      ((scSpineHead t = .S ∧ scSpineArgs t = f :: g :: x :: rest ∧
        scSpineArgs u = scSpineArgs f ++ x :: .app g x :: rest) ∨
       (scSpineHead t = .C ∧ scSpineArgs t = f :: g :: x :: rest ∧
        scSpineArgs u = scSpineArgs f ++ x :: g :: rest))) := by
  induction h with
  | S_red f g x =>
      refine .inr ⟨f, g, x, [], rfl, .inl ⟨rfl, ?_, ?_⟩⟩
      · show scSpineArgs (.app (.app (.app .S f) g) x) = [f, g, x]
        simp [scSpineArgs]
      · show scSpineArgs (.app (.app f x) (.app g x))
          = scSpineArgs f ++ [x, .app g x]
        simp [scSpineArgs]
  | C_red f g x =>
      refine .inr ⟨f, g, x, [], rfl, .inr ⟨rfl, ?_, ?_⟩⟩
      · show scSpineArgs (.app (.app (.app .C f) g) x) = [f, g, x]
        simp [scSpineArgs]
      · show scSpineArgs (.app (.app f x) g) = scSpineArgs f ++ [x, g]
        simp [scSpineArgs]
  | @appL t₀ t₀' y h' ih =>
      rcases ih with ⟨hh, hargs⟩ | ⟨f, g, x, rest, hf, hcase⟩
      · exact .inl ⟨hh, scStepAt_append hargs⟩
      · refine .inr ⟨f, g, x, rest ++ [y], hf, ?_⟩
        rcases hcase with ⟨hS, hargs, hargs'⟩ | ⟨hC, hargs, hargs'⟩
        · refine .inl ⟨hS, ?_, ?_⟩
          · show scSpineArgs t₀ ++ [y] = f :: g :: x :: (rest ++ [y])
            rw [hargs]; rfl
          · show scSpineArgs t₀' ++ [y]
              = scSpineArgs f ++ x :: .app g x :: (rest ++ [y])
            rw [hargs']; simp
        · refine .inr ⟨hC, ?_, ?_⟩
          · show scSpineArgs t₀ ++ [y] = f :: g :: x :: (rest ++ [y])
            rw [hargs]; rfl
          · show scSpineArgs t₀' ++ [y]
              = scSpineArgs f ++ x :: g :: (rest ++ [y])
            rw [hargs']; simp
  | appR h' =>
      exact .inl ⟨rfl, scStepAt_last _ h'⟩

/-- **The call lemma**: the machine's next program is always its first argument — the
head changes only by calling `a₁`. -/
theorem sc_call_source {t u : SCTerm} (h : RS.SC.step t u) :
    scSpineHead u = scSpineHead t ∨
    ∃ f rest, scSpineArgs t = f :: rest ∧ scSpineHead u = scSpineHead f := by
  rcases sc_spine_dichotomy h with ⟨hh, _⟩ | ⟨f, g, x, rest, hf, hcase⟩
  · exact .inl hh
  · rcases hcase with ⟨_, hargs, _⟩ | ⟨_, hargs, _⟩
    · exact .inr ⟨f, g :: x :: rest, hargs, hf⟩
    · exact .inr ⟨f, g :: x :: rest, hargs, hf⟩

-- ## Stage 212: head provenance — the return stack, iterated
-- The dichotomy, closed under reduction. For ANY multi-step reduction, the final head
-- atom either survived from the very start (a pure mutation history — all computation
-- argument-internal) or was SUPPLIED BY THE FIRST ARGUMENT of some reachable state: the
-- last call's callee. There is no third source. For recurrent machines this is the
-- return-stack law: a machine that restores its head after calling has necessarily
-- re-supplied that head from its own a₁-chain — the reader does it every period (its
-- consultation product is its next front), and C10 asks whether the re-supplied copy
-- can ever carry an incremented address.

/-- **Head provenance**: over any reduction, the head either survives or is the head of
a first argument of some reachable state. -/
theorem sc_head_provenance {t u : SCTerm} (h : RS.SC.Steps t u) :
    scSpineHead u = scSpineHead t ∨
    ∃ v f rest, RS.SC.Steps t v ∧ scSpineArgs v = f :: rest ∧
      scSpineHead u = scSpineHead f := by
  refine h.rec (motive := fun (a b : SCTerm) _ =>
      scSpineHead b = scSpineHead a ∨
      ∃ v f rest, RS.SC.Steps a v ∧ scSpineArgs v = f :: rest ∧
        scSpineHead b = scSpineHead f) ?_ ?_
  · intro a
    exact .inl rfl
  · intro a b c s rest' ih
    rcases ih with hh | ⟨v, f, fr, hv, hargs, hf⟩
    · rcases sc_call_source s with hs | ⟨f, fr, hargs, hf⟩
      · exact .inl (hh.trans hs)
      · exact .inr ⟨a, f, fr, @RS.Steps.refl RS.SC a, hargs, hh.trans hf⟩
    · exact .inr ⟨v, f, fr, RS.Steps.tail s hv, hargs, hf⟩

-- ## Stage 213: the numeral speed limit — wall six, quantitative
-- Address flow, resolved by a stronger source theorem. `sc_numerals_are_sources`
-- generalizes bits-are-sources to every numeral depth: NO step ever produces a numeral
-- as its result — root fires make double applications, appL-targets would need a
-- produced atom, and appR-targets descend infinitely through the wrap. Numerals exist
-- only where they were written. The corollary is the program's sixth wall, and its first
-- QUANTITATIVE one: the maximum numeral depth in a term grows by AT MOST ONE per fire
-- (`sc_numeral_speed_limit`) — every fresh wrap comes from an atom `C` meeting the
-- x-seat, and one fire has one x-seat. Any C10 odometer is fire-paced: a machine of
-- period p can advance its address by at most p per lap, and every unit of advance
-- costs a mint fire the machine must also afford to regrow.

/-- Numeral recognition: `C^k S ↦ k`. -/
def scIsReg : SCTerm → Option Nat
  | .S => some 0
  | .app .C w => (scIsReg w).map (· + 1)
  | _ => none

/-- **Numerals are sources**: no step produces a numeral. -/
theorem sc_numerals_are_sources : ∀ {t u : SCTerm}, RS.SC.step t u → scIsReg u = none
  | _, _, h => by
      induction h with
      | S_red f g x => rfl
      | C_red f g x => rfl
      | appL h' ih =>
          cases h' <;> rfl
      | @appR t₀ y y' h' ih =>
          cases t₀ with
          | S => rfl
          | C => show (scIsReg y').map (· + 1) = none; rw [ih]; rfl
          | app a b => rfl

/-- Maximum numeral depth occurring in a term. -/
def scMaxReg : SCTerm → Nat
  | .S => 0
  | .C => 0
  | .app f x => max (max (scMaxReg f) (scMaxReg x)) ((scIsReg (.app f x)).getD 0)

/-- A term's own numeral value is at most its max depth. -/
theorem scMaxReg_ge_isReg : ∀ t : SCTerm, (scIsReg t).getD 0 ≤ scMaxReg t
  | .S => Nat.le_refl 0
  | .C => Nat.zero_le 0
  | .app _ _ => Nat.le_max_right _ _

/-- A fresh wrap's value is bounded by its body's depth plus one. -/
theorem sc_wrap_bound (f x : SCTerm) :
    (scIsReg (.app f x)).getD 0 ≤ scMaxReg x + 1 := by
  cases f with
  | S => exact Nat.zero_le _
  | C =>
      show ((scIsReg x).map (· + 1)).getD 0 ≤ scMaxReg x + 1
      cases hx : scIsReg x with
      | none => exact Nat.zero_le _
      | some j =>
          have := scMaxReg_ge_isReg x
          rw [hx] at this
          simpa using Nat.succ_le_succ this
  | app a b => exact Nat.zero_le _

/-- **The numeral speed limit**: one fire advances the maximum numeral depth by at most
one — every fresh wrap costs an atom `C` meeting the x-seat, and a fire has one x-seat. -/
theorem sc_numeral_speed_limit : ∀ {t u : SCTerm}, RS.SC.step t u →
    scMaxReg u ≤ scMaxReg t + 1 := by
  intro t u h
  induction h with
  | S_red f g x =>
      have h1 := sc_wrap_bound f x
      have h2 := sc_wrap_bound g x
      have r1 : scIsReg (SCTerm.app (.app f x) (.app g x)) = none := rfl
      have r2 : scIsReg (SCTerm.app (.app (.app .S f) g) x) = none := rfl
      have r3 : scIsReg (SCTerm.app (.app .S f) g) = none := rfl
      have r4 : scIsReg (SCTerm.app .S f) = none := rfl
      simp only [scMaxReg, r1, r2, r3, r4, Option.getD_none]
      omega
  | C_red f g x =>
      have h1 := sc_wrap_bound f x
      have r1 : scIsReg (SCTerm.app (.app f x) g) = none := rfl
      have r2 : scIsReg (SCTerm.app (.app (.app .C f) g) x) = none := rfl
      have r3 : scIsReg (SCTerm.app (.app .C f) g) = none := rfl
      simp only [scMaxReg, r1, r2, r3, Option.getD_none]
      omega
  | @appL t₀ t₀' y h' ih =>
      have h1 : scIsReg (.app t₀' y) = none := by
        cases h' <;> rfl
      have h2 : (scIsReg (.app t₀ y)).getD 0 ≤ scMaxReg (.app t₀ y) :=
        scMaxReg_ge_isReg _
      simp only [scMaxReg, h1, Option.getD_none] at *
      omega
  | @appR t₀ y y' h' ih =>
      have h1 : scIsReg (.app t₀ y') = none := by
        cases t₀ with
        | S => rfl
        | C =>
            show (scIsReg y').map (· + 1) = none
            rw [sc_numerals_are_sources h']
            rfl
        | app a b => rfl
      simp only [scMaxReg, h1, Option.getD_none] at *
      omega

/-- Over a counted reduction, numeral depth grows at most linearly in the fire count. -/
theorem sc_numeral_speed_limit_run : ∀ {n : Nat} {t u : SCTerm},
    RS.SC.StepsN n t u → scMaxReg u ≤ scMaxReg t + n := by
  intro n t u h
  refine h.rec (motive := fun (n : Nat) (a b : SCTerm) _ =>
      scMaxReg b ≤ scMaxReg a + n) ?_ ?_
  · intro a
    exact Nat.le_refl _
  · intro m a b c s rest ih
    have := sc_numeral_speed_limit s
    omega

-- ## Stage 214: the cargo law — the rightmost argument survives every fire
-- A positional corollary of the dichotomy, and the theorem behind every FIFO machine in
-- the program. The rightmost spine argument of any term survives every step: usually
-- verbatim in last position, sometimes stepped in place, and in exactly one case
-- displaced — a BOTTOM CALL, a call whose frame consumes the entire argument list
-- (arity exactly three), which slides the old cargo to second-to-last and installs the
-- call's product as the new last. Cargo is never erased and never skipped: a machine
-- must burn down to arity three to touch its own tail — which is precisely how the
-- biodegradable word machines (Stage 148) always worked, now as a theorem.

theorem scStepAt_snoc : ∀ {l m : List SCTerm} {y : SCTerm},
    scStepAt (l ++ [y]) m →
    (∃ l', m = l' ++ [y] ∧ scStepAt l l') ∨
    (∃ y' : SCTerm, RS.SC.step y y' ∧ m = l ++ [y']) := by
  intro l
  induction l with
  | nil =>
      intro m y h
      cases h with
      | head s => exact .inr ⟨_, s, rfl⟩
      | tail h' => cases h'
  | cons a l₀ ih =>
      intro m y h
      cases h with
      | head s => exact .inl ⟨_ :: l₀, rfl, scStepAt.head s⟩
      | tail h' =>
          rcases ih h' with ⟨l', rfl, hl⟩ | ⟨y', hy, rfl⟩
          · exact .inl ⟨a :: l', rfl, scStepAt.tail hl⟩
          · exact .inr ⟨y', hy, rfl⟩

/-- **The cargo law**: the rightmost spine argument survives every fire — verbatim in
last position, stepped in place, or (bottom call only, arity exactly three) displaced
one slot with the call's product installed after it. -/
theorem sc_cargo_law {t u : SCTerm} (h : RS.SC.step t u) {pre : List SCTerm}
    {y : SCTerm} (hargs : scSpineArgs t = pre ++ [y]) :
    (∃ pre', scSpineArgs u = pre' ++ [y]) ∨
    (∃ (pre' : List SCTerm) (y' : SCTerm),
      RS.SC.step y y' ∧ scSpineArgs u = pre' ++ [y']) ∨
    (∃ f g w, pre = [f, g] ∧ scSpineArgs u = scSpineArgs f ++ [y, w]) := by
  rcases sc_spine_dichotomy h with ⟨_, hstep⟩ | ⟨f, g, x, rest, _, hcase⟩
  · rw [hargs] at hstep
    rcases scStepAt_snoc hstep with ⟨l', hm, _⟩ | ⟨y', hy, hm⟩
    · exact .inl ⟨l', hm⟩
    · exact .inr (.inl ⟨_, y', hy, hm⟩)
  · have hargst : scSpineArgs t = f :: g :: x :: rest :=
      hcase.elim (fun hc => hc.2.1) (fun hc => hc.2.1)
    obtain ⟨w, hu⟩ : ∃ w, scSpineArgs u = scSpineArgs f ++ x :: w :: rest :=
      hcase.elim (fun hc => ⟨.app g x, hc.2.2⟩) (fun hc => ⟨g, hc.2.2⟩)
    rcases List.eq_nil_or_concat rest with hrest | ⟨zs, z, hrest⟩
    · subst hrest
      have h3 : pre ++ [y] = [f, g] ++ [x] := by
        rw [← hargs, hargst]
        rfl
      have hlen : pre.length = 2 := by
        have h4 := congrArg List.length h3
        simp at h4
        omega
      obtain ⟨hpre, hyx⟩ := List.append_inj h3 (by simp [hlen])
      have hy : y = x := by simpa using hyx
      subst hy
      exact .inr (.inr ⟨f, g, w, hpre, by rw [hu]⟩)
    · subst hrest
      have h3 : pre ++ [y] = (f :: g :: x :: zs) ++ [z] := by
        rw [← hargs, hargst]
        simp
      have hyz : y = z := by
        have hlen : pre.length = (f :: g :: x :: zs).length := by
          have := congrArg List.length h3
          simp at this
          simpa using this
        obtain ⟨_, hy⟩ := List.append_inj h3 hlen
        simpa using hy
      subst hyz
      refine .inl ⟨scSpineArgs f ++ x :: w :: zs, ?_⟩
      rw [hu]
      simp

-- ## Stage 215: the stamp — one fire wraps the x-seat in any prefab
-- The write-half primitive the tag step needs, and the common generalization of the
-- successor (Stage 201) and the assembler: `S f g x ⟶ (f x) (g x)` read as an
-- INSTRUCTION says the prefab `g` STAMPS the x-seat — `g = C` mints numeral successors,
-- `g = C C` mints CELLS (`sc_cell_mint`), any `g` mints `g`-applications — with the
-- continuation `f` receiving the raw operand beside the stamped copy. Rotation status,
-- from the cargo law plus the pinned traversal: the READ half of the identity tag step
-- exists (scBWord traversal delivers word contents as FIFO arguments); the WRITE half is
-- cell-stamping arguments back into a chain, for which this is the per-symbol fire. The
-- remaining engineering is the walk: a head that stamps each argument in turn and folds
-- the stamped cells into a word — the rotator sweep (24,036 heads, zero) says that walk
-- exceeds seven leaves, not that it is walled.

/-- **The stamp**: one fire wraps the x-seat in any prefab, continuation alongside. -/
theorem sc_stamp (f g x : SCTerm) :
    RS.SC.step (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x)) :=
  SCStep.S_red f g x

/-- **The cell mint**: stamping with `C C` builds a cell of the operand — the write-half
of the tag step, one fire per symbol. -/
theorem sc_cell_mint (f x : SCTerm) :
    RS.SC.step (.app (.app (.app .S f) (.app .C .C)) x)
      (.app (.app f x) (.app (.app .C .C) x)) :=
  SCStep.S_red f (.app .C .C) x

-- ## Stage 217: the suffix law — no overtaking on the spine
-- The fueled-walk sweep was chasing an impossible shape, and the impossibility is the
-- theorem. Any argument-list suffix lying beyond the call frame (the first three
-- arguments) is untouchable: a step either leaves it verbatim — same elements, same
-- order, same distance from the end — or steps ONE of its elements in place. Products
-- never migrate rightward past surviving material; the unread queue is sacred; stamped
-- output accumulating "behind" the queue cannot exist. Walk architectures are therefore
-- forced onto the scBWord chassis — queue in the head-chain, products appended by the
-- per-cell bottom calls — which is precisely the one machine family in the program that
-- already does both halves. The walk's remaining freedom is one dimension: the arm
-- supply.

theorem scStepAt_split : ∀ {pre suf m : List SCTerm},
    scStepAt (pre ++ suf) m →
    (∃ pre', m = pre' ++ suf ∧ scStepAt pre pre') ∨
    (∃ suf', m = pre ++ suf' ∧ scStepAt suf suf') := by
  intro pre
  induction pre with
  | nil =>
      intro suf m h
      exact .inr ⟨m, rfl, h⟩
  | cons a pre₀ ih =>
      intro suf m h
      cases h with
      | head s => exact .inl ⟨_ :: pre₀, rfl, scStepAt.head s⟩
      | tail h' =>
          rcases ih h' with ⟨pre', rfl, hp⟩ | ⟨suf', rfl, hs⟩
          · exact .inl ⟨a :: pre', rfl, scStepAt.tail hp⟩
          · exact .inr ⟨suf', rfl, hs⟩

/-- **The suffix law**: an argument suffix beyond the call frame survives every step —
verbatim, or with one element stepped in place. No product ever overtakes it. -/
theorem sc_suffix_law {t u : SCTerm} (h : RS.SC.step t u) {pre suf : List SCTerm}
    (hargs : scSpineArgs t = pre ++ suf) (hlen : 3 ≤ pre.length) :
    ∃ pre', (scSpineArgs u = pre' ++ suf) ∨
      (∃ suf', scStepAt suf suf' ∧ scSpineArgs u = pre' ++ suf') := by
  rcases sc_spine_dichotomy h with ⟨_, hstep⟩ | ⟨f, g, x, rest, _, hcase⟩
  · rw [hargs] at hstep
    rcases scStepAt_split hstep with ⟨pre', hm, _⟩ | ⟨suf', hm, hs⟩
    · exact ⟨pre', .inl hm⟩
    · exact ⟨pre, .inr ⟨suf', hs, hm⟩⟩
  · have hargst : scSpineArgs t = f :: g :: x :: rest :=
      hcase.elim (fun hc => hc.2.1) (fun hc => hc.2.1)
    obtain ⟨w, hu⟩ : ∃ w, scSpineArgs u = scSpineArgs f ++ x :: w :: rest :=
      hcase.elim (fun hc => ⟨.app g x, hc.2.2⟩) (fun hc => ⟨g, hc.2.2⟩)
    have h3 : f :: g :: x :: rest = pre ++ suf := by rw [← hargst, hargs]
    match pre, hlen with
    | [a, b, c], _ =>
        have : f = a ∧ g = b ∧ x = c ∧ rest = suf := by
          simpa using h3
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact ⟨scSpineArgs f ++ [x, w], .inl (by rw [hu]; simp)⟩
    | a :: b :: c :: d :: pre₀, _ =>
        have : f = a ∧ g = b ∧ x = c ∧ rest = (d :: pre₀) ++ suf := by
          simpa using h3
        obtain ⟨rfl, rfl, rfl, hrest⟩ := this
        refine ⟨scSpineArgs f ++ x :: w :: d :: pre₀, .inl ?_⟩
        rw [hu, hrest]
        simp

-- ## Stage 218: the pass-through word — one fire per symbol, the arm conserved
-- The arm-supply search ended in one C_red: the PASS-THROUGH CELL `C M W` fires on any
-- arm `A` as `(C M W) A ⟶ (M A) W` — the arm hands through to the next cell untouched
-- and the symbol appends behind it. A word stored as nested C-pairs (`scCWord`) therefore
-- unrolls at ONE fire per symbol on a SINGLE conserved arm — against the Stage 148
-- chassis's seven fires and one consumed arm per symbol — and the symbols emerge in
-- rotation order: the front of the stored word lands rightmost. Read-half of the tag
-- step, final form. The arm-supply dimension is closed: nothing is consumed. What
-- remains of the identity tag machine is only the loop: an end-marker that re-packs
-- emitted arguments into a fresh C-word — the walk, now with its cost floor known
-- (one fire per symbol is optimal; the pass-through achieves it).

/-- A word as nested pass-through cells. -/
def scCWord : List SCTerm → SCTerm → SCTerm
  | [], E => E
  | W :: ws, E => .app (.app .C (scCWord ws E)) W

/-- Left-application of a list of arguments. -/
def scAppList : SCTerm → List SCTerm → SCTerm
  | t, [] => t
  | t, w :: ws => scAppList (.app t w) ws

/-- **The pass-through cell**: one fire; the arm survives, the symbol appends. -/
theorem sc_passthrough (M W A : SCTerm) :
    RS.SC.step (.app (.app (.app .C M) W) A) (.app (.app M A) W) :=
  SCStep.C_red M W A

/-- Reversed unroll target: symbols emerge front-to-rightmost. -/
def scUnrolled (E A : SCTerm) : List SCTerm → SCTerm
  | [] => .app E A
  | W :: ws => .app (scUnrolled E A ws) W

/-- **The one-arm traversal**: a k-symbol word unrolls in exactly k fires on one
conserved arm, front symbol landing rightmost — rotation order. -/
theorem sc_cword_run : ∀ (ws : List SCTerm) (E A : SCTerm),
    RS.SC.StepsN ws.length (.app (scCWord ws E) A) (scUnrolled E A ws)
  | [], E, A => @RS.StepsN.refl RS.SC (.app E A)
  | W :: ws, E, A => by
      show RS.SC.StepsN (ws.length + 1) _ _
      exact RS.StepsN.tail (sc_passthrough (scCWord ws E) W A)
        (scStepsN_appL W (sc_cword_run ws E A))

-- ## Stage 220: the burn — the reader's storage reads itself back
-- Stage 179 called the reader's junk C-shelled register storage; Stage 218 identified
-- the shell as a pass-through cell; this stage certifies the consequence: THE STORAGE IS
-- LIVE. Three junk blocks applied to each other ignite — the first fire is the
-- pass-through, two more expose the stored register in head position, and the fourth
-- fire is a CONSULTATION: the register `S S C` fires on stored material. The burn does
-- not decay: probe-traced, the stream metabolizes — registers consult, fresh cells form
-- around junk pairs (second-order storage), and the configuration grows reader-like.
-- The alternator's burn phase exists; grow and burn are two behaviors of one medium.

/-- **The ignition**: three junk blocks ignite in four fires — pass-through, register
exposure, and the stored register's consultation fire. -/
theorem sc_junk_ignition :
    RS.SC.StepsN 4 (.app (.app scRdrJ scRdrJ) scRdrJ)
      (.app (.app (.app (.app (.app .S (.app .C scRdrReg))
        (.app .C (.app .C scRdrReg))) scRdrJ) (.app .C scRdrReg)) scRdrJ) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scRdrP (.app .C scRdrReg) scRdrJ))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scRdrReg) (.app .C scRdrReg) scRdrJ)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ (.app .C scRdrReg))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app .C scRdrReg)))))
  (@RS.StepsN.refl RS.SC _)))))

/-- The junk block is a pass-through cell: one fire unloads it onto any arm. -/
theorem sc_junk_is_cell (A : SCTerm) :
    RS.SC.step (.app scRdrJ A) (.app (.app scRdrP A) (.app .C scRdrReg)) :=
  SCStep.C_red scRdrP (.app .C scRdrReg) A

-- ## Stage 222: the pulse, pinned — the toolkit's fourth recurrence technology
-- The burn's period-12 wave decodes into a VERBATIM-PERIODIC family after all — the
-- front detector missed it because the growth is mid-spine (before the conserved tail,
-- exactly as the cargo law dictates). The family: `scPulse m` is the spine
-- `S · PRE · BLOCK^m · SUF` over the reader's junk vocabulary, with the 67-leaf block
-- `[C r, C J J, C (C (C r) J) J]`. Pinned: the ignition lands on `scPulse 0` (fire 4 —
-- the Stage 220 target IS the pulse's phase zero), twelve more fires reach `scPulse 1`
-- (`sc_pulse_entry`), and the CORE LAW — twelve fires grow one block inside a six-
-- argument window, everything beyond riding by the new `scStepsN_appList` lift — gives
-- `scPulse (m+1) ⟶¹² scPulse (m+2)` for every m (`sc_pulse_law`). Corollary: the junk
-- medium's burn is an ETERNAL WAVE (`sc_burn_wave`: three junk blocks reach every pulse
-- phase). Periodic drift joins verbatim, cyclic, and graded recurrence as certified
-- technology — and the alternator's burn phase is now a pinned persistent process.

/-- `StepsN` under any rider list. -/
theorem scStepsN_appList {n : Nat} {t t' : SCTerm} (l : List SCTerm)
    (h : RS.SC.StepsN n t t') :
    RS.SC.StepsN n (scAppList t l) (scAppList t' l) := by
  induction l generalizing t t' with
  | nil => exact h
  | cons w ws ih => exact ih (scStepsN_appL w h)

theorem scAppList_append : ∀ (l₁ l₂ : List SCTerm) (t : SCTerm),
    scAppList t (l₁ ++ l₂) = scAppList (scAppList t l₁) l₂
  | [], _, _ => rfl
  | _ :: l₁, l₂, _ => scAppList_append l₁ l₂ _

/-- The pulse's fixed prelude arguments. -/
def scBurnPre : List SCTerm :=
  [.app .C scRdrReg, .app .C (.app .C scRdrReg), scRdrJ]

/-- The 67-leaf pulse block. -/
def scBurnBlock : List SCTerm :=
  [.app .C scRdrReg, .app (.app .C scRdrJ) scRdrJ,
   .app (.app .C (.app (.app .C (.app .C scRdrReg)) scRdrJ)) scRdrJ]

/-- The pulse's conserved tail. -/
def scBurnSuf : List SCTerm := [.app .C scRdrReg, scRdrJ]

def scBurnArgs : Nat → List SCTerm
  | 0 => scBurnSuf
  | m + 1 => scBurnBlock ++ scBurnArgs m

/-- The pulse family: `S · PRE · BLOCK^m · SUF`. -/
def scPulseW (m : Nat) : SCTerm := scAppList .S (scBurnPre ++ scBurnArgs m)

/-- The ignition target is the pulse's phase zero. -/
theorem sc_ignition_is_pulse :
    RS.SC.StepsN 4 (.app (.app scRdrJ scRdrJ) scRdrJ) (scPulseW 0) :=
  sc_junk_ignition

/-- Twelve fires from phase zero to phase one. -/
theorem sc_pulse_entry : RS.SC.StepsN 12 (scPulseW 0) (scPulseW 1) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C scRdrReg) (.app .C (.app .C scRdrReg)) scRdrJ)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ (.app (.app .C (.app .C scRdrReg)) scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app (.app .C (.app .C scRdrReg)) scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C (.app .C scRdrReg)) scRdrJ) (.app .C (.app (.app .C (.app .C scRdrReg)) scRdrJ)) scRdrJ)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scRdrReg) scRdrJ scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red scRdrJ (.app .C scRdrJ) scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrP (.app .C scRdrReg) scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scRdrReg) (.app .C scRdrReg) scRdrJ))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ (.app .C scRdrReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app .C scRdrReg))))))))
  (@RS.StepsN.refl RS.SC (scPulseW 1))))))))))))))

/-- **The core law**: twelve fires grow one block inside the six-argument window. -/
theorem sc_pulse_core :
    RS.SC.StepsN 12 (scAppList .S (scBurnPre ++ scBurnBlock))
      (scAppList .S (scBurnPre ++ (scBurnBlock ++ scBurnBlock))) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C scRdrReg) (.app .C (.app .C scRdrReg)) scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ (.app (.app .C (.app .C scRdrReg)) scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app (.app .C (.app .C scRdrReg)) scRdrJ))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C (.app .C scRdrReg)) scRdrJ) (.app .C (.app (.app .C (.app .C scRdrReg)) scRdrJ)) scRdrJ))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scRdrReg) scRdrJ scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C scRdrJ))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red scRdrJ (.app .C scRdrJ) scRdrJ)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrP (.app .C scRdrReg) scRdrJ))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scRdrReg) (.app .C scRdrReg) scRdrJ)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scRdrReg scRdrJ (.app .C scRdrReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S .C (.app .C scRdrReg)))))))))
  (@RS.StepsN.refl RS.SC (scAppList .S (scBurnPre ++ (scBurnBlock ++ scBurnBlock))))))))))))))))

/-- **The pulse law**: every phase reaches the next in twelve fires. -/
theorem sc_pulse_law (m : Nat) :
    RS.SC.StepsN 12 (scPulseW (m + 1)) (scPulseW (m + 2)) := by
  have h := scStepsN_appList (scBurnArgs m) sc_pulse_core
  rw [← scAppList_append, ← scAppList_append] at h
  show RS.SC.StepsN 12 (scAppList .S (scBurnPre ++ (scBurnBlock ++ scBurnArgs m)))
    (scAppList .S (scBurnPre ++ (scBurnBlock ++ (scBurnBlock ++ scBurnArgs m))))
  rw [show scBurnPre ++ (scBurnBlock ++ scBurnArgs m)
      = (scBurnPre ++ scBurnBlock) ++ scBurnArgs m from by simp,
    show scBurnPre ++ (scBurnBlock ++ (scBurnBlock ++ scBurnArgs m))
      = (scBurnPre ++ (scBurnBlock ++ scBurnBlock)) ++ scBurnArgs m from by simp]
  exact h

/-- **The eternal wave**: three junk blocks reach every pulse phase — the burn is a
pinned persistent process. -/
theorem sc_burn_wave : ∀ m, RS.SC.Steps (.app (.app scRdrJ scRdrJ) scRdrJ) (scPulseW m)
  | 0 => RS.StepsN.toSteps sc_ignition_is_pulse
  | 1 => RS.Steps.trans (RS.StepsN.toSteps sc_ignition_is_pulse)
      (RS.StepsN.toSteps sc_pulse_entry)
  | m + 2 => RS.Steps.trans (sc_burn_wave (m + 1))
      (RS.StepsN.toSteps (sc_pulse_law m))

-- ## Stage 223: the alternator, coexistence form — grow and burn in one term
-- Both alternator phases are pinned waves; the two-clocks chassis holds them together.
-- `S · Front · (J J J)` reaches `S · (Front·Jⁿ) · (pulse m)` for EVERY n and m: one term
-- in which the reader writes storage forever while a burn wave consumes storage forever,
-- schedule-interleaved at will. This is the alternator's COEXISTENCE form — C8-final's
-- machinery demonstrated jointly. The FEEDING form (the grow-phase's own junk igniting)
-- reduces, by the probes of this stage, to exactly one missing mechanism: FRONT DEATH.
-- In-place ignition is impossible (a junk block is an inert two-argument cell until it
-- reaches head position), the immortal reader never yields the head, and the mortal-
-- reader candidate (bit `C C`) turns out to be a third wave rather than a corpse. The
-- alternator's remaining gap is a front that expires — the fate machine's halt, inside
-- a reader — and that is a design target with both endpoint technologies pinned.

/-- **The alternator, coexistence form**: the chassis holds an eternal writer beside an
eternal burner — every joint phase `(n, m)` is reachable. -/
theorem sc_alternator_coexist (n m : Nat) :
    RS.SC.Steps
      (.app (.app .S scRdrFront) (.app (.app scRdrJ scRdrJ) scRdrJ))
      (.app (.app .S (scReader n)) (scPulseW m)) :=
  sc_two_clocks
    (show RS.SC.Steps scRdrFront (scReader n) from by
      have h : ∀ k, RS.SC.Steps scRdrFront (scReader k) := by
        intro k
        induction k with
        | zero => exact @RS.Steps.refl RS.SC scRdrFront
        | succ j ih => exact RS.Steps.trans ih (scReader_step j)
      exact h n)
    (sc_burn_wave m)

-- ## Stage 224: the ouroboros — the front that writes its storage and then eats it
-- FRONT DEATH, found at three leaves. Put the register `ρ = S (S S)` in the reader
-- frame: the first fire WRITES the junk block (the reader's own write mechanism,
-- verbatim); the register's consultations then route that block leftward — `ρ`'s fire
-- duplicates the junk into operator position — and at fire ten THE WRITTEN BLOCK TAKES
-- THE HEAD; fire eleven unloads its stored payload. One 24-leaf term: grow feeds burn.
-- The alternator's feeding form exists — not as two coupled machines but as one machine
-- whose register calls its own storage. C8-final's last mechanism, pinned; probe-traced
-- past the pin, the burn metabolizes onward (a third wave, growing through 400 leaves).

def scOuroReg : SCTerm := .app .S (.app .S .S)

def scOuroP : SCTerm :=
  .app (.app .C (.app .C scOuroReg)) (.app .C scOuroReg)

def scOuroJ : SCTerm := .app (.app .C scOuroP) (.app .C scOuroReg)

/-- The ouroboros front: the reader frame over `S (S S)`. -/
def scOuro : SCTerm :=
  .app (.app (.app .S scOuroP) (.app .C scOuroP)) (.app .C scOuroReg)

/-- **The write beat**: the first fire writes the junk block, verbatim reader mechanics. -/
theorem sc_ouro_writes :
    RS.SC.step scOuro (.app (.app scOuroP (.app .C scOuroReg)) scOuroJ) :=
  SCStep.S_red scOuroP (.app .C scOuroP) (.app .C scOuroReg)

/-- **The ouroboros**: eleven fires — the block written at fire one takes the head at
fire ten and unloads at fire eleven. Grow feeds burn in one term. -/
theorem sc_ouroboros :
    RS.SC.StepsN 11 scOuro
      (.app (.app (.app (.app scOuroP (.app .C scOuroReg)) (.app .C scOuroReg))
        (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))
          scOuroJ))
        (.app (.app (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg)))
          (.app (.app (.app .C scOuroReg)
            (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ))) :=
  (RS.StepsN.tail (SCStep.S_red scOuroP (.app .C scOuroP) (.app .C scOuroReg))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C scOuroReg) (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) scOuroJ))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .S .S) scOuroJ (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.S_red (.app scOuroJ (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red scOuroP (.app .C scOuroReg) (.app .C scOuroReg))))
  (@RS.StepsN.refl RS.SC _))))))))))))

-- ## Stage 225: the ouroboros wave — the medium's third wave, pinned
-- The post-splice burn templates exactly like the pulse: `scOuroWave m` is the spine
-- `C · PRE · BLOCK^m · SUF` over the ouroboros vocabulary, BLOCK a 160-leaf quadruple,
-- period SIXTEEN fires. Same recipe as Stage 222: forty concrete fires from the
-- ouroboros seed to phase one (`sc_ouroWave_entry` — the write, the feeding, and the
-- first full period in one chain), a sixteen-fire core law in an eight-argument window
-- (`sc_ouroWave_core`), the rider lift, and every phase reachable (`sc_ouro_eternal`).
-- All three observed behaviors of the junk medium are now certified processes: the
-- reader wave (period 7, verbatim), the burn pulse (period 12, drift), and the
-- ouroboros wave (period 16, drift) — one substance, three pinned metabolisms, and the
-- machine that writes its own food is immortal after all: it eats and GROWS.

def scOuroPre : List SCTerm := [scOuroReg,
   (.app (.app .C scOuroReg) (.app .C scOuroReg)),
   (.app .C scOuroReg),
   (.app .C scOuroReg)]

/-- The 160-leaf wave block. -/
def scOuroBlock : List SCTerm := [(.app (.app (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))) (.app .C scOuroReg)),
   (.app (.app .C scOuroReg) (.app .C scOuroReg)),
   (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))),
   (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))]

def scOuroSuf : List SCTerm := [(.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))),
   (.app (.app (.app .C scOuroReg) (.app (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)))),
   (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ),
   (.app (.app (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ))]

def scOuroArgs : Nat → List SCTerm
  | 0 => scOuroSuf
  | m + 1 => scOuroBlock ++ scOuroArgs m

/-- The ouroboros wave family: `C · PRE · BLOCK^m · SUF`. -/
def scOuroWave (m : Nat) : SCTerm := scAppList .C (scOuroPre ++ scOuroArgs m)

/-- Forty fires from the ouroboros seed to the wave's phase one — write, feed, burn,
and the first full period in one chain. -/
theorem sc_ouroWave_entry : RS.SC.StepsN 40 scOuro (scOuroWave 1) :=
  (RS.StepsN.tail (SCStep.S_red scOuroP (.app .C scOuroP) (.app .C scOuroReg))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C scOuroReg) (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.S_red (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ)
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) scOuroJ))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .S .S) scOuroJ (.app .C scOuroReg)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.S_red (.app scOuroJ (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app scOuroJ (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) scOuroJ))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red scOuroP (.app .C scOuroReg) (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scOuroReg) (.app .C scOuroReg) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app .C scOuroReg)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))) (.app .C scOuroReg)))))))))
  (@RS.StepsN.refl RS.SC (scOuroWave 1))))))))))))))))))))))))))))))))))))))))))

/-- **The core law**: sixteen fires grow one block in an eight-argument window. -/
theorem sc_ouroWave_core :
    RS.SC.StepsN 16 (scAppList .C (scOuroPre ++ scOuroBlock))
      (scAppList .C (scOuroPre ++ (scOuroBlock ++ scOuroBlock))) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg)))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app (.app (.app (.app .C scOuroReg) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg)))) (.app .C scOuroReg))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scOuroReg (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app .S .S) (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .S (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)))))))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg)) (.app (.app .C scOuroReg) (.app (.app (.app .C scOuroReg) (.app (.app .C scOuroReg) (.app .C scOuroReg))) (.app .C scOuroReg))) (.app .C scOuroReg)))))))))
  (@RS.StepsN.refl RS.SC (scAppList .C (scOuroPre ++ (scOuroBlock ++ scOuroBlock))))))))))))))))))))

/-- **The wave law**: every phase to the next in sixteen fires. -/
theorem sc_ouroWave_law (m : Nat) :
    RS.SC.StepsN 16 (scOuroWave (m + 1)) (scOuroWave (m + 2)) := by
  have h := scStepsN_appList (scOuroArgs m) sc_ouroWave_core
  rw [← scAppList_append, ← scAppList_append] at h
  show RS.SC.StepsN 16 (scAppList .C (scOuroPre ++ (scOuroBlock ++ scOuroArgs m)))
    (scAppList .C (scOuroPre ++ (scOuroBlock ++ (scOuroBlock ++ scOuroArgs m))))
  rw [show scOuroPre ++ (scOuroBlock ++ scOuroArgs m)
      = (scOuroPre ++ scOuroBlock) ++ scOuroArgs m from by simp,
    show scOuroPre ++ (scOuroBlock ++ (scOuroBlock ++ scOuroArgs m))
      = (scOuroPre ++ (scOuroBlock ++ scOuroBlock)) ++ scOuroArgs m from by simp]
  exact h

/-- **The eternal ouroboros**: the self-eating front reaches every wave phase. -/
theorem sc_ouro_eternal : ∀ m, RS.SC.Steps scOuro (scOuroWave (m + 1))
  | 0 => RS.StepsN.toSteps sc_ouroWave_entry
  | m + 1 => RS.Steps.trans (sc_ouro_eternal m)
      (RS.StepsN.toSteps (sc_ouroWave_law m))

-- ## Stage 228: the waves are numeral-free — no-deepening, first pinned instances
-- The bestiary said the medium copies but never counts; here that becomes theorem for
-- every pinned wave. Spine nodes over a non-`C`-atom head are never numerals, so a
-- numeral-free head with numeral-free arguments stays numeral-free under application
-- (`scMaxReg_appList_zero`); the wave families are explicit lists over a numeral-free
-- vocabulary, so induction over phases gives `scMaxReg (scPulseW m) = 0` and
-- `scMaxReg (scOuroWave m) = 0` for EVERY m. The eternal processes of this calculus run
-- at numeral depth zero, forever — the speed limit's budget of one deepening per fire is
-- never spent. C10's no-deepening invariant has its first two certified cases, covering
-- every pinned eternal machine of the medium.

/-- A numeral-free head with numeral-free arguments stays numeral-free. -/
theorem scMaxReg_appList_zero : ∀ (l : List SCTerm) (t : SCTerm),
    (t = .S ∨ ∃ a b, t = .app a b) → scMaxReg t = 0 →
    (∀ x ∈ l, scMaxReg x = 0) →
    scMaxReg (scAppList t l) = 0
  | [], _, _, ht0, _ => ht0
  | a :: l, t, ht, ht0, hl => by
      have ha : scMaxReg a = 0 := hl a List.mem_cons_self
      have hIsReg : scIsReg (.app t a) = none := by
        rcases ht with rfl | ⟨f, g, rfl⟩ <;> rfl
      have h0 : scMaxReg (.app t a) = 0 := by
        show max (max (scMaxReg t) (scMaxReg a)) ((scIsReg (.app t a)).getD 0) = 0
        rw [hIsReg, ht0, ha]
        rfl
      exact scMaxReg_appList_zero l (.app t a) (.inr ⟨t, a, rfl⟩) h0
        (fun x hx => hl x (List.mem_cons_of_mem a hx))

theorem scBurnArgs_numeral_free : ∀ m, ∀ x ∈ scBurnArgs m, scMaxReg x = 0
  | 0, x, hx => by
      have : ∀ y ∈ scBurnSuf, scMaxReg y = 0 := by decide
      exact this x hx
  | m + 1, x, hx => by
      rcases List.mem_append.mp hx with h | h
      · have : ∀ y ∈ scBurnBlock, scMaxReg y = 0 := by decide
        exact this x h
      · exact scBurnArgs_numeral_free m x h

/-- **The pulse is numeral-free at every phase.** -/
theorem sc_pulse_numeral_free (m : Nat) : scMaxReg (scPulseW m) = 0 := by
  refine scMaxReg_appList_zero _ .S (.inl rfl) rfl ?_
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · have : ∀ y ∈ scBurnPre, scMaxReg y = 0 := by decide
    exact this x h
  · exact scBurnArgs_numeral_free m x h

theorem scOuroArgs_numeral_free : ∀ m, ∀ x ∈ scOuroArgs m, scMaxReg x = 0
  | 0, x, hx => by
      have : ∀ y ∈ scOuroSuf, scMaxReg y = 0 := by decide
      exact this x hx
  | m + 1, x, hx => by
      rcases List.mem_append.mp hx with h | h
      · have : ∀ y ∈ scOuroBlock, scMaxReg y = 0 := by decide
        exact this x h
      · exact scOuroArgs_numeral_free m x h

/-- **The ouroboros wave is numeral-free at every phase.** -/
theorem sc_ouroWave_numeral_free (m : Nat) : scMaxReg (scOuroWave m) = 0 := by
  have hargs : ∀ x ∈ scOuroPre ++ scOuroArgs m, scMaxReg x = 0 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · have : ∀ y ∈ scOuroPre, scMaxReg y = 0 := by decide
      exact this x h
    · exact scOuroArgs_numeral_free m x h
  show scMaxReg (scAppList .C (scOuroPre ++ scOuroArgs m)) = 0
  cases hl : scOuroPre ++ scOuroArgs m with
  | nil => rfl
  | cons a rest =>
      have ha : scMaxReg a = 0 := hargs a (hl ▸ List.mem_cons_self)
      have hIsReg : scIsReg (.app .C a) = none := by
        have : a = scOuroReg := by
          have := congrArg (List.head?) hl
          simp [scOuroPre] at this ⊢
          exact this.symm
        rw [this]
        rfl
      have h0 : scMaxReg (.app .C a) = 0 := by
        show max (max (scMaxReg .C) (scMaxReg a)) ((scIsReg (.app .C a)).getD 0) = 0
        rw [hIsReg, ha]
        rfl
      show scMaxReg (scAppList (.app .C a) rest) = 0
      exact scMaxReg_appList_zero rest (.app .C a) (.inr ⟨.C, a, rfl⟩) h0
        (fun x hx => hargs x (hl ▸ List.mem_cons_of_mem a hx))

-- ## Stage 229: the carrier theorem — any depth rides forever; only deepening is forbidden
-- The chapter's capstone calibration. Numeral registers cannot POWER eternity (the
-- reader-frame halts on every pure numeral — flips have no engine), but eternity can
-- CARRY numerals: the odd parity orbits hold their numeral verbatim at every phase, and
-- here that is quantitative — `scMaxReg (scParityOrbT k) = k` for every k. Together with
-- Stage 228: the medium's eternal processes realize numeral depth k for EVERY k, held
-- constant forever; across all pinned machines and 3.5 million probes, depth never
-- grows along any run. C10's final calibration: carrying is free at every level,
-- deepening has never been seen, and the speed limit prices it at one fire per level.

theorem scIsReg_parityReg : ∀ k, scIsReg (scParityReg k) = some k
  | 0 => rfl
  | k + 1 => by
      show (scIsReg (scParityReg k)).map (· + 1) = some (k + 1)
      rw [scIsReg_parityReg k]
      rfl

theorem scMaxReg_parityReg : ∀ k, scMaxReg (scParityReg k) = k
  | 0 => rfl
  | k + 1 => by
      show max (max (scMaxReg .C) (scMaxReg (scParityReg k)))
        ((scIsReg (.app .C (scParityReg k))).getD 0) = k + 1
      have h1 : scIsReg (.app .C (scParityReg k)) = some (k + 1) := by
        show (scIsReg (scParityReg k)).map (· + 1) = some (k + 1)
        rw [scIsReg_parityReg k]
        rfl
      rw [h1, scMaxReg_parityReg k]
      show max (max 0 k) (k + 1) = k + 1
      omega

theorem scIsReg_app_parityReg (k : Nat) (x : SCTerm) :
    scIsReg (.app (scParityReg k) x) = none := by
  cases k with
  | zero => rfl
  | succ j => rfl

/-- **The carrier theorem**: the parity orbit at index k holds numeral depth exactly k —
combined with its eternity (Stage 192), every depth rides forever. -/
theorem sc_orbit_carries_depth (k : Nat) : scMaxReg (scParityOrbT k) = k := by
  have hM : scMaxReg (.app (scParityReg k) scW) = k := by
    show max (max (scMaxReg (scParityReg k)) (scMaxReg scW))
      ((scIsReg (.app (scParityReg k) scW)).getD 0) = k
    rw [scMaxReg_parityReg k, scIsReg_app_parityReg k]
    show max (max k 0) 0 = k
    omega
  have hN : ∀ i, scMaxReg (scNof (scParityReg k) i) = k := by
    intro i
    induction i with
    | zero => exact hM
    | succ j ih =>
        show max (max (scMaxReg scW) (scMaxReg (scNof (scParityReg k) j)))
          ((scIsReg (.app scW (scNof (scParityReg k) j))).getD 0) = k
        have : scIsReg (.app scW (scNof (scParityReg k) j)) = none := rfl
        rw [this, ih]
        show max (max 0 k) 0 = k
        omega
  show max (max (scMaxReg (.app (.app (scParityReg k) scW) (scNof (scParityReg k) 1)))
      (scMaxReg (scNof (scParityReg k) 2)))
    ((scIsReg (scParityOrbT k)).getD 0) = k
  have h2 : scIsReg (scParityOrbT k) = none := by
    show scIsReg (.app (.app (.app (scParityReg k) scW) _) _) = none
    rfl
  have h3 : scMaxReg (.app (.app (scParityReg k) scW) (scNof (scParityReg k) 1)) = k := by
    show max (max (scMaxReg (.app (scParityReg k) scW))
        (scMaxReg (scNof (scParityReg k) 1)))
      ((scIsReg (.app (.app (scParityReg k) scW) (scNof (scParityReg k) 1))).getD 0) = k
    have : scIsReg (.app (.app (scParityReg k) scW) (scNof (scParityReg k) 1)) = none := rfl
    rw [this, hM, hN 1]
    show max (max k k) 0 = k
    omega
  rw [h2, h3, hN 2]
  show max (max k k) 0 = k
  omega

-- ## Stage 230: C10, formalized — the deepening question as a proposition
-- The regrowth question becomes a Lean statement: `scDeepening` — some single term whose
-- reachable set attains every numeral depth. The quantifier order IS the question: the
-- counting chain gives the swapped form for free (`sc_depth_breadth`: for every n, SOME
-- term reaches depth n — breadth), and the speed limit prices the strong form
-- (`sc_depth_cost`: reaching depth n from a depth-zero term costs at least n fires —
-- deepening is linear-time at best). Every pinned eternal machine refutes its own
-- candidacy (Stages 228–229); 3.5 million probes found no witness; and no counting
-- invariant can refute it (S-stock farms). The program's second frontier now lives in
-- the theory itself, one definition long.

/-- **C10, the deepening question**: does any single term reach every numeral depth? -/
def scDeepening : Prop :=
  ∃ t : SCTerm, ∀ n : Nat, ∃ u : SCTerm, RS.SC.Steps t u ∧ n ≤ scMaxReg u

/-- **Breadth is free**: for every depth, SOME term reaches it — the counting chain
delivers `C^n S` to a continuation. The quantifier swap between this and `scDeepening`
is the entire question. -/
theorem sc_depth_breadth : ∀ n : Nat, ∃ t u : SCTerm,
    RS.SC.Steps t u ∧ n ≤ scMaxReg u := by
  intro n
  obtain ⟨u, hu, hunder⟩ := sc_bounded_odometer n 0 .S
  refine ⟨.app (scChain n .S) (scParityReg 0), u, hu, ?_⟩
  have : scMaxReg (.app .S (scParityReg (0 + n))) = n := by
    show max (max (scMaxReg .S) (scMaxReg (scParityReg (0 + n))))
      ((scIsReg (.app .S (scParityReg (0 + n)))).getD 0) = n
    have h1 : scIsReg (.app .S (scParityReg (0 + n))) = none := rfl
    rw [h1, scMaxReg_parityReg]
    show max (max 0 (0 + n)) 0 = n
    omega
  clear hu
  induction hunder with
  | refl => omega
  | @app w x _ ih =>
      show n ≤ max (max (scMaxReg w) (scMaxReg x)) ((scIsReg (.app w x)).getD 0)
      omega

/-- **Deepening is linear-time at best**: reaching depth `n` from a depth-zero start
costs at least `n` fires. -/
theorem sc_depth_cost {n m : Nat} {t u : SCTerm}
    (h : RS.SC.StepsN m t u) (ht : scMaxReg t = 0) (hu : n ≤ scMaxReg u) :
    n ≤ m := by
  have := sc_numeral_speed_limit_run h
  omega

-- ## Stage 231: the medium reads order — words in junk, fate in sequence
-- Mixed junk streams are WORDS: over 231 register pairs, twenty-seven give
-- order-sensitive burns — the same multiset of blocks, applied in different orders, has
-- different fates. Pinned exemplar: blocks `J(S)` and `J(C C)` (the reader-frame junk of
-- the atoms). The order `J(CC)·J(S)·J(S)` dies in nineteen fires at a 21-leaf normal
-- form (`sc_order_halts`, axiom-free, normality included); the order `J(S)·J(CC)·J(S)`
-- ignites a period-2 growth wave, past 2,500 leaves by fire 149 (probe; its template is
-- a compound insert-and-mutate process, recorded unpinned). The burn is not just alive —
-- it is a READER of block sequences, and junk streams carry information in their order:
-- the medium is a tape after all, written by machines and read by fate.

/-- The junk block of the atom `S`. -/
def scJS : SCTerm :=
  .app (.app .C (.app (.app .C (.app .C .S)) (.app .C .S))) (.app .C .S)

/-- The junk block of the dead bit `C C`. -/
def scJW : SCTerm :=
  .app (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C .C))))
    (.app .C (.app .C .C))

/-- The halting order's normal form. -/
def scOrderNf : SCTerm :=
  .app (.app .C scJS) (.app (.app .S scJS) (.app .C (.app .C .C)))

/-- **Order decides fate, halting side**: `J(CC)·J(S)·J(S)` dies in nineteen fires. -/
theorem sc_order_halts :
    RS.SC.StepsN 19 (.app (.app scJW scJS) scJS) scOrderNf :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C .C))) (.app .C (.app .C .C)) scJS))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app .C .C)) (.app .C (.app .C .C)) scJS)))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) scJS (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app .C .C)) scJS)))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red scJS (.app .C (.app .C .C)) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C (.app .C .S)) (.app .C .S)) (.app .C .S) (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .S) (.app .C .S) (.app .C (.app .C .C))))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C (.app .C .C)) (.app .C .S)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C .S) (.app .C (.app .C .C)) (.app .C .S))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .S) (.app (.app .C (.app .C .C)) (.app .C .S)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app (.app .C (.app .C .C)) (.app .C .S)) (.app .C .S) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C .S) (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app .C .C)) (.app .C .S))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .S) (.app .C (.app .C .C)) (.app (.app .C .S) (.app .C (.app .C .C)))))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S (.app (.app .C .S) (.app .C (.app .C .C))) (.app .C (.app .C .C))))
  (RS.StepsN.tail (SCStep.S_red (.app .C (.app .C .C)) (.app (.app .C .S) (.app .C (.app .C .C))) scJS)
  (RS.StepsN.tail (SCStep.C_red (.app .C .C) scJS (.app (.app (.app .C .S) (.app .C (.app .C .C))) scJS))
  (RS.StepsN.tail (SCStep.C_red .C (.app (.app (.app .C .S) (.app .C (.app .C .C))) scJS) scJS)
  (RS.StepsN.tail (SCStep.appR (SCStep.C_red .S (.app .C (.app .C .C)) scJS))
  (@RS.StepsN.refl RS.SC scOrderNf))))))))))))))))))))

theorem scOrderNf_normal : ∀ v, ¬ RS.SC.step scOrderNf v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scOrderNf = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

-- ## Stage 232: the n=16 mountain — excess 101, five rungs
-- The graft heuristic's fourth straight win (208 tries): a 16-leaf climber in the same
-- structural family runs a fully forced 600-step prefix to a 308-leaf peak (step 503),
-- with a 207-leaf off-prefix target four checked steps past the end. Excess 101 — the
-- ladder crosses one hundred: 12, 44, 69, 86, 101 at n = 8, 10, 12, 14, 16, one family
-- of climbers, cost still linear in the path (march-600).

/-- Sixteen leaves: the n=14 champion with the same graft pattern extended. -/
def scMt8T : SCTerm := (.app (.app (.app (.app (.app .C (.app .S (.app .S .S))) .S) (.app .S .S)) .C) (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))

/-- 207 leaves, four checked steps past the 600-step forced prefix. -/
def scMt8U : SCTerm := (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S .C) (.app (.app .S (.app (.app .S .S) .S)) .C)))

def scMt8Path : List SCTerm := scForcedMarch scMt8T 600 ++
  [(.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S .C) (.app (.app .S (.app (.app .S .S) .S)) .C))),
   (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S .C) (.app (.app .S (.app (.app .S .S) .S)) .C))),
   (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S .C) (.app (.app .S (.app (.app .S .S) .S)) .C))),
   (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C) (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app (.app .C (.app .C (.app .C .C))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C))))))))))))))))))))))))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app .C (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)) (.app .C (.app (.app .S (.app (.app .C .S) (.app .C (.app .C (.app .C .C))))) .C)))) (.app (.app .S .C) (.app (.app .S (.app (.app .S .S) .S)) .C)))]

section
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000

#guard scMt8T.leafCount = 16
#guard scMt8U.leafCount = 207
#guard (scForcedMarch scMt8T 600).length = 600

/-- The crossing exists. -/
theorem scMt8_steps : RS.SC.Steps scMt8T scMt8U :=
  scChained_steps scMt8Path scMt8T scMt8U (by decide) (by decide)

/-- **The n=16 mountain**: no path from 16 to 207 leaves stays within 307. -/
theorem scMt8_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 307 scMt8T scMt8U :=
  scForced_mountain (scForcedMarch scMt8T 600) (scForcedMarch_forced 600 scMt8T)
    (by decide) (by decide)

end

/-- **The n=16 floor**: every valid bounding function clears 308 at (16, 207). -/
theorem sc_bound_floor_308 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    308 ≤ f 16 207 := by
  by_cases h : 308 ≤ f 16 207
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 16 207) scMt8T scMt8U :=
      hf scMt8T scMt8U scMt8_steps
    exact scMt8_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 233: the corridor — one term, unbounded forced flight, mountains on the path
-- The n=12 climber `scMt5T` does not merely climb once: its reduction path is FORCED for
-- at least sixty thousand fires (probe), oscillating through peaks past 3,500 leaves —
-- a single 12-leaf term whose entire reachable set is one corridor. Mountains now live
-- ON the path: the new lemma `scForced_mountain_last` certifies capped-path exclusion
-- for an on-path target (every path to the corridor's fire-k state IS the corridor's
-- first k fires), and the pinned instance takes the fire-1958 peak (666 leaves) against
-- the fire-2109 dip (515 leaves): `sc_bound_floor_666` — excess 151 at (12, 515), from
-- the same term that gave excess 57 at Stage 187. The corridor's deeper dips give excess
-- 241, 420, and beyond (probe); the kernel march is the only budget.

/-- On-path version of the chain-bound: a forced chain ending at `u` bounds every
earlier element under any capped path to `u`. -/
theorem scForced_all_le_last : ∀ (l₁ : List SCTerm) (t u : SCTerm) (c : Nat),
    SCForced t (l₁ ++ [u]) → RS.StepsLe RS.SC SCTerm.leafCount c t u →
    u ∉ t :: l₁ → ∀ x ∈ t :: l₁, x.leafCount ≤ c := by
  intro l₁
  induction l₁ with
  | nil =>
      intro t u c hf h hu x hx
      have hne : t ≠ u := fun he => hu (he ▸ List.mem_cons_self)
      have hx' : x = t := by
        rcases List.mem_cons.mp hx with h' | h'
        · exact h'
        · exact absurd h' List.not_mem_nil
      rw [hx']
      exact RS.StepsLe.head_le h
  | cons v l₁ ih =>
      intro t u c hf h hu x hx
      have hne : t ≠ u := fun he => hu (he ▸ List.mem_cons_self)
      obtain ⟨b, s, rest⟩ := RS.StepsLe.cases_ne h hne
      have hb := scSucc_complete s
      rw [hf.1] at hb
      have hbv : b = v := by
        rcases List.mem_cons.mp hb with h' | h'
        · exact h'
        · exact absurd h' List.not_mem_nil
      subst hbv
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact RS.StepsLe.head_le h
      · exact ih b u c hf.2 rest
          (fun hmem => hu (List.mem_cons_of_mem t hmem)) x hx'

/-- **The on-path mountain**: a forced chain to `u` with an earlier over-cap peak
excludes every capped path to `u`. -/
theorem scForced_mountain_last {c : Nat} {t u : SCTerm} (l₁ : List SCTerm)
    (hf : SCForced t (l₁ ++ [u])) (hpeak : ∃ x ∈ t :: l₁, c < x.leafCount)
    (hu : u ∉ t :: l₁) :
    ¬ RS.StepsLe RS.SC SCTerm.leafCount c t u := by
  intro h
  obtain ⟨x, hx, hcx⟩ := hpeak
  exact absurd (scForced_all_le_last l₁ t u c hf h hu x hx) (by omega)

/-- The corridor's fire-2109 state: 515 leaves, past the 666-leaf peak. -/
def scMt9U : SCTerm := (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app .S .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))))))))))))))))))))))))))))))))))))))))))))))))))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))

section
set_option maxRecDepth 90000
set_option maxHeartbeats 40000000

#guard scMt9U.leafCount = 515
#guard (scForcedMarch scMt5T 2109).length = 2109
#guard (scForcedMarch scMt5T 2109).getLastD scMt5T == scMt9U

/-- The crossing: the corridor itself. -/
theorem scMt9_steps : RS.SC.Steps scMt5T scMt9U :=
  scChained_steps (scForcedMarch scMt5T 2109) scMt5T scMt9U
    (scForced_chained _ _ (scForcedMarch_forced 2109 scMt5T)) (by decide)

/-- **The corridor mountain**: no path from `scMt5T` to the fire-2109 state stays
within 665 leaves. -/
theorem scMt9_no_capped_path : ¬ RS.StepsLe RS.SC SCTerm.leafCount 665 scMt5T scMt9U :=
  scForced_mountain_last (scForcedMarch scMt5T 2108)
    (by
      have h : scForcedMarch scMt5T 2108 ++ [scMt9U] = scForcedMarch scMt5T 2109 := by
        decide
      rw [h]
      exact scForcedMarch_forced 2109 scMt5T)
    (by decide) (by decide)

end

/-- **The corridor floor**: every valid bounding function clears 666 at (12, 515) —
the same 12-leaf term that held the excess-57 record now yields excess 151, with
241-plus available deeper in its corridor. -/
theorem sc_bound_floor_666 (f : Nat → Nat → Nat)
    (hf : ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u) :
    666 ≤ f 12 515 := by
  by_cases h : 666 ≤ f 12 515
  · exact h
  · exfalso
    have hs : RS.StepsLe RS.SC SCTerm.leafCount (f 12 515) scMt5T scMt9U :=
      hf scMt5T scMt9U scMt9_steps
    exact scMt9_no_capped_path (RS.StepsLe.weaken (by omega) hs)

-- ## Stage 236: the spiral family, anchored — C11's formal ground floor
-- The Φ(j) family of the spiral law, defined exactly from the corridor's template and
-- ANCHORED: forty-four concrete fires take the n=12 climber `scMt5T` to `scSpiral 0`.
-- The family: `Φ(j) = C · A · (C · x · B₁ · Y · T(j) · B₂^(3+j))` with the tower growing
-- by the pass-through context `(C C)·(C ·)` per cycle and the run adding one B₂. C11 —
-- `∀ j, Φ(j) ⟶^(30+6j) Φ(j+1)` — is stated as the target; its proof (twelve fixed fires
-- plus six per run-block, tower passive) is the program's next formalization arc, with
-- every constant verified through eighty probe cycles.

/-- The spiral's outer argument. -/
def scSpA : SCTerm := (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- The prefix block. -/
def scSpB1 : SCTerm := (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))))

/-- The run block. -/
def scSpB2 : SCTerm := (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- The nineteen-leaf anchor argument. -/
def scSpY : SCTerm := (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))))))

/-- The tower's base. -/
def scSpT0 : SCTerm := (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))))))

/-- The tower: one pass-through context per cycle. -/
def scSpTower : Nat → SCTerm
  | 0 => scSpT0
  | j + 1 => .app (.app .C .C) (.app .C (scSpTower j))

/-- The spiral state at cycle `j`. -/
def scSpiral (j : Nat) : SCTerm :=
  .app (.app .C scSpA)
    (scAppList .C ([.C, scSpB1, scSpY, scSpTower j] ++ List.replicate (3 + j) scSpB2))

/-- **The anchor**: forty-four fires from the n=12 climber to the spiral's ground state. -/
theorem sc_spiral_anchor : RS.SC.StepsN 44 scMt5T (scSpiral 0) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .S .S (.app .S .S))))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app .S .S) .S .C))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .S .C (.app .S .C)))
  (RS.StepsN.tail (SCStep.S_red (.app .S .C) (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))
  (RS.StepsN.tail (SCStep.S_red .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpA)
  (RS.StepsN.tail (SCStep.appR (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C scSpA))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red .S (.app .C .C) scSpA)))
  (RS.StepsN.tail (SCStep.appR (SCStep.S_red scSpA (.app .C .C) (.app .C scSpA)))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))
  (RS.StepsN.tail (SCStep.appR (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 (.app (.app .C .C) (.app .C scSpA))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C (.app (.app .C .C) (.app .C scSpA)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.S_red (.app (.app .C .C) (.app .C scSpA)) (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C scSpA) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (.app .C scSpA))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C scSpA)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app .C scSpA) (.app .C scSpA) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red scSpA (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (.app .C scSpA))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (.app .C .C) scSpB1))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app (.app .C .C) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (.app (.app .C .C) scSpB1) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app (.app .C .C) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (.app (.app .C .C) scSpB1) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C scSpA) (.app (.app .C .C) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (.app (.app .C .C) scSpB1) (.app .C scSpA)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpA) (.app .C scSpA) (.app (.app .C .C) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red scSpA (.app (.app .C .C) scSpB1) (.app .C scSpA)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 (.app (.app .C .C) scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C (.app (.app .C .C) scSpB1))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) (.app (.app .C .C) scSpB1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .C) scSpB1) (.app .C .C) scSpY)))))
  (@RS.StepsN.refl RS.SC (scSpiral 0))))))))))))))))))))))))))))))))))))))))))))))

/-- **C11, the spiral law** (registered target): every cycle in `30 + 6j` fires. -/
def scSpiralLaw : Prop :=
  ∀ j : Nat, RS.SC.StepsN (30 + 6 * j) (scSpiral j) (scSpiral (j + 1))

-- ## Stage 237: the spiral turns — cycle law at j = 0 and j = 1
-- The first two turns of the spiral, kernel-certified: thirty fires from `scSpiral 0`
-- to `scSpiral 1`, thirty-six from `scSpiral 1` to `scSpiral 2` — the 30 + 6j schedule
-- live, the family definitions exact against the corridor. With the anchor this gives
-- `scMt5T ⟶⁴⁴⁺³⁰⁺³⁶ scSpiral 2` outright, and the parametric `scSpiralLaw` now rests on
-- one remaining lemma: the six-fire run-block step, whose shape these two concrete
-- cycles pin from both ends.

/-- **The first turn**: thirty fires, `scSpiral 0` to `scSpiral 1`. -/
theorem sc_spiral_turn0 : RS.SC.StepsN 30 (scSpiral 0) (scSpiral 1) :=
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpY))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpB1 scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) scSpT0 scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpB1))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 scSpB1 scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) scSpT0 scSpB1)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpB1))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) scSpT0 (.app .C (.app (.app .C .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) scSpT0 (.app .C (.app (.app .C .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C scSpA) scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) scSpT0 (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpA) (.app .C scSpA) scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpA scSpT0 (.app .C scSpA))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 scSpT0)))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C scSpT0))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) scSpT0)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red scSpT0 (.app .C .C) (.app .C scSpT0)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY (.app .C scSpT0))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpT0) scSpY (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpT0 (scSpTower 1) scSpY))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY scSpY)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpY (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) (scSpTower 1) scSpY))))))
  (@RS.StepsN.refl RS.SC (scSpiral 1))))))))))))))))))))))))))))))))

/-- **The second turn**: thirty-six fires, `scSpiral 1` to `scSpiral 2`. -/
theorem sc_spiral_turn1 : RS.SC.StepsN 36 (scSpiral 1) (scSpiral 2) :=
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpY)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpB1 (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) (scSpTower 1) scSpB1))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpB1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 scSpB1 (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (scSpTower 1) scSpB1))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpB1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 (.app .C (.app (.app .C .C) (.app .C scSpA))) (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (scSpTower 1) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))) (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (scSpTower 1) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C scSpA) (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (scSpTower 1) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpA) (.app .C scSpA) (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpA (scSpTower 1) (.app .C scSpA)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 (scSpTower 1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C (scSpTower 1))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) (scSpTower 1)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (scSpTower 1) (.app .C .C) (.app .C (scSpTower 1)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpT0) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (scSpTower 1)) (.app .C scSpT0) (.app (.app .C .C) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (scSpTower 1) (.app (.app .C .C) (.app .C (scSpTower 1))) (.app .C scSpT0))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpT0) (.app .C scSpT0)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpT0) (.app .C scSpT0) (.app (.app .C .C) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpT0 (.app (.app .C .C) (.app .C (scSpTower 1))) (.app .C scSpT0))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY (.app .C scSpT0)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpT0) scSpY (.app (.app .C .C) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpT0 (.app (.app .C .C) (.app .C (scSpTower 1))) scSpY)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY scSpY))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpY (.app (.app .C .C) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) (.app (.app .C .C) (.app .C (scSpTower 1))) scSpY)))))))
  (@RS.StepsN.refl RS.SC (scSpiral 2))))))))))))))))))))))))))))))))))))))

/-- The climber reaches the spiral's third state in 110 fires. -/
theorem sc_spiral_reach2 : RS.SC.StepsN 110 scMt5T (scSpiral 2) := by
  have h := RS.StepsN.trans sc_spiral_anchor
    (RS.StepsN.trans sc_spiral_turn0 sc_spiral_turn1)
  rw [show (110 : Nat) = 44 + (30 + 36) from rfl]
  exact h


-- ## Stage 238: the third turn — and the cycle's true anatomy
-- Forty-two more fires certify the third schedule point (30, 36, 42 all kernel facts).
-- The walker analysis corrected the cycle's anatomy: the block run never ignites — it
-- rides as passive suffix, exactly as the cargo law prescribes; all thirty-plus fires
-- churn the blob's leading four arguments. The head matter burns, the TOWER passes
-- through the mill and re-emerges one layer taller, a fresh run-block is minted at the
-- burn's bottom, and the front rebuilds. The 6j in the schedule is six fires per TOWER
-- LAYER (tower and block count are locked at +1 per cycle, indistinguishable by
-- arithmetic alone — only the trace separates them). The spiral is head-metabolism with
-- a passive wake: the machine reprocesses its own growing tower every cycle, the first
-- pinned process whose period grows because its own state does.

/-- **The third turn**: forty-two fires, `scSpiral 2` to `scSpiral 3`. -/
theorem sc_spiral_turn2 : RS.SC.StepsN 42 (scSpiral 2) (scSpiral 3) :=
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpY))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpB1 (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) (scSpTower 2) scSpB1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpB1 scSpB1))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 scSpB1 (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (scSpTower 2) scSpB1)))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) scSpB1))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpB1 (.app .C (.app (.app .C .C) (.app .C scSpA))) (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C (.app (.app .C .C) (.app .C scSpA)))) (scSpTower 2) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C (.app (.app .C .C) (.app .C scSpA))) (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (scSpTower 2) (.app .C (.app (.app .C .C) (.app .C scSpA))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C (.app (.app .C .C) (.app .C scSpA)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C scSpA))) (.app .C scSpA) (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app .C scSpA)) (scSpTower 2) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpA) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpA) (.app .C scSpA) (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpA (scSpTower 2) (.app .C scSpA))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scSpA)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red .C (.app .C scSpA) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) scSpB2 (scSpTower 2))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C (scSpTower 2)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) (scSpTower 2))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.S_red (scSpTower 2) (.app .C .C) (.app .C (scSpTower 2))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (scSpTower 1)) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (scSpTower 2)) (.app .C (scSpTower 1)) (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (scSpTower 2) (.app (.app .C .C) (.app .C (scSpTower 2))) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C (scSpTower 1)) (.app .C (scSpTower 1)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (scSpTower 1)) (.app .C (scSpTower 1)) (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (scSpTower 1) (.app (.app .C .C) (.app .C (scSpTower 2))) (.app .C (scSpTower 1))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpT0) (.app .C (scSpTower 1)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (scSpTower 1)) (.app .C scSpT0) (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (scSpTower 1) (.app (.app .C .C) (.app .C (scSpTower 2))) (.app .C scSpT0)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app .C scSpT0) (.app .C scSpT0))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpT0) (.app .C scSpT0) (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpT0 (.app (.app .C .C) (.app .C (scSpTower 2))) (.app .C scSpT0)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY (.app .C scSpT0))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C scSpT0) scSpY (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpT0 (.app (.app .C .C) (.app .C (scSpTower 2))) scSpY))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C scSpY scSpY)))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red scSpY scSpY (.app (.app .C .C) (.app .C (scSpTower 2)))))))))))
  (RS.StepsN.tail (SCStep.appR (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) scSpB1) (.app (.app .C .C) (.app .C (scSpTower 2))) scSpY))))))))
  (@RS.StepsN.refl RS.SC (scSpiral 3))))))))))))))))))))))))))))))))))))))))))))

/-- The climber reaches the spiral's fourth state in 152 fires. -/
theorem sc_spiral_reach3 : RS.SC.StepsN 152 scMt5T (scSpiral 3) := by
  have h := RS.StepsN.trans sc_spiral_reach2 sc_spiral_turn2
  rw [show (152 : Nat) = 110 + 42 from rfl]
  exact h
