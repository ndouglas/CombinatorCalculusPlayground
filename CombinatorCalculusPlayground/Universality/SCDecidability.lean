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

-- ## Stage 240: THE MILL LAWS — C11 dissolves into two six-fire lemmas
-- The spiral's engine, fully reverse-engineered, is almost nothing: the corridor runs on
-- a two-counter machine `G a m = T_a · (C T_a) · T_m` over the layer grammar
-- `L x = (C C)(C x)` and a nine-leaf core `K` — and B₁, Y, the tower, even the junk
-- block are all tower-terms in disguise (B₁ = C·T₂, Y = C·T₃, B₂ = (C·K)·tail₈ with
-- tail₈ the climber's own original tail). Two laws drive everything: THE DESCENT
-- (`(L x)·(C (L x))·y ⟶⁶ x·(C x)·y`, any x y — the counter strips a layer) and THE
-- TURNOVER (`K·(C K)·M ⟶⁶ M·(C M)·(L M)·B₂`, any M — at zero the core fires, the
-- counter is REBUILT AS A COPY OF THE TOWER in one duplication, the tower gains a
-- layer, one junk block falls out). The cycle law, the eternal spiral, and the
-- unbounded corridor are arithmetic over these two lemmas. C11, proved.

/-- The layer: `L x = (C C)(C x)`. -/
def scMillL (x : SCTerm) : SCTerm := .app (.app .C .C) (.app .C x)

/-- The nine-leaf core at the bottom of every tower. -/
def scMillK : SCTerm := (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- The tower: `m` layers over the core. -/
def scMillT : Nat → SCTerm
  | 0 => scMillK
  | m + 1 => scMillL (scMillT m)

/-- The junk block: the core, C-parked, holding the climber's original tail. -/
def scMillB2 : SCTerm := (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))

/-- The two-counter state. -/
def scMillG (a m : Nat) : SCTerm :=
  .app (.app (scMillT a) (.app .C (scMillT a))) (scMillT m)

/-- **THE DESCENT**: six fires strip one counter layer — any payloads. -/
theorem sc_mill_descent (x y : SCTerm) :
    RS.SC.StepsN 6
      (.app (.app (scMillL x) (.app .C (scMillL x))) y)
      (.app (.app x (.app .C x)) y) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C x) (.app .C (.app (.app .C .C) (.app .C x)))))
  (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C x))) (.app .C x) y)
  (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C x)) y (.app .C x))
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C x) (.app .C x)))
  (RS.StepsN.tail (SCStep.C_red (.app .C x) (.app .C x) y)
  (RS.StepsN.tail (SCStep.C_red x y (.app .C x))
  (@RS.StepsN.refl RS.SC (.app (.app x (.app .C x)) y))))))))

/-- **THE TURNOVER**: at counter zero the core fires — the counter is rebuilt as a copy
of the tower (one duplication, six fires at every scale), the tower gains a layer, one
junk block is emitted. -/
theorem sc_mill_turnover (M : SCTerm) :
    RS.SC.StepsN 6
      (.app (.app scMillK (.app .C scMillK)) M)
      (.app (.app (.app M (.app .C M)) (.app (.app .C .C) (.app .C M))) scMillB2) :=
  (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app .C scMillK)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red .C (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))
  (RS.StepsN.tail (SCStep.C_red (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) M)
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app (.app .C .S) (.app .C .C)) .C M))
  (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .S (.app .C .C) M)))
  (RS.StepsN.tail (SCStep.appL (SCStep.S_red M (.app .C .C) (.app .C M)))
  (@RS.StepsN.refl RS.SC (.app (.app (.app M (.app .C M)) (.app (.app .C .C) (.app .C M))) scMillB2))))))))

/-- Descent, iterated. -/
theorem sc_mill_descent_run : ∀ (d a m : Nat),
    RS.SC.StepsN (6 * d) (scMillG (a + d) m) (scMillG a m)
  | 0, _, _ => @RS.StepsN.refl RS.SC _
  | d + 1, a, m => by
      rw [show 6 * (d + 1) = 6 + 6 * d from by omega,
        show a + (d + 1) = (a + d) + 1 from by omega]
      exact RS.StepsN.trans (sc_mill_descent (scMillT (a + d)) (scMillT m))
        (sc_mill_descent_run d a m)

/-- **THE CYCLE**: one revolution from counter zero in `6(m+1)` fires, one block out. -/
theorem sc_mill_cycle (m : Nat) :
    RS.SC.StepsN (6 * (m + 1)) (scMillG 0 m) (.app (scMillG 0 (m + 1)) scMillB2) := by
  have h1 := sc_mill_turnover (scMillT m)
  have h2 : RS.SC.StepsN (6 * m) (.app (scMillG (0 + m) (m + 1)) scMillB2)
      (.app (scMillG 0 (m + 1)) scMillB2) :=
    scStepsN_appL scMillB2 (sc_mill_descent_run m 0 (m + 1))
  rw [show (0 : Nat) + m = m from by omega] at h2
  rw [show 6 * (m + 1) = 6 + 6 * m from by omega]
  exact RS.StepsN.trans h1 h2

/-- `Steps` under a rider list. -/
theorem scSteps_appList {t t' : SCTerm} (l : List SCTerm) (h : RS.SC.Steps t t') :
    RS.SC.Steps (scAppList t l) (scAppList t' l) := by
  induction l generalizing t t' with
  | nil => exact h
  | cons w ws ih => exact ih (scSteps_appL w h)

/-- **THE ETERNAL SPIRAL**: `k` revolutions raise the tower by `k`, leave `k` blocks. -/
theorem sc_mill_eternal : ∀ (k m : Nat),
    RS.SC.Steps (scMillG 0 m)
      (scAppList (scMillG 0 (m + k)) (List.replicate k scMillB2))
  | 0, m => @RS.Steps.refl RS.SC (scMillG 0 m)
  | k + 1, m => by
      have hstep : RS.SC.StepsN (6 * (m + k + 1))
          (scAppList (scMillG 0 (m + k)) (List.replicate k scMillB2))
          (scAppList (.app (scMillG 0 (m + k + 1)) scMillB2)
            (List.replicate k scMillB2)) :=
        scStepsN_appList (List.replicate k scMillB2) (sc_mill_cycle (m + k))
      have h := RS.Steps.trans (sc_mill_eternal k m) (RS.StepsN.toSteps hstep)
      rw [show m + (k + 1) = m + k + 1 from by omega, List.replicate_succ]
      exact h

theorem scMillT_size : ∀ m, (scMillT m).leafCount = 9 + 3 * m
  | 0 => rfl
  | m + 1 => by
      show 1 + 1 + (1 + (scMillT m).leafCount) = 9 + 3 * (m + 1)
      rw [scMillT_size m]
      omega

theorem scAppList_leaf_ge : ∀ (l : List SCTerm) (t : SCTerm),
    t.leafCount ≤ (scAppList t l).leafCount
  | [], _ => Nat.le_refl _
  | w :: ws, t => by
      have h1 : t.leafCount ≤ (SCTerm.app t w).leafCount := by
        show t.leafCount ≤ t.leafCount + w.leafCount
        omega
      exact Nat.le_trans h1 (scAppList_leaf_ge ws (.app t w))

/-- The spiral's ground state is a zero-phase-adjacent mill state, three blocks riding. -/
theorem sc_spiral_is_mill :
    scSpiral 0 = .app (.app .C scSpA)
      (scAppList (scMillG 3 4) (List.replicate 3 scMillB2)) := by
  decide

/-- **THE CORRIDOR IS INFINITE**: the 12-leaf climber's reachable set is unbounded —
certified end to end, anchor through mill. C11's headline corollary. -/
theorem sc_corridor_unbounded (n : Nat) :
    ∃ u : SCTerm, RS.SC.Steps scMt5T u ∧ n ≤ u.leafCount := by
  refine ⟨.app (.app .C scSpA)
    (scAppList (scAppList (scMillG 0 (4 + n)) (List.replicate n scMillB2))
      (List.replicate 3 scMillB2)), ?_, ?_⟩
  · have h0 : RS.SC.Steps scMt5T (scSpiral 0) := RS.StepsN.toSteps sc_spiral_anchor
    rw [sc_spiral_is_mill] at h0
    have hd : RS.SC.StepsN (6 * 3) (scMillG (0 + 3) 4) (scMillG 0 4) :=
      sc_mill_descent_run 3 0 4
    have hd' : RS.SC.Steps (scMillG 3 4) (scMillG 0 4) := by
      have := RS.StepsN.toSteps hd
      rw [show (0 : Nat) + 3 = 3 from rfl] at this
      exact this
    exact RS.Steps.trans h0 (scSteps_appR _
      (RS.Steps.trans (scSteps_appList _ hd')
        (scSteps_appList _ (sc_mill_eternal n 4))))
  · have hk : (scMillT 0).leafCount = 9 := rfl
    have hm := scMillT_size (4 + n)
    have hG : n ≤ (scMillG 0 (4 + n)).leafCount := by
      show n ≤ (scMillT 0).leafCount + (1 + (scMillT 0).leafCount)
        + (scMillT (4 + n)).leafCount
      omega
    have h1 := scAppList_leaf_ge (List.replicate n scMillB2) (scMillG 0 (4 + n))
    have h2 := scAppList_leaf_ge (List.replicate 3 scMillB2)
      (scAppList (scMillG 0 (4 + n)) (List.replicate n scMillB2))
    show n ≤ (1 + scSpA.leafCount)
      + (scAppList (scAppList (scMillG 0 (4 + n)) (List.replicate n scMillB2))
          (List.replicate 3 scMillB2)).leafCount
    omega

-- ## Stage 241 (part): the towers are normal — forcedness groundwork
-- The mill's data is inert: the core and every tower over it are normal forms. This is
-- the ground layer of the parametric-forcedness project (the mill path as the UNIQUE
-- path, which would make every mill peak an on-path mountain at every scale).

theorem scMillK_normal : ∀ v, ¬ RS.SC.step scMillK v := by
  intro v h
  have hm := scSucc_complete h
  rw [show scSucc scMillK = [] from rfl] at hm
  exact absurd hm List.not_mem_nil

theorem scMillL_normal {t : SCTerm} (ht : ∀ v, ¬ RS.SC.step t v) :
    ∀ v, ¬ RS.SC.step (scMillL t) v := by
  intro v h
  rcases scCPair_inv h with ⟨x', hx, _⟩ | ⟨y', hy, _⟩
  · cases hx
  · obtain ⟨m', hm, _⟩ := scWrap_inv hy
    exact ht m' hm

theorem scMillT_normal : ∀ m, ∀ v, ¬ RS.SC.step (scMillT m) v
  | 0 => scMillK_normal
  | m + 1 => scMillL_normal (scMillT_normal m)

-- ## Stage 242 (feat): the mill is FORCED — unique successors, parametrically
-- The mill laws gave existence; these give uniqueness. Given normal payloads, every
-- state of the descent and the turnover has EXACTLY ONE successor — the mill path is
-- the only path, parametrically in the towers. With `SCForced_append` the revolutions
-- chain, and the parametric staircase (every mill peak an on-path mountain, at every
-- scale, in one theorem) is now an assembly task over these pieces.

/-- Normality computes: a normal term has an empty successor list. -/
theorem scSucc_nil_of_normal {t : SCTerm} (h : ∀ v, ¬ RS.SC.step t v) :
    scSucc t = [] := by
  cases hs : scSucc t with
  | nil => rfl
  | cons a l =>
      exact absurd (scSucc_sound (hs ▸ List.mem_cons_self)) (h a)

/-- Forced chains concatenate. -/
theorem SCForced_append : ∀ {l₁ l₂ : List SCTerm} {t : SCTerm},
    SCForced t l₁ → SCForced (l₁.getLastD t) l₂ → SCForced t (l₁ ++ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ t _ h2; exact h2
  | cons v rest ih =>
      intro l₂ t h1 h2
      refine ⟨h1.1, ih h1.2 ?_⟩
      have : (v :: rest).getLastD t = rest.getLastD v := by
        cases rest <;> rfl
      rw [← this]
      exact h2

/-- **The descent is forced**: with normal payloads, each of its six fires is the only
possible fire. -/
theorem sc_mill_descent_forced (x y : SCTerm)
    (hx : scSucc x = []) (hy : scSucc y = []) :
    SCForced (.app (.app (scMillL x) (.app .C (scMillL x))) y)
      [(.app (.app (.app .C (.app .C (.app (.app .C .C) (.app .C x)))) (.app .C x)) y),
       (.app (.app (.app .C (.app (.app .C .C) (.app .C x))) y) (.app .C x)),
       (.app (.app (.app (.app .C .C) (.app .C x)) (.app .C x)) y),
       (.app (.app (.app .C (.app .C x)) (.app .C x)) y),
       (.app (.app (.app .C x) y) (.app .C x)),
       (.app (.app x (.app .C x)) y)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    simp [scMillL, scSucc, scSuccRoot, hx, hy]

/-- **The turnover is forced**: with a normal tower, each of its six fires is the only
possible fire. -/
theorem sc_mill_turnover_forced (M : SCTerm) (hM : scSucc M = []) :
    SCForced (.app (.app scMillK (.app .C scMillK)) M)
      [(.app (.app (.app (.app .S .C) (.app .C scMillK)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) M),
       (.app (.app (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) M),
       (.app (.app (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) M) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
       (.app (.app (.app (.app (.app .C .S) (.app .C .C)) M) (.app .C M)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
       (.app (.app (.app (.app .S M) (.app .C .C)) (.app .C M)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
       (.app (.app (.app M (.app .C M)) (.app (.app .C .C) (.app .C M))) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    simp [scMillK, scSucc, scSuccRoot, hM]

-- ## Stage 242 (part two): the forced descent run — the staircase's spine
-- The descent chain as an explicit list-family, forced at every counter height: the run
-- from `G (a+d) m` to `G a m` is the ONLY reduction, parametrically.

/-- The six descent states for counter payload `x` and tower payload `y`. -/
def scMillDescentStates (x y : SCTerm) : List SCTerm :=
  [(.app (.app (.app .C (.app .C (.app (.app .C .C) (.app .C x)))) (.app .C x)) y),
   (.app (.app (.app .C (.app (.app .C .C) (.app .C x))) y) (.app .C x)),
   (.app (.app (.app (.app .C .C) (.app .C x)) (.app .C x)) y),
   (.app (.app (.app .C (.app .C x)) (.app .C x)) y),
   (.app (.app (.app .C x) y) (.app .C x)),
   (.app (.app x (.app .C x)) y)]

/-- The descent chain from height `a + d` down to `a`. -/
def scMillDescentChain : (d a m : Nat) → List SCTerm
  | 0, _, _ => []
  | d + 1, a, m =>
      scMillDescentStates (scMillT (a + d)) (scMillT m) ++ scMillDescentChain d a m

/-- **The forced descent run**: the mill's way down is the only way. -/
theorem sc_mill_descent_run_forced : ∀ (d a m : Nat),
    SCForced (scMillG (a + d) m) (scMillDescentChain d a m)
  | 0, _, _ => trivial
  | d + 1, a, m => by
      have hx : scSucc (scMillT (a + d)) = [] :=
        scSucc_nil_of_normal (scMillT_normal (a + d))
      have hy : scSucc (scMillT m) = [] :=
        scSucc_nil_of_normal (scMillT_normal m)
      exact SCForced_append
        (by
          show SCForced (scMillG (a + (d + 1)) m)
            (scMillDescentStates (scMillT (a + d)) (scMillT m))
          have h := sc_mill_descent_forced (scMillT (a + d)) (scMillT m) hx hy
          rw [show a + (d + 1) = (a + d) + 1 from by omega]
          exact h)
        (by
          show SCForced ((scMillDescentStates (scMillT (a + d))
            (scMillT m)).getLastD _) (scMillDescentChain d a m)
          exact sc_mill_descent_run_forced d a m)

-- ## Stage 244 (feat): forcedness survives riders — the corridor's junk changes nothing
-- The mill emits a junk block every revolution, so the corridor's states carry ever more
-- riders; this lemma says the riders never open an escape: if a chain is forced and the
-- rider is normal (and no root redex forms at the join), the ridden chain is forced too.
-- With it, forcedness propagates through the junk stack — the last ingredient of the
-- no-normal-form corollary and the parametric staircase.

/-- Forced chains stay forced under a normal rider that forms no root redex. -/
theorem sc_forced_rider : ∀ {l : List SCTerm} {t x : SCTerm},
    scSucc x = [] →
    (∀ u ∈ t :: l, scSuccRoot (.app u x) = []) →
    SCForced t l →
    SCForced (.app t x) (l.map (.app · x)) := by
  intro l
  induction l with
  | nil => intro t x _ _ _; exact trivial
  | cons v rest ih =>
      intro t x hx hroot hf
      refine ⟨?_, ?_⟩
      · show scSucc (.app t x) = [.app v x]
        show scSuccRoot (.app t x)
          ++ (scSucc t).map (fun f' => .app f' x)
          ++ (scSucc x).map (fun x' => .app t x') = [.app v x]
        rw [hroot t List.mem_cons_self, hf.1, hx]
        rfl
      · exact ih hx
          (fun u hu => hroot u (List.mem_cons_of_mem t hu)) hf.2

-- Stage 244 assembly: root-vanishing helpers and the generic no-normal-form principle.

theorem scMillT_isApp : ∀ m, ∃ a b : SCTerm, scMillT m = .app a b
  | 0 => ⟨_, _, rfl⟩
  | _ + 1 => ⟨_, _, rfl⟩

/-- A four-deep application spine has no root redex. -/
theorem scSuccRoot_deep_nil {p q g x z : SCTerm} :
    scSuccRoot (.app (.app (.app (.app p q) g) x) z) = [] := rfl

/-- **The no-normal-form principle**: an infinite family of nonempty forced chains,
each ending where the next begins, traps every reduction — everything reachable from
the family's start still steps. -/
theorem sc_forced_forever_no_nf (F : Nat → SCTerm) (chain : Nat → List SCTerm)
    (hf : ∀ k, SCForced (F k) (chain k))
    (hlast : ∀ k, (chain k).getLastD (F k) = F (k + 1))
    (hne : ∀ k, chain k ≠ []) :
    ∀ u, RS.SC.Steps (F 0) u → ∃ v, RS.SC.step u v := by
  have hmem_succ : ∀ k u, (u = F k ∨ u ∈ chain k) → ∃ w,
      scSucc u = [w] ∧
        ((w = F (k + 1) ∨ w ∈ chain (k + 1)) ∨ w ∈ chain k) := by
    intro k u hu
    rcases hu with rfl | hu
    · cases hc : chain k with
      | nil => exact absurd hc (hne k)
      | cons v rest =>
          have h1 := hf k
          rw [hc] at h1
          exact ⟨v, h1.1, .inr List.mem_cons_self⟩
    · have hwalk : ∀ (l : List SCTerm) (t : SCTerm), SCForced t l →
          l.getLastD t = F (k + 1) → ∀ u ∈ l, ∃ w, scSucc u = [w] ∧
            ((w = F (k + 1) ∨ w ∈ chain (k + 1)) ∨ w ∈ l) := by
        intro l
        induction l with
        | nil => intro t _ _ u hu; exact absurd hu List.not_mem_nil
        | cons v rest ih =>
            intro t hfl hl u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · cases hr : rest with
              | nil =>
                  have hv : u = F (k + 1) := by
                    rw [hr] at hl
                    simpa using hl
                  cases hc2 : chain (k + 1) with
                  | nil => exact absurd hc2 (hne (k + 1))
                  | cons w2 r2 =>
                      have h2 := hf (k + 1)
                      rw [hc2] at h2
                      exact ⟨w2, by rw [hv]; exact h2.1,
                        .inl (.inr List.mem_cons_self)⟩
              | cons v2 r2 =>
                  have h2 := hfl.2
                  rw [hr] at h2
                  exact ⟨v2, h2.1,
                    .inr (List.mem_cons.mpr (.inr List.mem_cons_self))⟩
            · have hl' : rest.getLastD v = F (k + 1) := by
                have hstep : (v :: rest).getLastD t = rest.getLastD v := by
                  cases rest <;> rfl
                rw [← hstep, hl]
              obtain ⟨w, hw, hwm⟩ := ih v hfl.2 hl' u hu'
              exact ⟨w, hw, hwm.imp id (List.mem_cons_of_mem v)⟩
      obtain ⟨w, hw, hwm⟩ := hwalk (chain k) (F k) (hf k) (hlast k) u hu
      exact ⟨w, hw, hwm⟩
  have hreach : ∀ (a u : SCTerm), RS.SC.Steps a u →
      (∃ k, a = F k ∨ a ∈ chain k) → ∃ k, u = F k ∨ u ∈ chain k := by
    intro a u h
    refine h.rec (motive := fun (x y : SCTerm) _ =>
        (∃ k, x = F k ∨ x ∈ chain k) → ∃ k, y = F k ∨ y ∈ chain k) ?_ ?_
    · intro _ hx
      exact hx
    · intro x y c s rest ih hx
      obtain ⟨k, hk⟩ := hx
      obtain ⟨w, hw, hwm⟩ := hmem_succ k x hk
      have hy : y = w := by
        have hm := scSucc_complete s
        rw [hw] at hm
        simpa using hm
      subst hy
      apply ih
      rcases hwm with h1 | h2
      · exact ⟨k + 1, h1.imp id id⟩
      · exact ⟨k, .inr h2⟩
  intro u hsteps
  obtain ⟨k, hk⟩ := hreach (F 0) u hsteps ⟨0, .inl rfl⟩
  obtain ⟨w, hw, _⟩ := hmem_succ k u hk
  exact ⟨w, scSucc_sound (hw ▸ List.mem_cons_self)⟩

-- ## Stage 245: the corridor no-NF assembly, piece A — carriers and chain plumbing.

/-- Mirror of the rider lemma: forcedness survives an inert left carrier. -/
theorem sc_forced_carrier : ∀ {l : List SCTerm} {t c : SCTerm},
    scSucc c = [] →
    (∀ u ∈ t :: l, scSuccRoot (.app c u) = []) →
    SCForced t l →
    SCForced (.app c t) (l.map (.app c ·)) := by
  intro l
  induction l with
  | nil => intro t c _ _ _; exact trivial
  | cons v rest ih =>
      intro t c hc hroot hf
      refine ⟨?_, ?_⟩
      · show scSucc (.app c t) = [.app c v]
        show scSuccRoot (.app c t)
          ++ (scSucc c).map (fun f' => .app f' t)
          ++ (scSucc t).map (fun x' => .app c x') = [.app c v]
        rw [hroot t List.mem_cons_self, hc, hf.1]
        rfl
      · exact ih hc (fun u hu => hroot u (List.mem_cons_of_mem t hu)) hf.2

/-- The outer spiral carrier is inert. -/
theorem scSpCarrier_succ_nil : scSucc (.app .C scSpA) = [] := rfl

/-- The outer carrier never forms a root redex. -/
theorem scSpCarrier_root_nil (u : SCTerm) :
    scSuccRoot (.app (.app .C scSpA) u) = [] := rfl

/-- `getLastD` of an append with a nonempty right part. -/
theorem List.getLastD_append_right {α : Type} {l₂ : List α} (l₁ : List α)
    (h : l₂ ≠ []) : ∀ d d' : α, (l₁ ++ l₂).getLastD d = l₂.getLastD d' := by
  induction l₁ with
  | nil =>
      intro d d'
      cases l₂ with
      | nil => exact absurd rfl h
      | cons a t => rw [List.nil_append, List.getLastD_cons, List.getLastD_cons]
  | cons a l₁ ih =>
      intro d d'
      rw [List.cons_append, List.getLastD_cons]
      exact ih a d'

-- ## Stage 245 piece B: spine depth, iterated riders, and the revolution chain.
-- The route to no-normal-form: every corridor state has left-spine depth ≥ 3, so no
-- rider (junk block or stack) can ever complete a root redex; forcedness therefore
-- survives the whole junk stack and the outer carrier, and the revolutions chain into
-- the family the principle needs.

/-- Left-spine depth at least three: enough structure that no rider completes a redex. -/
def SCSpine3 (u : SCTerm) : Prop :=
  ∃ p q g x : SCTerm, u = .app (.app (.app p q) g) x

/-- A spine-3 term ridden by anything has no root redex. -/
theorem scSuccRoot_nil_of_spine3 {u z : SCTerm} (h : SCSpine3 u) :
    scSuccRoot (.app u z) = [] := by
  obtain ⟨p, q, g, x, rfl⟩ := h
  exact scSuccRoot_deep_nil

/-- Spine depth only grows under application. -/
theorem SCSpine3.app {u : SCTerm} (h : SCSpine3 u) (z : SCTerm) :
    SCSpine3 (.app u z) := by
  obtain ⟨p, q, g, x, rfl⟩ := h
  exact ⟨.app p q, g, x, z, rfl⟩

/-- The two-counter state is spine-3 (towers are applications). -/
theorem scMillG_spine3 (a m : Nat) : SCSpine3 (scMillG a m) := by
  obtain ⟨p, q, hpq⟩ := scMillT_isApp a
  refine ⟨p, q, .app .C (scMillT a), scMillT m, ?_⟩
  show SCTerm.app (.app (scMillT a) (.app .C (scMillT a))) (scMillT m) = _
  rw [hpq]

/-- Every descent state is spine-3 when the counter payload is an application. -/
theorem scMillDescentStates_spine3 {x : SCTerm} (y : SCTerm)
    (hx : ∃ a b, x = .app a b) :
    ∀ u ∈ scMillDescentStates x y, SCSpine3 u := by
  obtain ⟨a, b, rfl⟩ := hx
  intro u hu
  simp only [scMillDescentStates, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl⟩

/-- Every state of the descent run is spine-3. -/
theorem scMillDescentChain_spine3 : ∀ (d a m : Nat),
    ∀ u ∈ scMillDescentChain d a m, SCSpine3 u
  | 0, _, _ => by intro u hu; exact absurd hu (List.not_mem_nil)
  | d + 1, a, m => by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact scMillDescentStates_spine3 (scMillT m) (scMillT_isApp (a + d)) u h
      · exact scMillDescentChain_spine3 d a m u h

/-- A positive descent run is a nonempty chain. -/
theorem scMillDescentChain_ne (d a m : Nat) (hd : 1 ≤ d) :
    scMillDescentChain d a m ≠ [] := by
  cases d with
  | zero => omega
  | succ d =>
      show scMillDescentStates _ _ ++ _ ≠ []
      simp [scMillDescentStates]

/-- The descent run ends at the ground state `G a m`. -/
theorem scMillDescentChain_last (a m : Nat) : ∀ d, 1 ≤ d → ∀ dflt : SCTerm,
    (scMillDescentChain d a m).getLastD dflt = scMillG a m := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
      intro _ dflt
      cases d with
      | zero =>
          show (scMillDescentStates (scMillT (a + 0)) (scMillT m)
            ++ scMillDescentChain 0 a m).getLastD dflt = scMillG a m
          rw [show scMillDescentChain 0 a m = [] from rfl, List.append_nil]
          rfl
      | succ d' =>
          show (scMillDescentStates (scMillT (a + (d' + 1))) (scMillT m)
            ++ scMillDescentChain (d' + 1) a m).getLastD dflt = scMillG a m
          rw [List.getLastD_append_right _
            (scMillDescentChain_ne (d' + 1) a m (by omega)) dflt dflt]
          exact ih (by omega) dflt

/-- The junk block is inert. -/
theorem scMillB2_succ_nil : scSucc scMillB2 = [] := rfl

/-- Forced chains stay forced under a whole stack of inert riders, provided every state
is spine-3 (so no root redex ever forms at any level of the stack). -/
theorem sc_forced_riders : ∀ (zs : List SCTerm) {t : SCTerm} {l : List SCTerm},
    (∀ z ∈ zs, scSucc z = []) →
    (∀ u ∈ t :: l, SCSpine3 u) →
    SCForced t l →
    SCForced (scAppList t zs) (l.map (scAppList · zs)) := by
  intro zs
  induction zs with
  | nil =>
      intro t l _ _ hf
      show SCForced t (l.map (scAppList · []))
      rw [show l.map (scAppList · []) = l from by simp [scAppList]]
      exact hf
  | cons z zs ih =>
      intro t l hz hsp hf
      show SCForced (scAppList (.app t z) zs) (l.map (scAppList · (z :: zs)))
      rw [show l.map (scAppList · (z :: zs))
          = (l.map (.app · z)).map (scAppList · zs) from by
        rw [List.map_map]; rfl]
      refine ih (fun w hw => hz w (List.mem_cons_of_mem z hw)) ?_ ?_
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (hsp t List.mem_cons_self).app z
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
          exact (hsp w (List.mem_cons_of_mem t hw)).app z
      · exact sc_forced_rider (hz z List.mem_cons_self)
          (fun u hu => scSuccRoot_nil_of_spine3 (hsp u hu)) hf

/-- The six turnover states for tower payload `M`. -/
def scMillTurnStates (M : SCTerm) : List SCTerm :=
  [(.app (.app (.app (.app .S .C) (.app .C scMillK)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) M),
   (.app (.app (.app .C (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))) M),
   (.app (.app (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C) M) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
   (.app (.app (.app (.app (.app .C .S) (.app .C .C)) M) (.app .C M)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
   (.app (.app (.app (.app .S M) (.app .C .C)) (.app .C M)) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))),
   (.app (.app (.app M (.app .C M)) (.app (.app .C .C) (.app .C M))) (.app (.app .C scMillK) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))]

/-- The turnover, restated over the named states: from `G 0 m`, six forced fires. -/
theorem scMillTurnStates_forced (m : Nat) :
    SCForced (scMillG 0 m) (scMillTurnStates (scMillT m)) :=
  sc_mill_turnover_forced (scMillT m) (scSucc_nil_of_normal (scMillT_normal m))

/-- Every turnover state is spine-3 when the tower payload is an application. -/
theorem scMillTurnStates_spine3 {M : SCTerm} (hM : ∃ a b, M = .app a b) :
    ∀ u ∈ scMillTurnStates M, SCSpine3 u := by
  obtain ⟨a, b, rfl⟩ := hM
  intro u hu
  simp only [scMillTurnStates, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl⟩

/-- One full revolution from `G 0 m`: six turnover fires, then the descent home under
the freshly emitted junk rider. -/
def scMillRevStates (m : Nat) : List SCTerm :=
  scMillTurnStates (scMillT m)
    ++ (scMillDescentChain m 0 (m + 1)).map (.app · scMillB2)

/-- **The revolution is forced** — from `G 0 m`, the whole cycle is the only reduction. -/
theorem scMillRevStates_forced (m : Nat) :
    SCForced (scMillG 0 m) (scMillRevStates m) := by
  refine SCForced_append (scMillTurnStates_forced m) ?_
  rw [show (scMillTurnStates (scMillT m)).getLastD (scMillG 0 m)
      = .app (scMillG m (m + 1)) scMillB2 from rfl]
  refine sc_forced_rider scMillB2_succ_nil ?_ ?_
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact scSuccRoot_nil_of_spine3 (scMillG_spine3 m (m + 1))
    · exact scSuccRoot_nil_of_spine3 (scMillDescentChain_spine3 m 0 (m + 1) u hu)
  · have h := sc_mill_descent_run_forced m 0 (m + 1)
    rw [Nat.zero_add] at h
    exact h

/-- The revolution ends one tower higher, one junk block richer. -/
theorem scMillRevStates_getLastD (m : Nat) (hm : 1 ≤ m) (dflt : SCTerm) :
    (scMillRevStates m).getLastD dflt = .app (scMillG 0 (m + 1)) scMillB2 := by
  have h1 : (scMillRevStates m).getLastD dflt
      = ((scMillDescentChain m 0 (m + 1)).map (.app · scMillB2)).getLastD
          (.app (scMillG 0 (m + 1)) scMillB2) :=
    List.getLastD_append_right _
      (fun h => scMillDescentChain_ne m 0 (m + 1) hm (List.map_eq_nil_iff.mp h))
      dflt _
  have h2 : ((scMillDescentChain m 0 (m + 1)).map (SCTerm.app · scMillB2)).getLastD
      (SCTerm.app (scMillG 0 (m + 1)) scMillB2)
      = SCTerm.app ((scMillDescentChain m 0 (m + 1)).getLastD (scMillG 0 (m + 1))) scMillB2 :=
    List.getLastD_map
  rw [h1, h2, scMillDescentChain_last 0 (m + 1) m hm]

/-- Revolutions are nonempty chains. -/
theorem scMillRevStates_ne (m : Nat) : scMillRevStates m ≠ [] := by
  show scMillTurnStates (scMillT m) ++ _ ≠ []
  simp [scMillTurnStates]

/-- Every revolution state is spine-3. -/
theorem scMillRevStates_spine3 (m : Nat) :
    ∀ u ∈ scMillRevStates m, SCSpine3 u := by
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact scMillTurnStates_spine3 (scMillT_isApp m) u h
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact (scMillDescentChain_spine3 m 0 (m + 1) w hw).app scMillB2

-- ## Stage 245 piece C: the family, and the climber's no-normal-form theorem.
-- The chain family the principle needs: the forty-four-fire anchor march, the initial
-- three-layer descent, then one ridden revolution per generation — each under the
-- spiral carrier and an ever-deeper junk stack.

/-- The corridor's generation-`k` state: the climber, the spiral ground state, then
tower `4+j` over a `3+j`-deep junk stack under the carrier. -/
def scNoNFF : Nat → SCTerm
  | 0 => scMt5T
  | 1 => .app (.app .C scSpA) (scAppList (scMillG 3 4) (List.replicate 3 scMillB2))
  | j + 2 => .app (.app .C scSpA)
      (scAppList (scMillG 0 (4 + j)) (List.replicate (3 + j) scMillB2))

/-- The generation-`k` forced chain: anchor march, ridden initial descent, then the
ridden revolutions. -/
def scNoNFChain : Nat → List SCTerm
  | 0 => scForcedMarch scMt5T 44
  | 1 => ((scMillDescentChain 3 0 4).map
      (scAppList · (List.replicate 3 scMillB2))).map (.app (.app .C scSpA) ·)
  | j + 2 => ((scMillRevStates (4 + j)).map
      (scAppList · (List.replicate (3 + j) scMillB2))).map (.app (.app .C scSpA) ·)

/-- Every generation's chain is forced. -/
theorem scNoNFF_forced : ∀ k, SCForced (scNoNFF k) (scNoNFChain k)
  | 0 => scForcedMarch_forced 44 scMt5T
  | 1 => by
      refine sc_forced_carrier scSpCarrier_succ_nil
        (fun u _ => scSpCarrier_root_nil u) ?_
      refine sc_forced_riders _ ?_ ?_ ?_
      · intro z hz; rw [List.eq_of_mem_replicate hz]; exact scMillB2_succ_nil
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact scMillG_spine3 3 4
        · exact scMillDescentChain_spine3 3 0 4 u hu
      · exact sc_mill_descent_run_forced 3 0 4
  | j + 2 => by
      refine sc_forced_carrier scSpCarrier_succ_nil
        (fun u _ => scSpCarrier_root_nil u) ?_
      refine sc_forced_riders _ ?_ ?_ ?_
      · intro z hz; rw [List.eq_of_mem_replicate hz]; exact scMillB2_succ_nil
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact scMillG_spine3 0 (4 + j)
        · exact scMillRevStates_spine3 (4 + j) u hu
      · exact scMillRevStates_forced (4 + j)

/-- Each generation's chain ends exactly where the next generation begins. -/
theorem scNoNFChain_last : ∀ k, (scNoNFChain k).getLastD (scNoNFF k) = scNoNFF (k + 1)
  | 0 => by
      have h : (scForcedMarch scMt5T 44).getLastD scMt5T = scSpiral 0 := by decide
      show (scForcedMarch scMt5T 44).getLastD scMt5T = scNoNFF 1
      rw [h, sc_spiral_is_mill]
      rfl
  | 1 => by
      have h1 : (((scMillDescentChain 3 0 4).map
            (scAppList · (List.replicate 3 scMillB2))).map
              (.app (.app .C scSpA) ·)).getLastD
            (SCTerm.app (.app .C scSpA)
              (scAppList (scMillG 3 4) (List.replicate 3 scMillB2)))
          = SCTerm.app (.app .C scSpA)
              (((scMillDescentChain 3 0 4).map
                (scAppList · (List.replicate 3 scMillB2))).getLastD
                  (scAppList (scMillG 3 4) (List.replicate 3 scMillB2))) :=
        List.getLastD_map
      have h2 : ((scMillDescentChain 3 0 4).map
            (scAppList · (List.replicate 3 scMillB2))).getLastD
            (scAppList (scMillG 3 4) (List.replicate 3 scMillB2))
          = scAppList ((scMillDescentChain 3 0 4).getLastD (scMillG 3 4))
              (List.replicate 3 scMillB2) :=
        List.getLastD_map
      show (((scMillDescentChain 3 0 4).map
          (scAppList · (List.replicate 3 scMillB2))).map
            (.app (.app .C scSpA) ·)).getLastD (scNoNFF 1) = scNoNFF 2
      exact h1.trans (by rw [h2, scMillDescentChain_last 0 4 3 (by omega)]; exact rfl)
  | k + 2 => by
      have h1 : (((scMillRevStates (4 + k)).map
            (scAppList · (List.replicate (3 + k) scMillB2))).map
              (.app (.app .C scSpA) ·)).getLastD
            (SCTerm.app (.app .C scSpA)
              (scAppList (scMillG 0 (4 + k)) (List.replicate (3 + k) scMillB2)))
          = SCTerm.app (.app .C scSpA)
              (((scMillRevStates (4 + k)).map
                (scAppList · (List.replicate (3 + k) scMillB2))).getLastD
                  (scAppList (scMillG 0 (4 + k)) (List.replicate (3 + k) scMillB2))) :=
        List.getLastD_map
      have h2 : ((scMillRevStates (4 + k)).map
            (scAppList · (List.replicate (3 + k) scMillB2))).getLastD
            (scAppList (scMillG 0 (4 + k)) (List.replicate (3 + k) scMillB2))
          = scAppList ((scMillRevStates (4 + k)).getLastD (scMillG 0 (4 + k)))
              (List.replicate (3 + k) scMillB2) :=
        List.getLastD_map
      show (((scMillRevStates (4 + k)).map
          (scAppList · (List.replicate (3 + k) scMillB2))).map
            (.app (.app .C scSpA) ·)).getLastD (scNoNFF (k + 2)) = scNoNFF (k + 3)
      refine h1.trans ?_
      rw [h2, scMillRevStates_getLastD (4 + k) (by omega) (scMillG 0 (4 + k))]
      show SCTerm.app (.app .C scSpA)
          (scAppList (scMillG 0 (4 + k + 1)) (List.replicate (3 + k + 1) scMillB2))
        = scNoNFF (k + 3)
      rw [show 4 + k + 1 = 4 + (k + 1) from by omega,
          show 3 + k + 1 = 3 + (k + 1) from by omega]
      exact rfl

/-- No generation's chain is empty. -/
theorem scNoNFChain_ne : ∀ k, scNoNFChain k ≠ []
  | 0 => fun h => by
      have h0 := scNoNFChain_last 0
      rw [h] at h0
      exact absurd h0 (by decide)
  | 1 => fun h => by
      have h' : ((scMillDescentChain 3 0 4).map
          (scAppList · (List.replicate 3 scMillB2))).map
            (SCTerm.app (.app .C scSpA) ·) = [] := h
      exact scMillDescentChain_ne 3 0 4 (by omega)
        (List.map_eq_nil_iff.mp (List.map_eq_nil_iff.mp h'))
  | k + 2 => fun h => by
      have h' : ((scMillRevStates (4 + k)).map
          (scAppList · (List.replicate (3 + k) scMillB2))).map
            (SCTerm.app (.app .C scSpA) ·) = [] := h
      exact scMillRevStates_ne (4 + k)
        (List.map_eq_nil_iff.mp (List.map_eq_nil_iff.mp h'))

/-- **THE CLIMBER NEVER RESTS**: every term reachable from the census's twelve-leaf
climber still has a step — `scMt5T` has no reachable normal form. The corridor is not
just unbounded (Stage 240); it is inescapable: forty-four anchor fires, the initial
descent, and then one forced revolution after another, forever, with the junk stack
and the carrier never opening an exit. -/
theorem sc_mt5T_no_nf : ∀ u, RS.SC.Steps scMt5T u → ∃ v, RS.SC.step u v :=
  sc_forced_forever_no_nf scNoNFF scNoNFChain scNoNFF_forced scNoNFChain_last
    scNoNFChain_ne

-- ## Stage 246: the parametric staircase — unbounded excess along the corridor.
-- The mill's peaks pinned at every scale: right after each turnover the state stands
-- `6m` leaves above the ground it descends to, and the road runs through both. The
-- hand-built floor ladder measured this at three scales; here it is for all of them.

/-- From any member of a checked chain, the reduction continues to the chain's last. -/
theorem scChained_steps_last : ∀ (l : List SCTerm) (t u : SCTerm), SCChained t l →
    u ∈ t :: l → RS.SC.Steps u (l.getLastD t) := by
  intro l
  induction l with
  | nil =>
      intro t u _ hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact @RS.Steps.refl RS.SC u
      · exact absurd hu (List.not_mem_nil)
  | cons v rest ih =>
      intro t u hc hu
      rw [List.getLastD_cons]
      rcases List.mem_cons.mp hu with rfl | hu
      · exact RS.Steps.tail (scSucc_sound hc.1) (ih v v hc.2 List.mem_cons_self)
      · exact ih v u hc.2 hu

/-- Every generation's start is reachable from the climber. -/
theorem scNoNFF_steps : ∀ k, RS.SC.Steps scMt5T (scNoNFF k)
  | 0 => @RS.Steps.refl RS.SC scMt5T
  | k + 1 => by
      have h2 : RS.SC.Steps (scNoNFF k) ((scNoNFChain k).getLastD (scNoNFF k)) :=
        scChained_steps_last (scNoNFChain k) (scNoNFF k) (scNoNFF k)
          (scForced_chained _ _ (scNoNFF_forced k)) List.mem_cons_self
      rw [scNoNFChain_last k] at h2
      exact RS.Steps.trans (scNoNFF_steps k) h2

/-- The peak inside each revolution: right after the turnover, before the descent. -/
def scMillPeak (m : Nat) : SCTerm := .app (scMillG m (m + 1)) scMillB2

/-- The peak is the turnover's last state. -/
theorem scMillPeak_mem (m : Nat) :
    scMillPeak m ∈ scMillTurnStates (scMillT m) :=
  List.Mem.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

/-- The full-dress peak at generation `j`: under the carrier, over the junk stack. -/
def scNoNFPeak (j : Nat) : SCTerm :=
  .app (.app .C scSpA)
    (scAppList (scMillPeak (4 + j)) (List.replicate (3 + j) scMillB2))

/-- The full-dress peak lies on generation `j`'s forced chain. -/
theorem scNoNFPeak_mem (j : Nat) : scNoNFPeak j ∈ scNoNFChain (j + 2) := by
  show _ ∈ ((scMillRevStates (4 + j)).map
      (scAppList · (List.replicate (3 + j) scMillB2))).map
        (SCTerm.app (.app .C scSpA) ·)
  exact List.mem_map_of_mem
    (List.mem_map_of_mem
      (List.mem_append_left _ (scMillPeak_mem (4 + j))))

/-- The climber reaches every peak. -/
theorem scNoNFPeak_reach (j : Nat) : RS.SC.Steps scMt5T (scNoNFPeak j) :=
  RS.Steps.trans (scNoNFF_steps (j + 2))
    (scChained_steps _ _ _ (scForced_chained _ _ (scNoNFF_forced (j + 2)))
      (List.mem_cons_of_mem _ (scNoNFPeak_mem j)))

/-- Every peak descends to the next generation's start. -/
theorem scNoNFPeak_descends (j : Nat) :
    RS.SC.Steps (scNoNFPeak j) (scNoNFF (j + 3)) := by
  have h := scChained_steps_last (scNoNFChain (j + 2)) (scNoNFF (j + 2)) (scNoNFPeak j)
    (scForced_chained _ _ (scNoNFF_forced (j + 2)))
    (List.mem_cons_of_mem _ (scNoNFPeak_mem j))
  rw [scNoNFChain_last (j + 2)] at h
  exact h

/-- Leaf count distributes over an application list. -/
theorem scAppList_size : ∀ (zs : List SCTerm) (t : SCTerm),
    (scAppList t zs).leafCount = t.leafCount + (zs.map SCTerm.leafCount).sum := by
  intro zs
  induction zs with
  | nil => intro t; simp [scAppList]
  | cons z zs ih =>
      intro t
      show (scAppList (.app t z) zs).leafCount = _
      rw [ih (.app t z), List.map_cons, List.sum_cons,
        show (SCTerm.app t z).leafCount = t.leafCount + z.leafCount from rfl]
      omega

/-- The junk block weighs sixteen leaves. -/
theorem scMillB2_size : scMillB2.leafCount = 16 := rfl

/-- The junk stack's total weight. -/
theorem scRepB2_sum : ∀ n : Nat,
    ((List.replicate n scMillB2).map SCTerm.leafCount).sum = 16 * n
  | 0 => rfl
  | n + 1 => by
      show 16 + ((List.replicate n scMillB2).map SCTerm.leafCount).sum = 16 * (n + 1)
      rw [scRepB2_sum n]
      omega

/-- The two-counter state's weight. -/
theorem scMillG_size (a m : Nat) : (scMillG a m).leafCount = 28 + 6 * a + 3 * m := by
  show (scMillT a).leafCount + (1 + (scMillT a).leafCount) + (scMillT m).leafCount = _
  rw [scMillT_size, scMillT_size]
  omega

/-- The peak's weight. -/
theorem scMillPeak_size (m : Nat) : (scMillPeak m).leafCount = 47 + 9 * m := by
  show (scMillG m (m + 1)).leafCount + scMillB2.leafCount = _
  rw [scMillG_size, scMillB2_size]
  omega

/-- The full-dress peak's weight at generation `j`. -/
theorem scNoNFPeak_size (j : Nat) : (scNoNFPeak j).leafCount = 141 + 25 * j := by
  show 1 + scSpA.leafCount
      + (scAppList (scMillPeak (4 + j)) (List.replicate (3 + j) scMillB2)).leafCount = _
  rw [scAppList_size, scRepB2_sum, scMillPeak_size,
    show scSpA.leafCount = 9 from rfl]
  omega

/-- The generation start's weight. -/
theorem scNoNFF_size (j : Nat) : (scNoNFF (j + 3)).leafCount = 117 + 19 * j := by
  show 1 + scSpA.leafCount
      + (scAppList (scMillG 0 (4 + (j + 1)))
          (List.replicate (3 + (j + 1)) scMillB2)).leafCount = _
  rw [scAppList_size, scRepB2_sum, scMillG_size,
    show scSpA.leafCount = 9 from rfl]
  omega

/-- **THE PARAMETRIC STAIRCASE**: excess is unbounded along the corridor — at every
scale `d`, the climber's road climbs to a peak at least `d` leaves above a state the
peak itself still reaches. The floor ladder, at all scales at once. -/
theorem sc_corridor_excess (d : Nat) : ∃ u w : SCTerm,
    RS.SC.Steps scMt5T u ∧ RS.SC.Steps u w ∧ w.leafCount + d ≤ u.leafCount := by
  refine ⟨scNoNFPeak d, scNoNFF (d + 3), scNoNFPeak_reach d,
    scNoNFPeak_descends d, ?_⟩
  rw [scNoNFPeak_size, scNoNFF_size]
  omega

-- ## Stage 247: the reachable-set characterization — the corridor, exactly.
-- The no-NF principle's induction knows more than "everything still steps": it knows
-- WHERE everything is. Extracted here: every term reachable from the family's start
-- lies on the family; instantiated to the climber, with the converse, this is the
-- complete description of the wildest census term's reachable set.

/-- **The family membership theorem**: everything reachable from `F 0` is a generation
start or lies on a generation's chain. -/
theorem sc_forced_family_mem (F : Nat → SCTerm) (chain : Nat → List SCTerm)
    (hf : ∀ k, SCForced (F k) (chain k))
    (hlast : ∀ k, (chain k).getLastD (F k) = F (k + 1))
    (hne : ∀ k, chain k ≠ []) :
    ∀ u, RS.SC.Steps (F 0) u → ∃ k, u = F k ∨ u ∈ chain k := by
  have hmem_succ : ∀ k u, (u = F k ∨ u ∈ chain k) → ∃ w,
      scSucc u = [w] ∧
        ((w = F (k + 1) ∨ w ∈ chain (k + 1)) ∨ w ∈ chain k) := by
    intro k u hu
    rcases hu with rfl | hu
    · cases hc : chain k with
      | nil => exact absurd hc (hne k)
      | cons v rest =>
          have h1 := hf k
          rw [hc] at h1
          exact ⟨v, h1.1, .inr List.mem_cons_self⟩
    · have hwalk : ∀ (l : List SCTerm) (t : SCTerm), SCForced t l →
          l.getLastD t = F (k + 1) → ∀ u ∈ l, ∃ w, scSucc u = [w] ∧
            ((w = F (k + 1) ∨ w ∈ chain (k + 1)) ∨ w ∈ l) := by
        intro l
        induction l with
        | nil => intro t _ _ u hu; exact absurd hu List.not_mem_nil
        | cons v rest ih =>
            intro t hfl hl u hu
            rcases List.mem_cons.mp hu with rfl | hu'
            · cases hr : rest with
              | nil =>
                  have hv : u = F (k + 1) := by
                    rw [hr] at hl
                    simpa using hl
                  cases hc2 : chain (k + 1) with
                  | nil => exact absurd hc2 (hne (k + 1))
                  | cons w2 r2 =>
                      have h2 := hf (k + 1)
                      rw [hc2] at h2
                      exact ⟨w2, by rw [hv]; exact h2.1,
                        .inl (.inr List.mem_cons_self)⟩
              | cons v2 r2 =>
                  have h2 := hfl.2
                  rw [hr] at h2
                  exact ⟨v2, h2.1,
                    .inr (List.mem_cons.mpr (.inr List.mem_cons_self))⟩
            · have hl' : rest.getLastD v = F (k + 1) := by
                have hstep : (v :: rest).getLastD t = rest.getLastD v := by
                  cases rest <;> rfl
                rw [← hstep, hl]
              obtain ⟨w, hw, hwm⟩ := ih v hfl.2 hl' u hu'
              exact ⟨w, hw, hwm.imp id (List.mem_cons_of_mem v)⟩
      obtain ⟨w, hw, hwm⟩ := hwalk (chain k) (F k) (hf k) (hlast k) u hu
      exact ⟨w, hw, hwm⟩
  have hreach : ∀ (a u : SCTerm), RS.SC.Steps a u →
      (∃ k, a = F k ∨ a ∈ chain k) → ∃ k, u = F k ∨ u ∈ chain k := by
    intro a u h
    refine h.rec (motive := fun (x y : SCTerm) _ =>
        (∃ k, x = F k ∨ x ∈ chain k) → ∃ k, y = F k ∨ y ∈ chain k) ?_ ?_
    · intro _ hx
      exact hx
    · intro x y c s rest ih hx
      obtain ⟨k, hk⟩ := hx
      obtain ⟨w, hw, hwm⟩ := hmem_succ k x hk
      have hy : y = w := by
        have hm := scSucc_complete s
        rw [hw] at hm
        simpa using hm
      subst hy
      apply ih
      rcases hwm with h1 | h2
      · exact ⟨k + 1, h1.imp id id⟩
      · exact ⟨k, .inr h2⟩
  intro u hsteps
  exact hreach (F 0) u hsteps ⟨0, .inl rfl⟩

/-- **THE CORRIDOR, EXACTLY**: a term is reachable from the census's twelve-leaf
climber if and only if it is a generation start or lies on a generation's forced
chain. The complete reachable set of the wildest known term, in closed form. -/
theorem sc_mt5T_reach_iff (u : SCTerm) :
    RS.SC.Steps scMt5T u ↔ ∃ k, u = scNoNFF k ∨ u ∈ scNoNFChain k := by
  constructor
  · exact sc_forced_family_mem scNoNFF scNoNFChain scNoNFF_forced scNoNFChain_last
      scNoNFChain_ne u
  · rintro ⟨k, rfl | hu⟩
    · exact scNoNFF_steps k
    · exact RS.Steps.trans (scNoNFF_steps k)
        (scChained_steps _ _ _ (scForced_chained _ _ (scNoNFF_forced k))
          (List.mem_cons_of_mem _ hu))

-- ## Stage 248: reachability from the climber is DECIDABLE.
-- The closed-form reachable set plus a size floor per generation turns membership into
-- a terminating search: no state of generation `j+2` weighs less than `59 + 16j`, so a
-- candidate of `n` leaves can only live in the first `n + 2` generations.

/-- The generation size floor: nothing in generation `j+2` weighs less than `59+16j`. -/
theorem scNoNFGen_size_lb (j : Nat) (u : SCTerm)
    (hu : u = scNoNFF (j + 2) ∨ u ∈ scNoNFChain (j + 2)) :
    59 + 16 * j ≤ u.leafCount := by
  rcases hu with rfl | hu
  · show 59 + 16 * j ≤ 1 + scSpA.leafCount
      + (scAppList (scMillG 0 (4 + j)) (List.replicate (3 + j) scMillB2)).leafCount
    rw [scAppList_size, scRepB2_sum, scMillG_size,
      show scSpA.leafCount = 9 from rfl]
    omega
  · have h' : u ∈ ((scMillRevStates (4 + j)).map
        (scAppList · (List.replicate (3 + j) scMillB2))).map
          (SCTerm.app (.app .C scSpA) ·) := hu
    obtain ⟨w1, hw1, rfl⟩ := List.mem_map.mp h'
    obtain ⟨w0, _, rfl⟩ := List.mem_map.mp hw1
    show 59 + 16 * j ≤ 1 + scSpA.leafCount
      + (scAppList w0 (List.replicate (3 + j) scMillB2)).leafCount
    rw [scAppList_size, scRepB2_sum, show scSpA.leafCount = 9 from rfl]
    have := SCTerm.leafCount_pos w0
    omega

/-- The reachable set, bounded: only the first `|u| + 2` generations can hold `u`. -/
theorem sc_mt5T_reach_bounded (u : SCTerm) :
    RS.SC.Steps scMt5T u
      ↔ ∃ k, k < u.leafCount + 2 ∧ (u = scNoNFF k ∨ u ∈ scNoNFChain k) := by
  rw [sc_mt5T_reach_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    rcases Nat.lt_or_ge k (u.leafCount + 2) with h | h
    · exact h
    · have hb := scNoNFGen_size_lb (k - 2) u
        (by rw [show k - 2 + 2 = k from by omega]; exact hk)
      omega
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- The decider: scan the first `|u| + 2` generations. -/
def scMt5TReach (u : SCTerm) : Bool :=
  (List.range (u.leafCount + 2)).any
    (fun k => decide (u = scNoNFF k) || decide (u ∈ scNoNFChain k))

/-- The decider is correct. -/
theorem scMt5TReach_iff (u : SCTerm) :
    scMt5TReach u = true ↔ RS.SC.Steps scMt5T u := by
  rw [sc_mt5T_reach_bounded]
  show ((List.range (u.leafCount + 2)).any
    (fun k => decide (u = scNoNFF k) || decide (u ∈ scNoNFChain k))) = true ↔ _
  simp [List.any_eq_true, List.mem_range]

/-- **REACHABILITY FROM THE CLIMBER IS DECIDABLE**: the first decision procedure for
reachability from a growth-unbounded {S,C} term, certified end to end. -/
instance scMt5TReach_decidable (u : SCTerm) : Decidable (RS.SC.Steps scMt5T u) :=
  decidable_of_iff (scMt5TReach u = true) (scMt5TReach_iff u)

#guard scMt5TReach .S = false
#guard scMt5TReach (.app .S .S) = false

-- ## Stage 249: the six champions are corridors — every n=12 drop-leader is forced.
-- The crash screen's top six terms by drop, probed for 6000 fires each: ZERO branch
-- points, all with mill-signature revolutions whose periods grow arithmetically
-- (+6 or +4 per cycle). Pinned here: five hundred consecutive forced fires apiece.

def scChamp211 : SCTerm := (.app .S (.app (.app (.app (.app .S .S) .C) (.app .S .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)))
def scChamp209 : SCTerm := (.app (.app (.app .S (.app (.app .C .C) .S)) (.app .C .C)) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C))
def scChamp206 : SCTerm := (.app .S (.app (.app (.app (.app .S .S) .C) (.app (.app .S (.app (.app .C .S) (.app .C .C))) .C)) (.app .C .S)))
def scChamp205 : SCTerm := (.app (.app (.app (.app .S .S) .C) (.app (.app .S .C) .C)) (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C)))
def scChamp170 : SCTerm := (.app (.app (.app (.app .C (.app (.app .S .C) .C)) .S) (.app (.app .S (.app (.app .C .S) .C)) .C)) (.app .C .C))
def scChamp159 : SCTerm := (.app (.app (.app .S (.app .S (.app (.app .C .S) .C))) (.app .S (.app (.app .C .S) .C))) (.app .C (.app .C .C)))

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

/-- Five hundred forced fires: the n=12 drop champion is a corridor. -/
theorem sc_champ211_corridor : (scForcedMarch scChamp211 500).length = 500 := by decide
/-- Five hundred forced fires apiece: every n=12 drop-leader is a corridor. -/
theorem sc_champ209_corridor : (scForcedMarch scChamp209 500).length = 500 := by decide
theorem sc_champ206_corridor : (scForcedMarch scChamp206 500).length = 500 := by decide
theorem sc_champ205_corridor : (scForcedMarch scChamp205 500).length = 500 := by decide
theorem sc_champ170_corridor : (scForcedMarch scChamp170 500).length = 500 := by decide
theorem sc_champ159_corridor : (scForcedMarch scChamp159 500).length = 500 := by decide

-- ## Stage 250: THE CLIMBER NEVER DEEPENS — flatness over the whole reachable set.
-- The mill's towers are `(C C)(C ·)`-nests, not numerals: no state the climber ever
-- reaches holds a register deeper than one. The wildest term is size-unbounded,
-- dynamically rigid — and numerically FLAT. In particular it is no C10 witness.

theorem scIsReg_app_app (p q x : SCTerm) : scIsReg (.app (.app p q) x) = none := rfl
theorem scIsReg_app_S (x : SCTerm) : scIsReg (.app .S x) = none := rfl
theorem scIsReg_atomC : scIsReg .C = none := rfl
theorem scIsReg_CS : scIsReg (.app .C .S) = some 1 := rfl
theorem scIsReg_CC : scIsReg (.app .C .C) = none := rfl
theorem scIsReg_c_app_app (p q x : SCTerm) :
    scIsReg (.app .C (.app (.app p q) x)) = none := rfl
theorem scIsReg_c_app_S (x : SCTerm) :
    scIsReg (.app .C (.app .S x)) = none := rfl
theorem scIsReg_cc_app_app (p q x : SCTerm) :
    scIsReg (.app .C (.app .C (.app (.app p q) x))) = none := rfl
theorem scIsReg_millT : ∀ m, scIsReg (scMillT m) = none
  | 0 => rfl
  | _ + 1 => rfl

/-- A `C`-parked tower is no numeral. -/
theorem scIsReg_c_millT (m : Nat) : scIsReg (.app .C (scMillT m)) = none := by
  show (scIsReg (scMillT m)).map (· + 1) = none
  rw [scIsReg_millT]
  rfl

/-- Nor is a doubly parked one. -/
theorem scIsReg_cc_millT (m : Nat) :
    scIsReg (.app .C (.app .C (scMillT m))) = none := by
  show (scIsReg (.app .C (scMillT m))).map (· + 1) = none
  rw [scIsReg_c_millT]
  rfl

/-- A tower in function position blocks the register pattern. -/
theorem scIsReg_millT_app (m : Nat) (x : SCTerm) :
    scIsReg (.app (scMillT m) x) = none := by
  obtain ⟨p, q, hp⟩ := scMillT_isApp m
  rw [hp]
  exact scIsReg_app_app p q x

/-- A spine-3 term in function position blocks the register pattern. -/
theorem scIsReg_of_spine3 {u : SCTerm} (h : SCSpine3 u) (z : SCTerm) :
    scIsReg (.app u z) = none := by
  obtain ⟨p, q, g, x, rfl⟩ := h
  exact scIsReg_app_app _ _ _

/-- Spine-3 terms are applications. -/
theorem SCSpine3.isApp {u : SCTerm} (h : SCSpine3 u) : ∃ p q, u = .app p q := by
  obtain ⟨p, q, g, x, rfl⟩ := h
  exact ⟨_, _, rfl⟩

/-- The towers are flat: no register deeper than one, at any height. -/
theorem scMaxReg_millT : ∀ m, scMaxReg (scMillT m) ≤ 1
  | 0 => Nat.le_refl 1
  | m + 1 => by
      have ih := scMaxReg_millT m
      show scMaxReg (.app (.app .C .C) (.app .C (scMillT m))) ≤ 1
      simp only [scMaxReg, Option.getD, scIsReg_app_app, scIsReg_CC,
        scIsReg_c_millT]
      omega

/-- Flatness climbs one application, absent a fresh register at the root. -/
theorem scMaxReg_app_le {f x : SCTerm} (h : scIsReg (.app f x) = none)
    (hf : scMaxReg f ≤ 1) (hx : scMaxReg x ≤ 1) : scMaxReg (.app f x) ≤ 1 := by
  show max (max (scMaxReg f) (scMaxReg x)) ((scIsReg (.app f x)).getD 0) ≤ 1
  rw [h]
  simp only [Option.getD]
  omega

/-- Every descent state is flat. -/
theorem scMaxReg_descentStates (a m : Nat) :
    ∀ u ∈ scMillDescentStates (scMillT a) (scMillT m), scMaxReg u ≤ 1 := by
  have ha := scMaxReg_millT a
  have hm := scMaxReg_millT m
  intro u hu
  simp only [scMillDescentStates, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [scMaxReg, Option.getD, scIsReg_app_app, scIsReg_CC,
      scIsReg_c_app_app, scIsReg_cc_app_app, scIsReg_c_millT, scIsReg_cc_millT,
      scIsReg_millT_app]; omega)

/-- Every state of the descent run is flat. -/
theorem scMaxReg_descentChain : ∀ (d a m : Nat),
    ∀ u ∈ scMillDescentChain d a m, scMaxReg u ≤ 1
  | 0, _, _ => by intro u hu; exact absurd hu (List.not_mem_nil)
  | d + 1, a, m => by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact scMaxReg_descentStates (a + d) m u h
      · exact scMaxReg_descentChain d a m u h

/-- Every turnover state is flat. -/
theorem scMaxReg_turnStates (m : Nat) :
    ∀ u ∈ scMillTurnStates (scMillT m), scMaxReg u ≤ 1 := by
  have hm := scMaxReg_millT m
  intro u hu
  simp only [scMillTurnStates, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [scMillK, scMaxReg, Option.getD, scIsReg_app_app, scIsReg_app_S,
      scIsReg_CC, scIsReg_CS, scIsReg_c_app_app, scIsReg_c_app_S,
      scIsReg_c_millT, scIsReg_millT_app];
     omega)

/-- The two-counter state is flat. -/
theorem scMaxReg_millG (a m : Nat) : scMaxReg (scMillG a m) ≤ 1 := by
  have ha := scMaxReg_millT a
  have hm := scMaxReg_millT m
  show scMaxReg (.app (.app (scMillT a) (.app .C (scMillT a))) (scMillT m)) ≤ 1
  simp only [scMaxReg, Option.getD, scIsReg_app_app, scIsReg_c_millT,
    scIsReg_millT_app]
  omega

/-- The junk block is flat. -/
theorem scMaxReg_millB2 : scMaxReg scMillB2 = 1 := rfl

/-- Every revolution state is flat. -/
theorem scMaxReg_revStates (m : Nat) :
    ∀ u ∈ scMillRevStates m, scMaxReg u ≤ 1 := by
  intro u hu
  rcases List.mem_append.mp hu with h | h
  · exact scMaxReg_turnStates m u h
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact scMaxReg_app_le
      (scIsReg_of_spine3 (scMillDescentChain_spine3 m 0 (m + 1) w hw) scMillB2)
      (scMaxReg_descentChain m 0 (m + 1) w hw)
      (Nat.le_of_eq scMaxReg_millB2)

/-- Flatness survives the junk stack. -/
theorem scMaxReg_appList : ∀ (zs : List SCTerm) {t : SCTerm},
    (∃ p q, t = .app p q) → scMaxReg t ≤ 1 →
    (∀ z ∈ zs, scMaxReg z ≤ 1) → scMaxReg (scAppList t zs) ≤ 1 := by
  intro zs
  induction zs with
  | nil => intro t _ ht _; exact ht
  | cons z zs ih =>
      intro t hap ht hz
      obtain ⟨p, q, rfl⟩ := hap
      show scMaxReg (scAppList (.app (.app p q) z) zs) ≤ 1
      exact ih ⟨_, _, rfl⟩
        (scMaxReg_app_le (scIsReg_app_app _ _ _) ht (hz z List.mem_cons_self))
        (fun w hw => hz w (List.mem_cons_of_mem z hw))

/-- Flatness survives the carrier. -/
theorem scMaxReg_carrier {x : SCTerm} (hx : scMaxReg x ≤ 1) :
    scMaxReg (.app (.app .C scSpA) x) ≤ 1 :=
  scMaxReg_app_le (scIsReg_app_app _ _ _)
    (Nat.le_of_eq (rfl : scMaxReg (.app .C scSpA) = 1)) hx

/-- Every generation is flat. -/
theorem scMaxReg_gen : ∀ k, ∀ u, (u = scNoNFF k ∨ u ∈ scNoNFChain k) →
    scMaxReg u ≤ 1
  | 0 => by
      intro u hu
      rcases hu with rfl | hu
      · decide
      · revert hu
        revert u
        decide
  | 1 => by
      intro u hu
      have hrep : ∀ z ∈ List.replicate 3 scMillB2, scMaxReg z ≤ 1 := by
        intro z hz
        rw [List.eq_of_mem_replicate hz]
        exact Nat.le_of_eq scMaxReg_millB2
      rcases hu with rfl | hu
      · exact scMaxReg_carrier
          (scMaxReg_appList _ ⟨_, _, rfl⟩ (scMaxReg_millG 3 4) hrep)
      · have h' : u ∈ ((scMillDescentChain 3 0 4).map
            (scAppList · (List.replicate 3 scMillB2))).map
              (SCTerm.app (.app .C scSpA) ·) := hu
        obtain ⟨w1, hw1, rfl⟩ := List.mem_map.mp h'
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw1
        exact scMaxReg_carrier (scMaxReg_appList _
          (scMillDescentChain_spine3 3 0 4 w0 hw0).isApp
          (scMaxReg_descentChain 3 0 4 w0 hw0) hrep)
  | j + 2 => by
      intro u hu
      have hrep : ∀ z ∈ List.replicate (3 + j) scMillB2, scMaxReg z ≤ 1 := by
        intro z hz
        rw [List.eq_of_mem_replicate hz]
        exact Nat.le_of_eq scMaxReg_millB2
      rcases hu with rfl | hu
      · exact scMaxReg_carrier (scMaxReg_appList _ ⟨_, _, rfl⟩
          (scMaxReg_millG 0 (4 + j)) hrep)
      · have h' : u ∈ ((scMillRevStates (4 + j)).map
            (scAppList · (List.replicate (3 + j) scMillB2))).map
              (SCTerm.app (.app .C scSpA) ·) := hu
        obtain ⟨w1, hw1, rfl⟩ := List.mem_map.mp h'
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw1
        exact scMaxReg_carrier (scMaxReg_appList _
          (scMillRevStates_spine3 (4 + j) w0 hw0).isApp
          (scMaxReg_revStates (4 + j) w0 hw0) hrep)

/-- **THE CLIMBER NEVER DEEPENS**: no reachable state holds a register deeper than
one. Size-unbounded, dynamically rigid — and numerically flat. -/
theorem sc_mt5T_flat : ∀ u, RS.SC.Steps scMt5T u → scMaxReg u ≤ 1 := by
  intro u h
  obtain ⟨k, hk⟩ := (sc_mt5T_reach_iff u).mp h
  exact scMaxReg_gen k u hk

/-- The climber is no C10 witness: its reachable set misses every depth past one. -/
theorem sc_mt5T_not_deepening :
    ¬ (∀ n : Nat, ∃ u : SCTerm, RS.SC.Steps scMt5T u ∧ n ≤ scMaxReg u) := by
  intro h
  obtain ⟨u, hu, hn⟩ := h 2
  have := sc_mt5T_flat u hu
  omega

-- ## Stage 255: THE LINE — the climber's reachable set is totally ordered.
-- Forcedness means there is only one road: any two reachable states are comparable
-- under reduction. The strongest closed-form corollary of the reachable-set theorem,
-- and the formal seed of every must-pass/all-paths statement about the corridor.

/-- Along a checked chain, any two states are comparable. -/
theorem scChained_comparable : ∀ (l : List SCTerm) (t : SCTerm), SCChained t l →
    ∀ u ∈ t :: l, ∀ v ∈ t :: l, RS.SC.Steps u v ∨ RS.SC.Steps v u := by
  intro l
  induction l with
  | nil =>
      intro t _ u hu v hv
      have hu' : u = t := by
        rcases List.mem_cons.mp hu with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      have hv' : v = t := by
        rcases List.mem_cons.mp hv with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      rw [hu', hv']
      exact .inl (@RS.Steps.refl RS.SC t)
  | cons w rest ih =>
      intro t hc u hu v hv
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact .inl (scChained_steps _ _ _ hc hv)
      · rcases List.mem_cons.mp hv with rfl | hv'
        · exact .inr (scChained_steps _ _ _ hc hu)
        · exact ih w hc.2 u hu' v hv'

/-- Any state of generation `k` reduces to the next generation's start. -/
theorem scNoNF_mem_to_next (k : Nat) {u : SCTerm}
    (hu : u = scNoNFF k ∨ u ∈ scNoNFChain k) :
    RS.SC.Steps u (scNoNFF (k + 1)) := by
  have h := scChained_steps_last (scNoNFChain k) (scNoNFF k) u
    (scForced_chained _ _ (scNoNFF_forced k)) (List.mem_cons.mpr hu)
  rw [scNoNFChain_last k] at h
  exact h

/-- Generation starts reduce forward. -/
theorem scNoNFF_steps_from (k : Nat) : ∀ d, RS.SC.Steps (scNoNFF k) (scNoNFF (k + d))
  | 0 => @RS.Steps.refl RS.SC _
  | d + 1 => RS.Steps.trans (scNoNFF_steps_from k d)
      (scNoNF_mem_to_next (k + d) (.inl rfl))

/-- **THE LINE**: any two states reachable from the climber are comparable — the
reachable set is one infinite road, totally ordered by reduction. -/
theorem sc_mt5T_line : ∀ u v, RS.SC.Steps scMt5T u → RS.SC.Steps scMt5T v →
    RS.SC.Steps u v ∨ RS.SC.Steps v u := by
  have cross : ∀ k k', k < k' → ∀ u v, (u = scNoNFF k ∨ u ∈ scNoNFChain k) →
      (v = scNoNFF k' ∨ v ∈ scNoNFChain k') → RS.SC.Steps u v := by
    intro k k' hkk u v hu hv
    have h1 : RS.SC.Steps u (scNoNFF (k + 1)) := scNoNF_mem_to_next k hu
    have h2 : RS.SC.Steps (scNoNFF (k + 1)) (scNoNFF k') := by
      have h := scNoNFF_steps_from (k + 1) (k' - (k + 1))
      rw [show k + 1 + (k' - (k + 1)) = k' from by omega] at h
      exact h
    have h3 : RS.SC.Steps (scNoNFF k') v := by
      rcases hv with rfl | hv
      · exact @RS.Steps.refl RS.SC _
      · exact scChained_steps _ _ _ (scForced_chained _ _ (scNoNFF_forced k'))
          (List.mem_cons_of_mem _ hv)
    exact RS.Steps.trans h1 (RS.Steps.trans h2 h3)
  intro u v hu hv
  obtain ⟨k, hk⟩ := (sc_mt5T_reach_iff u).mp hu
  obtain ⟨k', hk'⟩ := (sc_mt5T_reach_iff v).mp hv
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact .inl (cross k k' h u v hk hk')
  · subst h
    exact scChained_comparable (scNoNFChain k) (scNoNFF k)
      (scForced_chained _ _ (scNoNFF_forced k)) u (List.mem_cons.mpr hk)
      v (List.mem_cons.mpr hk')
  · exact .inr (cross k' k h v u hk' hk)

-- ## Stage 257: THE SWAPMILL — the second engine species, core laws.
-- Inside scChamp170 (and its +4-period siblings) runs a leaner mill: the counter is a
-- bare C-chain `C^k B`, descent is rider ping-pong (one C-fire per layer, two per net
-- pair), and the turnover is three fires through the driver `S ((C S) C) C` — which
-- re-emits the SAME `x·(C x)` pattern that drives the first mill, plus the junk seed
-- `C (C T)`. The driver even lives inside the chain's ten-leaf base: the engine
-- carries its own blueprint. Species one grows 3 leaves per layer and pays 6 fires;
-- the swapmill grows 1 and pays 2 — the leanest G-machine yet seen.

/-- The swap tower: a bare `C`-chain over base `f`. -/
def scSwapT : Nat → SCTerm → SCTerm
  | 0, f => f
  | k + 1, f => .app .C (scSwapT k f)

/-- The swapmill driver's argument block. -/
def scSwapA : SCTerm := .app (.app .C .S) .C

/-- **THE SWAP**: one fire exchanges the two riders and strips a layer. -/
theorem sc_swap (f y z : SCTerm) :
    RS.SC.StepsN 1 (.app (.app (.app .C f) y) z) (.app (.app f z) y) :=
  RS.StepsN.tail (SCStep.C_red f y z) (@RS.StepsN.refl RS.SC _)

/-- **THE DOUBLE SWAP**: two fires strip two layers and restore rider order. -/
theorem sc_swap2 (f y z : SCTerm) :
    RS.SC.StepsN 2 (.app (.app (.app .C (.app .C f)) y) z) (.app (.app f y) z) :=
  RS.StepsN.tail (SCStep.C_red (.app .C f) y z)
    (RS.StepsN.tail (SCStep.C_red f z y) (@RS.StepsN.refl RS.SC _))

/-- **THE SWAP DESCENT**: an even chain unwinds in one fire per layer, riders home. -/
theorem sc_swap_run : ∀ (j : Nat) (f y z : SCTerm),
    RS.SC.StepsN (2 * j) (.app (.app (scSwapT (2 * j) f) y) z) (.app (.app f y) z)
  | 0, f, y, z => @RS.StepsN.refl RS.SC _
  | j + 1, f, y, z => by
      show RS.SC.StepsN (2 * j + 2)
        (.app (.app (scSwapT (2 * j + 2) f) y) z) (.app (.app f y) z)
      have h := RS.StepsN.trans (sc_swap2 (scSwapT (2 * j) f) y z)
        (sc_swap_run j f y z)
      rw [show (2 : Nat) + 2 * j = 2 * j + 2 from by omega] at h
      exact h

/-- **THE SWAP TURNOVER**: three fires through the driver re-emit the mill pattern
`T·(C T)` and the junk seed `C (C T)`. -/
theorem sc_swap_turnover (T : SCTerm) :
    RS.SC.StepsN 3 (.app (.app (.app .S scSwapA) .C) T)
      (.app (.app T (.app .C T)) (.app .C (.app .C T))) :=
  RS.StepsN.tail (SCStep.S_red scSwapA .C T)
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S .C T))
      (RS.StepsN.tail (SCStep.S_red T .C (.app .C T)) (@RS.StepsN.refl RS.SC _)))

-- ## Stage 258: the swapmill cycle — turnover and descent composed, and the reseed.
-- The abstract revolution, parametric in BOTH the layer count and the base: from the
-- driver over an even chain, `3 + 2j` fires reach the base holding `C T` — and `C T`
-- IS the next tower: regrowth costs nothing, the turnover's junk seed pays for it.
-- The concrete base then reseeds in two fires, handing `(C T)` its own successor.

/-- The swapmill's ten-leaf base, as found in scChamp170's valleys: it carries the
driver inside itself. -/
def scSwapB : SCTerm :=
  .app (.app .C .C) (.app (.app .C (.app (.app .S scSwapA) .C)) (.app .C .C))

/-- **THE SWAPMILL CYCLE**: turnover then full descent, parametric in layer count and
base — `3 + 2j` fires from the driver to the base holding the grown tower `C T`. -/
theorem sc_swap_cycle (j : Nat) (B : SCTerm) :
    RS.SC.StepsN (3 + 2 * j)
      (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) B))
      (.app (.app B (.app .C (scSwapT (2 * j) B)))
        (.app .C (.app .C (scSwapT (2 * j) B)))) :=
  RS.StepsN.trans (sc_swap_turnover (scSwapT (2 * j) B))
    (sc_swap_run j B (.app .C (scSwapT (2 * j) B))
      (.app .C (.app .C (scSwapT (2 * j) B))))

/-- **THE RESEED**: the concrete base hands its riders forward in two fires,
exposing the junk block `G = (C (S scSwapA C)) (C C)`. -/
theorem sc_swap_reseed (y z : SCTerm) :
    RS.SC.StepsN 2 (.app (.app scSwapB y) z)
      (.app (.app y z)
        (.app (.app .C (.app (.app .S scSwapA) .C)) (.app .C .C))) :=
  RS.StepsN.tail
    (SCStep.appL
      (SCStep.C_red .C (.app (.app .C (.app (.app .S scSwapA) .C)) (.app .C .C)) y))
    (RS.StepsN.tail
      (SCStep.C_red y (.app (.app .C (.app (.app .S scSwapA) .C)) (.app .C .C)) z)
      (@RS.StepsN.refl RS.SC _))

-- ## Stage 260: THE UNIT DROP LAW — no fire loses more than one leaf.
-- The arithmetic beneath the storm floor: an S-fire duplicates its third argument and
-- never shrinks (Δ = |x| − 1 ≥ 0); a C-fire drops exactly its own head (Δ = −1). So
-- any path's total descent is bounded by its C-fire count — and the probes show storm
-- states hold only a handful of C-redexes (median 9), which is why adversarial digs
-- max out at 26: the drop budget IS the C-redex inventory.

/-- **THE UNIT DROP LAW**: every fire loses at most one leaf. -/
theorem sc_unit_drop : ∀ {t u : SCTerm}, RS.SC.step t u →
    t.leafCount ≤ u.leafCount + 1 := by
  intro t u h
  induction h with
  | S_red f g x =>
      show SCTerm.leafCount .S + f.leafCount + g.leafCount + x.leafCount
        ≤ f.leafCount + x.leafCount + (g.leafCount + x.leafCount) + 1
      have := SCTerm.leafCount_pos x
      show 1 + f.leafCount + g.leafCount + x.leafCount ≤ _
      omega
  | C_red f g x =>
      show SCTerm.leafCount .C + f.leafCount + g.leafCount + x.leafCount
        ≤ f.leafCount + x.leafCount + g.leafCount + 1
      show 1 + f.leafCount + g.leafCount + x.leafCount ≤ _
      omega
  | appL h ih =>
      show _ + _ ≤ _ + _ + 1
      omega
  | appR h ih =>
      show _ + _ ≤ _ + _ + 1
      omega

/-- **THE DESCENT SPEED LIMIT**: over `n` fires, at most `n` leaves are lost — reaching
a small term from a big one takes at least their size difference in fires. -/
theorem sc_descent_speed : ∀ {n : Nat} {t u : SCTerm}, RS.SC.StepsN n t u →
    t.leafCount ≤ u.leafCount + n := by
  intro n t u h
  refine h.rec (motive := fun n t u _ =>
      SCTerm.leafCount t ≤ SCTerm.leafCount u + n) ?_ ?_
  · intro a
    exact Nat.le_refl _
  · intro m a b c s rest ih
    have h1 := sc_unit_drop s
    omega

-- ## Stage 262: THE COLD LAW — C-fires never mint C-redexes.
-- The probe said it (390 C-fires, not one inventory increase); here is why. The
-- fired redex is consumed, and at most one of the two fresh application nodes can
-- complete a new redex — paid for exactly by the head shape the fire destroys. The
-- invariant is `Cinv + isC3` (inventory plus a two-spine head indicator), monotone
-- under every C-fire. The ninth wall, and one half of C14's minting ledger.

/-- Indicator: the atom `C`. -/
def scIsAtomC : SCTerm → Nat
  | .C => 1
  | _ => 0

/-- Indicator: a `C`-headed one-app (whose parent-of-parent is a redex). -/
def scIsHd1C : SCTerm → Nat
  | .app .C _ => 1
  | _ => 0

/-- Indicator: a `C`-headed two-spine (the shape that makes its parent a redex). -/
def scIsC3 : SCTerm → Nat
  | .app (.app .C _) _ => 1
  | _ => 0

/-- The C-redex inventory. -/
def scCInv : SCTerm → Nat
  | .S => 0
  | .C => 0
  | .app a b => scIsC3 a + scCInv a + scCInv b

/-- The two-spine indicator of an application, read off its function part. -/
theorem scIsC3_app (p q : SCTerm) : scIsC3 (.app p q) = scIsHd1C p := by
  rcases p with _ | _ | ⟨(_ | _ | ⟨a, b⟩), s⟩ <;> rfl

/-- The one-app indicator of an application, read off its function part. -/
theorem scIsHd1C_app (p q : SCTerm) : scIsHd1C (.app p q) = scIsAtomC p := by
  cases p <;> rfl

/-- The three head shapes are mutually exclusive. -/
theorem sc_shape_excl (x : SCTerm) :
    scIsHd1C x + scIsC3 x + scIsAtomC x ≤ 1 := by
  rcases x with _ | _ | ⟨(_ | _ | ⟨(_ | _ | ⟨a, b⟩), s⟩), v⟩ <;> simp [scIsHd1C, scIsC3, scIsAtomC]

/-- The two-spine indicator is at most one. -/
theorem scIsC3_le_one (q : SCTerm) : scIsC3 q ≤ 1 := by
  have := sc_shape_excl q
  omega

/-- Reading the two-spine indicator backwards. -/
theorem scIsC3_eq_one {q : SCTerm} (h : scIsC3 q = 1) :
    ∃ w v, q = .app (.app .C w) v := by
  rcases q with _ | _ | ⟨(_ | _ | ⟨(_ | _ | ⟨a, b⟩), s⟩), v⟩
  · simp [scIsC3] at h
  · simp [scIsC3] at h
  · simp [scIsC3] at h
  · simp [scIsC3] at h
  · simp [scIsC3] at h
  · exact ⟨s, v, rfl⟩
  · simp [scIsC3] at h

/-- C-steps fire inside applications. -/
theorem scStepC_src_app {r r' : SCTerm} (h : SCStepC r r') :
    ∃ a b, r = .app a b := by
  cases h with
  | C_red x y z => exact ⟨_, _, rfl⟩
  | appL _ => exact ⟨_, _, rfl⟩
  | appR _ => exact ⟨_, _, rfl⟩

/-- C-steps land on applications. -/
theorem scStepC_tgt_app {r r' : SCTerm} (h : SCStepC r r') :
    ∃ a b, r' = .app a b := by
  cases h with
  | C_red x y z => exact ⟨_, _, rfl⟩
  | appL _ => exact ⟨_, _, rfl⟩
  | appR _ => exact ⟨_, _, rfl⟩

/-- The one-app head indicator is invariant under C-fires. -/
theorem scStepC_hd1C {p p' : SCTerm} (h : SCStepC p p') :
    scIsHd1C p' = scIsHd1C p := by
  cases h with
  | C_red x y z => rfl
  | appL h' =>
      obtain ⟨a, b, rfl⟩ := scStepC_src_app h'
      obtain ⟨a', b', rfl⟩ := scStepC_tgt_app h'
      rfl
  | appR h' =>
      rename_i r s s'
      cases r <;> rfl

/-- Two-spines stay two-spines under C-fires: the root cannot fire, and inner fires
preserve the skeleton. -/
theorem scStepC_c3 {w v u : SCTerm}
    (h : SCStepC (.app (.app .C w) v) u) : scIsC3 u = 1 := by
  cases h with
  | appL h' =>
      cases h' with
      | appL h'' => cases h''
      | appR h'' => rfl
  | appR h' => rfl

/-- **The cold invariant**: `Cinv + isC3` never increases across a C-fire. -/
theorem scStepC_psi : ∀ {t u : SCTerm}, SCStepC t u →
    scCInv u + scIsC3 u ≤ scCInv t + scIsC3 t := by
  intro t u h
  induction h with
  | C_red x y z =>
      have e1 : scCInv (.app (.app (.app .C x) y) z)
          = 1 + scCInv x + scCInv y + scCInv z := by
        show 1 + (0 + (0 + 0 + scCInv x) + scCInv y) + scCInv z = _
        omega
      have e2 : scCInv (.app (.app x z) y)
          = scIsHd1C x + (scIsC3 x + scCInv x + scCInv z) + scCInv y := by
        show scIsC3 (.app x z) + (scIsC3 x + scCInv x + scCInv z) + scCInv y = _
        rw [scIsC3_app]
      have e3 : scIsC3 (.app (.app x z) y) = scIsAtomC x := by
        rw [scIsC3_app, scIsHd1C_app]
      have e4 : scIsC3 (.app (.app (.app .C x) y) z) = 0 := rfl
      have e5 := sc_shape_excl x
      rw [e1, e2, e3, e4]
      omega
  | appL h' ih =>
      rename_i p p' q
      rw [show scCInv (.app p' q) = scIsC3 p' + scCInv p' + scCInv q from rfl,
        show scCInv (.app p q) = scIsC3 p + scCInv p + scCInv q from rfl,
        scIsC3_app, scIsC3_app, scStepC_hd1C h']
      omega
  | appR h' ih =>
      rename_i p q q'
      rw [show scCInv (.app p q') = scIsC3 p + scCInv p + scCInv q' from rfl,
        show scCInv (.app p q) = scIsC3 p + scCInv p + scCInv q from rfl,
        scIsC3_app, scIsC3_app]
      have hq : scCInv q' ≤ scCInv q := by
        rcases hc : scIsC3 q with _ | n
        · omega
        · have hone : scIsC3 q = 1 := by
            have := scIsC3_le_one q
            omega
          obtain ⟨w, v, rfl⟩ := scIsC3_eq_one hone
          have h1 := scStepC_c3 h'
          have h2 : scIsC3 (.app (.app .C w) v) = 1 := rfl
          omega
      omega

/-- **THE COLD LAW**: a C-fire never increases the C-redex inventory. -/
theorem sc_cold_law {t u : SCTerm} (h : SCStepC t u) : scCInv u ≤ scCInv t := by
  have hpsi := scStepC_psi h
  rcases hc : scIsC3 t with _ | n
  · omega
  · have hone : scIsC3 t = 1 := by
      have := scIsC3_le_one t
      omega
    obtain ⟨w, v, rfl⟩ := scIsC3_eq_one hone
    have h1 := scStepC_c3 h
    have h2 : scIsC3 (.app (.app .C w) v) = 1 := rfl
    omega

-- ## Stage 263: THE MINTING LAW — inventory growth is paid for in leaves.
-- The hot half of C14's ledger, for the FULL step relation: across any fire, the
-- C-redex inventory (plus the head indicator) grows by at most the leaf growth plus
-- two. An S-fire's mint is dominated by its own duplication — a term's inventory
-- sits strictly below its leaf count — and a C-fire's mint is paid by the shape it
-- destroys. With the cold law and the unit drop law, every reduction's descent
-- budget is now accounted: drops come from C-fires, C-fires come from inventory,
-- and inventory comes from growth.

/-- Inventory sits strictly below leaf count. -/
theorem scCInv_succ_le_leaf : ∀ t : SCTerm, scCInv t + 1 ≤ t.leafCount
  | .S => Nat.le_refl 1
  | .C => Nat.le_refl 1
  | .app a b => by
      have ha := scCInv_succ_le_leaf a
      have hb := scCInv_succ_le_leaf b
      have hc := scIsC3_le_one a
      show scIsC3 a + scCInv a + scCInv b + 1 ≤ a.leafCount + b.leafCount
      omega

/-- Full steps fire inside applications. -/
theorem scStep_src_app {r r' : SCTerm} (h : SCStep r r') :
    ∃ a b, r = .app a b := by
  cases h with
  | S_red f g x => exact ⟨_, _, rfl⟩
  | C_red f g x => exact ⟨_, _, rfl⟩
  | appL _ => exact ⟨_, _, rfl⟩
  | appR _ => exact ⟨_, _, rfl⟩

/-- Full steps land on applications. -/
theorem scStep_tgt_app {r r' : SCTerm} (h : SCStep r r') :
    ∃ a b, r' = .app a b := by
  cases h with
  | S_red f g x => exact ⟨_, _, rfl⟩
  | C_red f g x => exact ⟨_, _, rfl⟩
  | appL _ => exact ⟨_, _, rfl⟩
  | appR _ => exact ⟨_, _, rfl⟩

/-- The one-app head indicator is invariant under all fires. -/
theorem scStep_hd1C {p p' : SCTerm} (h : SCStep p p') :
    scIsHd1C p' = scIsHd1C p := by
  cases h with
  | S_red f g x => rfl
  | C_red f g x => rfl
  | appL h' =>
      obtain ⟨a, b, rfl⟩ := scStep_src_app h'
      obtain ⟨a', b', rfl⟩ := scStep_tgt_app h'
      rfl
  | appR h' =>
      rename_i r s s'
      cases r <;> rfl

/-- Two-spines stay two-spines under all fires. -/
theorem scStep_c3 {w v u : SCTerm}
    (h : SCStep (.app (.app .C w) v) u) : scIsC3 u = 1 := by
  cases h with
  | appL h' =>
      cases h' with
      | appL h'' => cases h''
      | appR h'' => rfl
  | appR h' => rfl

/-- **THE MINTING LAW**: across any fire, inventory-plus-indicator grows by at most
the leaf growth plus two. -/
theorem sc_minting_law : ∀ {t u : SCTerm}, SCStep t u →
    scCInv u + scIsC3 u + t.leafCount
      ≤ scCInv t + scIsC3 t + u.leafCount + 2 := by
  intro t u h
  induction h with
  | S_red f g x =>
      have e1 : scCInv (.app (.app (.app .S f) g) x)
          = scCInv f + scCInv g + scCInv x := by
        show 0 + (0 + (0 + 0 + scCInv f) + scCInv g) + scCInv x = _
        omega
      have e2 : scCInv (.app (.app f x) (.app g x))
          = scIsHd1C f + (scIsC3 f + scCInv f + scCInv x)
            + (scIsC3 g + scCInv g + scCInv x) := by
        show scIsC3 (.app f x) + (scIsC3 f + scCInv f + scCInv x)
          + (scIsC3 g + scCInv g + scCInv x) = _
        rw [scIsC3_app]
      have e3 : scIsC3 (.app (.app f x) (.app g x)) = scIsAtomC f := by
        rw [scIsC3_app, scIsHd1C_app]
      have e4 : scIsC3 (.app (.app (.app .S f) g) x) = 0 := rfl
      have e5 := sc_shape_excl f
      have e6 := scIsC3_le_one g
      have e7 := scCInv_succ_le_leaf x
      have e8 : (SCTerm.app (.app (.app .S f) g) x).leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := by
        show 1 + f.leafCount + g.leafCount + x.leafCount = _
        omega
      have e9 : (SCTerm.app (.app f x) (.app g x)).leafCount
          = f.leafCount + x.leafCount + (g.leafCount + x.leafCount) := rfl
      rw [e1, e2, e3, e4, e8, e9]
      omega
  | C_red f g x =>
      have e1 : scCInv (.app (.app (.app .C f) g) x)
          = 1 + scCInv f + scCInv g + scCInv x := by
        show 1 + (0 + (0 + 0 + scCInv f) + scCInv g) + scCInv x = _
        omega
      have e2 : scCInv (.app (.app f x) g)
          = scIsHd1C f + (scIsC3 f + scCInv f + scCInv x) + scCInv g := by
        show scIsC3 (.app f x) + (scIsC3 f + scCInv f + scCInv x) + scCInv g = _
        rw [scIsC3_app]
      have e3 : scIsC3 (.app (.app f x) g) = scIsAtomC f := by
        rw [scIsC3_app, scIsHd1C_app]
      have e4 : scIsC3 (.app (.app (.app .C f) g) x) = 0 := rfl
      have e5 := sc_shape_excl f
      have e8 : (SCTerm.app (.app (.app .C f) g) x).leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := by
        show 1 + f.leafCount + g.leafCount + x.leafCount = _
        omega
      have e9 : (SCTerm.app (.app f x) g).leafCount
          = f.leafCount + x.leafCount + g.leafCount := rfl
      rw [e1, e2, e3, e4, e8, e9]
      omega
  | appL h' ih =>
      rename_i p p' q
      rw [show scCInv (.app p' q) = scIsC3 p' + scCInv p' + scCInv q from rfl,
        show scCInv (.app p q) = scIsC3 p + scCInv p + scCInv q from rfl,
        scIsC3_app, scIsC3_app, scStep_hd1C h',
        show (SCTerm.app p' q).leafCount = p'.leafCount + q.leafCount from rfl,
        show (SCTerm.app p q).leafCount = p.leafCount + q.leafCount from rfl]
      omega
  | appR h' ih =>
      rename_i p q q'
      rw [show scCInv (.app p q') = scIsC3 p + scCInv p + scCInv q' from rfl,
        show scCInv (.app p q) = scIsC3 p + scCInv p + scCInv q from rfl,
        scIsC3_app, scIsC3_app,
        show (SCTerm.app p q').leafCount = p.leafCount + q'.leafCount from rfl,
        show (SCTerm.app p q).leafCount = p.leafCount + q.leafCount from rfl]
      have hq : scCInv q' + q.leafCount ≤ scCInv q + q'.leafCount + 2 := by
        rcases hc : scIsC3 q with _ | n
        · omega
        · have hone : scIsC3 q = 1 := by
            have := scIsC3_le_one q
            omega
          obtain ⟨w, v, rfl⟩ := scIsC3_eq_one hone
          have h1 := scStep_c3 h'
          have h2 : scIsC3 (.app (.app .C w) v) = 1 := rfl
          omega
      omega

-- ## Stage 266: the integrated minting law — the ledger, summed along any path.
-- Over `n` fires, inventory-plus-indicator grows by at most the net leaf growth plus
-- `2n`. With the descent speed limit this bounds every reduction's bookkeeping from
-- both sides: leaves fall at most one per fire, and the C-redex stock that pays for
-- those falls is minted at a bounded exchange rate against the leaves gained.

/-- **The integrated minting law**: over `n` fires, inventory grows by at most the
net leaf growth plus `2n`. -/
theorem sc_minting_run : ∀ {n : Nat} {t u : SCTerm}, RS.SC.StepsN n t u →
    scCInv u + scIsC3 u + t.leafCount
      ≤ scCInv t + scIsC3 t + u.leafCount + 2 * n := by
  intro n t u h
  refine h.rec (motive := fun n t u _ =>
      scCInv u + scIsC3 u + SCTerm.leafCount t
        ≤ scCInv t + scIsC3 t + SCTerm.leafCount u + 2 * n) ?_ ?_
  · intro a
    omega
  · intro m a b c s rest ih
    have h1 := sc_minting_law s
    omega

-- ## Stage 267: THE RIDDEN REVOLUTION — the swapmill's full cycle, generic riders.
-- The revolution decomposes into seven phases, five already pinned: the cycle
-- (turnover + first descent), the reseed, a one-fire trigger, the SECOND descent
-- (the same run law), a second reseed, and the one-fire REBIRTH — where the junk
-- block `J₁ = (C driver)(C C)` reveals itself as a parked copy of the driver, and
-- the twice-wrapped old tower `C (C T)` becomes the new tower. Growth by wrapping,
-- rebirth by unparking: the engine's whole biography in `4j + 9` fires, and the law
-- is fully generic in the rider stack — the junk pairs `(C C, J₁)` are emitted in
-- front and nothing behind them is ever touched.

/-- The swapmill's junk block: the driver, C-parked over `C C` — the reseed's gift. -/
def scSwapJ1 : SCTerm :=
  .app (.app .C (.app (.app .S scSwapA) .C)) (.app .C .C)

/-- **THE TRIGGER**: one fire hands the fresh junk to the tower. -/
theorem sc_swap_trigger (T z : SCTerm) :
    RS.SC.StepsN 1
      (.app (.app (.app .C T) z) scSwapJ1)
      (.app (.app T scSwapJ1) z) :=
  RS.StepsN.tail (SCStep.C_red T z scSwapJ1) (@RS.StepsN.refl RS.SC _)

/-- **THE REBIRTH**: one fire unparks the driver from the junk block, and the
twice-wrapped tower rides into place. -/
theorem sc_swap_rebirth (w z : SCTerm) :
    RS.SC.StepsN 1
      (.app (.app scSwapJ1 w) z)
      (.app (.app (.app (.app (.app .S scSwapA) .C) w) (.app .C .C)) z) :=
  RS.StepsN.tail
    (SCStep.appL (SCStep.C_red (.app (.app .S scSwapA) .C) (.app .C .C) w))
    (@RS.StepsN.refl RS.SC _)

/-- **THE RIDDEN REVOLUTION**: from the driver over an even tower, under ANY rider
stack, `4j + 9` fires reach the driver over the tower-plus-two, with the junk pair
`(C C, J₁)` emitted in front of the untouched stack. -/
theorem sc_swap_revolution (j : Nat) (zs : List SCTerm) :
    RS.SC.StepsN (4 * j + 9)
      (scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) scSwapB)) zs)
      (scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j + 2) scSwapB))
        (.app .C .C :: scSwapJ1 :: zs)) := by
  have core : RS.SC.StepsN (4 * j + 9)
      (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) scSwapB))
      (scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j + 2) scSwapB))
        [.app .C .C, scSwapJ1]) := by
    have h1 := sc_swap_cycle j scSwapB
    have h2 := sc_swap_reseed (.app .C (scSwapT (2 * j) scSwapB))
      (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
    have h3 := sc_swap_trigger (scSwapT (2 * j) scSwapB)
      (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
    have h4 := sc_swap_run j scSwapB scSwapJ1
      (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
    have h5 := sc_swap_reseed scSwapJ1
      (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
    have h6 := sc_swap_rebirth
      (.app .C (.app .C (scSwapT (2 * j) scSwapB))) scSwapJ1
    have hcomp := RS.StepsN.trans h1 (RS.StepsN.trans h2 (RS.StepsN.trans h3
      (RS.StepsN.trans h4 (RS.StepsN.trans h5 h6))))
    rw [show 3 + 2 * j + (2 + (1 + (2 * j + (2 + 1)))) = 4 * j + 9 from by omega] at hcomp
    exact hcomp
  have lifted := scStepsN_appList zs core
  rw [← scAppList_append] at lifted
  exact lifted

-- ## Stage 268: THE SWAPMILL IS ETERNAL — the second engine runs forever.
-- Iterating the ridden revolution: from the fifteen-leaf pure seed, every number of
-- revolutions is realized, the tower climbs two per cycle, and the junk pairs pile
-- up in front of a stack nothing ever touches. The second species' analog of
-- sc_mill_eternal and sc_corridor_unbounded, at half the leaf budget.

/-- `r` revolutions' worth of emitted junk pairs. -/
def scSwapPairs : Nat → List SCTerm
  | 0 => []
  | r + 1 => .app .C .C :: scSwapJ1 :: scSwapPairs r

/-- Uniform pairs slide past one pair. -/
theorem scSwapPairs_shift : ∀ (r : Nat) (zs : List SCTerm),
    scSwapPairs r ++ .app .C .C :: scSwapJ1 :: zs
      = .app .C .C :: scSwapJ1 :: (scSwapPairs r ++ zs)
  | 0, zs => rfl
  | r + 1, zs => by
      show .app .C .C :: scSwapJ1 :: (scSwapPairs r ++ .app .C .C :: scSwapJ1 :: zs)
        = .app .C .C :: scSwapJ1 :: (.app .C .C :: scSwapJ1 :: (scSwapPairs r ++ zs))
      rw [scSwapPairs_shift r zs]

/-- The swapmill's state after `r` revolutions from tower height `2j`. -/
def scSwapState (j : Nat) (zs : List SCTerm) : SCTerm :=
  scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) scSwapB)) zs

/-- **THE SWAPMILL IS ETERNAL**: every revolution count is realized. -/
theorem sc_swap_eternal : ∀ (r j : Nat) (zs : List SCTerm),
    RS.SC.Steps (scSwapState j zs) (scSwapState (j + r) (scSwapPairs r ++ zs))
  | 0, j, zs => @RS.Steps.refl RS.SC _
  | r + 1, j, zs => by
      have h1 : RS.SC.Steps (scSwapState j zs)
          (scSwapState (j + 1) (.app .C .C :: scSwapJ1 :: zs)) := by
        have h := sc_swap_revolution j zs
        rw [show 2 * j + 2 = 2 * (j + 1) from by omega] at h
        exact RS.StepsN.toSteps h
      have h2 := sc_swap_eternal r (j + 1) (.app .C .C :: scSwapJ1 :: zs)
      have h := RS.Steps.trans h1 h2
      rw [show j + 1 + r = j + (r + 1) from by omega] at h
      rw [show scSwapPairs (r + 1) ++ zs
          = scSwapPairs r ++ (.app .C .C :: scSwapJ1 :: zs) from
        (scSwapPairs_shift r zs).symm]
      exact h

/-- The tower's weight. -/
theorem scSwapT_size : ∀ (k : Nat) (f : SCTerm),
    (scSwapT k f).leafCount = k + f.leafCount
  | 0, f => by show f.leafCount = 0 + f.leafCount; omega
  | k + 1, f => by
      show 1 + (scSwapT k f).leafCount = _
      rw [scSwapT_size k f]
      omega

/-- **THE SECOND CORRIDOR IS INFINITE**: the fifteen-leaf pure swapmill seed has an
unbounded reachable set. -/
theorem sc_swap_unbounded (n : Nat) :
    ∃ u, RS.SC.Steps (scSwapState 0 []) u ∧ n ≤ u.leafCount := by
  have hs := sc_swap_eternal n 0 []
  rw [Nat.zero_add] at hs
  refine ⟨scSwapState n (scSwapPairs n ++ []), hs, ?_⟩
  show n ≤ (scAppList (.app (.app (.app .S scSwapA) .C)
    (scSwapT (2 * n) scSwapB)) (scSwapPairs n ++ [])).leafCount
  have h := scAppList_leaf_ge (scSwapPairs n ++ [])
    (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * n) scSwapB))
  have h2 : (SCTerm.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * n) scSwapB)).leafCount
      = 5 + (scSwapT (2 * n) scSwapB).leafCount := by
    show 1 + 3 + 1 + (scSwapT (2 * n) scSwapB).leafCount = _
    omega
  rw [scSwapT_size] at h2
  have h3 : scSwapB.leafCount = 10 := rfl
  omega

-- ## Stage 269: THE FORCED SWAPMILL — every phase is the only move.
-- SCForced versions of the revolution's phases: towers of C over a normal base are
-- normal, the ping-pong run is forced at every layer (with the riders swapping), and
-- the four concrete phases (turnover, reseed, trigger, rebirth) are forced given
-- normal payloads. The generic pipeline (family membership, no-normal-form,
-- decidability) is already proved once and for all — these are its inputs.

/-- Towers over a normal base are normal. -/
theorem scSwapT_succ_nil {f : SCTerm} (hf : scSucc f = []) :
    ∀ k, scSucc (scSwapT k f) = []
  | 0 => hf
  | k + 1 => by
      show scSuccRoot (.app .C (scSwapT k f))
        ++ (scSucc .C).map (fun f' => .app f' (scSwapT k f))
        ++ (scSucc (scSwapT k f)).map (fun x' => .app .C x') = []
      rw [scSwapT_succ_nil hf k]
      rfl

/-- The base and the junk block are inert. -/
theorem scSwapB_succ_nil : scSucc scSwapB = [] := rfl
theorem scSwapJ1_succ_nil : scSucc scSwapJ1 = [] := rfl

/-- The ping-pong run's states: one swap per layer, riders alternating. -/
def scSwapRunChain : (d : Nat) → SCTerm → SCTerm → SCTerm → List SCTerm
  | 0, _, _, _ => []
  | d + 1, f, y, z =>
      (.app (.app (scSwapT d f) z) y) :: scSwapRunChain d f z y

/-- **The run is forced**: at every layer, the swap is the only move. -/
theorem scSwapRun_forced : ∀ (d : Nat) (f y z : SCTerm),
    scSucc f = [] → scSucc y = [] → scSucc z = [] →
    SCForced (.app (.app (scSwapT d f) y) z) (scSwapRunChain d f y z)
  | 0, _, _, _ => fun _ _ _ => trivial
  | d + 1, f, y, z => by
      intro hf hy hz
      refine ⟨?_, scSwapRun_forced d f z y hf hz hy⟩
      show scSucc (.app (.app (.app .C (scSwapT d f)) y) z)
        = [.app (.app (scSwapT d f) z) y]
      simp [scSucc, scSuccRoot, scSwapT_succ_nil hf, hy, hz]

/-- The run chain is never empty for positive height. -/
theorem scSwapRunChain_ne (d : Nat) (f y z : SCTerm) :
    scSwapRunChain (d + 1) f y z ≠ [] := by
  show _ :: _ ≠ []
  simp

/-- A positive even run ends at the base with riders home. -/
theorem scSwapRunChain_last : ∀ (j : Nat) (f y z dflt : SCTerm), 1 ≤ j →
    (scSwapRunChain (2 * j) f y z).getLastD dflt = .app (.app f y) z := by
  intro j
  induction j with
  | zero => intro _ _ _ _ h; omega
  | succ j ih =>
      intro f y z dflt _
      show ((.app (.app (scSwapT (2 * j + 1) f) z) y)
        :: (.app (.app (scSwapT (2 * j) f) y) z)
        :: scSwapRunChain (2 * j) f y z).getLastD dflt = .app (.app f y) z
      rw [List.getLastD_cons, List.getLastD_cons]
      cases j with
      | zero => rfl
      | succ j' => exact ih f y z _ (by omega)

/-- **The turnover is forced**: with a normal tower, each of its three fires is the
only possible fire. -/
theorem sc_swap_turnover_forced (T : SCTerm) (hT : scSucc T = []) :
    SCForced (.app (.app (.app .S scSwapA) .C) T)
      [(.app (.app scSwapA T) (.app .C T)),
       (.app (.app (.app .S T) .C) (.app .C T)),
       (.app (.app T (.app .C T)) (.app .C (.app .C T)))] := by
  refine ⟨?_, ?_, ?_, trivial⟩ <;>
    simp [scSucc, scSuccRoot, scSwapA, hT]

/-- **The reseed is forced**: with normal riders, both fires are the only moves. -/
theorem sc_swap_reseed_forced (y z : SCTerm)
    (hy : scSucc y = []) (hz : scSucc z = []) :
    SCForced (.app (.app scSwapB y) z)
      [(.app (.app (.app .C y) scSwapJ1) z),
       (.app (.app y z) scSwapJ1)] := by
  refine ⟨?_, ?_, trivial⟩ <;>
    simp [scSucc, scSuccRoot, scSwapB, scSwapJ1, scSwapA, hy, hz]

/-- **The trigger is forced.** -/
theorem sc_swap_trigger_forced (T z : SCTerm)
    (hT : scSucc T = []) (hz : scSucc z = []) :
    SCForced (.app (.app (.app .C T) z) scSwapJ1)
      [(.app (.app T scSwapJ1) z)] := by
  refine ⟨?_, trivial⟩
  simp [scSucc, scSuccRoot, scSwapJ1, scSwapA, hT, hz]

/-- **The rebirth is forced.** -/
theorem sc_swap_rebirth_forced (w z : SCTerm)
    (hw : scSucc w = []) (hz : scSucc z = []) :
    SCForced (.app (.app scSwapJ1 w) z)
      [(.app (.app (.app (.app (.app .S scSwapA) .C) w) (.app .C .C)) z)] := by
  refine ⟨?_, trivial⟩
  simp [scSucc, scSuccRoot, scSwapJ1, scSwapA, hw, hz]

-- ## Stage 270: THE FORCED REVOLUTION — the swapmill's whole cycle admits no choice.
-- The five phase chains, appended: turnover, first run, reseed, trigger, second run,
-- second reseed, rebirth — `4j + 9` states, every one the only possible successor.

/-- The revolution's full state chain from the driver over tower `2j`. -/
def scSwapRevChain (j : Nat) : List SCTerm :=
  [(.app (.app scSwapA (scSwapT (2 * j) scSwapB))
      (.app .C (scSwapT (2 * j) scSwapB))),
   (.app (.app (.app .S (scSwapT (2 * j) scSwapB)) .C)
      (.app .C (scSwapT (2 * j) scSwapB))),
   (.app (.app (scSwapT (2 * j) scSwapB) (.app .C (scSwapT (2 * j) scSwapB)))
      (.app .C (.app .C (scSwapT (2 * j) scSwapB))))]
  ++ (scSwapRunChain (2 * j) scSwapB (.app .C (scSwapT (2 * j) scSwapB))
        (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
  ++ ([(.app (.app (.app .C (.app .C (scSwapT (2 * j) scSwapB))) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))),
       (.app (.app (.app .C (scSwapT (2 * j) scSwapB))
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) scSwapJ1)]
  ++ ([(.app (.app (scSwapT (2 * j) scSwapB) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB))))]
  ++ (scSwapRunChain (2 * j) scSwapB scSwapJ1
        (.app .C (.app .C (scSwapT (2 * j) scSwapB)))
  ++ ([(.app (.app (.app .C scSwapJ1) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))),
       (.app (.app scSwapJ1 (.app .C (.app .C (scSwapT (2 * j) scSwapB))))
          scSwapJ1)]
  ++ [(.app (.app (.app (.app (.app .S scSwapA) .C)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) (.app .C .C))
          scSwapJ1)])))))

/-- **THE FORCED REVOLUTION**: from the driver over a positive even tower, all
`4j + 9` fires of the revolution are the only possible fires. -/
theorem sc_swap_rev_forced (j : Nat) (hj : 1 ≤ j) :
    SCForced (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) scSwapB))
      (scSwapRevChain j) := by
  have hB := scSwapB_succ_nil
  have hT := scSwapT_succ_nil hB (2 * j)
  have hCT : scSucc (.app .C (scSwapT (2 * j) scSwapB)) = [] :=
    scSwapT_succ_nil hB (2 * j + 1)
  have hCCT : scSucc (.app .C (.app .C (scSwapT (2 * j) scSwapB))) = [] :=
    scSwapT_succ_nil hB (2 * j + 2)
  have hJ := scSwapJ1_succ_nil
  refine SCForced_append (sc_swap_turnover_forced _ hT) ?_
  rw [show ([(.app (.app scSwapA (scSwapT (2 * j) scSwapB))
      (.app .C (scSwapT (2 * j) scSwapB))),
     (.app (.app (.app .S (scSwapT (2 * j) scSwapB)) .C)
      (.app .C (scSwapT (2 * j) scSwapB))),
     (.app (.app (scSwapT (2 * j) scSwapB) (.app .C (scSwapT (2 * j) scSwapB)))
      (.app .C (.app .C (scSwapT (2 * j) scSwapB))))] : List SCTerm).getLastD _
      = (.app (.app (scSwapT (2 * j) scSwapB)
          (.app .C (scSwapT (2 * j) scSwapB)))
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) from rfl]
  refine SCForced_append (scSwapRun_forced (2 * j) scSwapB _ _ hB hCT hCCT) ?_
  rw [scSwapRunChain_last j scSwapB _ _ _ hj]
  refine SCForced_append (sc_swap_reseed_forced _ _ hCT hCCT) ?_
  rw [show ([(.app (.app (.app .C (.app .C (scSwapT (2 * j) scSwapB))) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))),
       (.app (.app (.app .C (scSwapT (2 * j) scSwapB))
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) scSwapJ1)] : List SCTerm).getLastD _
      = (.app (.app (.app .C (scSwapT (2 * j) scSwapB))
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) scSwapJ1) from rfl]
  refine SCForced_append (sc_swap_trigger_forced _ _ hT hCCT) ?_
  rw [show ([(.app (.app (scSwapT (2 * j) scSwapB) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB))))] : List SCTerm).getLastD _
      = (.app (.app (scSwapT (2 * j) scSwapB) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) from rfl]
  refine SCForced_append (scSwapRun_forced (2 * j) scSwapB _ _ hB hJ hCCT) ?_
  rw [scSwapRunChain_last j scSwapB _ _ _ hj]
  refine SCForced_append (sc_swap_reseed_forced _ _ hJ hCCT) ?_
  rw [show ([(.app (.app (.app .C scSwapJ1) scSwapJ1)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))),
       (.app (.app scSwapJ1 (.app .C (.app .C (scSwapT (2 * j) scSwapB))))
          scSwapJ1)] : List SCTerm).getLastD _
      = (.app (.app scSwapJ1 (.app .C (.app .C (scSwapT (2 * j) scSwapB))))
          scSwapJ1) from rfl]
  exact sc_swap_rebirth_forced _ _ hCCT hJ

-- ## Stage 271: THE SWAPMILL NEVER RESTS — family, membership, no normal form.
-- The 245-replay on species two: revolutions as a chain family under growing junk,
-- every state spine-3, the generic principle instantiated. The pure seventeen-leaf
-- seed (driver over the two-layer tower) has no reachable normal form.

/-- Swap towers are applications. -/
theorem scSwapT_isApp : ∀ (k : Nat), ∃ a b, scSwapT k scSwapB = .app a b
  | 0 => ⟨_, _, rfl⟩
  | _ + 1 => ⟨_, _, rfl⟩

/-- Run states are spine-3 when the base is an application. -/
theorem scSwapRunChain_spine3 : ∀ (d : Nat) (f y z : SCTerm),
    (∃ a b, f = .app a b) →
    ∀ u ∈ scSwapRunChain d f y z, SCSpine3 u
  | 0, _, _, _ => by intro _ u hu; exact absurd hu List.not_mem_nil
  | d + 1, f, y, z => by
      intro hf u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · cases d with
        | zero =>
            obtain ⟨a, b, hab⟩ := hf
            exact ⟨a, b, z, y, by rw [show scSwapT 0 f = f from rfl, hab]⟩
        | succ d' => exact ⟨_, _, _, _, rfl⟩
      · exact scSwapRunChain_spine3 d f z y hf u hu

/-- Every revolution state is spine-3. -/
theorem scSwapRevChain_spine3 (j : Nat) :
    ∀ u ∈ scSwapRevChain j, SCSpine3 u := by
  intro u hu
  obtain ⟨a, b, hT⟩ := scSwapT_isApp (2 * j)
  rcases List.mem_append.mp hu with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨_, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, rfl⟩
    · exact ⟨a, b, _, _, by rw [hT]⟩
  rcases List.mem_append.mp h with h | h
  · exact scSwapRunChain_spine3 (2 * j) scSwapB _ _ ⟨_, _, rfl⟩ u h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨_, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, rfl⟩
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    exact ⟨a, b, _, _, by rw [hT]⟩
  rcases List.mem_append.mp h with h | h
  · exact scSwapRunChain_spine3 (2 * j) scSwapB _ _ ⟨_, _, rfl⟩ u h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨_, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl
    exact ⟨_, _, _, _, rfl⟩

/-- The driver state is spine-3. -/
theorem scSwapDriver_spine3 (j : Nat) :
    SCSpine3 (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * j) scSwapB)) :=
  ⟨_, _, _, _, rfl⟩

/-- The revolution chain is nonempty. -/
theorem scSwapRevChain_ne (j : Nat) : scSwapRevChain j ≠ [] := by
  show _ :: _ ≠ []
  simp

/-- The revolution chain ends at the rebirth state. -/
theorem scSwapRevChain_last (j : Nat) (dflt : SCTerm) :
    (scSwapRevChain j).getLastD dflt
      = .app (.app (.app (.app (.app .S scSwapA) .C)
          (.app .C (.app .C (scSwapT (2 * j) scSwapB)))) (.app .C .C))
          scSwapJ1 := by
  have hne : ∀ (l r : List SCTerm), r ≠ [] → l ++ r ≠ [] :=
    fun l r hr h => hr (List.append_eq_nil_iff.mp h).2
  have h1 : ∀ zs : List SCTerm, zs ≠ [] → ∀ (l : List SCTerm) (d d' : SCTerm),
      (l ++ zs).getLastD d = zs.getLastD d' :=
    fun zs hzs l d d' => List.getLastD_append_right l hzs d d'
  simp only [scSwapRevChain]
  rw [h1 _ (hne _ _ (hne _ _ (hne _ _ (hne _ _ (hne _ _ (by simp)))))) _ dflt dflt]
  rw [h1 _ (hne _ _ (hne _ _ (hne _ _ (hne _ _ (by simp))))) _ dflt dflt]
  rw [h1 _ (hne _ _ (hne _ _ (hne _ _ (by simp)))) _ dflt dflt]
  rw [h1 _ (hne _ _ (hne _ _ (by simp))) _ dflt dflt]
  rw [h1 _ (hne _ _ (by simp)) _ dflt dflt]
  rw [h1 _ (by simp) _ dflt dflt]
  rfl

/-- The junk stack is inert. -/
theorem scSwapPairs_succ_nil : ∀ (r : Nat), ∀ z ∈ scSwapPairs r, scSucc z = []
  | 0 => by intro z hz; exact absurd hz List.not_mem_nil
  | r + 1 => by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact scSwapJ1_succ_nil
        · exact scSwapPairs_succ_nil r z hz

/-- The swapmill family: generation `r` is the driver over tower `2(1+r)` riding
`r` junk pairs. -/
def scSwapF (r : Nat) : SCTerm :=
  scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * (1 + r)) scSwapB))
    (scSwapPairs r)

/-- The family's chains: the ridden revolutions. -/
def scSwapChain (r : Nat) : List SCTerm :=
  (scSwapRevChain (1 + r)).map (scAppList · (scSwapPairs r))

/-- Every generation's chain is forced. -/
theorem scSwapF_forced (r : Nat) : SCForced (scSwapF r) (scSwapChain r) := by
  refine sc_forced_riders _ (scSwapPairs_succ_nil r) ?_
    (sc_swap_rev_forced (1 + r) (by omega))
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact scSwapDriver_spine3 (1 + r)
  · exact scSwapRevChain_spine3 (1 + r) u hu

/-- Each generation's chain ends where the next begins. -/
theorem scSwapChain_last (r : Nat) :
    (scSwapChain r).getLastD (scSwapF r) = scSwapF (r + 1) := by
  have h1 : (scSwapChain r).getLastD
      (scAppList (.app (.app (.app .S scSwapA) .C)
        (scSwapT (2 * (1 + r)) scSwapB)) (scSwapPairs r))
      = scAppList ((scSwapRevChain (1 + r)).getLastD
          (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * (1 + r)) scSwapB)))
          (scSwapPairs r) :=
    List.getLastD_map
  rw [show scSwapF r = scAppList (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + r)) scSwapB)) (scSwapPairs r) from rfl, h1,
    scSwapRevChain_last]
  show scAppList (scAppList (.app (.app (.app .S scSwapA) .C)
      (.app .C (.app .C (scSwapT (2 * (1 + r)) scSwapB))))
      [.app .C .C, scSwapJ1]) (scSwapPairs r) = _
  rw [← scAppList_append]
  show scAppList (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + r) + 2) scSwapB))
      (.app .C .C :: scSwapJ1 :: scSwapPairs r) = _
  rw [show 2 * (1 + r) + 2 = 2 * (1 + (r + 1)) from by omega]
  rfl

/-- Chains are nonempty. -/
theorem scSwapChain_ne (r : Nat) : scSwapChain r ≠ [] := by
  intro h
  exact scSwapRevChain_ne (1 + r) (List.map_eq_nil_iff.mp h)

/-- **THE SWAPMILL NEVER RESTS**: the pure seventeen-leaf seed has no reachable
normal form. -/
theorem sc_swapseed_no_nf :
    ∀ u, RS.SC.Steps (scSwapF 0) u → ∃ v, RS.SC.step u v :=
  sc_forced_forever_no_nf scSwapF scSwapChain scSwapF_forced scSwapChain_last
    scSwapChain_ne

/-- Every generation start is reachable from the seed. -/
theorem scSwapF_steps : ∀ k, RS.SC.Steps (scSwapF 0) (scSwapF k)
  | 0 => @RS.Steps.refl RS.SC _
  | k + 1 => by
      have h2 : RS.SC.Steps (scSwapF k) ((scSwapChain k).getLastD (scSwapF k)) :=
        scChained_steps_last (scSwapChain k) (scSwapF k) (scSwapF k)
          (scForced_chained _ _ (scSwapF_forced k)) List.mem_cons_self
      rw [scSwapChain_last k] at h2
      exact RS.Steps.trans (scSwapF_steps k) h2

/-- **THE SECOND CORRIDOR, EXACTLY**: a term is reachable from the swapmill seed iff
it is a generation start or lies on a generation's forced chain. -/
theorem sc_swapseed_reach_iff (u : SCTerm) :
    RS.SC.Steps (scSwapF 0) u ↔ ∃ k, u = scSwapF k ∨ u ∈ scSwapChain k := by
  constructor
  · exact sc_forced_family_mem scSwapF scSwapChain scSwapF_forced scSwapChain_last
      scSwapChain_ne u
  · rintro ⟨k, rfl | hu⟩
    · exact scSwapF_steps k
    · exact RS.Steps.trans (scSwapF_steps k)
        (scChained_steps _ _ _ (scForced_chained _ _ (scSwapF_forced k))
          (List.mem_cons_of_mem _ hu))

-- ## Stage 272: THE LINE, GENERIC — total order is a property of forced families.
-- Extracted from the mill's proof: ANY forced chain family's reachable set is
-- totally ordered by reduction. Both engines get their lines as instances; so will
-- every engine C13's classification ever finds.

/-- Any family state reduces to the next generation's start. -/
theorem sc_forced_family_to_next (F : Nat → SCTerm) (chain : Nat → List SCTerm)
    (hf : ∀ k, SCForced (F k) (chain k))
    (hlast : ∀ k, (chain k).getLastD (F k) = F (k + 1))
    (k : Nat) {u : SCTerm} (hu : u = F k ∨ u ∈ chain k) :
    RS.SC.Steps u (F (k + 1)) := by
  have h := scChained_steps_last (chain k) (F k) u
    (scForced_chained _ _ (hf k)) (List.mem_cons.mpr hu)
  rw [hlast k] at h
  exact h

/-- Generation starts reduce forward. -/
theorem sc_forced_family_steps_from (F : Nat → SCTerm) (chain : Nat → List SCTerm)
    (hf : ∀ k, SCForced (F k) (chain k))
    (hlast : ∀ k, (chain k).getLastD (F k) = F (k + 1)) :
    ∀ (k d : Nat), RS.SC.Steps (F k) (F (k + d))
  | _, 0 => @RS.Steps.refl RS.SC _
  | k, d + 1 =>
      RS.Steps.trans (sc_forced_family_steps_from F chain hf hlast k d)
        (sc_forced_family_to_next F chain hf hlast (k + d) (.inl rfl))

/-- **THE LINE, GENERIC**: a forced chain family's reachable set is totally ordered
by reduction — one road, for every engine. -/
theorem sc_forced_family_line (F : Nat → SCTerm) (chain : Nat → List SCTerm)
    (hf : ∀ k, SCForced (F k) (chain k))
    (hlast : ∀ k, (chain k).getLastD (F k) = F (k + 1))
    (hne : ∀ k, chain k ≠ []) :
    ∀ u v, RS.SC.Steps (F 0) u → RS.SC.Steps (F 0) v →
      RS.SC.Steps u v ∨ RS.SC.Steps v u := by
  have cross : ∀ k k', k < k' → ∀ u v, (u = F k ∨ u ∈ chain k) →
      (v = F k' ∨ v ∈ chain k') → RS.SC.Steps u v := by
    intro k k' hkk u v hu hv
    have h1 := sc_forced_family_to_next F chain hf hlast k hu
    have h2 : RS.SC.Steps (F (k + 1)) (F k') := by
      have h := sc_forced_family_steps_from F chain hf hlast (k + 1) (k' - (k + 1))
      rw [show k + 1 + (k' - (k + 1)) = k' from by omega] at h
      exact h
    have h3 : RS.SC.Steps (F k') v := by
      rcases hv with rfl | hv
      · exact @RS.Steps.refl RS.SC _
      · exact scChained_steps _ _ _ (scForced_chained _ _ (hf k'))
          (List.mem_cons_of_mem _ hv)
    exact RS.Steps.trans h1 (RS.Steps.trans h2 h3)
  intro u v hu hv
  obtain ⟨k, hk⟩ := sc_forced_family_mem F chain hf hlast hne u hu
  obtain ⟨k', hk'⟩ := sc_forced_family_mem F chain hf hlast hne v hv
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact .inl (cross k k' h u v hk hk')
  · subst h
    exact scChained_comparable (chain k) (F k)
      (scForced_chained _ _ (hf k)) u (List.mem_cons.mpr hk)
      v (List.mem_cons.mpr hk')
  · exact .inr (cross k' k h v u hk' hk)

/-- **THE SECOND LINE**: the swapmill seed's reachable set is one road. -/
theorem sc_swapseed_line : ∀ u v,
    RS.SC.Steps (scSwapF 0) u → RS.SC.Steps (scSwapF 0) v →
    RS.SC.Steps u v ∨ RS.SC.Steps v u :=
  sc_forced_family_line scSwapF scSwapChain scSwapF_forced scSwapChain_last
    scSwapChain_ne

-- ## Stage 273: REACHABILITY FROM THE SWAPMILL SEED IS DECIDABLE.
-- The second certified decision procedure, by the same bounded scan: junk pairs
-- weigh ten leaves each, so a candidate of `n` leaves can only live in the first
-- `n` generations.

/-- The junk stack's weight: ten leaves per pair. -/
theorem scSwapPairs_sum : ∀ r : Nat,
    ((scSwapPairs r).map SCTerm.leafCount).sum = 10 * r
  | 0 => rfl
  | r + 1 => by
      show 2 + (8 + ((scSwapPairs r).map SCTerm.leafCount).sum) = 10 * (r + 1)
      rw [scSwapPairs_sum r]
      omega

/-- The generation size floor: nothing in generation `k` weighs less than `1+10k`. -/
theorem scSwapGen_size_lb (k : Nat) (u : SCTerm)
    (hu : u = scSwapF k ∨ u ∈ scSwapChain k) :
    1 + 10 * k ≤ u.leafCount := by
  rcases hu with rfl | hu
  · show 1 + 10 * k ≤ (scAppList (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + k)) scSwapB)) (scSwapPairs k)).leafCount
    rw [scAppList_size, scSwapPairs_sum]
    have := SCTerm.leafCount_pos (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + k)) scSwapB))
    omega
  · have h' : u ∈ (scSwapRevChain (1 + k)).map
        (scAppList · (scSwapPairs k)) := hu
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp h'
    rw [scAppList_size, scSwapPairs_sum]
    have := SCTerm.leafCount_pos w
    omega

/-- The reachable set, bounded: only the first `|u|` generations can hold `u`. -/
theorem sc_swapseed_reach_bounded (u : SCTerm) :
    RS.SC.Steps (scSwapF 0) u
      ↔ ∃ k, k < u.leafCount ∧ (u = scSwapF k ∨ u ∈ scSwapChain k) := by
  rw [sc_swapseed_reach_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    rcases Nat.lt_or_ge k u.leafCount with h | h
    · exact h
    · have hb := scSwapGen_size_lb k u hk
      omega
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- The decider: scan the first `|u|` generations. -/
def scSwapReach (u : SCTerm) : Bool :=
  (List.range u.leafCount).any
    (fun k => decide (u = scSwapF k) || decide (u ∈ scSwapChain k))

/-- The decider is correct. -/
theorem scSwapReach_iff (u : SCTerm) :
    scSwapReach u = true ↔ RS.SC.Steps (scSwapF 0) u := by
  rw [sc_swapseed_reach_bounded]
  show ((List.range u.leafCount).any
    (fun k => decide (u = scSwapF k) || decide (u ∈ scSwapChain k))) = true ↔ _
  simp [List.any_eq_true, List.mem_range]

/-- **REACHABILITY FROM THE SWAPMILL SEED IS DECIDABLE**: the second certified
decision procedure, from the same generic pipeline. -/
instance scSwapReach_decidable (u : SCTerm) :
    Decidable (RS.SC.Steps (scSwapF 0) u) :=
  decidable_of_iff (scSwapReach u = true) (scSwapReach_iff u)

#guard scSwapReach .S = false
#guard scSwapReach (.app .S .C) = false

-- ## Stage 274: THE CHAMPION ANCHOR — scChamp170 joins the swapmill family.
-- The census's fifth drop-champion reaches the swapmill engine in thirteen fires
-- (driver over the bare base, one junk rider) and completes its first even-tower
-- valley at fire twenty-two. The family, generalized over any inert base stack,
-- then carries it forever: the champion has no reachable normal form.

/-- The swapmill family over an arbitrary inert base stack. -/
def scSwapFam (zs : List SCTerm) (r : Nat) : SCTerm :=
  scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * (1 + r)) scSwapB))
    (scSwapPairs r ++ zs)

/-- Its chains: the ridden revolutions. -/
def scSwapFamChain (zs : List SCTerm) (r : Nat) : List SCTerm :=
  (scSwapRevChain (1 + r)).map (scAppList · (scSwapPairs r ++ zs))

/-- Forced, for any inert base stack. -/
theorem scSwapFam_forced (zs : List SCTerm) (hzs : ∀ z ∈ zs, scSucc z = [])
    (r : Nat) : SCForced (scSwapFam zs r) (scSwapFamChain zs r) := by
  refine sc_forced_riders _ ?_ ?_ (sc_swap_rev_forced (1 + r) (by omega))
  · intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact scSwapPairs_succ_nil r z h
    · exact hzs z h
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact scSwapDriver_spine3 (1 + r)
    · exact scSwapRevChain_spine3 (1 + r) u hu

/-- Chain ends meet generation starts. -/
theorem scSwapFamChain_last (zs : List SCTerm) (r : Nat) :
    (scSwapFamChain zs r).getLastD (scSwapFam zs r) = scSwapFam zs (r + 1) := by
  have h1 : (scSwapFamChain zs r).getLastD
      (scAppList (.app (.app (.app .S scSwapA) .C)
        (scSwapT (2 * (1 + r)) scSwapB)) (scSwapPairs r ++ zs))
      = scAppList ((scSwapRevChain (1 + r)).getLastD
          (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * (1 + r)) scSwapB)))
          (scSwapPairs r ++ zs) :=
    List.getLastD_map
  rw [show scSwapFam zs r = scAppList (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + r)) scSwapB)) (scSwapPairs r ++ zs) from rfl, h1,
    scSwapRevChain_last]
  show scAppList (scAppList (.app (.app (.app .S scSwapA) .C)
      (.app .C (.app .C (scSwapT (2 * (1 + r)) scSwapB))))
      [.app .C .C, scSwapJ1]) (scSwapPairs r ++ zs) = _
  rw [← scAppList_append]
  show scAppList (.app (.app (.app .S scSwapA) .C)
      (scSwapT (2 * (1 + r) + 2) scSwapB))
      (.app .C .C :: scSwapJ1 :: (scSwapPairs r ++ zs)) = _
  rw [show 2 * (1 + r) + 2 = 2 * (1 + (r + 1)) from by omega]
  rfl

/-- Chains are nonempty. -/
theorem scSwapFamChain_ne (zs : List SCTerm) (r : Nat) :
    scSwapFamChain zs r ≠ [] := by
  intro h
  exact scSwapRevChain_ne (1 + r) (List.map_eq_nil_iff.mp h)

/-- The champion's base stack after its transient. -/
def scChampStack : List SCTerm := [.app .C .C, scSwapJ1, scSwapJ1]

/-- The champion's stack is inert. -/
theorem scChampStack_nil : ∀ z ∈ scChampStack, scSucc z = [] := by
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  · exact absurd hz List.not_mem_nil

/-- **THE ANCHOR**: twenty-two forced fires take the champion into the family. -/
theorem sc_champ170_anchor :
    (scForcedMarch scChamp170 22).getLastD scChamp170
      = scSwapFam scChampStack 0 := by decide

/-- The champion's shifted family: itself, then the swapmill generations. -/
def scChampF : Nat → SCTerm
  | 0 => scChamp170
  | r + 1 => scSwapFam scChampStack r

def scChampChain : Nat → List SCTerm
  | 0 => scForcedMarch scChamp170 22
  | r + 1 => scSwapFamChain scChampStack r

theorem scChampF_forced : ∀ r, SCForced (scChampF r) (scChampChain r)
  | 0 => scForcedMarch_forced 22 scChamp170
  | r + 1 => scSwapFam_forced scChampStack scChampStack_nil r

theorem scChampChain_last : ∀ r,
    (scChampChain r).getLastD (scChampF r) = scChampF (r + 1)
  | 0 => sc_champ170_anchor
  | r + 1 => scSwapFamChain_last scChampStack r

theorem scChampChain_ne : ∀ r, scChampChain r ≠ []
  | 0 => fun h =>
      absurd (h : scForcedMarch scChamp170 22 = []) (by decide)
  | r + 1 => scSwapFamChain_ne scChampStack r

/-- **THE CHAMPION NEVER RESTS**: the census's fifth drop-champion — a wild
twelve-leaf term — has no reachable normal form. -/
theorem sc_champ170_no_nf :
    ∀ u, RS.SC.Steps scChamp170 u → ∃ v, RS.SC.step u v :=
  sc_forced_forever_no_nf scChampF scChampChain scChampF_forced scChampChain_last
    scChampChain_ne

-- ## Stage 278: C12, STATED — the linear-excess conjecture and its payoff, named.
-- The static-potential program for the storm floor ends here: both the inventory
-- floor and the depth-weighted potential are falsified by late-completing S-redexes
-- (duplications invisible to any static count). The viable mechanism was pinned at
-- Stage 132 all along: THE BACKBONE (sc_decidable_of_bound). What remains is its
-- hypothesis — stated now as a named conjecture, with the payoff as a theorem.

/-- **C12, the linear-excess conjecture**: some affine function of the endpoint
sizes bounds the intermediates of some path between any two reachable terms. -/
def scLinearExcess : Prop :=
  ∃ a b c : Nat, ∀ t u : SCTerm, RS.SC.Steps t u →
    RS.StepsLe RS.SC SCTerm.leafCount
      (a * t.leafCount + b * u.leafCount + c) t u

/-- **C12 SUFFICES**: the linear-excess conjecture implies `{S,C}` reachability is
decidable — the program's central question, reduced to one quantitative law. -/
theorem sc_c12_decides (h : scLinearExcess) :
    ∀ t u : SCTerm, Nonempty (Decidable (RS.SC.Steps t u)) := by
  obtain ⟨a, b, c, hf⟩ := h
  intro t u
  exact ⟨sc_decidable_of_bound (fun m n => a * m + b * n + c) hf t u⟩

-- ## Stage 281: THE DRIVER LAW — one turnover for the whole swap-driver family.
-- d159 decodes as the swap-driver with a heavier third slot (`C (C C)` in place of
-- `C`) and snapshot junk; the turnover computation never inspects that slot. So the
-- law generalizes: for ANY third slot `X` and tower `T`, three fires re-emit the
-- self-application pattern with `X T` as payload. The swapmill's turnover is the
-- `X = C` instance; d159's is `X = C (C C)`; every species this driver motif powers
-- inherits the law. C13's classification gains its first family-level theorem.

/-- **THE DRIVER LAW**: the swap-driver's turnover, parametric in the third slot. -/
theorem sc_driver_law (X T : SCTerm) :
    RS.SC.StepsN 3 (.app (.app (.app .S scSwapA) X) T)
      (.app (.app T (.app X T)) (.app .C (.app X T))) :=
  RS.StepsN.tail (SCStep.S_red scSwapA X T)
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .S .C T))
      (RS.StepsN.tail (SCStep.S_red T .C (.app X T)) (@RS.StepsN.refl RS.SC _)))

-- ## Stage 283: the species-3 descent — four fires per layer, riders home.
-- d159's tower runs on the layer `L₃ x = (C (C C)) (C x)`: four C-fires strip one
-- layer and return both riders to their places (no ping-pong parity). With the
-- family driver law, species 3's core is two laws deep — the C13 grid takes shape:
-- slot X × layer grammar × junk policy.

/-- The species-3 layer. -/
def scSwap3L (x : SCTerm) : SCTerm := .app (.app .C (.app .C .C)) (.app .C x)

/-- **THE SPECIES-3 DESCENT**: four fires strip a layer, riders home. -/
theorem sc_l3_descent (w y z : SCTerm) :
    RS.SC.StepsN 4 (.app (.app (scSwap3L w) y) z) (.app (.app w y) z) :=
  RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .C .C) (.app .C w) y))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C y (.app .C w)))
      (RS.StepsN.tail (SCStep.C_red (.app .C w) y z)
        (RS.StepsN.tail (SCStep.C_red w z y) (@RS.StepsN.refl RS.SC _))))

/-- The species-3 descent is forced with inert payloads. -/
theorem sc_l3_descent_forced (w y z : SCTerm)
    (hw : scSucc w = []) (hy : scSucc y = []) (hz : scSucc z = []) :
    SCForced (.app (.app (scSwap3L w) y) z)
      [(.app (.app (.app (.app .C .C) y) (.app .C w)) z),
       (.app (.app (.app .C (.app .C w)) y) z),
       (.app (.app (.app .C w) z) y),
       (.app (.app w y) z)] := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
    simp [scSwap3L, scSucc, scSuccRoot, hw, hy, hz]

-- ## Stage 284: THE METRONOME — a predicted species with new dynamics.
-- The C13 grid, asked to predict: seeds synthesized for unseen slots. X = C (C C)
-- runs eternal as a heavier tower-climber (as predicted); igniting slots branch (as
-- predicted); and X = C C is a DISCOVERY — a fixed-period oscillator. Its core block
-- never grows: seventeen forced fires return the core EXACTLY, emitting one junk
-- pair. Not a mill (no tower, no growing period) — a pump. The first constant-period
-- eternal engine, found by synthesis before any census ever saw it.

/-- The metronome's slot block (`X = C C`) driver, base, head, and junk. -/
def scMetroB : SCTerm :=
  .app (.app .C .C)
    (.app (.app .C (.app (.app .S scSwapA) (.app .C .C))) (.app .C .C))

def scMetroH : SCTerm := .app (.app .C .C) (.app .C (.app .C scMetroB))

def scMetroJ : SCTerm :=
  .app (.app .C (.app (.app .S scSwapA) (.app .C .C))) (.app .C .C)

/-- The metronome's core: seventeen fires from here return here. -/
def scMetroCore : SCTerm :=
  .app (.app (.app .C scMetroH) scMetroJ) (.app .C scMetroH)

/-- **THE METRONOME LAW**: seventeen fires, the core returns exactly, one junk pair
emitted — a fixed point modulo emission. -/
theorem sc_metro_law :
    RS.SC.StepsN 17 scMetroCore
      (.app (.app scMetroCore (.app .C .C)) scMetroJ) :=
    (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))))
    (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))
    (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))
    (RS.StepsN.tail (SCStep.C_red (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))
    (RS.StepsN.tail (SCStep.C_red (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))
    (RS.StepsN.tail (SCStep.C_red (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C)) (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app (.app .C .S) .C) (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .S .C (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.S_red (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))) .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))) (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))) (.app .C (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))) (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C)) (.app (.app .C .C) (.app .C (.app .C (.app (.app .C .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C .C))) (.app .C .C))))))))))
    (@RS.StepsN.refl RS.SC _))))))))))))))))))

/-- `r` pump cycles' worth of junk pairs. -/
def scMetroPairs : Nat → List SCTerm
  | 0 => []
  | r + 1 => .app .C .C :: scMetroJ :: scMetroPairs r

/-- Uniform pairs slide past one pair. -/
theorem scMetroPairs_shift : ∀ (r : Nat) (zs : List SCTerm),
    scMetroPairs r ++ .app .C .C :: scMetroJ :: zs
      = .app .C .C :: scMetroJ :: (scMetroPairs r ++ zs)
  | 0, zs => rfl
  | r + 1, zs => by
      show .app .C .C :: scMetroJ :: (scMetroPairs r ++ .app .C .C :: scMetroJ :: zs)
        = .app .C .C :: scMetroJ :: (.app .C .C :: scMetroJ :: (scMetroPairs r ++ zs))
      rw [scMetroPairs_shift r zs]

/-- **THE METRONOME IS ETERNAL**: constant-period pumping forever, under any riders. -/
theorem sc_metro_eternal : ∀ (r : Nat) (zs : List SCTerm),
    RS.SC.Steps (scAppList scMetroCore zs)
      (scAppList scMetroCore (scMetroPairs r ++ zs))
  | 0, zs => @RS.Steps.refl RS.SC _
  | r + 1, zs => by
      have h1 : RS.SC.Steps (scAppList scMetroCore zs)
          (scAppList scMetroCore (.app .C .C :: scMetroJ :: zs)) := by
        have h := scStepsN_appList zs sc_metro_law
        exact RS.StepsN.toSteps h
      have h2 := sc_metro_eternal r (.app .C .C :: scMetroJ :: zs)
      have h := RS.Steps.trans h1 h2
      rw [show scMetroPairs (r + 1) ++ zs
          = scMetroPairs r ++ (.app .C .C :: scMetroJ :: zs) from
        (scMetroPairs_shift r zs).symm]
      exact h

-- ## Stage 286: THE METRONOME'S TRICHOTOMY — the cheapest portrait yet.
-- Constant chains make everything decide-powered: the forced march IS the chain,
-- its last state and nonemptiness are kernel computations, and the family is pure
-- pairs. Third complete portrait; first for the pumping regime.

/-- A Bool spine-3 check, for decide-powered membership sweeps. -/
def scSpine3b : SCTerm → Bool
  | .app (.app (.app _ _) _) _ => true
  | _ => false

theorem scSpine3b_sound : ∀ {u : SCTerm}, scSpine3b u = true → SCSpine3 u
  | .app (.app (.app p q) g) x, _ => ⟨p, q, g, x, rfl⟩
  | .S, h => Bool.noConfusion h
  | .C, h => Bool.noConfusion h
  | .app .S _, h => Bool.noConfusion h
  | .app .C _, h => Bool.noConfusion h
  | .app (.app .S _) _, h => Bool.noConfusion h
  | .app (.app .C _) _, h => Bool.noConfusion h

/-- The metronome family: the core over `r` cycles of junk pairs. -/
def scMetroF (r : Nat) : SCTerm := scAppList scMetroCore (scMetroPairs r)

/-- Its chains: the ridden seventeen-fire march. -/
def scMetroChain (r : Nat) : List SCTerm :=
  (scForcedMarch scMetroCore 17).map (scAppList · (scMetroPairs r))

/-- The pairs are inert. -/
theorem scMetroPairs_succ_nil : ∀ (r : Nat), ∀ z ∈ scMetroPairs r, scSucc z = []
  | 0 => by intro z hz; exact absurd hz List.not_mem_nil
  | r + 1 => by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · exact scMetroPairs_succ_nil r z hz

/-- Every generation is forced. -/
theorem scMetroF_forced (r : Nat) : SCForced (scMetroF r) (scMetroChain r) := by
  refine sc_forced_riders _ (scMetroPairs_succ_nil r) ?_
    (scForcedMarch_forced 17 scMetroCore)
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ⟨_, _, _, _, rfl⟩
  · exact scSpine3b_sound
      (List.all_eq_true.mp (by decide :
        (scForcedMarch scMetroCore 17).all scSpine3b = true) u hu)

/-- Chain ends meet generation starts. -/
theorem scMetroChain_last (r : Nat) :
    (scMetroChain r).getLastD (scMetroF r) = scMetroF (r + 1) := by
  have h1 : (scMetroChain r).getLastD (scAppList scMetroCore (scMetroPairs r))
      = scAppList ((scForcedMarch scMetroCore 17).getLastD scMetroCore)
          (scMetroPairs r) :=
    List.getLastD_map
  rw [show scMetroF r = scAppList scMetroCore (scMetroPairs r) from rfl, h1,
    show (scForcedMarch scMetroCore 17).getLastD scMetroCore
      = .app (.app scMetroCore (.app .C .C)) scMetroJ from by decide]
  rfl

/-- Chains are nonempty. -/
theorem scMetroChain_ne (r : Nat) : scMetroChain r ≠ [] := by
  intro h
  exact (by decide : scForcedMarch scMetroCore 17 ≠ [])
    (List.map_eq_nil_iff.mp h)

/-- **THE METRONOME NEVER RESTS.** -/
theorem sc_metro_no_nf :
    ∀ u, RS.SC.Steps (scMetroF 0) u → ∃ v, RS.SC.step u v :=
  sc_forced_forever_no_nf scMetroF scMetroChain scMetroF_forced scMetroChain_last
    scMetroChain_ne

/-- **THE THIRD CORRIDOR, EXACTLY.** -/
theorem sc_metro_reach_iff (u : SCTerm) :
    RS.SC.Steps (scMetroF 0) u ↔ ∃ k, u = scMetroF k ∨ u ∈ scMetroChain k := by
  constructor
  · exact sc_forced_family_mem scMetroF scMetroChain scMetroF_forced
      scMetroChain_last scMetroChain_ne u
  · rintro ⟨k, rfl | hu⟩
    · have h := sc_forced_family_steps_from scMetroF scMetroChain scMetroF_forced
        scMetroChain_last 0 k
      rw [Nat.zero_add] at h
      exact h
    · have h := sc_forced_family_steps_from scMetroF scMetroChain scMetroF_forced
        scMetroChain_last 0 k
      rw [Nat.zero_add] at h
      exact RS.Steps.trans h
        (scChained_steps _ _ _ (scForced_chained _ _ (scMetroF_forced k))
          (List.mem_cons_of_mem _ hu))

/-- The pairs' weight: eleven leaves per cycle. -/
theorem scMetroPairs_sum : ∀ r : Nat,
    ((scMetroPairs r).map SCTerm.leafCount).sum = 11 * r
  | 0 => rfl
  | r + 1 => by
      show 2 + (9 + ((scMetroPairs r).map SCTerm.leafCount).sum) = 11 * (r + 1)
      rw [scMetroPairs_sum r]
      omega

/-- The generation size floor. -/
theorem scMetroGen_size_lb (k : Nat) (u : SCTerm)
    (hu : u = scMetroF k ∨ u ∈ scMetroChain k) :
    1 + 11 * k ≤ u.leafCount := by
  rcases hu with rfl | hu
  · show 1 + 11 * k ≤ (scAppList scMetroCore (scMetroPairs k)).leafCount
    rw [scAppList_size, scMetroPairs_sum]
    have := SCTerm.leafCount_pos scMetroCore
    omega
  · have h' : u ∈ (scForcedMarch scMetroCore 17).map
        (scAppList · (scMetroPairs k)) := hu
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp h'
    rw [scAppList_size, scMetroPairs_sum]
    have := SCTerm.leafCount_pos w
    omega

/-- Bounded scan. -/
theorem sc_metro_reach_bounded (u : SCTerm) :
    RS.SC.Steps (scMetroF 0) u
      ↔ ∃ k, k < u.leafCount ∧ (u = scMetroF k ∨ u ∈ scMetroChain k) := by
  rw [sc_metro_reach_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk⟩
    rcases Nat.lt_or_ge k u.leafCount with h | h
    · exact h
    · have hb := scMetroGen_size_lb k u hk
      omega
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- The decider. -/
def scMetroReach (u : SCTerm) : Bool :=
  (List.range u.leafCount).any
    (fun k => decide (u = scMetroF k) || decide (u ∈ scMetroChain k))

theorem scMetroReach_iff (u : SCTerm) :
    scMetroReach u = true ↔ RS.SC.Steps (scMetroF 0) u := by
  rw [sc_metro_reach_bounded]
  show ((List.range u.leafCount).any
    (fun k => decide (u = scMetroF k) || decide (u ∈ scMetroChain k))) = true ↔ _
  simp [List.any_eq_true, List.mem_range]

/-- **REACHABILITY FROM THE METRONOME IS DECIDABLE** — the third certified decider. -/
instance scMetroReach_decidable (u : SCTerm) :
    Decidable (RS.SC.Steps (scMetroF 0) u) :=
  decidable_of_iff (scMetroReach u = true) (scMetroReach_iff u)

-- ## Stage 287: THE MILL FAMILY LAW — the second driver motif, slot-parametric.
-- The mill's six-fire turnover, hand-retraced, never inspects its layer block: for
-- ANY slot `z`, the core `K_z = (C (S C))((S ((C S) z)) C)` turns over to the
-- self-application pattern with layer `z (C M)` and junk `(C K_z)((S ((C S) z)) C)`.
-- The mill is the `z = C C` instance (kernel-checked against the pinned turnover).
-- Both driver motifs now have family-level laws: C13's enumeration is two axes of
-- slots over two cores.

/-- The mill-family core at slot `z`. -/
def scMillFamK (z : SCTerm) : SCTerm :=
  .app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) z)) .C)

/-- **THE MILL FAMILY LAW**: six fires, any slot — layer `z (C M)`, junk carries the
core. -/
theorem sc_millfam_law (z M : SCTerm) :
    RS.SC.StepsN 6
      (.app (.app (scMillFamK z) (.app .C (scMillFamK z))) M)
      (.app (.app (.app M (.app .C M)) (.app z (.app .C M)))
        (.app (.app .C (scMillFamK z)) (.app (.app .S (.app (.app .C .S) z)) .C))) :=
    (RS.StepsN.tail (SCStep.appL (SCStep.C_red (.app .S .C) (.app (.app .S (.app (.app .C .S) z)) .C) (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) z)) .C)))))
    (RS.StepsN.tail (SCStep.appL (SCStep.S_red .C (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) z)) .C))) (.app (.app .S (.app (.app .C .S) z)) .C)))
    (RS.StepsN.tail (SCStep.C_red (.app (.app .S (.app (.app .C .S) z)) .C) (.app (.app .C (.app (.app .C (.app .S .C)) (.app (.app .S (.app (.app .C .S) z)) .C))) (.app (.app .S (.app (.app .C .S) z)) .C)) M)
    (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app (.app .C .S) z) .C M))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .S z M)))
    (RS.StepsN.tail (SCStep.appL (SCStep.S_red M z (.app .C M)))
    (@RS.StepsN.refl RS.SC _)))))))

-- ## Stage 290: THE TENSTROKE — the second pump, pinned.
-- The grid's period-8-flagged engine resolves at period TEN: a twenty-six-leaf core
-- returns exactly every ten forced fires, emitting FOUR riders per stroke
-- (C, C, a twenty-leaf junk block, C C). Pumps are a family with varied periods and
-- emission signatures; each is a fixed point modulo emission, each pinnable by one
-- mechanical emission.

/-- The tenstroke's core. -/
def scTenCore : SCTerm :=
  (.app (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))

/-- Its twenty-leaf junk block. -/
def scTenJ : SCTerm :=
  (.app .C (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))

/-- **THE TENSTROKE LAW**: ten fires, the core returns, four riders emitted. -/
theorem sc_ten_law :
    RS.SC.StepsN 10 scTenCore
      (.app (.app (.app (.app scTenCore .C) .C) scTenJ) (.app .C .C)) :=
    (RS.StepsN.tail (SCStep.C_red (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C))) (.app .C .C) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))
    (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app (.app .C .S) .C) (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red .S .C (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.S_red (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))) .C (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) .C) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C .C (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))) .C (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C .C) .C) (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red .C .C (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))))
    (RS.StepsN.tail (SCStep.appL (SCStep.appL (SCStep.appL (SCStep.C_red (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)) .C (.app (.app .C (.app (.app .C .C) .C)) (.app (.app .C (.app (.app .S (.app (.app .C .S) .C)) (.app .C (.app (.app .C .C) .C)))) (.app .C .C)))))))
    (@RS.StepsN.refl RS.SC _)))))))))))

-- ## Stage 291: THE PUMP PRINCIPLE — one theorem, every pump eternal.
-- Any core satisfying a fixed-point-modulo-emission law pumps forever under any
-- riders. The metronome and the tenstroke become instances; so will every pump the
-- grid ever finds.

/-- `r` repetitions of an emission block. -/
def scRep : Nat → List SCTerm → List SCTerm
  | 0, _ => []
  | r + 1, em => em ++ scRep r em

/-- Repetitions slide past one block. -/
theorem scRep_shift : ∀ (r : Nat) (em zs : List SCTerm),
    scRep r em ++ (em ++ zs) = em ++ (scRep r em ++ zs)
  | 0, _, _ => rfl
  | r + 1, em, zs => by
      show (em ++ scRep r em) ++ (em ++ zs) = em ++ ((em ++ scRep r em) ++ zs)
      rw [List.append_assoc, scRep_shift r em zs, List.append_assoc]

/-- **THE PUMP PRINCIPLE**: a fixed point modulo emission pumps forever. -/
theorem sc_pump_eternal (core : SCTerm) (p : Nat) (em : List SCTerm)
    (hlaw : RS.SC.StepsN p core (scAppList core em)) :
    ∀ (r : Nat) (zs : List SCTerm),
      RS.SC.Steps (scAppList core zs) (scAppList core (scRep r em ++ zs))
  | 0, zs => @RS.Steps.refl RS.SC _
  | r + 1, zs => by
      have h1 : RS.SC.StepsN p (scAppList core zs)
          (scAppList core (em ++ zs)) := by
        have h := scStepsN_appList zs hlaw
        rw [← scAppList_append] at h
        exact h
      have h2 := sc_pump_eternal core p em hlaw r (em ++ zs)
      have h := RS.Steps.trans (RS.StepsN.toSteps h1) h2
      rw [show scRep (r + 1) em ++ zs = scRep r em ++ (em ++ zs) from by
        show (em ++ scRep r em) ++ zs = scRep r em ++ (em ++ zs)
        rw [scRep_shift r em zs, ← List.append_assoc]]
      exact h

/-- **THE TENSTROKE IS ETERNAL** — by the principle, in one line. -/
theorem sc_ten_eternal : ∀ (r : Nat) (zs : List SCTerm),
    RS.SC.Steps (scAppList scTenCore zs)
      (scAppList scTenCore (scRep r [.C, .C, scTenJ, .app .C .C] ++ zs)) :=
  sc_pump_eternal scTenCore 10 [.C, .C, scTenJ, .app .C .C] sc_ten_law

-- ## Stage 293: THE CLIMB PRINCIPLE — one theorem, every climber eternal.
-- The pump principle's growing twin: a family of cores, each reaching the next with
-- a fixed emission, climbs forever under any riders. The mill and the swapmill
-- become instances of ONE statement; the corridor phase's known dynamics are now
-- two principles over two family laws.

/-- **THE CLIMB PRINCIPLE**: a graded fixed point modulo emission climbs forever. -/
theorem sc_climb_eternal (core : Nat → SCTerm) (p : Nat → Nat) (em : List SCTerm)
    (hlaw : ∀ k, RS.SC.StepsN (p k) (core k) (scAppList (core (k + 1)) em)) :
    ∀ (r k : Nat) (zs : List SCTerm),
      RS.SC.Steps (scAppList (core k) zs)
        (scAppList (core (k + r)) (scRep r em ++ zs))
  | 0, k, zs => @RS.Steps.refl RS.SC _
  | r + 1, k, zs => by
      have h1 : RS.SC.StepsN (p k) (scAppList (core k) zs)
          (scAppList (core (k + 1)) (em ++ zs)) := by
        have h := scStepsN_appList zs (hlaw k)
        rw [← scAppList_append] at h
        exact h
      have h2 := sc_climb_eternal core p em hlaw r (k + 1) (em ++ zs)
      have h := RS.Steps.trans (RS.StepsN.toSteps h1) h2
      rw [show k + 1 + r = k + (r + 1) from by omega] at h
      rw [show scRep (r + 1) em ++ zs = scRep r em ++ (em ++ zs) from by
        show (em ++ scRep r em) ++ zs = scRep r em ++ (em ++ zs)
        rw [scRep_shift r em zs, ← List.append_assoc]]
      exact h

/-- **THE SWAPMILL CLIMBS, by the principle** — one line. -/
theorem sc_swap_eternal' : ∀ (r k : Nat) (zs : List SCTerm),
    RS.SC.Steps
      (scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * k) scSwapB)) zs)
      (scAppList (.app (.app (.app .S scSwapA) .C) (scSwapT (2 * (k + r)) scSwapB))
        (scRep r [.app .C .C, scSwapJ1] ++ zs)) := by
  intro r k zs
  have h := sc_climb_eternal
    (fun k => .app (.app (.app .S scSwapA) .C) (scSwapT (2 * k) scSwapB))
    (fun k => 4 * k + 9) [.app .C .C, scSwapJ1]
    (fun k => by
      have h2 := sc_swap_revolution k []
      rw [show 2 * k + 2 = 2 * (k + 1) from by omega] at h2
      exact h2) r k zs
  exact h

-- ## Stage 294: THE CONSERVATION ARC OPENS — strong normalization, founded.
-- WN = SN for {S,C} (the non-erasing conservation theorem) is the assembly's
-- largest remaining piece. Foundations first: SN as accessibility, its subterm
-- laws, and SN ⟹ WN. The route decision is recorded in the ledger.

/-- Strong normalization: every reduction from `t` terminates. -/
def SCSN (t : SCTerm) : Prop := Acc (fun u v => SCStep v u) t

/-- Atoms are strongly normalizing. -/
theorem scSN_S : SCSN .S := Acc.intro _ (fun _ h => nomatch h)
theorem scSN_C : SCSN .C := Acc.intro _ (fun _ h => nomatch h)

/-- SN passes to the function part. -/
theorem scSN_appL : ∀ {t : SCTerm}, SCSN t → ∀ a b, t = .app a b → SCSN a := by
  intro t ht
  induction ht with
  | intro x hx ih =>
      intro a b hx'
      subst hx'
      exact Acc.intro a (fun a' ha' =>
        ih (.app a' b) (SCStep.appL ha') a' b rfl)

/-- SN passes to the argument part. -/
theorem scSN_appR : ∀ {t : SCTerm}, SCSN t → ∀ a b, t = .app a b → SCSN b := by
  intro t ht
  induction ht with
  | intro x hx ih =>
      intro a b hx'
      subst hx'
      exact Acc.intro b (fun b' hb' =>
        ih (.app a b') (SCStep.appR hb') a b' rfl)

/-- Strong normalization yields a normal form. -/
theorem scSN_wn : ∀ {t : SCTerm}, SCSN t →
    ∃ n, RS.SC.Steps t n ∧ ∀ v, ¬ RS.SC.step n v := by
  intro t ht
  induction ht with
  | intro x hx ih =>
      cases hc : scSucc x with
      | nil =>
          refine ⟨x, @RS.Steps.refl RS.SC x, ?_⟩
          intro v hv
          have hm := scSucc_complete hv
          rw [hc] at hm
          exact absurd hm List.not_mem_nil
      | cons u rest =>
          have hstep : SCStep x u := scSucc_sound (by rw [hc]; exact List.mem_cons_self)
          obtain ⟨n, hn, hnf⟩ := ih u hstep
          exact ⟨n, RS.Steps.tail hstep hn, hnf⟩

-- ## Stage 295: THE ROOT EXPANSION LEMMAS — conservation's heart.
-- An infinite path from a root redex either stays inside the components forever
-- (impossible when they are SN) or eventually fires the root — landing on a REDUCT
-- of the contractum, since the components only stepped in the meantime. So strong
-- normalization of the contractum forces strong normalization of the redex. These
-- are the {S,C} analogs of the λI conservation kernel.

/-- SN is preserved by one step. -/
theorem scSN_step {t u : SCTerm} (h : SCSN t) (s : SCStep t u) : SCSN u :=
  h.inv s

/-- SN is preserved along reductions. -/
theorem scSN_steps : ∀ {t u : SCTerm}, SCSN t → RS.SC.Steps t u → SCSN u := by
  intro t u ht h
  refine h.rec (motive := fun (a b : SCTerm) _ => SCSN a → SCSN b) ?_ ?_ ht
  · intro _ h
    exact h
  · intro a b c s _ ih ha
    exact ih (scSN_step ha s)

/-- One step embeds into a reduction. -/
theorem scStep_toSteps {t u : SCTerm} (s : SCStep t u) : RS.SC.Steps t u :=
  RS.Steps.tail s (@RS.Steps.refl RS.SC u)

/-- **THE S-EXPANSION CORE**: SN components whose every joint future contractum is
SN make the S-redex SN. -/
theorem sc_sn_S_crit : ∀ (f g x : SCTerm),
    SCSN f → SCSN g → SCSN x →
    (∀ f' g' x', RS.SC.Steps f f' → RS.SC.Steps g g' → RS.SC.Steps x x' →
      SCSN (.app (.app f' x') (.app g' x'))) →
    SCSN (.app (.app (.app .S f) g) x) := by
  intro f g x hf
  induction hf generalizing g x with
  | intro f hfacc ihf =>
      intro hg
      induction hg generalizing x with
      | intro g hgacc ihg =>
          intro hx
          induction hx with
          | intro x hxacc ihx =>
              intro hcon
              refine Acc.intro _ (fun u hu => ?_)
              cases hu with
              | S_red _ _ _ =>
                  exact hcon f g x (@RS.Steps.refl RS.SC f)
                    (@RS.Steps.refl RS.SC g) (@RS.Steps.refl RS.SC x)
              | appL h' =>
                  cases h' with
                  | appL h'' =>
                      cases h'' with
                      | appL h3 => cases h3
                      | appR h3 =>
                          exact ihf _ h3 g x (Acc.intro g hgacc)
                            (Acc.intro x hxacc)
                            (fun f' g' x' hf' hg' hx' =>
                              hcon f' g' x'
                                (RS.Steps.tail h3 hf') hg' hx')
                  | appR h'' =>
                      exact ihg _ h'' x (Acc.intro x hxacc)
                        (fun f' g' x' hf' hg' hx' =>
                          hcon f' g' x' hf'
                            (RS.Steps.tail h'' hg') hx')
              | appR h' =>
                  exact ihx _ h'
                    (fun f' g' x' hf' hg' hx' =>
                      hcon f' g' x' hf' hg'
                        (RS.Steps.tail h' hx'))

/-- **THE C-EXPANSION CORE.** -/
theorem sc_sn_C_crit : ∀ (f g x : SCTerm),
    SCSN f → SCSN g → SCSN x →
    (∀ f' g' x', RS.SC.Steps f f' → RS.SC.Steps g g' → RS.SC.Steps x x' →
      SCSN (.app (.app f' x') g')) →
    SCSN (.app (.app (.app .C f) g) x) := by
  intro f g x hf
  induction hf generalizing g x with
  | intro f hfacc ihf =>
      intro hg
      induction hg generalizing x with
      | intro g hgacc ihg =>
          intro hx
          induction hx with
          | intro x hxacc ihx =>
              intro hcon
              refine Acc.intro _ (fun u hu => ?_)
              cases hu with
              | C_red _ _ _ =>
                  exact hcon f g x (@RS.Steps.refl RS.SC f)
                    (@RS.Steps.refl RS.SC g) (@RS.Steps.refl RS.SC x)
              | appL h' =>
                  cases h' with
                  | appL h'' =>
                      cases h'' with
                      | appL h3 => cases h3
                      | appR h3 =>
                          exact ihf _ h3 g x (Acc.intro g hgacc)
                            (Acc.intro x hxacc)
                            (fun f' g' x' hf' hg' hx' =>
                              hcon f' g' x'
                                (RS.Steps.tail h3 hf') hg' hx')
                  | appR h'' =>
                      exact ihg _ h'' x (Acc.intro x hxacc)
                        (fun f' g' x' hf' hg' hx' =>
                          hcon f' g' x' hf'
                            (RS.Steps.tail h'' hg') hx')
              | appR h' =>
                  exact ihx _ h'
                    (fun f' g' x' hf' hg' hx' =>
                      hcon f' g' x' hf' hg'
                        (RS.Steps.tail h' hx'))

/-- **S-EXPANSION**: SN of the contractum forces SN of the redex. -/
theorem sc_sn_S_step (f g x : SCTerm)
    (h : SCSN (.app (.app f x) (.app g x))) :
    SCSN (.app (.app (.app .S f) g) x) := by
  refine sc_sn_S_crit f g x ?_ ?_ ?_ ?_
  · exact scSN_appL (scSN_appL h _ _ rfl) f x rfl
  · exact scSN_appL (scSN_appR h _ _ rfl) g x rfl
  · exact scSN_appR (scSN_appL h _ _ rfl) f x rfl
  · intro f' g' x' hf' hg' hx'
    exact scSN_steps h
      (scSteps_congApp (scSteps_congApp hf' hx') (scSteps_congApp hg' hx'))

/-- **C-EXPANSION**: SN of the contractum forces SN of the redex. -/
theorem sc_sn_C_step (f g x : SCTerm)
    (h : SCSN (.app (.app f x) g)) :
    SCSN (.app (.app (.app .C f) g) x) := by
  refine sc_sn_C_crit f g x ?_ ?_ ?_ ?_
  · exact scSN_appL (scSN_appL h _ _ rfl) f x rfl
  · exact scSN_appR h _ _ rfl
  · exact scSN_appR (scSN_appL h _ _ rfl) f x rfl
  · intro f' g' x' hf' hg' hx'
    exact scSN_steps h
      (scSteps_congApp (scSteps_congApp hf' hx') hg')

-- ## Stage 296: SHAPE STABILITY — two-spines stay two-spines, componentwise.
-- Needed by every conservation route: a two-spine's reducts are two-spines with the
-- same head and componentwise-reduced parts, so a contractum-of-reducts is always a
-- reduct of the contractum.

/-- Reducts of an S-two-spine are S-two-spines, componentwise. -/
theorem sc_steps_S2 : ∀ {t u : SCTerm}, RS.SC.Steps t u →
    ∀ f g, t = .app (.app .S f) g →
    ∃ f' g', u = .app (.app .S f') g' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps g g' := by
  intro t u h
  refine h.rec (motive := fun (a b : SCTerm) _ => ∀ f g, a = .app (.app .S f) g →
    ∃ f' g', b = .app (.app .S f') g' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps g g') ?_ ?_
  · intro a f g rfl
    exact ⟨f, g, rfl, @RS.Steps.refl RS.SC f, @RS.Steps.refl RS.SC g⟩
  · intro a b c s _ ih f g ha
    subst ha
    cases s with
    | appL h' =>
        cases h' with
        | appL h'' => cases h''
        | @appR _ _ f₁ h'' =>
            obtain ⟨f', g', hb, hf, hg⟩ := ih f₁ g rfl
            exact ⟨f', g', hb, RS.Steps.tail h'' hf, hg⟩
    | @appR _ _ g₁ h' =>
        obtain ⟨f', g', hb, hf, hg⟩ := ih f g₁ rfl
        exact ⟨f', g', hb, hf, RS.Steps.tail h' hg⟩

/-- Reducts of a C-two-spine are C-two-spines, componentwise. -/
theorem sc_steps_C2 : ∀ {t u : SCTerm}, RS.SC.Steps t u →
    ∀ f g, t = .app (.app .C f) g →
    ∃ f' g', u = .app (.app .C f') g' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps g g' := by
  intro t u h
  refine h.rec (motive := fun (a b : SCTerm) _ => ∀ f g, a = .app (.app .C f) g →
    ∃ f' g', b = .app (.app .C f') g' ∧ RS.SC.Steps f f' ∧ RS.SC.Steps g g') ?_ ?_
  · intro a f g rfl
    exact ⟨f, g, rfl, @RS.Steps.refl RS.SC f, @RS.Steps.refl RS.SC g⟩
  · intro a b c s _ ih f g ha
    subst ha
    cases s with
    | appL h' =>
        cases h' with
        | appL h'' => cases h''
        | @appR _ _ f₁ h'' =>
            obtain ⟨f', g', hb, hf, hg⟩ := ih f₁ g rfl
            exact ⟨f', g', hb, RS.Steps.tail h'' hf, hg⟩
    | @appR _ _ g₁ h' =>
        obtain ⟨f', g', hb, hf, hg⟩ := ih f g₁ rfl
        exact ⟨f', g', hb, hf, RS.Steps.tail h' hg⟩

-- ## Stage 298: THE SN-CLASS DECIDER — reachability from any SN term is decidable.
-- Pillar one, completed modulo conservation itself: strong normalization makes the
-- reachable set searchable by well-founded recursion over the successor lists. Once
-- WN ⟹ SN lands, every normalizing term inherits this decider.

/-- Reachability unfolds one step. -/
theorem scSteps_head_cases {t u : SCTerm} (h : RS.SC.Steps t u) :
    u = t ∨ ∃ v, SCStep t v ∧ RS.SC.Steps v u := by
  refine h.rec (motive := fun (a b : SCTerm) _ =>
    b = a ∨ ∃ v, SCStep a v ∧ RS.SC.Steps v b) ?_ ?_
  · intro a
    exact .inl rfl
  · intro a b c s rest _
    exact .inr ⟨b, s, rest⟩

/-- Membership-dependent bounded existential decision. -/
def scDecideBEx : (l : List SCTerm) → (P : SCTerm → Prop) →
    (∀ v ∈ l, Decidable (P v)) → Decidable (∃ v ∈ l, P v)
  | [], _, _ => isFalse (by rintro ⟨v, hv, _⟩; exact absurd hv List.not_mem_nil)
  | v :: rest, P, hd =>
      match hd v List.mem_cons_self with
      | isTrue h => isTrue ⟨v, List.mem_cons_self, h⟩
      | isFalse hn =>
          match scDecideBEx rest P
              (fun w hw => hd w (List.mem_cons_of_mem v hw)) with
          | isTrue hex => isTrue (by
              obtain ⟨w, hw, hp⟩ := hex
              exact ⟨w, List.mem_cons_of_mem v hw, hp⟩)
          | isFalse hn2 => isFalse (by
              rintro ⟨w, hw, hp⟩
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact hn hp
              · exact hn2 ⟨w, hw', hp⟩)

/-- **Reachability from a strongly normalizing term is decidable.** -/
def sc_sn_decide (t : SCTerm) (h : SCSN t) : ∀ u, Decidable (RS.SC.Steps t u) :=
  h.rec (motive := fun t _ => ∀ u, Decidable (RS.SC.Steps t u))
    (fun t _ ih u =>
      match (inferInstanceAs (DecidableEq SCTerm)) u t with
      | isTrue hut =>
          isTrue (by subst hut; exact @RS.Steps.refl RS.SC u)
      | isFalse hut =>
          match scDecideBEx (scSucc t) (fun v => RS.SC.Steps v u)
              (fun v hv => ih v (scSucc_sound hv) u) with
          | isTrue hex => isTrue (by
              obtain ⟨v, hv, hs⟩ := hex
              exact RS.Steps.tail (scSucc_sound hv) hs)
          | isFalse hn => isFalse (by
              intro hs
              rcases scSteps_head_cases hs with rfl | ⟨v, hv, hs'⟩
              · exact hut rfl
              · exact hn ⟨v, scSucc_complete hv, hs'⟩))

-- ## Stage 299: PARALLEL DERIVATIONS AS DATA — the finite-development kernel.
-- The conservation endgame needs to MEASURE how much development work a parallel
-- step still owes; Prop-level SCPar cannot carry a measure, so here is its
-- Type-level twin, the canonical complete-development derivation, the FD weight
-- (duplicating slots count double), and the kernel dichotomy: a single step is
-- either ALIGNED with a derivation (and strictly decreases its weight) or ESCAPES it.

/-- Type-level parallel derivations. -/
inductive SCParD : SCTerm → SCTerm → Type
  | S : SCParD .S .S
  | C : SCParD .C .C
  | app {t t' u u' : SCTerm} :
      SCParD t t' → SCParD u u' → SCParD (.app t u) (.app t' u')
  | S_red {f f' g g' x x' : SCTerm} :
      SCParD f f' → SCParD g g' → SCParD x x' →
      SCParD (.app (.app (.app .S f) g) x) (.app (.app f' x') (.app g' x'))
  | C_red {x x' y y' z z' : SCTerm} :
      SCParD x x' → SCParD y y' → SCParD z z' →
      SCParD (.app (.app (.app .C x) y) z) (.app (.app x' z') y')

/-- Derivations are sound for the Prop-level relation. -/
def SCParD.toPar : ∀ {t u : SCTerm}, SCParD t u → SCPar t u
  | _, _, .S => SCPar.S
  | _, _, .C => SCPar.C
  | _, _, .app d₁ d₂ => SCPar.app d₁.toPar d₂.toPar
  | _, _, .S_red df dg dx => SCPar.S_red df.toPar dg.toPar dx.toPar
  | _, _, .C_red dx dy dz => SCPar.C_red dx.toPar dy.toPar dz.toPar

/-- The identity derivation. -/
def SCParD.refl : ∀ (t : SCTerm), SCParD t t
  | .S => .S
  | .C => .C
  | .app a b => .app (SCParD.refl a) (SCParD.refl b)

/-- The finite-development weight: one per contracted redex, duplicating slots
count double. -/
def SCParD.mu : ∀ {t u : SCTerm}, SCParD t u → Nat
  | _, _, .S => 0
  | _, _, .C => 0
  | _, _, .app d₁ d₂ => d₁.mu + d₂.mu
  | _, _, .S_red df dg dx => 1 + df.mu + dg.mu + 2 * dx.mu
  | _, _, .C_red dx dy dz => 1 + dx.mu + dy.mu + dz.mu

/-- Every step admits a derivation (steps are Props, so the derivation lives in an
existential). -/
theorem scStep_exists_parD : ∀ {t u : SCTerm}, SCStep t u →
    Nonempty (SCParD t u) := by
  intro t u h
  induction h with
  | S_red f g x =>
      exact ⟨.S_red (SCParD.refl f) (SCParD.refl g) (SCParD.refl x)⟩
  | C_red f g x =>
      exact ⟨.C_red (SCParD.refl f) (SCParD.refl g) (SCParD.refl x)⟩
  | appL _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.app d (SCParD.refl _)⟩
  | appR _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.app (SCParD.refl _) d⟩

/-- The canonical complete-development derivation. -/
def SCParD.toDev : ∀ (t : SCTerm), SCParD t (scDev t)
  | .S => .S
  | .C => .C
  | .app (.app (.app .S f) g) x =>
      .S_red (SCParD.toDev f) (SCParD.toDev g) (SCParD.toDev x)
  | .app (.app (.app .C f) g) x =>
      .C_red (SCParD.toDev f) (SCParD.toDev g) (SCParD.toDev x)
  | .app .S u => .app .S (SCParD.toDev u)
  | .app .C u => .app .C (SCParD.toDev u)
  | .app (.app .S f) g =>
      .app (.app .S (SCParD.toDev f)) (SCParD.toDev g)
  | .app (.app .C f) g =>
      .app (.app .C (SCParD.toDev f)) (SCParD.toDev g)
  | .app (.app (.app (.app a b) c) d) e =>
      .app (SCParD.toDev (.app (.app (.app a b) c) d)) (SCParD.toDev e)

/-- The identity derivation weighs nothing. -/
theorem SCParD.mu_refl : ∀ (t : SCTerm), (SCParD.refl t).mu = 0
  | .S => rfl
  | .C => rfl
  | .app a b => by
      show (SCParD.refl a).mu + (SCParD.refl b).mu = 0
      rw [SCParD.mu_refl a, SCParD.mu_refl b]

-- ## Stage 300: THE PROJECTION METHOD — conservation without residuals.
-- The breakthrough route: fix an INNERMOST redex σ (a redex whose arguments are
-- normal — its occurrences in any term are pairwise disjoint, nothing ever fires
-- inside one, and it never occurs in its own contractum). Collapse every occurrence
-- at once with a simple recursive function. The per-step ledger (next stage) then
-- says: a step either contracts an occurrence (projection stalls, count drops by
-- one) or projects to at least one real step with creations paid for by the count.
-- No positions, no residuals, no derivation measures — counting and recursion.

/-- An innermost redex with its contractum: arguments normal, both rule shapes. -/
def SCInnerRedex (σ r : SCTerm) : Prop :=
  (∃ f g x, scSucc f = [] ∧ scSucc g = [] ∧ scSucc x = [] ∧
    σ = .app (.app (.app .S f) g) x ∧ r = .app (.app f x) (.app g x)) ∨
  (∃ f g x, scSucc f = [] ∧ scSucc g = [] ∧ scSucc x = [] ∧
    σ = .app (.app (.app .C f) g) x ∧ r = .app (.app f x) g)

/-- Occurrence count of a fixed subterm. -/
def scCount (σ : SCTerm) : SCTerm → Nat
  | .app a b => if .app a b = σ then 1 else scCount σ a + scCount σ b
  | _ => 0

/-- Collapse every occurrence of `σ` to `r`. -/
def scProj (σ r : SCTerm) : SCTerm → SCTerm
  | .app a b => if .app a b = σ then r else .app (scProj σ r a) (scProj σ r b)
  | .S => .S
  | .C => .C

/-- Normal applications decompose. -/
theorem scSucc_app_nil {a b : SCTerm} (h : scSucc (.app a b) = []) :
    scSuccRoot (.app a b) = [] ∧ scSucc a = [] ∧ scSucc b = [] := by
  have h' : scSuccRoot (.app a b)
      ++ (scSucc a).map (fun f' => .app f' b)
      ++ (scSucc b).map (fun x' => .app a x') = [] := h
  rcases List.append_eq_nil_iff.mp h' with ⟨h12, h3⟩
  rcases List.append_eq_nil_iff.mp h12 with ⟨h1, h2⟩
  exact ⟨h1, List.map_eq_nil_iff.mp h2, List.map_eq_nil_iff.mp h3⟩

/-- The innermost redex is not normal. -/
theorem scInner_not_normal {σ r : SCTerm} (h : SCInnerRedex σ r) :
    ¬ scSucc σ = [] := by
  rcases h with ⟨f, g, x, _, _, _, rfl, _⟩ | ⟨f, g, x, _, _, _, rfl, _⟩ <;>
    (intro hn
     have h1 := (scSucc_app_nil hn).1
     exact absurd h1 (by simp [scSuccRoot]))

/-- Normal terms hold no occurrences. -/
theorem scCount_normal {σ r : SCTerm} (h : SCInnerRedex σ r) :
    ∀ {t : SCTerm}, scSucc t = [] → scCount σ t = 0
  | .S, _ => rfl
  | .C, _ => rfl
  | .app a b, hn => by
      obtain ⟨_, ha, hb⟩ := scSucc_app_nil hn
      show (if .app a b = σ then 1 else scCount σ a + scCount σ b) = 0
      rw [if_neg (fun hσ => scInner_not_normal h (by rw [← hσ]; exact hn))]
      rw [scCount_normal h ha, scCount_normal h hb]

/-- Projection fixes normal terms. -/
theorem scProj_normal {σ r : SCTerm} (h : SCInnerRedex σ r) :
    ∀ {t : SCTerm}, scSucc t = [] → scProj σ r t = t
  | .S, _ => rfl
  | .C, _ => rfl
  | .app a b, hn => by
      obtain ⟨_, ha, hb⟩ := scSucc_app_nil hn
      show (if .app a b = σ then r else .app (scProj σ r a) (scProj σ r b))
        = .app a b
      rw [if_neg (fun hσ => scInner_not_normal h (by rw [← hσ]; exact hn))]
      rw [scProj_normal h ha, scProj_normal h hb]

/-- The redex never occurs in its own contractum. -/
theorem scCount_contractum {σ r : SCTerm} (h : SCInnerRedex σ r) :
    scCount σ r = 0 := by
  rcases h with ⟨f, g, x, hf, hg, hx, hσ, hr⟩ | ⟨f, g, x, hf, hg, hx, hσ, hr⟩
  · have hinner : SCInnerRedex σ r := .inl ⟨f, g, x, hf, hg, hx, hσ, hr⟩
    subst hσ hr
    have e1 : SCTerm.app (.app f x) (.app g x)
        ≠ SCTerm.app (.app (.app .S f) g) x := by
      intro he
      have h2 : (SCTerm.app (.app f x) (.app g x)).leafCount
          = (SCTerm.app (.app (.app .S f) g) x).leafCount := by rw [he]
      have h3 : f.leafCount + x.leafCount + (g.leafCount + x.leafCount)
          = 1 + f.leafCount + g.leafCount + x.leafCount := h2
      have h5 := SCTerm.leafCount_pos x
      have h6 := congrArg (fun t => match t with
        | SCTerm.app _ b => b.leafCount | _ => 0) he
      have h7 : g.leafCount + x.leafCount = x.leafCount := h6
      have h8 := SCTerm.leafCount_pos g
      omega
    have e2 : SCTerm.app f x ≠ SCTerm.app (.app (.app .S f) g) x := by
      intro he
      have h2 : (SCTerm.app f x).leafCount
          = (SCTerm.app (.app (.app .S f) g) x).leafCount := by rw [he]
      have h3 : f.leafCount + x.leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := h2
      have h5 := SCTerm.leafCount_pos g
      omega
    have e3 : SCTerm.app g x ≠ SCTerm.app (.app (.app .S f) g) x := by
      intro he
      have h2 : (SCTerm.app g x).leafCount
          = (SCTerm.app (.app (.app .S f) g) x).leafCount := by rw [he]
      have h3 : g.leafCount + x.leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := h2
      have h5 := SCTerm.leafCount_pos f
      omega
    show (if SCTerm.app (.app f x) (.app g x)
        = SCTerm.app (.app (.app .S f) g) x then 1
      else scCount _ (.app f x) + scCount _ (.app g x)) = 0
    rw [if_neg e1]
    show (if SCTerm.app f x = SCTerm.app (.app (.app .S f) g) x then 1
        else scCount _ f + scCount _ x)
      + ((if SCTerm.app g x = SCTerm.app (.app (.app .S f) g) x then 1
        else scCount _ g + scCount _ x)) = 0
    rw [if_neg e2, if_neg e3, scCount_normal hinner hf, scCount_normal hinner hg,
      scCount_normal hinner hx]
  · have hinner : SCInnerRedex σ r := .inr ⟨f, g, x, hf, hg, hx, hσ, hr⟩
    subst hσ hr
    have e1 : SCTerm.app (.app f x) g
        ≠ SCTerm.app (.app (.app .C f) g) x := by
      intro he
      have h2 : (SCTerm.app (.app f x) g).leafCount
          = (SCTerm.app (.app (.app .C f) g) x).leafCount := by rw [he]
      have h3 : f.leafCount + x.leafCount + g.leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := h2
      omega
    have e2 : SCTerm.app f x ≠ SCTerm.app (.app (.app .C f) g) x := by
      intro he
      have h2 : (SCTerm.app f x).leafCount
          = (SCTerm.app (.app (.app .C f) g) x).leafCount := by rw [he]
      have h3 : f.leafCount + x.leafCount
          = 1 + f.leafCount + g.leafCount + x.leafCount := h2
      have h5 := SCTerm.leafCount_pos g
      omega
    show (if SCTerm.app (.app f x) g
        = SCTerm.app (.app (.app .C f) g) x then 1
      else scCount _ (.app f x) + scCount _ g) = 0
    rw [if_neg e1]
    show (if SCTerm.app f x = SCTerm.app (.app (.app .C f) g) x then 1
        else scCount _ f + scCount _ x) + scCount _ g = 0
    rw [if_neg e2, scCount_normal hinner hf, scCount_normal hinner hg,
      scCount_normal hinner hx]

/-- A positive count survives to the enclosing application. -/
theorem scCount_pos_left {σ r : SCTerm} (_ : SCInnerRedex σ r) {a : SCTerm}
    (b : SCTerm) (ha : 1 ≤ scCount σ a) : 1 ≤ scCount σ (.app a b) := by
  show 1 ≤ if SCTerm.app a b = σ then 1 else scCount σ a + scCount σ b
  by_cases he : SCTerm.app a b = σ
  · rw [if_pos he]
    exact Nat.le_refl 1
  · rw [if_neg he]
    omega

/-- A positive count survives to the enclosing application (right). -/
theorem scCount_pos_right {σ r : SCTerm} (_ : SCInnerRedex σ r) (a : SCTerm)
    {b : SCTerm} (hb : 1 ≤ scCount σ b) : 1 ≤ scCount σ (.app a b) := by
  show 1 ≤ if SCTerm.app a b = σ then 1 else scCount σ a + scCount σ b
  by_cases he : SCTerm.app a b = σ
  · rw [if_pos he]
    exact Nat.le_refl 1
  · rw [if_neg he]
    omega

/-- **Innermost existence**: every non-normal term holds an innermost occurrence. -/
theorem sc_inner_exists : ∀ {t : SCTerm}, scSucc t ≠ [] →
    ∃ σ r, SCInnerRedex σ r ∧ 1 ≤ scCount σ t
  | .S, h => absurd rfl h
  | .C, h => absurd rfl h
  | .app a b, h => by
      by_cases ha : scSucc a = []
      · by_cases hb : scSucc b = []
        · -- components normal: the root must be the redex
          have hroot : scSuccRoot (.app a b) ≠ [] := by
            intro hr
            apply h
            show scSuccRoot (.app a b)
              ++ (scSucc a).map (fun f' => .app f' b)
              ++ (scSucc b).map (fun x' => .app a x') = []
            rw [hr, ha, hb]
            rfl
          -- extract the 3-spine shape
          rcases a with _ | _ | ⟨(_ | _ | ⟨(_ | _ | ⟨p, q⟩), g0⟩), f0⟩
          · exact absurd rfl hroot
          · exact absurd rfl hroot
          · exact absurd rfl hroot
          · exact absurd rfl hroot
          · obtain ⟨_, ha1, ha2⟩ := scSucc_app_nil ha
            obtain ⟨_, ha3, ha4⟩ := scSucc_app_nil ha1
            refine ⟨_, _, .inl ⟨g0, f0, b, ha4, ha2, hb, rfl, rfl⟩, ?_⟩
            show 1 ≤ if SCTerm.app (.app (.app .S g0) f0) b
              = SCTerm.app (.app (.app .S g0) f0) b then 1 else _
            rw [if_pos rfl]
            exact Nat.le_refl 1
          · obtain ⟨_, ha1, ha2⟩ := scSucc_app_nil ha
            obtain ⟨_, ha3, ha4⟩ := scSucc_app_nil ha1
            refine ⟨_, _, .inr ⟨g0, f0, b, ha4, ha2, hb, rfl, rfl⟩, ?_⟩
            show 1 ≤ if SCTerm.app (.app (.app .C g0) f0) b
              = SCTerm.app (.app (.app .C g0) f0) b then 1 else _
            rw [if_pos rfl]
            exact Nat.le_refl 1
          · exact absurd rfl hroot
        · obtain ⟨σ, r, hi, hc⟩ := sc_inner_exists hb
          exact ⟨σ, r, hi, scCount_pos_right hi a hc⟩
      · obtain ⟨σ, r, hi, hc⟩ := sc_inner_exists ha
        exact ⟨σ, r, hi, scCount_pos_left hi b hc⟩

-- ## Stage 301: THE PROJECTION LEDGER — every step, accounted.
-- Helpers, then the beast: a step either contracts an occurrence (projection
-- stalls, count drops by one) or projects to at least one step, creations paid.

/-- Occurrence-free terms project to themselves. -/
theorem scProj_of_count_zero {σ r : SCTerm} :
    ∀ {t : SCTerm}, scCount σ t = 0 → scProj σ r t = t
  | .S, _ => rfl
  | .C, _ => rfl
  | .app a b, hc => by
      have hne : SCTerm.app a b ≠ σ := by
        intro he
        rw [show scCount σ (.app a b) = 1 from by
          show (if SCTerm.app a b = σ then 1 else _) = 1
          rw [if_pos he]] at hc
        exact absurd hc (by omega)
      have hc' : scCount σ a + scCount σ b = 0 := by
        have : scCount σ (.app a b) = scCount σ a + scCount σ b := by
          show (if SCTerm.app a b = σ then 1 else _) = _
          rw [if_neg hne]
        omega
      show (if SCTerm.app a b = σ then r
        else .app (scProj σ r a) (scProj σ r b)) = .app a b
      rw [if_neg hne, scProj_of_count_zero (by omega : scCount σ a = 0),
        scProj_of_count_zero (by omega : scCount σ b = 0)]

/-- The innermost redex fires to its contractum. -/
theorem scInner_step {σ r : SCTerm} (h : SCInnerRedex σ r) : SCStep σ r := by
  rcases h with ⟨f, g, x, _, _, _, rfl, rfl⟩ | ⟨f, g, x, _, _, _, rfl, rfl⟩
  · exact SCStep.S_red f g x
  · exact SCStep.C_red f g x

/-- Normal terms take no step. -/
theorem scNormal_no_step {t u : SCTerm} (hn : scSucc t = []) (hs : SCStep t u) :
    False := by
  have hm := scSucc_complete hs
  rw [hn] at hm
  exact absurd hm List.not_mem_nil

/-- One-apps with atom heads are not the redex. -/
theorem scInner_ne1 {σ r : SCTerm} (h : SCInnerRedex σ r)
    {A : SCTerm} (hA : A = .S ∨ A = .C) (u : SCTerm) :
    SCTerm.app A u ≠ σ := by
  rcases h with ⟨f, g, x, _, _, _, rfl, _⟩ | ⟨f, g, x, _, _, _, rfl, _⟩ <;>
    (intro he
     rcases SCTerm.app.injEq .. ▸ he with ⟨h1, _⟩
     rcases hA with rfl | rfl <;> exact SCTerm.noConfusion h1)

/-- Two-spines with atom heads are not the redex. -/
theorem scInner_ne2 {σ r : SCTerm} (h : SCInnerRedex σ r)
    {A : SCTerm} (hA : A = .S ∨ A = .C) (u v : SCTerm) :
    SCTerm.app (.app A u) v ≠ σ := by
  rcases h with ⟨f, g, x, _, _, _, rfl, _⟩ | ⟨f, g, x, _, _, _, rfl, _⟩ <;>
    (intro he
     rcases SCTerm.app.injEq .. ▸ he with ⟨h1, _⟩
     rcases SCTerm.app.injEq .. ▸ h1 with ⟨h2, _⟩
     rcases hA with rfl | rfl <;> exact SCTerm.noConfusion h2)

/-- Two-spines over normal parts are normal. -/
theorem scSucc_2spine_nil {A f g : SCTerm} (hA : A = .S ∨ A = .C)
    (hf : scSucc f = []) (hg : scSucc g = []) :
    scSucc (.app (.app A f) g) = [] := by
  have h1 : scSucc (.app A f) = [] := by
    show scSuccRoot (.app A f) ++ (scSucc A).map _ ++ (scSucc f).map _ = []
    rcases hA with rfl | rfl <;> (rw [hf]; rfl)
  show scSuccRoot (.app (.app A f) g)
    ++ (scSucc (.app A f)).map _ ++ (scSucc g).map _ = []
  rw [h1, hg]
  rcases hA with rfl | rfl <;> rfl

/-- If the redex appears as an application, its two components are normal. -/
theorem scInner_components {σ r a b : SCTerm} (h : SCInnerRedex σ r)
    (he : σ = .app a b) : scSucc a = [] ∧ scSucc b = [] := by
  rcases h with ⟨f, g, x, hf, hg, hx, hσ, _⟩ | ⟨f, g, x, hf, hg, hx, hσ, _⟩
  · rw [hσ] at he
    rcases SCTerm.app.injEq .. ▸ he.symm with ⟨h1, h2⟩
    subst h1
    subst h2
    exact ⟨scSucc_2spine_nil (.inl rfl) hf hg, hx⟩
  · rw [hσ] at he
    rcases SCTerm.app.injEq .. ▸ he.symm with ⟨h1, h2⟩
    subst h1
    subst h2
    exact ⟨scSucc_2spine_nil (.inr rfl) hf hg, hx⟩

/-- Count at a matched node. -/
theorem scCount_self {σ a b : SCTerm} (h : SCTerm.app a b = σ) :
    scCount σ (.app a b) = 1 := by
  show (if SCTerm.app a b = σ then 1 else _) = 1
  rw [if_pos h]

/-- Count at an unmatched node. -/
theorem scCount_app_ne {σ a b : SCTerm} (h : SCTerm.app a b ≠ σ) :
    scCount σ (.app a b) = scCount σ a + scCount σ b := by
  show (if SCTerm.app a b = σ then 1 else _) = _
  rw [if_neg h]

/-- Projection at a matched node. -/
theorem scProj_self {σ r a b : SCTerm} (h : SCTerm.app a b = σ) :
    scProj σ r (.app a b) = r := by
  show (if SCTerm.app a b = σ then r else _) = r
  rw [if_pos h]

/-- Projection at an unmatched node. -/
theorem scProj_app_ne {σ r a b : SCTerm} (h : SCTerm.app a b ≠ σ) :
    scProj σ r (.app a b) = .app (scProj σ r a) (scProj σ r b) := by
  show (if SCTerm.app a b = σ then r else _) = _
  rw [if_neg h]

/-- The ledger's conclusion, named. -/
def SCLedger (σ r t s : SCTerm) : Prop :=
  (scProj σ r t = scProj σ r s ∧ scCount σ s + 1 = scCount σ t) ∨
  (∃ j, 1 ≤ j ∧ RS.SC.StepsN j (scProj σ r t) (scProj σ r s) ∧
    j + scCount σ t ≤ 1 + scCount σ s)

/-- The S-fire ledger. -/
theorem sc_ledger_S {σ r : SCTerm} (h : SCInnerRedex σ r) (f g x : SCTerm) :
    SCLedger σ r (.app (.app (.app .S f) g) x) (.app (.app f x) (.app g x)) := by
  by_cases ht : SCTerm.app (.app (.app .S f) g) x = σ
  · -- the step contracts the occurrence itself
    rcases h with ⟨f₀, g₀, x₀, hf, hg, hx, hσ, hr⟩ | ⟨f₀, g₀, x₀, hf, hg, hx, hσ, hr⟩
    · rw [hσ] at ht
      rcases SCTerm.app.injEq .. ▸ ht with ⟨h1, h2⟩
      rcases SCTerm.app.injEq .. ▸ h1 with ⟨h3, h4⟩
      rcases SCTerm.app.injEq .. ▸ h3 with ⟨_, h5⟩
      subst h2; subst h4; subst h5
      subst hσ; subst hr
      have hinner : SCInnerRedex (.app (.app (.app .S f) g) x)
          (.app (.app f x) (.app g x)) :=
        .inl ⟨f, g, x, hf, hg, hx, rfl, rfl⟩
      refine .inl ⟨?_, ?_⟩
      · rw [scProj_self rfl, scProj_of_count_zero (scCount_contractum hinner)]
      · rw [scCount_self rfl, scCount_contractum hinner]
    · rw [hσ] at ht
      rcases SCTerm.app.injEq .. ▸ ht with ⟨h1, _⟩
      rcases SCTerm.app.injEq .. ▸ h1 with ⟨h3, _⟩
      rcases SCTerm.app.injEq .. ▸ h3 with ⟨h5, _⟩
      exact absurd h5 (fun hh => SCTerm.noConfusion hh)
  · -- the occurrence survives; the step projects
    have hP : scProj σ r (.app (.app (.app .S f) g) x)
        = .app (.app (.app .S (scProj σ r f)) (scProj σ r g)) (scProj σ r x) := by
      rw [scProj_app_ne ht, scProj_app_ne (scInner_ne2 h (.inl rfl) f g),
        scProj_app_ne (scInner_ne1 h (.inl rfl) f)]
      rfl
    have hN : scCount σ (.app (.app (.app .S f) g) x)
        = scCount σ f + scCount σ g + scCount σ x := by
      rw [scCount_app_ne ht, scCount_app_ne (scInner_ne2 h (.inl rfl) f g),
        scCount_app_ne (scInner_ne1 h (.inl rfl) f)]
      show 0 + scCount σ f + scCount σ g + scCount σ x = _
      omega
    by_cases hs : SCTerm.app (.app f x) (.app g x) = σ
    · -- the fire ASSEMBLES the occurrence at the root
      obtain ⟨hfx, hgx⟩ := scInner_components h hs.symm
      obtain ⟨_, hfn, hxn⟩ := scSucc_app_nil hfx
      obtain ⟨_, hgn, _⟩ := scSucc_app_nil hgx
      have hPf := scProj_normal h hfn (σ := σ) (r := r)
      have hPg := scProj_normal h hgn (σ := σ) (r := r)
      have hPx := scProj_normal h hxn (σ := σ) (r := r)
      refine .inr ⟨2, by omega, ?_, ?_⟩
      · rw [hP, hPf, hPg, hPx, scProj_self hs]
        exact RS.StepsN.tail (SCStep.S_red f g x)
          (RS.StepsN.tail (by rw [hs]; exact scInner_step h)
            (@RS.StepsN.refl RS.SC r))
      · rw [hN, scCount_self hs, scCount_normal h hfn, scCount_normal h hgn,
          scCount_normal h hxn]
        omega
    · -- no assembly at the root; check the two fresh nodes
      have hPs : scProj σ r (.app (.app f x) (.app g x))
          = .app (scProj σ r (.app f x)) (scProj σ r (.app g x)) :=
        scProj_app_ne hs
      have hNs : scCount σ (.app (.app f x) (.app g x))
          = scCount σ (.app f x) + scCount σ (.app g x) :=
        scCount_app_ne hs
      by_cases h1 : SCTerm.app f x = σ <;> by_cases h2 : SCTerm.app g x = σ
      · -- both assembled
        obtain ⟨hfn, hxn⟩ := scInner_components h h1.symm
        obtain ⟨hgn, _⟩ := scInner_components h h2.symm
        refine .inr ⟨3, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_normal h hfn, scProj_normal h hgn,
            scProj_normal h hxn, scProj_self h1, scProj_self h2]
          exact RS.StepsN.tail (SCStep.S_red f g x)
            (RS.StepsN.tail (SCStep.appL (by rw [h1]; exact scInner_step h))
              (RS.StepsN.tail (SCStep.appR (by rw [h2]; exact scInner_step h))
                (@RS.StepsN.refl RS.SC _)))
        · rw [hN, hNs, scCount_self h1, scCount_self h2,
            scCount_normal h hfn, scCount_normal h hgn, scCount_normal h hxn]
          omega
      · -- left assembled only
        obtain ⟨hfn, hxn⟩ := scInner_components h h1.symm
        refine .inr ⟨2, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_normal h hfn, scProj_normal h hxn,
            scProj_self h1, scProj_app_ne h2, scProj_normal h hxn]
          exact RS.StepsN.tail (SCStep.S_red f (scProj σ r g) x)
            (RS.StepsN.tail (SCStep.appL (by rw [h1]; exact scInner_step h))
              (@RS.StepsN.refl RS.SC _))
        · rw [hN, hNs, scCount_self h1, scCount_app_ne h2,
            scCount_normal h hfn, scCount_normal h hxn]
          omega
      · -- right assembled only
        obtain ⟨hgn, hxn⟩ := scInner_components h h2.symm
        refine .inr ⟨2, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_normal h hgn, scProj_normal h hxn,
            scProj_self h2, scProj_app_ne h1, scProj_normal h hxn]
          exact RS.StepsN.tail (SCStep.S_red (scProj σ r f) g x)
            (RS.StepsN.tail (SCStep.appR (by rw [h2]; exact scInner_step h))
              (@RS.StepsN.refl RS.SC _))
        · rw [hN, hNs, scCount_self h2, scCount_app_ne h1,
            scCount_normal h hgn, scCount_normal h hxn]
          omega
      · -- neither
        refine .inr ⟨1, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_app_ne h1, scProj_app_ne h2]
          exact RS.StepsN.tail
            (SCStep.S_red (scProj σ r f) (scProj σ r g) (scProj σ r x))
            (@RS.StepsN.refl RS.SC _)
        · rw [hN, hNs, scCount_app_ne h1, scCount_app_ne h2]
          omega

/-- The C-fire ledger. -/
theorem sc_ledger_C {σ r : SCTerm} (h : SCInnerRedex σ r) (f g x : SCTerm) :
    SCLedger σ r (.app (.app (.app .C f) g) x) (.app (.app f x) g) := by
  by_cases ht : SCTerm.app (.app (.app .C f) g) x = σ
  · rcases h with ⟨f₀, g₀, x₀, hf, hg, hx, hσ, hr⟩ | ⟨f₀, g₀, x₀, hf, hg, hx, hσ, hr⟩
    · rw [hσ] at ht
      rcases SCTerm.app.injEq .. ▸ ht with ⟨h1, _⟩
      rcases SCTerm.app.injEq .. ▸ h1 with ⟨h3, _⟩
      rcases SCTerm.app.injEq .. ▸ h3 with ⟨h5, _⟩
      exact absurd h5 (fun hh => SCTerm.noConfusion hh)
    · rw [hσ] at ht
      rcases SCTerm.app.injEq .. ▸ ht with ⟨h1, h2⟩
      rcases SCTerm.app.injEq .. ▸ h1 with ⟨h3, h4⟩
      rcases SCTerm.app.injEq .. ▸ h3 with ⟨_, h5⟩
      subst h2; subst h4; subst h5
      subst hσ; subst hr
      have hinner : SCInnerRedex (.app (.app (.app .C f) g) x)
          (.app (.app f x) g) :=
        .inr ⟨f, g, x, hf, hg, hx, rfl, rfl⟩
      refine .inl ⟨?_, ?_⟩
      · rw [scProj_self rfl, scProj_of_count_zero (scCount_contractum hinner)]
      · rw [scCount_self rfl, scCount_contractum hinner]
  · have hP : scProj σ r (.app (.app (.app .C f) g) x)
        = .app (.app (.app .C (scProj σ r f)) (scProj σ r g)) (scProj σ r x) := by
      rw [scProj_app_ne ht, scProj_app_ne (scInner_ne2 h (.inr rfl) f g),
        scProj_app_ne (scInner_ne1 h (.inr rfl) f)]
      rfl
    have hN : scCount σ (.app (.app (.app .C f) g) x)
        = scCount σ f + scCount σ g + scCount σ x := by
      rw [scCount_app_ne ht, scCount_app_ne (scInner_ne2 h (.inr rfl) f g),
        scCount_app_ne (scInner_ne1 h (.inr rfl) f)]
      show 0 + scCount σ f + scCount σ g + scCount σ x = _
      omega
    by_cases hs : SCTerm.app (.app f x) g = σ
    · obtain ⟨hfx, hgn⟩ := scInner_components h hs.symm
      obtain ⟨_, hfn, hxn⟩ := scSucc_app_nil hfx
      refine .inr ⟨2, by omega, ?_, ?_⟩
      · rw [hP, scProj_normal h hfn, scProj_normal h hgn,
          scProj_normal h hxn, scProj_self hs]
        exact RS.StepsN.tail (SCStep.C_red f g x)
          (RS.StepsN.tail (by rw [hs]; exact scInner_step h)
            (@RS.StepsN.refl RS.SC r))
      · rw [hN, scCount_self hs, scCount_normal h hfn, scCount_normal h hgn,
          scCount_normal h hxn]
        omega
    · have hPs : scProj σ r (.app (.app f x) g)
          = .app (scProj σ r (.app f x)) (scProj σ r g) :=
        scProj_app_ne hs
      have hNs : scCount σ (.app (.app f x) g)
          = scCount σ (.app f x) + scCount σ g :=
        scCount_app_ne hs
      by_cases h1 : SCTerm.app f x = σ
      · obtain ⟨hfn, hxn⟩ := scInner_components h h1.symm
        refine .inr ⟨2, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_normal h hfn, scProj_normal h hxn,
            scProj_self h1]
          exact RS.StepsN.tail (SCStep.C_red f (scProj σ r g) x)
            (RS.StepsN.tail (SCStep.appL (by rw [h1]; exact scInner_step h))
              (@RS.StepsN.refl RS.SC _))
        · rw [hN, hNs, scCount_self h1,
            scCount_normal h hfn, scCount_normal h hxn]
          omega
      · refine .inr ⟨1, by omega, ?_, ?_⟩
        · rw [hP, hPs, scProj_app_ne h1]
          exact RS.StepsN.tail
            (SCStep.C_red (scProj σ r f) (scProj σ r g) (scProj σ r x))
            (@RS.StepsN.refl RS.SC _)
        · rw [hN, hNs, scCount_app_ne h1]
          omega

/-- **THE PROJECTION LEDGER**: every step either contracts an occurrence (the
projection stalls, the count drops by one) or projects to at least one step, with
any assembled occurrences paid for by the count. -/
theorem sc_proj_ledger {σ r : SCTerm} (h : SCInnerRedex σ r) :
    ∀ {t s : SCTerm}, SCStep t s → SCLedger σ r t s := by
  intro t s hstep
  induction hstep with
  | S_red f g x => exact sc_ledger_S h f g x
  | C_red f g x => exact sc_ledger_C h f g x
  | @appL a a' b h' ih =>
      have ht : SCTerm.app a b ≠ σ := by
        intro he
        obtain ⟨han, _⟩ := scInner_components h he.symm
        exact scNormal_no_step han h'
      have hPt : scProj σ r (.app a b)
          = .app (scProj σ r a) (scProj σ r b) := scProj_app_ne ht
      have hNt : scCount σ (.app a b)
          = scCount σ a + scCount σ b := scCount_app_ne ht
      by_cases hs : SCTerm.app a' b = σ
      · obtain ⟨ha'n, hbn⟩ := scInner_components h hs.symm
        have hca' : scCount σ a' = 0 := scCount_normal h ha'n
        rcases ih with ⟨hpe, hce⟩ | ⟨j, hj1, hsteps, hled⟩
        · refine .inr ⟨1, by omega, ?_, ?_⟩
          · rw [hPt, scProj_self hs, hpe, scProj_normal h ha'n,
              scProj_normal h hbn]
            exact RS.StepsN.tail (by rw [hs]; exact scInner_step h)
              (@RS.StepsN.refl RS.SC r)
          · rw [hNt, scCount_self hs, scCount_normal h hbn]
            omega
        · refine .inr ⟨j + 1, by omega, ?_, ?_⟩
          · rw [hPt, scProj_self hs]
            have hch := scStepsN_appL (scProj σ r b) hsteps
            have hfin : SCStep (.app (scProj σ r a') (scProj σ r b)) r := by
              rw [scProj_normal h ha'n, scProj_normal h hbn, hs]
              exact scInner_step h
            exact RS.StepsN.trans hch
              (RS.StepsN.tail hfin (@RS.StepsN.refl RS.SC r))
          · rw [hNt, scCount_self hs, scCount_normal h hbn]
            omega
      · have hPs : scProj σ r (.app a' b)
            = .app (scProj σ r a') (scProj σ r b) := scProj_app_ne hs
        have hNs : scCount σ (.app a' b)
            = scCount σ a' + scCount σ b := scCount_app_ne hs
        rcases ih with ⟨hpe, hce⟩ | ⟨j, hj1, hsteps, hled⟩
        · exact .inl ⟨by rw [hPt, hPs, hpe], by rw [hNt, hNs]; omega⟩
        · refine .inr ⟨j, hj1, ?_, ?_⟩
          · rw [hPt, hPs]
            exact scStepsN_appL (scProj σ r b) hsteps
          · rw [hNt, hNs]
            omega
  | @appR a b b' h' ih =>
      have ht : SCTerm.app a b ≠ σ := by
        intro he
        obtain ⟨_, hbn⟩ := scInner_components h he.symm
        exact scNormal_no_step hbn h'
      have hPt : scProj σ r (.app a b)
          = .app (scProj σ r a) (scProj σ r b) := scProj_app_ne ht
      have hNt : scCount σ (.app a b)
          = scCount σ a + scCount σ b := scCount_app_ne ht
      by_cases hs : SCTerm.app a b' = σ
      · obtain ⟨han, hb'n⟩ := scInner_components h hs.symm
        have hcb' : scCount σ b' = 0 := scCount_normal h hb'n
        rcases ih with ⟨hpe, hce⟩ | ⟨j, hj1, hsteps, hled⟩
        · refine .inr ⟨1, by omega, ?_, ?_⟩
          · rw [hPt, scProj_self hs, hpe, scProj_normal h hb'n,
              scProj_normal h han]
            exact RS.StepsN.tail (by rw [hs]; exact scInner_step h)
              (@RS.StepsN.refl RS.SC r)
          · rw [hNt, scCount_self hs, scCount_normal h han]
            omega
        · refine .inr ⟨j + 1, by omega, ?_, ?_⟩
          · rw [hPt, scProj_self hs]
            have hch := scStepsN_appR (scProj σ r a) hsteps
            have hfin : SCStep (.app (scProj σ r a) (scProj σ r b')) r := by
              rw [scProj_normal h han, scProj_normal h hb'n, hs]
              exact scInner_step h
            exact RS.StepsN.trans hch
              (RS.StepsN.tail hfin (@RS.StepsN.refl RS.SC r))
          · rw [hNt, scCount_self hs, scCount_normal h han]
            omega
      · have hPs : scProj σ r (.app a b')
            = .app (scProj σ r a) (scProj σ r b') := scProj_app_ne hs
        have hNs : scCount σ (.app a b')
            = scCount σ a + scCount σ b' := scCount_app_ne hs
        rcases ih with ⟨hpe, hce⟩ | ⟨j, hj1, hsteps, hled⟩
        · exact .inl ⟨by rw [hPt, hPs, hpe], by rw [hNt, hNs]; omega⟩
        · refine .inr ⟨j, hj1, ?_, ?_⟩
          · rw [hPt, hPs]
            exact scStepsN_appR (scProj σ r a) hsteps
          · rw [hNt, hNs]
            omega
