--! # The generic decidability engine (Stage 142)
-- Stages 133–139 built the capped-reachability engine, saturation, and the
-- decidable⟺bounded equivalence for `{S,C}`. The moment a second consumer appeared — SK has a
-- verified successor function (`succs`, Reachability.lean) and a complete enumerator
-- (`skSmallTerms`, Census/SKComplete.lean) — the machinery earns genericity, per the
-- no-premature-abstraction rule. This module is the Stage 133/134/139 chain over an abstract
-- `RS.SuccKit` (size, verified successors, complete bounded enumeration), delivering
-- `RS.SuccKit.decidable_iff_bound` at EVERY equipped rung. SK is instantiated below:
-- `sk_decidable_iff_bound` — the bounded-intermediates question IS the decidability question
-- at rung 0 exactly as at rung 3. The `{S,C}` originals stay as pinned, and `scKit` re-derives
-- their equivalence as a sanity instance.
import CombinatorCalculusPlayground.Universality.SCDecidability
import CombinatorCalculusPlayground.Reachability
import CombinatorCalculusPlayground.Census.SKComplete

/-- Everything the engine needs from a rewriting system: a size, a verified successor
function, and a complete bounded enumeration. -/
structure RS.SuccKit (A : RS) where
  size : A.Carrier → Nat
  succ : A.Carrier → List A.Carrier
  enumLe : Nat → List A.Carrier
  succ_sound : ∀ {t u : A.Carrier}, u ∈ succ t → A.step t u
  succ_complete : ∀ {t u : A.Carrier}, A.step t u → u ∈ succ t
  enumLe_complete : ∀ {c : Nat} {t : A.Carrier}, size t ≤ c → t ∈ enumLe c

namespace RS.SuccKit

variable {A : RS} [DecidableEq A.Carrier] (K : RS.SuccKit A)

/-- Insert without duplicating. -/
def kInsert (ts : List A.Carrier) (u : A.Carrier) : List A.Carrier :=
  if u ∈ ts then ts else u :: ts

theorem kInsert_mem {ts : List A.Carrier} {u v : A.Carrier} :
    v ∈ kInsert ts u ↔ v = u ∨ v ∈ ts := by
  unfold kInsert
  by_cases h : u ∈ ts
  · rw [if_pos h]
    constructor
    · intro hv; exact Or.inr hv
    · rintro (rfl | hv)
      · exact h
      · exact hv
  · rw [if_neg h]
    exact List.mem_cons

theorem kInsert_nodup {ts : List A.Carrier} {u : A.Carrier} (h : ts.Nodup) :
    (kInsert ts u).Nodup := by
  unfold kInsert
  by_cases hm : u ∈ ts
  · rw [if_pos hm]; exact h
  · rw [if_neg hm]; exact List.nodup_cons.mpr ⟨hm, h⟩

theorem kInsert_sub {ts : List A.Carrier} {u : A.Carrier} :
    ∀ v ∈ ts, v ∈ kInsert ts u :=
  fun _ hv => kInsert_mem.mpr (Or.inr hv)

theorem kFoldInsert_mem : ∀ (ns ts : List A.Carrier) (v : A.Carrier),
    v ∈ ns.foldl kInsert ts ↔ v ∈ ts ∨ v ∈ ns := by
  intro ns
  induction ns with
  | nil =>
      intro ts v
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h List.not_mem_nil
  | cons n ns ih =>
      intro ts v
      show v ∈ ns.foldl kInsert (kInsert ts n) ↔ _
      rw [ih, kInsert_mem]
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

theorem kFoldInsert_nodup : ∀ (ns ts : List A.Carrier), ts.Nodup →
    (ns.foldl kInsert ts).Nodup := by
  intro ns
  induction ns with
  | nil => intro ts h; exact h
  | cons n ns ih => intro ts h; exact ih _ (kInsert_nodup h)

/-- One saturation round. -/
def kRound (c : Nat) (ts : List A.Carrier) : List A.Carrier :=
  ((ts.flatMap K.succ).filter (fun u => K.size u ≤ c)).foldl kInsert ts

theorem kRound_mem {c : Nat} {ts : List A.Carrier} {v : A.Carrier} :
    v ∈ K.kRound c ts ↔ v ∈ ts ∨ (∃ w ∈ ts, A.step w v ∧ K.size v ≤ c) := by
  unfold kRound
  rw [kFoldInsert_mem]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have h' := List.mem_filter.mp h
      obtain ⟨w, hw, hsucc⟩ := List.mem_flatMap.mp h'.1
      exact ⟨w, hw, K.succ_sound hsucc, by simpa using h'.2⟩
  · rintro (h | ⟨w, hw, hstep, hcap⟩)
    · exact Or.inl h
    · right
      refine List.mem_filter.mpr ⟨?_, by simpa⟩
      exact List.mem_flatMap.mpr ⟨w, hw, K.succ_complete hstep⟩

theorem kRound_nodup {c : Nat} {ts : List A.Carrier} (h : ts.Nodup) :
    (K.kRound c ts).Nodup :=
  kFoldInsert_nodup _ _ h

theorem kRound_sub {c : Nat} {ts : List A.Carrier} : ∀ v ∈ ts, v ∈ K.kRound c ts :=
  fun _ hv => K.kRound_mem.mpr (Or.inl hv)

/-- The capped reachability engine. -/
def kReach (c : Nat) (t : A.Carrier) : Nat → List A.Carrier
  | 0 => [t]
  | n + 1 => K.kRound c (kReach c t n)

theorem kReach_nodup (c : Nat) (t : A.Carrier) : ∀ n, (K.kReach c t n).Nodup
  | 0 => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => K.kRound_nodup (kReach_nodup c t n)

theorem kReach_mono {c : Nat} {t : A.Carrier} {n : Nat} :
    ∀ v ∈ K.kReach c t n, v ∈ K.kReach c t (n + 1) :=
  fun v hv => K.kRound_sub v hv

theorem kReach_capped {c : Nat} {t : A.Carrier} (ht : K.size t ≤ c) :
    ∀ {n : Nat} {v : A.Carrier}, v ∈ K.kReach c t n → K.size v ≤ c := by
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
      rcases K.kRound_mem.mp hv with h | ⟨_, _, _, hcap⟩
      · exact ih h
      · exact hcap

/-- Bounded soundness: engine members are reached by capped paths. -/
theorem kReach_soundLe {c : Nat} {t : A.Carrier} (ht : K.size t ≤ c) :
    ∀ {n : Nat} {v : A.Carrier}, v ∈ K.kReach c t n →
    RS.StepsLe A K.size c t v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hvt : v = t := by
        rcases List.mem_cons.mp hv with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      rw [hvt]
      exact RS.StepsLe.refl t ht
  | succ n ih =>
      intro v hv
      rcases K.kRound_mem.mp hv with h | ⟨w, hw, hstep, hcap⟩
      · exact ih h
      · exact RS.StepsLe.snoc (ih hw) hstep hcap

/-- Completeness: capped paths land in the cone at some fuel. -/
theorem kReach_complete {c : Nat} {t : A.Carrier} :
    ∀ {v u : A.Carrier}, RS.StepsLe A K.size c v u →
    ∀ n, v ∈ K.kReach c t n → ∃ m, u ∈ K.kReach c t m := by
  intro v u h
  refine h.rec (motive := fun (v u : A.Carrier) _ =>
      ∀ n, v ∈ K.kReach c t n → ∃ m, u ∈ K.kReach c t m) ?_ ?_
  · intro a _ n hn
    exact ⟨n, hn⟩
  · intro a b d s _ rest ih n hn
    refine ih (n + 1) ?_
    exact K.kRound_mem.mpr (Or.inr ⟨a, hn, s, RS.StepsLe.head_le rest⟩)

theorem kReach_complete_start {c : Nat} {t u : A.Carrier}
    (h : RS.StepsLe A K.size c t u) :
    ∃ m, u ∈ K.kReach c t m :=
  K.kReach_complete h 0 List.mem_cons_self

theorem kReach_mono_add {c : Nat} {t : A.Carrier} (a m : Nat) :
    ∀ v ∈ K.kReach c t a, v ∈ K.kReach c t (a + m) := by
  induction m with
  | zero => intro v hv; exact hv
  | succ m ih => intro v hv; exact K.kReach_mono v (ih v hv)

theorem kReach_mono_le {c : Nat} {t : A.Carrier} {a b : Nat} (hab : a ≤ b) :
    ∀ v ∈ K.kReach c t a, v ∈ K.kReach c t b := by
  intro v hv
  have h := K.kReach_mono_add a (b - a) v hv
  rw [Nat.add_sub_cancel' hab] at h
  exact h

theorem kReach_stable_step {c : Nat} {t : A.Carrier} {n : Nat}
    (h : (K.kReach c t (n + 1)).length ≤ (K.kReach c t n).length) :
    ∀ v ∈ K.kReach c t (n + 1), v ∈ K.kReach c t n := by
  intro v hv
  by_cases hin : v ∈ K.kReach c t n
  · exact hin
  · exfalso
    have hnd : (v :: K.kReach c t n).Nodup :=
      List.nodup_cons.mpr ⟨hin, K.kReach_nodup c t n⟩
    have hsub : ∀ a, a ∈ v :: K.kReach c t n → a ∈ K.kReach c t (n + 1) := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | h'
      · exact hv
      · exact K.kReach_mono a h'
    have hle := List.nodup_length_le _ _ hnd hsub
    have hlen : (v :: K.kReach c t n).length = (K.kReach c t n).length + 1 := rfl
    omega

theorem kReach_stable_forever {c : Nat} {t : A.Carrier} {n : Nat}
    (h : ∀ v ∈ K.kReach c t (n + 1), v ∈ K.kReach c t n) :
    ∀ m v, v ∈ K.kReach c t (n + m) → v ∈ K.kReach c t n := by
  intro m
  induction m with
  | zero => intro v hv; exact hv
  | succ m ih =>
      intro v hv
      rcases K.kRound_mem.mp hv with h' | ⟨w, hw, hstep, hcap⟩
      · exact ih v h'
      · have hw' := ih w hw
        exact h v (K.kRound_mem.mpr (Or.inr ⟨w, hw', hstep, hcap⟩))

theorem kReach_exists_stable {c : Nat} {t : A.Carrier} (ht : K.size t ≤ c) :
    ∃ k, k ≤ (K.enumLe c).length ∧
      ∀ v ∈ K.kReach c t (k + 1), v ∈ K.kReach c t k := by
  have hbound : ∀ n, (K.kReach c t n).length ≤ (K.enumLe c).length := by
    intro n
    exact List.nodup_length_le _ _ (K.kReach_nodup c t n)
      (fun a ha => K.enumLe_complete (K.kReach_capped ht ha))
  have key : ∀ (b j : Nat), (K.enumLe c).length ≤ (K.kReach c t j).length + b →
      ∃ k, j ≤ k ∧ k ≤ j + b ∧
        (K.kReach c t (k + 1)).length ≤ (K.kReach c t k).length := by
    intro b
    induction b with
    | zero =>
        intro j hj
        refine ⟨j, Nat.le_refl _, by omega, ?_⟩
        have := hbound (j + 1)
        omega
    | succ b ih =>
        intro j hj
        by_cases hstep : (K.kReach c t (j + 1)).length ≤ (K.kReach c t j).length
        · exact ⟨j, Nat.le_refl _, by omega, hstep⟩
        · obtain ⟨k, hk1, hk2, hk3⟩ := ih (j + 1) (by omega)
          exact ⟨k, by omega, by omega, hk3⟩
  obtain ⟨k, _, hk2, hk3⟩ := key (K.enumLe c).length 0 (by omega)
  exact ⟨k, by omega, K.kReach_stable_step hk3⟩

/-- Saturation: fuel `|enumLe c|` sees everything any fuel ever sees. -/
theorem kReach_saturates {c : Nat} {t : A.Carrier} (ht : K.size t ≤ c) :
    ∀ n v, v ∈ K.kReach c t n → v ∈ K.kReach c t (K.enumLe c).length := by
  obtain ⟨k, hkle, hstable⟩ := K.kReach_exists_stable ht
  intro n v hv
  by_cases hn : n ≤ k
  · exact K.kReach_mono_le (Nat.le_trans hn hkle) v hv
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
    exact K.kReach_mono_le hkle v (K.kReach_stable_forever hstable m v hv)

/-- Capped reachability is decidable at every equipped rung. -/
def stepsLe_decidable (c : Nat) (t u : A.Carrier) (ht : K.size t ≤ c) :
    Decidable (RS.StepsLe A K.size c t u) :=
  decidable_of_iff (u ∈ K.kReach c t (K.enumLe c).length) (by
    constructor
    · intro h
      exact K.kReach_soundLe ht h
    · intro h
      obtain ⟨m, hm⟩ := K.kReach_complete_start h
      exact K.kReach_saturates ht m u hm)

/-- Bound ⟹ decidable, at every equipped rung. -/
def decidable_of_bound (f : Nat → Nat → Nat)
    (hf : ∀ t u : A.Carrier, A.Steps t u →
        RS.StepsLe A K.size (f (K.size t) (K.size u)) t u) :
    ∀ t u : A.Carrier, Decidable (A.Steps t u) := fun t u =>
  have ht : K.size t ≤ max (f (K.size t) (K.size u)) (K.size t) :=
    Nat.le_max_right _ _
  decidable_of_iff
    (u ∈ K.kReach (max (f (K.size t) (K.size u)) (K.size t)) t
      (K.enumLe (max (f (K.size t) (K.size u)) (K.size t))).length) (by
    constructor
    · intro h
      exact RS.StepsLe.toSteps (K.kReach_soundLe ht h)
    · intro h
      have h1 : RS.StepsLe A K.size
          (max (f (K.size t) (K.size u)) (K.size t)) t u :=
        RS.StepsLe.weaken (Nat.le_max_left _ _) (hf t u h)
      obtain ⟨m, hm⟩ := K.kReach_complete_start h1
      exact K.kReach_saturates ht m u hm)

instance stepsLeDecPred (t u : A.Carrier) :
    DecidablePred (fun c => RS.StepsLe A K.size c t u) := fun c =>
  if h : K.size t ≤ c then K.stepsLe_decidable c t u h
  else isFalse (fun hle => h (RS.StepsLe.head_le hle))

/-- The ascent relation for least-witness search. -/
private def kLbp (p : Nat → Prop) (m n : Nat) : Prop :=
  m = n + 1 ∧ ∀ k, k ≤ n → ¬ p k

private theorem kLbp_acc (p : Nat → Prop) (H : ∃ n, p n) : ∀ m, Acc (kLbp p) m := by
  obtain ⟨n, hn⟩ := H
  have key : ∀ j m, n ≤ m + j → Acc (kLbp p) m := by
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

/-- Choice-free witness search. -/
private def kFind (p : Nat → Prop) [DecidablePred p] (H : ∃ n, p n) : {n // p n} :=
  (WellFounded.fix (C := fun m => (∀ k, k < m → ¬ p k) → {n // p n})
    ⟨kLbp_acc p H⟩
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

private def kAnyCap (t u : A.Carrier)
    (H : ∃ c, RS.StepsLe A K.size c t u) :
    {c // RS.StepsLe A K.size c t u} :=
  kFind _ H

private theorem kle_foldr_max : ∀ (l : List Nat) {x : Nat}, x ∈ l → x ≤ l.foldr max 0 := by
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
def boundFn (hdec : ∀ t u : A.Carrier, Decidable (A.Steps t u)) (n m : Nat) : Nat :=
  ((K.enumLe n).flatMap fun t =>
    (K.enumLe m).flatMap fun u =>
    match hdec t u with
    | isTrue h => [(K.kAnyCap t u (RS.Steps.exists_le _ h)).1]
    | isFalse _ => []).foldr max 0

/-- Decidable ⟹ bound, at every equipped rung. -/
theorem bound_of_decidable (hdec : ∀ t u : A.Carrier, Decidable (A.Steps t u)) :
    ∃ f : Nat → Nat → Nat, ∀ t u : A.Carrier, A.Steps t u →
      RS.StepsLe A K.size (f (K.size t) (K.size u)) t u := by
  refine ⟨K.boundFn hdec, ?_⟩
  intro t u h
  refine RS.StepsLe.weaken ?_ (K.kAnyCap t u (RS.Steps.exists_le _ h)).2
  refine kle_foldr_max _ ?_
  refine List.mem_flatMap.mpr ⟨t, K.enumLe_complete (Nat.le_refl _), ?_⟩
  refine List.mem_flatMap.mpr ⟨u, K.enumLe_complete (Nat.le_refl _), ?_⟩
  cases hdec t u with
  | isFalse h' => exact absurd h h'
  | isTrue h' => exact List.mem_cons_self

/-- **The equivalence, at every equipped rung**: reachability is decidable iff a computable
function of the endpoint sizes bounds witnessing paths' intermediates. -/
theorem decidable_iff_bound :
    Nonempty (∀ t u : A.Carrier, Decidable (A.Steps t u))
    ↔ ∃ f : Nat → Nat → Nat, ∀ t u : A.Carrier, A.Steps t u →
        RS.StepsLe A K.size (f (K.size t) (K.size u)) t u := by
  constructor
  · rintro ⟨hdec⟩
    exact K.bound_of_decidable hdec
  · rintro ⟨f, hf⟩
    exact ⟨K.decidable_of_bound f hf⟩

end RS.SuccKit

-- ## The instances

instance : DecidableEq RS.SK.Carrier := inferInstanceAs (DecidableEq Term)
instance : DecidableEq RS.SC.Carrier := inferInstanceAs (DecidableEq SCTerm)

/-- The SK kit: verified successors (Reachability) and complete enumeration (SKComplete). -/
def skKit : RS.SuccKit RS.SK where
  size := leafCount
  succ := succs
  enumLe := skSmallTerms
  succ_sound := succs_sound
  succ_complete := succs_complete
  enumLe_complete := mem_skSmallTerms

/-- The `{S,C}` kit: the Stage 121/134 pieces, bundled. -/
def scKit : RS.SuccKit RS.SC where
  size := SCTerm.leafCount
  succ := scSucc
  enumLe := scEnumLe
  succ_sound := scSucc_sound
  succ_complete := scSucc_complete
  enumLe_complete := scEnumLe_complete

/-- **The SK equivalence**: at rung 0 exactly as at rung 3, reachability is decidable iff a
computable intermediate bound exists. SK is combinatorially complete, so (externally) its
reachability is undecidable — by this equivalence, SK has NO computable intermediate bound;
that reading is external, but the equivalence itself is machine-checked. -/
theorem sk_decidable_iff_bound :
    Nonempty (∀ t u : Term, Decidable (RS.SK.Steps t u))
    ↔ ∃ f : Nat → Nat → Nat, ∀ t u : Term, RS.SK.Steps t u →
        RS.StepsLe RS.SK leafCount (f (leafCount t) (leafCount u)) t u :=
  skKit.decidable_iff_bound

/-- The `{S,C}` equivalence, re-derived through the generic engine (sanity instance; the
Stage 139 original remains pinned). -/
example :
    Nonempty (∀ t u : SCTerm, Decidable (RS.SC.Steps t u))
    ↔ ∃ f : Nat → Nat → Nat, ∀ t u : SCTerm, RS.SC.Steps t u →
        RS.StepsLe RS.SC SCTerm.leafCount (f t.leafCount u.leafCount) t u :=
  scKit.decidable_iff_bound
