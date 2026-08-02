--! # The member-position calculus (Stage 123)
-- The working theory of `{S,C}` interrogation dynamics — spine members, prefix fires,
-- passenger crossings — has carried Stages 108–122 as prose. This module makes it Lean: a
-- term is its spine head applied to its member list, and EVERY step is one of exactly three
-- member-actions — an S-fire on the first three members, a C-fire on the first three members,
-- or one member stepping in place. The characterization is the load-bearing theorem: the
-- crossing lemma, the bare-vars invariant, and the pairing deadlock (Stage 122's paper proof)
-- all sit on it.
import CombinatorCalculusPlayground.Universality.RungTermination

namespace SCV

/-- The spine head: descend left to the leaf. -/
def spineHead : SCV → SCV
  | .app f _ => spineHead f
  | t => t

/-- The member list: the spine's arguments, left to right. -/
def members : SCV → List SCV
  | .app f x => members f ++ [x]
  | _ => []

/-- Apply a head to a member list. -/
def appList : SCV → List SCV → SCV
  | f, [] => f
  | f, m :: ms => appList (.app f m) ms

theorem appList_append_one : ∀ (ms : List SCV) (f x : SCV),
    appList f (ms ++ [x]) = .app (appList f ms) x := by
  intro ms
  induction ms with
  | nil => intro f x; rfl
  | cons m ms ih =>
      intro f x
      show appList (.app f m) (ms ++ [x]) = _
      rw [ih]
      rfl

/-- Reconstruction: every term is its head applied to its members. -/
theorem recon : ∀ t : SCV, appList (spineHead t) (members t) = t := by
  intro t
  induction t with
  | S => rfl
  | C => rfl
  | var i => rfl
  | app f x ihf ihx =>
      show appList (spineHead f) (members f ++ [x]) = _
      rw [appList_append_one, ihf]

end SCV

/-- **The member-action characterization**: every `{S,C}` step (with variables) is an S-fire on
the first three members, a C-fire on the first three members, or one member stepping in place —
nothing else can happen. -/
theorem scvStep_members {t u : SCV} (h : SCVStep t u) :
    (∃ f g x T, t.spineHead = .S ∧ t.members = f :: g :: x :: T
      ∧ u = SCV.appList (.app (.app f x) (.app g x)) T)
    ∨ (∃ x y z T, t.spineHead = .C ∧ t.members = x :: y :: z :: T
      ∧ u = SCV.appList (.app (.app x z) y) T)
    ∨ (∃ pre m m' post, SCVStep m m' ∧ t.members = pre ++ m :: post
      ∧ u.spineHead = t.spineHead ∧ u.members = pre ++ m' :: post) := by
  induction h with
  | S_red f g x =>
      exact Or.inl ⟨f, g, x, [], rfl, rfl, rfl⟩
  | C_red x y z =>
      exact Or.inr (Or.inl ⟨x, y, z, [], rfl, rfl, rfl⟩)
  | @appL a a' b h ih =>
      rcases ih with ⟨f, g, x, T, hh, hm, hu⟩ | ⟨x, y, z, T, hh, hm, hu⟩
        | ⟨pre, m, m', post, hs, hm, hh', hm'⟩
      · refine Or.inl ⟨f, g, x, T ++ [b], hh, ?_, ?_⟩
        · show a.members ++ [b] = _
          rw [hm]
          rfl
        · show SCV.app a' b = _
          rw [hu, ← SCV.appList_append_one]
      · refine Or.inr (Or.inl ⟨x, y, z, T ++ [b], hh, ?_, ?_⟩)
        · show a.members ++ [b] = _
          rw [hm]
          rfl
        · show SCV.app a' b = _
          rw [hu, ← SCV.appList_append_one]
      · refine Or.inr (Or.inr ⟨pre, m, m', post ++ [b], hs, ?_, hh', ?_⟩)
        · show a.members ++ [b] = _
          rw [hm]
          simp
        · show a'.members ++ [b] = _
          rw [hm']
          simp
  | @appR a b b' h =>
      exact Or.inr (Or.inr ⟨a.members, b, b', [], h, rfl, rfl, rfl⟩)

-- ## Stage 124: variable counts are monotone — the search prunes become theorems
-- Every search since Stage 103 pruned on "atom counts never decrease"; the law is now
-- machine-checked. C-fires and congruence preserve each variable's count exactly; an S-fire
-- adds exactly one extra copy of its third argument's count. Corollary (the squeeze): on any
-- path whose endpoints agree on a count, EVERY step preserves it — the count-preservation
-- hypothesis the crossing lemma (next stage) needs, derived rather than assumed.

/-- Occurrences of variable `k`. -/
def SCV.countVar (k : Nat) : SCV → Nat
  | .var i => if i = k then 1 else 0
  | .S => 0
  | .C => 0
  | .app f x => countVar k f + countVar k x

/-- One step: the count is preserved exactly, or an S-fire adds its third argument's count. -/
theorem scvStep_countVar {k : Nat} {t u : SCV} (h : SCVStep t u) :
    u.countVar k = t.countVar k
    ∨ ∃ x : SCV, t.countVar k + x.countVar k = u.countVar k := by
  induction h with
  | S_red f g x =>
      right
      refine ⟨x, ?_⟩
      show (((0:Nat) + f.countVar k) + g.countVar k + x.countVar k) + x.countVar k
        = (f.countVar k + x.countVar k) + (g.countVar k + x.countVar k)
      omega
  | C_red x y z =>
      left
      show (x.countVar k + z.countVar k) + y.countVar k
        = ((0 + x.countVar k) + y.countVar k) + z.countVar k
      omega
  | appL h ih =>
      rcases ih with h1 | ⟨x, h1⟩
      · left
        show _ + _ = _ + _
        omega
      · right
        refine ⟨x, ?_⟩
        show (_ + _) + _ = _ + _
        omega
  | appR h ih =>
      rcases ih with h1 | ⟨x, h1⟩
      · left
        show _ + _ = _ + _
        omega
      · right
        refine ⟨x, ?_⟩
        show (_ + _) + _ = _ + _
        omega

/-- Counts never decrease. -/
theorem scvStep_countVar_mono {k : Nat} {t u : SCV} (h : SCVStep t u) :
    t.countVar k ≤ u.countVar k := by
  rcases scvStep_countVar (k := k) h with h1 | ⟨x, h1⟩
  · omega
  · omega

/-- Counts never decrease along paths. -/
theorem scvSteps_countVar_mono {k : Nat} {t u : SCV} (h : RS.SCV.Steps t u) :
    t.countVar k ≤ u.countVar k := by
  refine h.rec (motive := fun a b _ =>
      SCV.countVar k a ≤ SCV.countVar k b) ?_ ?_
  · intro a
    exact Nat.le_refl _
  · intro a b c s rest ih
    exact Nat.le_trans (scvStep_countVar_mono s) ih

/-- **The squeeze**: if a path's endpoints agree on a count, every step along it preserves
that count — stated for the first step; iterate as needed. -/
theorem scvSteps_countVar_squeeze {k : Nat} {t v u : SCV}
    (h1 : SCVStep t v) (h2 : RS.SCV.Steps v u)
    (heq : u.countVar k = t.countVar k) :
    v.countVar k = t.countVar k := by
  have m1 := scvStep_countVar_mono (k := k) h1
  have m2 := scvSteps_countVar_mono (k := k) h2
  omega

-- ## Stage 125: the crossing configuration — formalized
-- Stage 122's deadlock engine: on a count-preserving step (count exactly one), moving ANOTHER
-- member behind a last-position variable forces the three-member C-fire configuration, and the
-- new head is the old first member's head. Every other branch dies on variable counting, on
-- vars-don't-step, or on results-are-apps.

/-- The head of an applied list is the head of its function part. -/
theorem SCV.appList_spineHead : ∀ (ms : List SCV) (f : SCV),
    (SCV.appList f ms).spineHead = f.spineHead := by
  intro ms
  induction ms with
  | nil => intro f; rfl
  | cons m ms ih =>
      intro f
      show (SCV.appList (.app f m) ms).spineHead = _
      rw [ih]
      rfl

/-- Members of an applied list. -/
theorem SCV.appList_members : ∀ (ms : List SCV) (f : SCV),
    (SCV.appList f ms).members = f.members ++ ms := by
  intro ms
  induction ms with
  | nil => intro f; simp [SCV.appList]
  | cons m ms ih =>
      intro f
      show (SCV.appList (.app f m) ms).members = _
      rw [ih]
      show (f.members ++ [m]) ++ ms = _
      simp

/-- Count-sums over member lists: append law. -/
theorem SCV.msum_append (k : Nat) : ∀ (A B : List SCV),
    ((A ++ B).map (SCV.countVar k)).sum
      = (A.map (SCV.countVar k)).sum + (B.map (SCV.countVar k)).sum := by
  intro A B
  induction A with
  | nil => simp
  | cons a A ih =>
      show SCV.countVar k a + ((A ++ B).map (SCV.countVar k)).sum = _
      rw [ih]
      show _ = (SCV.countVar k a + (A.map (SCV.countVar k)).sum) + _
      omega

/-- Count-sums are reversal-invariant. -/
theorem SCV.msum_reverse (k : Nat) : ∀ (l : List SCV),
    ((l.reverse).map (SCV.countVar k)).sum = (l.map (SCV.countVar k)).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.reverse_cons, SCV.msum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- The count bridge: a term's count is its head's count plus its members' counts. -/
theorem SCV.countVar_members (k : Nat) : ∀ t : SCV,
    t.countVar k = t.spineHead.countVar k + (t.members.map (SCV.countVar k)).sum := by
  intro t
  induction t with
  | S => rfl
  | C => rfl
  | var i => rfl
  | app f x ihf ihx =>
      show f.countVar k + x.countVar k = _
      have hm : (SCV.app f x).members = f.members ++ [x] := rfl
      rw [hm, SCV.msum_append]
      show _ = f.spineHead.countVar k + ((f.members.map _).sum + (x.countVar k + 0))
      omega

theorem SCV.countVar_var (k : Nat) : SCV.countVar k (.var k) = 1 := by
  show (if k = k then 1 else 0) = 1
  rw [if_pos rfl]

/-- Two bare occurrences kill a count-one term. -/
theorem SCV.two_vars_dead {k : Nat} {t : SCV} {rest A B : List SCV}
    (hrev : t.members.reverse = .var k :: rest) (hAB : rest = A ++ .var k :: B)
    (h1 : t.countVar k = 1) : False := by
  have hm : t.members = (SCV.var k :: rest).reverse := by
    rw [← hrev, List.reverse_reverse]
  have hb := SCV.countVar_members k t
  rw [hm, SCV.msum_reverse] at hb
  subst hAB
  have h2 : ((SCV.var k :: (A ++ SCV.var k :: B)).map (SCV.countVar k)).sum
      = 1 + ((A.map (SCV.countVar k)).sum
        + (1 + (B.map (SCV.countVar k)).sum)) := by
    show SCV.countVar k (.var k) + ((A ++ SCV.var k :: B).map (SCV.countVar k)).sum = _
    rw [SCV.countVar_var, SCV.msum_append]
    show _ + (_ + (SCV.countVar k (.var k) + (B.map (SCV.countVar k)).sum)) = _
    rw [SCV.countVar_var]
  rw [h2] at hb
  omega

/-- No step leaves a variable. -/
theorem scv_no_step_from_var {k : Nat} {u : SCV} (h : SCVStep (.var k) u) : False := by
  cases h

/-- **The crossing configuration.** On a count-preserving step with count exactly one, if
variable `k` was the LAST member and is now second-to-last, the source had exactly three
members with head `C`, and the result's head is the old first member's head. -/
theorem scv_cross_last {t u : SCV} {k : Nat} (h : SCVStep t u)
    (hcount : u.countVar k = t.countVar k) (h1 : t.countVar k = 1)
    (hlast : ∃ M, t.members.reverse = .var k :: M)
    (hmoved : ∃ w N, u.members.reverse = w :: .var k :: N) :
    ∃ x y, t.members = [x, y, .var k] ∧ t.spineHead = .C
      ∧ u.spineHead = x.spineHead := by
  obtain ⟨M, hM⟩ := hlast
  obtain ⟨w, N, hN⟩ := hmoved
  rcases scvStep_members h with ⟨f, g, x, T, hh, hm, hu⟩ | ⟨x, y, z, T, hh, hm, hu⟩
    | ⟨pre, m, m', post, hs, hm, hh', hm'⟩
  · -- S-fire: dead
    exfalso
    have hum : u.members = (f.members ++ [x, .app g x]) ++ T := by
      rw [hu, SCV.appList_members]
      show ((SCV.app f x).members ++ [SCV.app g x]) ++ T = _
      show ((f.members ++ [x]) ++ [SCV.app g x]) ++ T = _
      simp
    have htr : t.members.reverse = T.reverse ++ [x, g, f] := by
      rw [hm]
      simp
    have hur : u.members.reverse
        = T.reverse ++ ([SCV.app g x, x] ++ f.members.reverse) := by
      rw [hum]
      simp
    rcases hT : T.reverse with _ | ⟨a, T₂⟩
    · -- T = []: the fired third argument IS the variable — counts break
      have hTnil : T = [] := by
        have := congrArg List.reverse hT
        simpa using this
      subst hTnil
      rw [hm] at hM
      simp at hM
      obtain ⟨hx, _⟩ := hM
      have hb := SCV.countVar_members k t
      rw [hm, hh] at hb
      have hcu : u.countVar k
          = (SCV.app (.app f x) (.app g x)).countVar k := by
        rw [hu]
        rfl
      subst hx
      have hcu2 : (SCV.app (.app f (.var k)) (.app g (.var k))).countVar k
          = f.countVar k + g.countVar k + 2 := by
        show (f.countVar k + (if k = k then 1 else 0))
          + (g.countVar k + (if k = k then 1 else 0)) = _
        rw [if_pos rfl]
        omega
      have hmt : (([f, g, SCV.var k]).map (SCV.countVar k)).sum
          = f.countVar k + g.countVar k + 1 := by
        show f.countVar k + (g.countVar k + (SCV.countVar k (.var k) + 0)) = _
        rw [SCV.countVar_var]
        omega
      rw [hmt] at hb
      rw [hcu, hcu2] at hcount
      have hS0 : SCV.countVar k SCV.S = 0 := rfl
      rw [hS0] at hb
      omega
    · -- T ends in the variable: a second occurrence appears — dead on counting
      rw [hT] at htr hur
      rw [hM] at htr
      injection htr with ha hrest
      rw [hN] at hur
      injection hur with hw hrest2
      rcases hT2 : T₂ with _ | ⟨b, T₃⟩
      · subst hT2
        simp at hrest2
      · subst hT2
        simp at hrest2
        obtain ⟨hbk, _⟩ := hrest2
        exact SCV.two_vars_dead (A := []) (B := T₃ ++ [x, g, f]) hM
          (by rw [hrest, hbk]; simp) h1
  · -- C-fire
    have hum : u.members = (x.members ++ [z, y]) ++ T := by
      rw [hu, SCV.appList_members]
      show ((SCV.app x z).members ++ [y]) ++ T = _
      show ((x.members ++ [z]) ++ [y]) ++ T = _
      simp
    have htr : t.members.reverse = T.reverse ++ [z, y, x] := by
      rw [hm]
      simp
    have hur : u.members.reverse
        = T.reverse ++ ([y, z] ++ x.members.reverse) := by
      rw [hum]
      simp
    rcases hT : T.reverse with _ | ⟨a, T₂⟩
    · -- LIVE: T = [], z = var k
      have hTnil : T = [] := by
        have := congrArg List.reverse hT
        simpa using this
      subst hTnil
      rw [hm] at hM
      simp at hM
      obtain ⟨hz, _⟩ := hM
      subst hz
      refine ⟨x, y, by rw [hm], hh, ?_⟩
      rw [hu, SCV.appList_spineHead]
      rfl
    · -- T ends in the variable: dead on counting or the second slot mismatches
      exfalso
      rw [hT] at htr hur
      rw [hM] at htr
      injection htr with ha hrest
      rw [hN] at hur
      injection hur with hw hrest2
      rcases hT2 : T₂ with _ | ⟨b, T₃⟩
      · subst hT2
        simp at hrest2 hrest
        obtain ⟨hy, _⟩ := hrest2
        -- y = var k, and rest = [z, y, x] contains it
        exact SCV.two_vars_dead (A := [z]) (B := [x]) hM
          (by rw [hrest, ← hy]; simp) h1
      · subst hT2
        simp at hrest2
        obtain ⟨hbk, _⟩ := hrest2
        exact SCV.two_vars_dead (A := []) (B := T₃ ++ [z, y, x]) hM
          (by rw [hrest, hbk]; simp) h1
  · -- member-internal: dead
    exfalso
    have htr : t.members.reverse = post.reverse ++ ([m] ++ pre.reverse) := by
      rw [hm]
      simp
    have hur : u.members.reverse = post.reverse ++ ([m'] ++ pre.reverse) := by
      rw [hm']
      simp
    rcases hP : post.reverse with _ | ⟨a, P₂⟩
    · have hPnil : post = [] := by
        have := congrArg List.reverse hP
        simpa using this
      subst hPnil
      rw [hm] at hM
      simp at hM
      obtain ⟨hmk, _⟩ := hM
      rw [hmk] at hs
      exact scv_no_step_from_var hs
    · rw [hP] at htr hur
      rw [hM] at htr
      injection htr with ha hrest
      rw [hN] at hur
      injection hur with hw hrest2
      rcases hP2 : P₂ with _ | ⟨b, P₃⟩
      · subst hP2
        simp at hrest2
        obtain ⟨hm'k, _⟩ := hrest2
        obtain ⟨p, q, hpq⟩ := scvStep_result_isApp hs
        rw [hpq] at hm'k
        exact SCV.noConfusion hm'k
      · subst hP2
        simp at hrest2
        obtain ⟨hbk, _⟩ := hrest2
        exact SCV.two_vars_dead (A := []) (B := (P₃ ++ [m]) ++ pre.reverse) hM
          (by rw [hrest, hbk]; simp) h1
