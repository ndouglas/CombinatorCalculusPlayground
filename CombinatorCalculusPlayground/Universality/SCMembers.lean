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

-- ## Stage 126: the last-variable invariant — the deadlock's path glue
-- The crossing lemma's sibling with the branch polarity inverted: on a count-preserving step,
-- a last-position variable either STAYS last, or the step was the three-member C-fire
-- configuration. Lifted to paths (threading the count squeeze), this says: along any
-- count-preserving reduction, the variable rides the tail until the one configuration that can
-- consume it — which Stage 127 shows cannot continue to a `var`-headed target.

/-- Variable `k` is the last member. -/
def SCV.lastVar (k : Nat) (t : SCV) : Prop :=
  ∃ M, t.members.reverse = .var k :: M

/-- One count-preserving step: the last variable stays last, or the source was the three-member
C-fire configuration. -/
theorem scv_lastVar_step {t u : SCV} {k : Nat} (h : SCVStep t u)
    (hcount : u.countVar k = t.countVar k) (h1 : t.countVar k = 1)
    (hlast : SCV.lastVar k t) :
    SCV.lastVar k u
    ∨ ∃ x y, t.members = [x, y, .var k] ∧ t.spineHead = .C
        ∧ u.spineHead = x.spineHead ∧ u = .app (.app x (.var k)) y := by
  obtain ⟨M, hM⟩ := hlast
  rcases scvStep_members h with ⟨f, g, x, T, hh, hm, hu⟩ | ⟨x, y, z, T, hh, hm, hu⟩
    | ⟨pre, m, m', post, hs, hm, hh', hm'⟩
  · -- S-fire
    have hum : u.members = (f.members ++ [x, .app g x]) ++ T := by
      rw [hu, SCV.appList_members]
      show ((SCV.app f x).members ++ [SCV.app g x]) ++ T = _
      show ((f.members ++ [x]) ++ [SCV.app g x]) ++ T = _
      simp
    rcases hT : T.reverse with _ | ⟨a, T₂⟩
    · -- T = []: the fire duplicates the variable — dead on counting
      exfalso
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
    · -- T nonempty: the variable stays last
      left
      have htr : t.members.reverse = T.reverse ++ [x, g, f] := by
        rw [hm]
        simp
      rw [hT] at htr
      rw [hM] at htr
      injection htr with ha _
      refine ⟨T₂ ++ ([SCV.app g x, x] ++ f.members.reverse), ?_⟩
      rw [hum]
      simp [hT]
      rw [← ha]
  · -- C-fire
    have hum : u.members = (x.members ++ [z, y]) ++ T := by
      rw [hu, SCV.appList_members]
      show ((SCV.app x z).members ++ [y]) ++ T = _
      show ((x.members ++ [z]) ++ [y]) ++ T = _
      simp
    rcases hT : T.reverse with _ | ⟨a, T₂⟩
    · -- T = []: THE CONFIGURATION
      right
      have hTnil : T = [] := by
        have := congrArg List.reverse hT
        simpa using this
      subst hTnil
      rw [hm] at hM
      simp at hM
      obtain ⟨hz, _⟩ := hM
      subst hz
      refine ⟨x, y, by rw [hm], hh, ?_, hu⟩
      rw [hu, SCV.appList_spineHead]
      rfl
    · -- T nonempty: the variable stays last
      left
      have htr : t.members.reverse = T.reverse ++ [z, y, x] := by
        rw [hm]
        simp
      rw [hT] at htr
      rw [hM] at htr
      injection htr with ha _
      refine ⟨T₂ ++ ([y, z] ++ x.members.reverse), ?_⟩
      rw [hum]
      simp [hT]
      rw [← ha]
  · -- member-internal
    rcases hP : post.reverse with _ | ⟨a, P₂⟩
    · exfalso
      have hPnil : post = [] := by
        have := congrArg List.reverse hP
        simpa using this
      subst hPnil
      rw [hm] at hM
      simp at hM
      obtain ⟨hmk, _⟩ := hM
      rw [hmk] at hs
      exact scv_no_step_from_var hs
    · left
      have htr : t.members.reverse = post.reverse ++ ([m] ++ pre.reverse) := by
        rw [hm]
        simp
      rw [hP] at htr
      rw [hM] at htr
      injection htr with ha _
      refine ⟨P₂ ++ ([m'] ++ pre.reverse), ?_⟩
      rw [hm']
      simp [hP]
      rw [← ha]

/-- The invariant along paths: the variable rides the tail until the configuration. -/
theorem scv_lastVar_steps {k : Nat} : ∀ {t u : SCV}, RS.SCV.Steps t u →
    u.countVar k = t.countVar k → t.countVar k = 1 → SCV.lastVar k t →
    SCV.lastVar k u
    ∨ ∃ w v x y, RS.SCV.Steps t w ∧ SCVStep w v ∧ RS.SCV.Steps v u
        ∧ w.members = [x, y, .var k] ∧ w.spineHead = .C
        ∧ v.spineHead = x.spineHead ∧ v = .app (.app x (.var k)) y := by
  intro t u h
  refine h.rec (motive := fun t u _ =>
      SCV.countVar k u = SCV.countVar k t → SCV.countVar k t = 1 → SCV.lastVar k t →
      SCV.lastVar k u
      ∨ ∃ w v x y, RS.SCV.Steps t w ∧ SCVStep w v ∧ RS.SCV.Steps v u
          ∧ w.members = [x, y, .var k] ∧ w.spineHead = .C
          ∧ v.spineHead = x.spineHead ∧ v = .app (.app x (.var k)) y) ?_ ?_
  · intro a _ _ hl
    exact Or.inl hl
  · intro a b c s rest ih hcount h1 hl
    have hbc : SCV.countVar k b = SCV.countVar k a :=
      scvSteps_countVar_squeeze s rest hcount
    rcases scv_lastVar_step s hbc h1 hl with hlb | ⟨x, y, hm, hh, hv, hsh⟩
    · rcases ih (by omega) (by omega) hlb with hlu
        | ⟨w, v, x, y, h1', h2', h3', h4', h5', h6', h7'⟩
      · exact Or.inl hlu
      · exact Or.inr ⟨w, v, x, y, RS.Steps.tail s h1', h2', h3', h4', h5', h6', h7'⟩
    · exact Or.inr ⟨a, b, x, y, @RS.Steps.refl RS.SCV a, s, rest, hm, hh, hv, hsh⟩

-- ## Stage 127: the funnel — every pairing path threads the needle
-- Assembly of the deadlock so far. Three new facts: a variable at the spine head freezes it
-- there forever (heads change only at root fires, which need `S`/`C`); the pairing target
-- `s a b` has EXACTLY ONE step-predecessor, the root C-fire from `C s b a` (S-fires and
-- member-internal steps would put an application among its all-variable members); and
-- therefore any path `P a b s ⟶* s a b` decomposes through the var-2 crossing configuration
-- (Stage 126) and then the canonical predecessor — with the configuration's first member
-- machine-headed and var-2-free, and the two payload variables split across its two
-- non-variable members. What Stage 128 must close: that split has no legal continuation.

/-- A spine head is never an application. -/
theorem SCV.spineHead_not_app : ∀ (t f a : SCV), t.spineHead ≠ .app f a := by
  intro t
  induction t with
  | S => intro f a h; exact SCV.noConfusion h
  | C => intro f a h; exact SCV.noConfusion h
  | var i => intro f a h; exact SCV.noConfusion h
  | app g x ihg ihx =>
      intro f a h
      exact ihg f a h

/-- A variable at the head freezes it: no root fire applies, so one step preserves the head. -/
theorem scv_varHead_step {t u : SCV} {i : Nat} (hh : t.spineHead = .var i)
    (h : SCVStep t u) : u.spineHead = .var i := by
  rcases scvStep_members h with ⟨f, g, x, T, hS, _, _⟩ | ⟨x, y, z, T, hC, _, _⟩
    | ⟨_, _, _, _, _, _, hh', _⟩
  · rw [hS] at hh
    exact SCV.noConfusion hh
  · rw [hC] at hh
    exact SCV.noConfusion hh
  · rw [hh']
    exact hh

/-- The freeze, along paths: once a variable heads the spine, it heads every reduct. -/
theorem scv_varHead_frozen {i : Nat} : ∀ {t u : SCV}, RS.SCV.Steps t u →
    t.spineHead = .var i → u.spineHead = .var i := by
  intro t u h
  refine h.rec (motive := fun a b _ =>
      SCV.spineHead a = .var i → SCV.spineHead b = .var i) ?_ ?_
  · intro a ha
    exact ha
  · intro a b c s _ ih ha
    exact ih (scv_varHead_step ha s)

/-- The pairing target `s a b` on opaque arguments. -/
def SCV.pairTarget : SCV := .app (.app (.var 2) (.var 0)) (.var 1)

/-- Its unique step-predecessor: `C s b a`. -/
def SCV.pairPre : SCV := .app (.app (.app .C (.var 2)) (.var 1)) (.var 0)

theorem scv_pairPre_step : SCVStep SCV.pairPre SCV.pairTarget :=
  SCVStep.C_red (.var 2) (.var 1) (.var 0)

/-- **The predecessor lemma**: the ONLY step into `s a b` is the root C-fire from `C s b a`.
An S-fire or a member-internal step would place an application among the target's
all-variable members. -/
theorem scv_pair_pred {t : SCV} (h : SCVStep t SCV.pairTarget) : t = SCV.pairPre := by
  rcases scvStep_members h with ⟨f, g, x, T, hh, hm, hu⟩ | ⟨x, y, z, T, hh, hm, hu⟩
    | ⟨pre, m, m', post, hs, hm, hh', hm'⟩
  · -- S-fire: the member (g x) is an application
    exfalso
    have h0 := congrArg SCV.members hu
    rw [SCV.appList_members] at h0
    have hum : ([.var 0, .var 1] : List SCV)
        = ((f.members ++ [x]) ++ [.app g x]) ++ T := h0
    rcases hfm : f.members with _ | ⟨a, l⟩
    · rw [hfm] at hum
      simp at hum
    · rw [hfm] at hum
      simp at hum
      obtain ⟨_, hrest⟩ := hum
      rcases l with _ | ⟨b, l₂⟩
      · simp at hrest
      · simp at hrest
  · -- C-fire: the live case
    have h0 := congrArg SCV.members hu
    rw [SCV.appList_members] at h0
    have hum : ([.var 0, .var 1] : List SCV) = ((x.members ++ [z]) ++ [y]) ++ T := h0
    have h1 := congrArg SCV.spineHead hu
    rw [SCV.appList_spineHead] at h1
    have hhd : (SCV.var 2) = x.spineHead := h1
    rcases hxm : x.members with _ | ⟨a, l⟩
    · rw [hxm] at hum
      simp at hum
      obtain ⟨hz, hy, hT⟩ := hum
      -- x has no members, so it IS its spine head: the variable 2
      have hx2 : x = SCV.var 2 := by
        cases x with
        | S => exact absurd hhd.symm (by intro hc; exact SCV.noConfusion hc)
        | C => exact absurd hhd.symm (by intro hc; exact SCV.noConfusion hc)
        | var n =>
            have : (SCV.var 2) = SCV.var n := hhd
            rw [this]
        | app f a => simp [SCV.members] at hxm
      have hrec := SCV.recon t
      rw [hm, hh, hx2, ← hz, ← hy, hT] at hrec
      exact hrec.symm
    · rw [hxm] at hum
      have hlen := congrArg List.length hum
      simp at hlen
      omega
  · -- member-internal: the stepped member is an application among all-variable members
    exfalso
    obtain ⟨p, q, hpq⟩ := scvStep_result_isApp hs
    have hum : ([.var 0, .var 1] : List SCV) = pre ++ m' :: post := hm'
    subst hpq
    rcases pre with _ | ⟨a, pre₂⟩
    · injection hum with h1 _
      exact SCV.noConfusion h1
    · injection hum with _ h2
      rcases pre₂ with _ | ⟨b, pre₃⟩
      · injection h2 with h3 _
        exact SCV.noConfusion h3
      · injection h2 with _ h4
        simp at h4

/-- **The funnel.** Every pairing path `P a b s ⟶* s a b` (machine `P` free of the three
variables) threads the needle: it reaches the var-2 crossing configuration `w = C x y s`
(Stage 126), fires it to `(x s) y`, continues to the canonical predecessor `C s b a`, and
fires that into the target. Moreover the configuration is counted out: `x` is machine-headed,
neither `x` nor `y` contains `s`, and the two payload variables are split across `x` and `y`
with one occurrence total each. -/
theorem scv_pair_funnel {P : SCV}
    (hP0 : P.countVar 0 = 0) (hP1 : P.countVar 1 = 0) (hP2 : P.countVar 2 = 0)
    (h : RS.SCV.Steps (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) SCV.pairTarget) :
    ∃ w x y,
      RS.SCV.Steps (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) w
      ∧ w.members = [x, y, .var 2] ∧ w.spineHead = .C
      ∧ SCVStep w (.app (.app x (.var 2)) y)
      ∧ RS.SCV.Steps (.app (.app x (.var 2)) y) SCV.pairPre
      ∧ (x.spineHead = .S ∨ x.spineHead = .C)
      ∧ x.countVar 2 = 0 ∧ y.countVar 2 = 0
      ∧ x.countVar 0 + y.countVar 0 = 1
      ∧ x.countVar 1 + y.countVar 1 = 1 := by
  have hc0 : SCV.countVar 0 (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) = 1 := by
    show P.countVar 0 + 1 + 0 + 0 = 1
    omega
  have hc1 : SCV.countVar 1 (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) = 1 := by
    show P.countVar 1 + 0 + 1 + 0 = 1
    omega
  have hc2 : SCV.countVar 2 (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) = 1 := by
    show P.countVar 2 + 0 + 0 + 1 = 1
    omega
  rcases RS.steps_last h with he | ⟨t', ht', hstep⟩
  · exfalso
    injection he with h1 h2
    injection h2 with h3
    omega
  · have hpre : t' = SCV.pairPre := scv_pair_pred hstep
    subst hpre
    have hl0 : SCV.lastVar 2 (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) := by
      refine ⟨SCV.var 1 :: SCV.var 0 :: P.members.reverse, ?_⟩
      show (((P.members ++ [SCV.var 0]) ++ [SCV.var 1]) ++ [SCV.var 2]).reverse = _
      simp
    have hcpre2 : SCV.countVar 2 SCV.pairPre = 1 := rfl
    rcases scv_lastVar_steps (k := 2) ht' (by rw [hcpre2, hc2]) hc2 hl0 with hlpre
      | ⟨w, v, x, y, hw, hstep2, hv, hm, hh, _, hshape⟩
    · exfalso
      obtain ⟨M, hM⟩ := hlpre
      have hM' : ([.var 0, .var 1, .var 2] : List SCV) = .var 2 :: M := hM
      injection hM' with h1 _
      injection h1 with h2
      omega
    · subst hshape
      have hxh : x.spineHead = SCV.S ∨ x.spineHead = SCV.C := by
        rcases hx : x.spineHead with _ | _ | i | ⟨f, a⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          have hvh : (SCV.app (.app x (.var 2)) y).spineHead = .var i := hx
          have hfr := scv_varHead_frozen hv hvh
          have hC : SCV.C = SCV.var i := hfr
          exact SCV.noConfusion hC
        · exact absurd hx (SCV.spineHead_not_app x f a)
      have key : ∀ kk : Nat,
          SCV.countVar kk (.app (.app (.app P (.var 0)) (.var 1)) (.var 2)) = 1 →
          SCV.countVar kk SCV.pairPre = 1 →
          w.countVar kk = 1 := by
        intro kk hsrc hpre
        have m1 := scvSteps_countVar_mono (k := kk) hw
        have m2 := scvStep_countVar_mono (k := kk) hstep2
        have m3 := scvSteps_countVar_mono (k := kk) hv
        omega
      have split : ∀ kk : Nat, w.countVar kk = 1 →
          x.countVar kk + (y.countVar kk + (SCV.countVar kk (.var 2) + 0)) = 1 := by
        intro kk hcw
        have hb := SCV.countVar_members kk w
        rw [hm, hh] at hb
        have hbb : w.countVar kk
            = 0 + (x.countVar kk + (y.countVar kk + (SCV.countVar kk (.var 2) + 0))) := hb
        omega
      have k2 : x.countVar 2 + (y.countVar 2 + (1 + 0)) = 1 :=
        split 2 (key 2 hc2 rfl)
      have k0 : x.countVar 0 + (y.countVar 0 + (0 + 0)) = 1 :=
        split 0 (key 0 hc0 rfl)
      have k1 : x.countVar 1 + (y.countVar 1 + (0 + 0)) = 1 :=
        split 1 (key 1 hc1 rfl)
      exact ⟨w, x, y, hw, hm, hh, hstep2, hv, hxh,
        by omega, by omega, by omega, by omega⟩
