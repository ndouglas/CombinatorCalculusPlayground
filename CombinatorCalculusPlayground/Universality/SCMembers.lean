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
