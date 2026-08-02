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
