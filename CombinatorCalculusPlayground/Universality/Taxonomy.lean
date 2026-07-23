--! # The implication lattice
-- Which universality definitions imply which, and at what price. The
-- shape of the answers (proved below):
--
--   reachability (Simulation) ══unconditionally══▶ Conv-preservation (→)
--   reachability + host Church–Rosser + image-closure ══▶ full ConvSim
--   reachability + NF-correspondence ══▶ Norm-preservation (→)
--
-- The reverse implications are NOT theorems here: a Conv- or Norm-
-- preserving encoding need not track steps at all. Each definition's
-- status per system lives in CONJECTURES.md's definitions ledger.
import CombinatorCalculusPlayground.Universality.Defs
import CombinatorCalculusPlayground.Confluence

namespace RS

/-- Diamond for the reflexive-transitive closure. -/
def Confluent (B : RS) : Prop :=
  ∀ {a b c : B.Carrier}, B.Steps a b → B.Steps a c → ∃ d, B.Steps b d ∧ B.Steps c d

/-- Convertible things rejoin. -/
def ChurchRosser (B : RS) : Prop :=
  ∀ {a b : B.Carrier}, B.Conv a b → ∃ c, B.Steps a c ∧ B.Steps b c

theorem ChurchRosser_of_confluent {B : RS} (h : B.Confluent) : B.ChurchRosser := by
  intro a b hconv
  induction hconv with
  | refl => exact ⟨_, RS.Steps.refl _, RS.Steps.refl _⟩
  | fwd s _ ih =>
    -- a → a₁ ~ b, and a₁, b rejoin at d: then a →* d via the extra step.
    obtain ⟨d, h1, h2⟩ := ih
    exact ⟨d, RS.Steps.tail s h1, h2⟩
  | bwd s _ ih =>
    -- a₁ → a and a₁ ~ b rejoining at d: confluence on (a₁ → a) vs (a₁ →* d).
    obtain ⟨d, h1, h2⟩ := ih
    obtain ⟨e, he1, he2⟩ := h (RS.Steps.single s) h1
    exact ⟨e, he1, RS.Steps.trans h2 he2⟩

-- ## The Stage 1 bridge: SK is Church–Rosser in RS-language.
theorem SK_confluent : RS.Confluent RS.SK := by
  intro a b c h1 h2
  obtain ⟨w, hw1, hw2⟩ := confluence (RS.SK_steps_iff.mp h1) (RS.SK_steps_iff.mp h2)
  exact ⟨w, RS.SK_steps_iff.mpr hw1, RS.SK_steps_iff.mpr hw2⟩

theorem SK_churchRosser : RS.ChurchRosser RS.SK :=
  RS.ChurchRosser_of_confluent RS.SK_confluent

end RS

namespace Simulation

variable {A B : RS}

-- ## Lattice edge 1 (unconditional): simulations preserve convertibility.
theorem conv_preserve (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Conv a a') : B.Conv (S.enc a) (S.enc a') := by
  induction h with
  | refl => exact RS.Conv.refl _
  | fwd s _ ih => exact RS.Conv.trans (RS.Conv.of_steps (S.fwd s)) ih
  | bwd s _ ih => exact RS.Conv.trans (RS.Conv.of_steps (S.fwd s)).symm ih

/-- Everything the host reaches from an encoded state can flow back to an
encoded state. Rules out the host wandering into junk it can never
account for. -/
def ImageClosed (S : Simulation A B) : Prop :=
  ∀ (a : A.Carrier) (b : B.Carrier),
    B.Steps (S.enc a) b → ∃ a', B.Steps b (S.enc a')

-- ## Lattice edge 2: with a Church–Rosser host and image-closure,
-- convertibility also REFLECTS — the encoding adds no equations.
theorem conv_reflect (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) {a a' : A.Carrier}
    (h : B.Conv (S.enc a) (S.enc a')) : A.Conv a a' := by
  obtain ⟨w, hw1, hw2⟩ := hcr h
  obtain ⟨a₁, hback⟩ := hic a w hw1
  have h1 : A.Steps a a₁ := S.bwd (RS.Steps.trans hw1 hback)
  have h2 : A.Steps a' a₁ := S.bwd (RS.Steps.trans hw2 hback)
  exact RS.Conv.trans (RS.Conv.of_steps h1) (RS.Conv.of_steps h2).symm

-- Packaging both directions: a full convertibility-preserving encoding.
theorem preservesConv (S : Simulation A B) (hcr : B.ChurchRosser)
    (hic : S.ImageClosed) : PreservesConv A B S.enc :=
  fun _ _ => ⟨S.conv_preserve, S.conv_reflect hcr hic⟩

-- ## Lattice edge 3: with normal-form correspondence, normalization is
-- preserved (one direction — reflection needs more, see module header).
theorem normalizes_preserve (S : Simulation A B)
    (hnf : ∀ a, A.NormalForm a → B.NormalForm (S.enc a))
    {a : A.Carrier} (h : A.Normalizes a) : B.Normalizes (S.enc a) := by
  obtain ⟨b, hsteps, hnfb⟩ := h
  exact ⟨S.enc b, S.fwd_steps hsteps, hnf b hnfb⟩

end Simulation

-- ## The lattice at the Universal* level
theorem UniversalReach.toUniversalConv {R B : RS}
    (h : UniversalReach R B) (hcr : B.ChurchRosser)
    (hic : ∀ S : Simulation R B, S.ImageClosed) : UniversalConv R B := by
  obtain ⟨S⟩ := h
  exact ⟨S.enc, S.preservesConv hcr (hic S)⟩
