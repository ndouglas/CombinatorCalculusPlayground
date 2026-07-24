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
-- Stated at the witness level: ONE good simulation (into a Church–Rosser
-- host, image-closed) already yields Conv-universality — exactly the form
-- Stage 4 needs. (An earlier version quantified image-closure over ALL
-- simulations; that was strictly weaker for a user holding a single
-- witness, so it was removed rather than kept alongside.)
theorem Simulation.toUniversalConv {R B : RS} (S : Simulation R B)
    (hcr : B.ChurchRosser) (hic : S.ImageClosed) : UniversalConv R B :=
  ⟨S, S.preservesConv hcr hic⟩

-- ## Negative control: the definitions measure nothing on the diagonal
-- Companion to `bareEncNorm_trivial` (Defs.lean), found while assessing
-- spec Goal 2's calibration-sandwich criterion (a). `Simulation.id` makes
-- ALL THREE Universal* predicates trivially true whenever the reference and
-- the host are the SAME system — so a cell of the definitions ledger carries
-- information only when R ≠ B, and "B is universal for B" is never evidence
-- of anything. Every row of the actual table has R = RS.Tag ≠ B, so nothing
-- in the ledger is affected; this is stated so nobody discharges criterion
-- (a) by pointing at a diagonal instance, which would be the reflexive
-- analogue of the oracle-encoder cheat.

theorem universalReach_self (A : RS) : UniversalReach A A :=
  ⟨Simulation.id A⟩

theorem universalNorm_self (A : RS) : UniversalNorm A A :=
  ⟨Simulation.id A, fun _ => Iff.rfl⟩

theorem universalConv_self (A : RS) : UniversalConv A A :=
  ⟨Simulation.id A, fun _ _ => Iff.rfl⟩

-- ## One refutation mechanism, stated once
-- Both hosting refutations (iota, Stage 4; pure S, Slice 2) are instances
-- of a single fact: an injective PATH-PRESERVING encoding cannot carry a
-- two-point reduction cycle into an acyclic host. Strict growth (iota)
-- and τ-termination (pure S) were just two CAUSES of acyclicity. Stating
-- the mechanism generically makes every future refutation a one-liner:
-- prove your host Acyclic, exhibit any source cycle, done. (The original
-- refutations remain the citable artifacts; this consolidates, it does
-- not deprecate.)
--
-- SLICE 4 CORRECTION: this mechanism was previously stated for
-- `Simulation` and described as refuting "step-faithful" hosting. That
-- under-claimed it. The proof below uses only `PathEncoding`'s two
-- fields, so it is stated at that level now, with the `Simulation` form
-- kept as a corollary (same name, same statement — nothing downstream
-- changes). Neither `bwd` nor any step-count condition is involved.

/-- No state begins a loop: a step out never comes back. -/
def RS.Acyclic (B : RS) : Prop :=
  ∀ {b b' : B.Carrier}, B.step b b' → B.Steps b' b → False

-- Peel a genuine first step off a nonempty path (generic twin of the
-- Term-level `Steps.head_of_ne` in Calibration.lean).
theorem RS.Steps.head_of_ne {B : RS} {b b' : B.Carrier}
    (h : B.Steps b b') (hne : b ≠ b') :
    ∃ w, B.step b w ∧ B.Steps w b' := by
  cases h with
  | refl => exact absurd rfl hne
  | tail s rest => exact ⟨_, s, rest⟩

/-- The mechanism at its true strength: injectivity plus path-preservation
are all it needs. A source cycle between two DISTINCT points cannot be
carried into an acyclic host by any such encoding. -/
theorem PathEncoding.refute_of_acyclic {A B : RS} (hB : RS.Acyclic B)
    {a a' : A.Carrier} (h1 : A.Steps a a') (h2 : A.Steps a' a)
    (hne : a ≠ a') : ¬ Nonempty (PathEncoding A B) := by
  rintro ⟨P⟩
  have e1 : B.Steps (P.enc a) (P.enc a') := P.path h1
  have e2 : B.Steps (P.enc a') (P.enc a) := P.path h2
  have hne' : P.enc a ≠ P.enc a' := fun h => hne (P.inj h)
  obtain ⟨w, hstep, hrest⟩ := RS.Steps.head_of_ne e1 hne'
  exact hB hstep (RS.Steps.trans hrest e2)

/-- The `Simulation` form, unchanged in statement, now a corollary of the
weaker hypothesis. Every existing citation of this name keeps working. -/
theorem Simulation.refute_of_acyclic {A B : RS} (hB : RS.Acyclic B)
    {a a' : A.Carrier} (h1 : A.Steps a a') (h2 : A.Steps a' a)
    (hne : a ≠ a') : ¬ Nonempty (Simulation A B) :=
  fun ⟨Sim⟩ =>
    PathEncoding.refute_of_acyclic hB h1 h2 hne ⟨Sim.toPathEncoding⟩
