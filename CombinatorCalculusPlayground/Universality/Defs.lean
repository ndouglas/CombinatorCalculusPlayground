--! # What "computationally universal" could mean
-- The prize question's hidden difficulty is DEFINITIONAL: universal under
-- which observations, and which encodings? This module pins the candidate
-- definitions as properties of (system, encoder, decoder) triples over
-- abstract rewriting systems.
--
-- ## The encoding class: what IS and IS NOT pinned here (required honesty)
-- PINNED, formally: the encoder is one fixed total function, uniform in
-- its input (no per-instance cleverness); the decoder inverts it on the
-- image (`dec_enc`), so encodings are faithful and answers can be read
-- back. Simulations must track steps structurally (`fwd`/`bwd`), which
-- blocks the grossest form of the 2007 Wolfram-prize objection (an
-- "encoding" that performs the computation itself and ships the answer).
-- ALL THREE Universal* definitions below range over this pinned
-- Simulation class, never over bare functions; the bare-function variant
-- survives only as a negative control (`bareEncNorm_trivial`) showing
-- what unpinned definitions collapse to.
-- NOT PINNED, and not formalizable in this zero-dependency setting: that
-- `enc`/`dec` are COMPUTABLE. Every Lean `def` is computable by
-- construction, but that is a metatheoretic fact, not a hypothesis these
-- definitions can state or use. A full internal answer needs a
-- computability theory (registered as an explicit limitation in
-- CONJECTURES.md, not papered over).
import CombinatorCalculusPlayground.RS

/-- A simulation of `A` inside `B`: encode, run, decode.
`fwd` says B can follow every A-step (in possibly many steps);
`bwd` says B's behavior between encoded states is not richer than A's —
reachability between image points reflects back. -/
structure Simulation (A B : RS) where
  enc : A.Carrier → B.Carrier
  dec : B.Carrier → Option A.Carrier
  dec_enc : ∀ a, dec (enc a) = some a
  fwd : ∀ {a a' : A.Carrier}, A.step a a' → B.Steps (enc a) (enc a')
  bwd : ∀ {a a' : A.Carrier}, B.Steps (enc a) (enc a') → A.Steps a a'

namespace Simulation

variable {A B : RS}

-- The decoder makes the encoder injective — distinct programs stay
-- distinct inside the host.
theorem enc_injective (S : Simulation A B) {a a' : A.Carrier}
    (h : S.enc a = S.enc a') : a = a' := by
  have h1 := S.dec_enc a
  have h2 := S.dec_enc a'
  rw [h] at h1
  rw [h1] at h2
  injection h2

-- fwd lifts from single steps to paths.
theorem fwd_steps (S : Simulation A B) {a a' : A.Carrier}
    (h : A.Steps a a') : B.Steps (S.enc a) (S.enc a') := by
  induction h with
  | refl => exact RS.Steps.refl _
  | tail s _ ih => exact RS.Steps.trans (S.fwd s) ih

end Simulation

-- ## The weak hypothesis: what the refutations actually need
-- Slice 4 audit finding. `Simulation.refute_of_acyclic` (Taxonomy.lean)
-- consumes exactly two consequences of the five-field `Simulation`:
-- injectivity of `enc` (via `dec_enc`) and path-preservation (via `fwd`,
-- which was ALREADY many-step — see `fwd`'s type above). It never touches
-- `bwd`, and it never uses step-count faithfulness. Naming that weaker
-- hypothesis widens every refutation built on it: what gets ruled out is
-- not merely step-faithful hosting, but ANY injective path-preserving
-- encoding. `PathEncoding` is proved STRICTLY weaker than `Simulation`
-- in Calibration.lean (`pathEncoding_strictly_weaker`), so the widening
-- is real rather than a renaming.

/-- An injective map carrying source paths to host paths — and nothing
else. No decoder, no backward reflection (`bwd`), no step-count
faithfulness: `path` grants the host arbitrarily many steps per source
path, exactly as `Simulation.fwd` already did per source step. -/
structure PathEncoding (A B : RS) where
  enc : A.Carrier → B.Carrier
  inj : ∀ {a a' : A.Carrier}, enc a = enc a' → a = a'
  path : ∀ {a a' : A.Carrier}, A.Steps a a' → B.Steps (enc a) (enc a')

/-- Every simulation is in particular a path encoding. This projection is
what lets the generic refutation, stated for the weaker class, still apply
to `Simulation` — so no existing result loses strength. -/
def Simulation.toPathEncoding {A B : RS} (S : Simulation A B) :
    PathEncoding A B where
  enc := S.enc
  inj := S.enc_injective
  path := S.fwd_steps

-- ## Adequacy: `bwd` from a stuttering abstraction function
-- `bwd` is the field that blocks spec Goal 2 criterion (a), and Stage 7
-- proved it load-bearing rather than incidental (a positive certification
-- must be made in the demanding class, so it cannot be dropped). The classic
-- way to discharge it is not to reason about paths between image points
-- directly, but to give an ABSTRACTION FUNCTION defined on ALL host states
-- such that every host step either stutters — leaving the abstraction
-- unchanged — or advances it by exactly one source step. Then any host path
-- projects onto a source path, and `bwd` follows.
--
-- WHAT THIS DOES AND DOES NOT DO: it does not make `bwd` easy. It makes it
-- STANDARD. The obligation becomes per-machine and mechanical (define the
-- abstraction, check each reduction rule stutters or advances) instead of
-- open-ended (characterise every path between encoded states). That is a
-- real change in kind, and it is the whole of this module's contribution to
-- criterion (a) — the encoding itself is still unbuilt.

/-- Every host path from an abstracted state lands on an abstracted state,
reachable in the source. The engine of `bwd_of_abstraction`; stated with
variable endpoints so `induction` applies. -/
theorem RS.abstraction_tracks {A B : RS}
    (abs : B.Carrier → Option A.Carrier)
    (hstep : ∀ {b b' : B.Carrier} {a : A.Carrier}, B.step b b' →
      abs b = some a →
      abs b' = some a ∨ ∃ a', A.step a a' ∧ abs b' = some a')
    {b b' : B.Carrier} (h : B.Steps b b') :
    ∀ a, abs b = some a → ∃ a₂, A.Steps a a₂ ∧ abs b' = some a₂ := by
  induction h with
  | refl _ => intro a ha; exact ⟨a, RS.Steps.refl _, ha⟩
  | @tail b w b' s _ ih =>
    intro a ha
    rcases hstep s ha with hstut | ⟨a₁, hadv, hw⟩
    · exact ih a hstut
    · obtain ⟨a₂, hpath, hb'⟩ := ih a₁ hw
      exact ⟨a₂, RS.Steps.tail hadv hpath, hb'⟩

/-- **Adequacy.** A stuttering abstraction function delivers `bwd`. -/
theorem RS.bwd_of_abstraction {A B : RS}
    (enc : A.Carrier → B.Carrier) (abs : B.Carrier → Option A.Carrier)
    (habs : ∀ a, abs (enc a) = some a)
    (hstep : ∀ {b b' : B.Carrier} {a : A.Carrier}, B.step b b' →
      abs b = some a →
      abs b' = some a ∨ ∃ a', A.step a a' ∧ abs b' = some a')
    {a a' : A.Carrier} (h : B.Steps (enc a) (enc a')) : A.Steps a a' := by
  obtain ⟨a₂, hpath, hend⟩ := RS.abstraction_tracks abs hstep h a (habs a)
  rw [habs a'] at hend
  exact (Option.some.inj hend) ▸ hpath

/-- Build a `Simulation` from an encoder, a stuttering abstraction function
that inverts it, and `fwd`. The abstraction doubles as the decoder, so
`dec_enc` and `bwd` are both discharged by the adequacy argument and the
only remaining obligation is `fwd`. -/
def Simulation.ofAbstraction {A B : RS}
    (enc : A.Carrier → B.Carrier) (abs : B.Carrier → Option A.Carrier)
    (habs : ∀ a, abs (enc a) = some a)
    (hstep : ∀ {b b' : B.Carrier} {a : A.Carrier}, B.step b b' →
      abs b = some a →
      abs b' = some a ∨ ∃ a', A.step a a' ∧ abs b' = some a')
    (fwd : ∀ {a a' : A.Carrier}, A.step a a' → B.Steps (enc a) (enc a')) :
    Simulation A B where
  enc := enc
  dec := abs
  dec_enc := habs
  fwd := fwd
  bwd := RS.bwd_of_abstraction enc abs habs hstep

-- ## The three observation modes
-- Same triple shape, different question asked of the host system.

/-- Normalization-based: the host halts exactly when the source does.
(For pure S this observable is externally known to be degenerate —
Waldmann 2000 shows S-normalization is decidable; see CONJECTURES.md.) -/
def PreservesNormalizes (A B : RS) (enc : A.Carrier → B.Carrier) : Prop :=
  ∀ a, A.Normalizes a ↔ B.Normalizes (enc a)

/-- Convertibility-based: the host's equational theory restricted to the
image is exactly the source's. -/
def PreservesConv (A B : RS) (enc : A.Carrier → B.Carrier) : Prop :=
  ∀ a a', A.Conv a a' ↔ B.Conv (enc a) (enc a')

-- ## Universality, relative to a reference system R
-- All three definitions quantify over the pinned Simulation class:
-- universality claims are ∃-Simulation (exhibit one step-faithful,
-- decodable encoding); non-universality claims are ∀-Simulation over the
-- same pinned class (the quantifier asymmetry from the spec). None of
-- them ranges over bare functions — see the negative control below for
-- why that would measure nothing.

/-- Reachability-based universality: B hosts a full step-faithful
simulation of the reference. -/
def UniversalReach (R B : RS) : Prop := Nonempty (Simulation R B)

/-- Normalization-based universality: some simulation's encoding makes
halting agree. -/
def UniversalNorm (R B : RS) : Prop :=
  ∃ S : Simulation R B, PreservesNormalizes R B S.enc

/-- Convertibility-based universality: some simulation's encoding embeds
the reference's equational theory. -/
def UniversalConv (R B : RS) : Prop :=
  ∃ S : Simulation R B, PreservesConv R B S.enc

-- ## Why the pinning matters (negative control)
-- If universality were merely "∃ some function making normalization
-- agree", a classical oracle encoder — decide the source's fate, ship a
-- canned answer — would witness it for ANY source system (given the host
-- has one normalizing and one non-normalizing state). That is the
-- 2007-dispute cheat in its purest form, and the reason UniversalNorm
-- and UniversalConv quantify over Simulation (step-faithful, decodable)
-- rather than bare functions. Machine-checked so nobody re-loosens the
-- definitions without noticing what they buy:
theorem bareEncNorm_trivial (R B : RS)
    (y : B.Carrier) (hy : B.Normalizes y)
    (n : B.Carrier) (hn : ¬ B.Normalizes n) :
    ∃ enc : R.Carrier → B.Carrier, PreservesNormalizes R B enc := by
  classical
  refine ⟨fun a => if R.Normalizes a then y else n, fun a => ?_⟩
  by_cases h : R.Normalizes a
  · simp [h]; exact hy
  · simp [h]; exact hn

-- ## Simulation algebra
-- Simulations compose, so universality is transitive along hosts — the
-- lattice's transport layer.

/-- Every system simulates itself. -/
def Simulation.id (A : RS) : Simulation A A where
  enc := fun a => a
  dec := fun a => some a
  dec_enc := fun _ => rfl
  fwd := fun s => RS.Steps.single s
  bwd := fun h => h

/-- A inside B and B inside C gives A inside C. -/
def Simulation.comp {A B C : RS} (S1 : Simulation A B) (S2 : Simulation B C) :
    Simulation A C where
  enc := fun a => S2.enc (S1.enc a)
  dec := fun c => (S2.dec c).bind S1.dec
  dec_enc := fun a => by simp [S2.dec_enc, S1.dec_enc]
  fwd := fun s => S2.fwd_steps (S1.fwd s)
  bwd := fun h => S1.bwd (S2.bwd h)

/-- Universality transports along a host-to-host simulation. -/
theorem UniversalReach.of_sim {R B C : RS}
    (h : UniversalReach R B) (S : Simulation B C) : UniversalReach R C := by
  obtain ⟨S1⟩ := h
  exact ⟨S1.comp S⟩
