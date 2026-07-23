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
