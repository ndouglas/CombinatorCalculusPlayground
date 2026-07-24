--! # A Simulation whose SOURCE is known-universal
-- Spec criterion (a) reads: "a correct definition must (a) certify
-- known-universal systems including one-combinator bases." Two things about
-- that, established in Stage 16 and recorded in CONJECTURES.md:
--
--   * the "including one-combinator bases" clause is REFUTED in first-order
--     scope — that is `no_pathEncoding_SK_iota` and, generally, C4. So
--     criterion (a) as written cannot be satisfied here, and that is a finding
--     about the criterion rather than a failure of the program;
--   * the general clause needs ONE certified known-universal system. The
--     interesting instance is SK via Tag, blocked on adequacy (Stages 10–13).
--
-- This module discharges the general clause with the cheapest honest instance:
-- a tag system embeds in a tag system over a larger alphabet. Both source and
-- target are m = 2 tag systems, hence known-universal by Cocke–Minsky (EXTERNAL,
-- cited, not machine-checked). `pureS_in_SK` could not do this — pure S is not
-- known-universal — and it was an inclusion, so its `bwd` was free.
--
-- SCOPE, before the theorem: this says NOTHING about SK. It shows the positive
-- side of the taxonomy is not vacuous when the source is required to be
-- known-universal. The claim that SK certifiably hosts a universal system
-- remains open and research-blocked.
--
-- It is also the first non-degenerate use of Stage 8's `Simulation.ofAbstraction`:
-- `bwd` comes from a stuttering abstraction rather than being free, and here the
-- abstraction never stutters — every host step advances the source by exactly
-- one tag step.
import CombinatorCalculusPlayground.Universality.Defs

/-- Alphabet extension: the same tag system over `Option Sym`, with the injected
symbols behaving as before and the new symbol `none` producing the empty word. -/
def TagSystem.extend (T : TagSystem) : TagSystem where
  Sym := Option T.Sym
  m := T.m
  rule := fun
    | some a => (T.rule a).map some
    | none => []

/-- Decode an injected word, failing if any symbol is the new one. -/
def deInject {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | some a :: rest => (deInject rest).map (a :: ·)
  | none :: _ => none

theorem deInject_map_some {α : Type} (w : List α) :
    deInject (w.map some) = some w := by
  induction w with
  | nil => rfl
  | cons a t ih => simp [deInject, ih]

/-- A successful decode means the word was fully injected. -/
theorem eq_map_some_of_deInject {α : Type} :
    ∀ {b : List (Option α)} {a : List α}, deInject b = some a → b = a.map some
  | [], a, h => by simp [deInject] at h; simp [← h]
  | some x :: rest, a, h => by
    simp only [deInject, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [eq_map_some_of_deInject ht]
  | none :: _, a, h => by simp [deInject] at h

-- ## The forward direction
-- A tag step on `w` is a tag step on `w.map some`, because the rule was
-- extended to agree on injected symbols and `map` commutes with `drop` and `++`.

theorem extend_step {T : TagSystem} {w w' : List T.Sym}
    (h : T.stepRel w w') :
    (T.extend).stepRel (w.map some) (w'.map some) := by
  obtain ⟨a, rest, hw, hlen, hw'⟩ := h
  refine ⟨some a, rest.map some, ?_, ?_, ?_⟩
  · rw [hw]; rfl
  · rw [List.length_map]; exact hlen
  · rw [hw', List.map_append, List.map_drop]
    rfl

-- ## The backward direction, via a stuttering abstraction
-- `deInject` is total on host words and every host step out of an injected word
-- ADVANCES the source by exactly one tag step — the abstraction never stutters.

theorem extend_abs_step {T : TagSystem}
    {b b' : List (Option T.Sym)} {a : List T.Sym}
    (hstep : (RS.Tag (T.extend)).step b b') (habs : deInject b = some a) :
    deInject b' = some a ∨
      ∃ a', (RS.Tag T).step a a' ∧ deInject b' = some a' := by
  -- b is fully injected, so its head symbol is an injected one
  have hb : b = a.map some := eq_map_some_of_deInject habs
  obtain ⟨sy, rest, hbeq, hlen, hb'⟩ := hstep
  subst hb
  -- the head of an injected word is `some x` for the head `x` of `a`
  match a, hbeq with
  | x :: t, hbeq =>
    have hsy : sy = some x := by
      simp only [List.map_cons, List.cons.injEq] at hbeq
      exact hbeq.1.symm
    subst hsy
    -- Take the source step in `stepRel`'s own canonical form, so the `drop`
    -- never has to be decomposed.
    refine Or.inr ⟨(x :: t).drop T.m ++ T.rule x, ?_, ?_⟩
    · exact ⟨x, t, rfl, (by rw [List.length_map] at hlen; exact hlen), rfl⟩
    · -- the host result is exactly the injection of that
      rw [hb']
      simp only [TagSystem.extend]
      rw [← List.map_drop, ← List.map_append]
      exact deInject_map_some _

/-- **A `Simulation` whose source is a known-universal system.** `bwd` is
delivered by Stage 8's adequacy machinery from an abstraction that never
stutters — its first non-degenerate use. -/
def tagInExtend (T : TagSystem) : Simulation (RS.Tag T) (RS.Tag (T.extend)) :=
  Simulation.ofAbstraction
    (enc := fun w => w.map some)
    (abs := deInject)
    (habs := deInject_map_some)
    (hstep := extend_abs_step)
    (fwd := fun s => RS.Steps.single (extend_step s))

/-- The taxonomy therefore certifies a known-universal system: `T.extend` is
Reach-universal for the reference `RS.Tag T`, and `m = 2` tag systems over
finite alphabets are universal (Cocke–Minsky 1964 — EXTERNAL, cited, not
machine-checked here). -/
theorem universalReach_extend (T : TagSystem) :
    UniversalReach (RS.Tag T) (RS.Tag (T.extend)) :=
  ⟨tagInExtend T⟩

-- Non-triviality: the encoder is NOT the identity and the carriers differ, so
-- this is not the diagonal instance the Stage 8 negative controls rule out.
-- A concrete step, carried across: in the m = 2 system over Bool with rule
-- a ↦ [a], the word [true, false, false] steps to [false, true], and the
-- injected word steps correspondingly.
example : (RS.Tag (⟨Bool, 2, fun a => [a]⟩ : TagSystem)).step
    [true, false, false] [false, true] :=
  ⟨true, [false, false], rfl, by simp, rfl⟩

example : (RS.Tag ((⟨Bool, 2, fun a => [a]⟩ : TagSystem).extend)).step
    ([true, false, false].map some) ([false, true].map some) :=
  extend_step ⟨true, [false, false], rfl, by simp, rfl⟩
