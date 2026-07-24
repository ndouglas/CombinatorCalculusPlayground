--! # Terms with variables
-- (Stage 8 found this file imported NOTHING — see the bridge section at the
-- bottom, added in Stage 9 to connect it to the Term/RS layer.)
import CombinatorCalculusPlayground.Step

-- Combinatory completeness needs something to be complete FOR: terms
-- built from variables and application. The variables live in a separate
-- syntax (TermV) so the core Term stays pure; nothing here touches the
-- census or the RS layer. Reduction is the same two rules — variables
-- are inert (no rule mentions them).

inductive TermV : Type
  | S : TermV
  | K : TermV
  | var : Nat → TermV
  | app : TermV → TermV → TermV
deriving Repr, DecidableEq

namespace TermV

def app2 (f a b : TermV) : TermV := .app (.app f a) b
def app3 (f a b c : TermV) : TermV := .app (.app (.app f a) b) c

inductive StepV : TermV → TermV → Prop
  | K_red (x y : TermV) : StepV (app2 .K x y) x
  | S_red (f g x : TermV) :
      StepV (app3 .S f g x) (.app (.app f x) (.app g x))
  | appL {t t' u : TermV} : StepV t t' → StepV (.app t u) (.app t' u)
  | appR {t u u' : TermV} : StepV u u' → StepV (.app t u) (.app t u')

inductive StepsV : TermV → TermV → Prop
  | refl (t : TermV) : StepsV t t
  | tail {t u v : TermV} : StepV t u → StepsV u v → StepsV t v

theorem StepsV.trans {t u v : TermV} (h1 : StepsV t u) (h2 : StepsV u v) :
    StepsV t v := by
  induction h1 with
  | refl => exact h2
  | tail s _ ih => exact tail s (ih h2)

theorem StepsV.congL {t t' u : TermV} (h : StepsV t t') :
    StepsV (.app t u) (.app t' u) := by
  induction h with
  | refl => exact StepsV.refl _
  | tail s _ ih => exact StepsV.tail (StepV.appL s) ih

theorem StepsV.congR {t u u' : TermV} (h : StepsV u u') :
    StepsV (.app t u) (.app t u') := by
  induction h with
  | refl => exact StepsV.refl _
  | tail s _ ih => exact StepsV.tail (StepV.appR s) ih

theorem StepsV.congApp {t t' u u' : TermV} (h1 : StepsV t t') (h2 : StepsV u u') :
    StepsV (.app t u) (.app t' u') :=
  StepsV.trans (StepsV.congL h1) (StepsV.congR h2)

/-- Substitute u for variable x. -/
def subst (x : Nat) (u : TermV) : TermV → TermV
  | .var y => if y = x then u else .var y
  | .S => .S
  | .K => .K
  | .app a b => .app (subst x u a) (subst x u b)

/-- Does variable x occur in t? -/
def occurs (x : Nat) : TermV → Bool
  | .var y => y == x
  | .app a b => occurs x a || occurs x b
  | _ => false

#guard subst 0 .S (.app (.var 0) (.var 1)) = .app .S (.var 1)
#guard subst 0 .S (.var 1) = .var 1
#guard occurs 0 (.app .K (.var 0)) = true
#guard occurs 1 (.app .K (.var 0)) = false
#guard occurs 0 (app2 .S .K .K) = false

-- ## Bracket abstraction
-- The NAIVE algorithm — no occurs-check optimization. Terms come out
-- bigger, proofs come out smaller; for calibration the proofs win (YAGNI).
--   [x]x       = S K K            (the I combinator, on the spot)
--   [x](var y) = K (var y)        (y ≠ x)
--   [x](a b)   = S ([x]a) ([x]b)
--   [x]S = K S,  [x]K = K K
def bracket (x : Nat) : TermV → TermV
  | .var y => if y = x then app2 .S .K .K else .app .K (.var y)
  | .app a b => app2 .S (bracket x a) (bracket x b)
  | .S => .app .K .S
  | .K => .app .K .K

#guard bracket 0 (.var 0) = TermV.app2 .S .K .K
#guard bracket 0 (.var 1) = .app .K (.var 1)
#guard bracket 0 (.app (.var 0) (.var 0))
       = TermV.app2 .S (TermV.app2 .S .K .K) (TermV.app2 .S .K .K)

-- ## Combinatory completeness of {S, K}
-- THE theorem of this file: applying the abstraction is substitution.
theorem bracket_beta (x : Nat) (t u : TermV) :
    StepsV (.app (bracket x t) u) (subst x u t) := by
  induction t with
  | S =>
    -- (K S) u → S
    exact StepsV.tail (StepV.K_red .S u) (StepsV.refl _)
  | K =>
    exact StepsV.tail (StepV.K_red .K u) (StepsV.refl _)
  | var y =>
    by_cases hy : y = x
    · -- (S K K) u → (K u) (K u) → u ; subst gives u via if_pos
      simp [bracket, subst, hy]
      exact StepsV.tail (StepV.S_red .K .K u)
        (StepsV.tail (StepV.K_red u (.app .K u)) (StepsV.refl u))
    · -- (K (var y)) u → var y ; subst gives var y via if_neg
      simp [bracket, subst, hy]
      exact StepsV.tail (StepV.K_red (.var y) u) (StepsV.refl _)
  | app a b iha ihb =>
    -- (S [x]a [x]b) u → ([x]a u) ([x]b u) →* (subst a)(subst b)
    exact StepsV.tail (StepV.S_red (bracket x a) (bracket x b) u)
      (StepsV.congApp (iha) (ihb))

-- The abstraction really binds: x is gone, other variables survive.
theorem occurs_bracket (x y : Nat) (t : TermV) :
    occurs y (bracket x t) = (occurs y t && !(y == x)) := by
  induction t with
  | S => simp [bracket, occurs]
  | K => simp [bracket, occurs]
  | var z =>
    simp only [bracket]
    by_cases hz : z = x <;> simp only [hz, if_true, if_false, occurs, app2] <;> grind
  | app a b iha ihb =>
    simp only [bracket, occurs, app2, iha, ihb]
    -- Boolean distribution: (p && c) || (q && c) = (p || q) && c
    cases occurs y a <;> cases occurs y b <;> cases (y == x) <;> rfl

/-- No variables at all. -/
def ClosedV (t : TermV) : Prop := ∀ y, occurs y t = false

theorem bracket_closed {x : Nat} {t : TermV}
    (h : ∀ y, occurs y t = true → y = x) : ClosedV (bracket x t) := by
  intro y
  rw [occurs_bracket]
  by_cases hy : occurs y t = true
  · have := h y hy
    subst this
    simp
  · simp [Bool.not_eq_true] at hy
    simp [hy]

/-- Packaging: any single-variable term is realized by a CLOSED combinator.
(Multi-variable completeness is this theorem iterated — deliberately not
formalized; one clean statement beats a fold nobody consumes. YAGNI.) -/
theorem combinatory_completeness (x : Nat) (t : TermV)
    (h : ∀ y, occurs y t = true → y = x) :
    ∃ F : TermV, ClosedV F ∧ ∀ u, StepsV (.app F u) (subst x u t) :=
  ⟨bracket x t, bracket_closed h, fun u => bracket_beta x t u⟩

end TermV

-- ## The bridge to the Term/RS layer (Stage 9)
-- Stage 8's scoping found that this file imported nothing at all: `TermV`,
-- `StepV` and `combinatory_completeness` had no connection to `Term`, `Step`
-- or the `RS` layer. That made the program's headline POSITIVE calibration
-- result live in a different universe from every one of its NEGATIVE results,
-- which are all stated about `RS.SK` over `Term`. The gap was structural, not
-- stylistic.
--
-- Two maps close it. `ofTerm` embeds `Term` into `TermV`; `toTerm` projects
-- back, sending variables to junk — harmless, because `toTerm` is proved
-- to invert `ofTerm` exactly (`toTerm_ofTerm`, `ofTerm_injective`) and because the step
-- transfer below needs no closedness hypothesis at all.

/-- Terms embed into terms-with-variables. -/
def ofTerm : Term → TermV
  | .S => .S
  | .K => .K
  | .app a b => .app (ofTerm a) (ofTerm b)

/-- ...and project back. Variables have no `Term` counterpart, so they go to
junk; `ofTerm_injective` shows this is invisible on the image of `ofTerm`,
which is the only place the bridge uses it. -/
def toTerm : TermV → Term
  | .S => .S
  | .K => .K
  | .var _ => .S
  | .app a b => .app (toTerm a) (toTerm b)

@[simp] theorem toTerm_ofTerm (t : Term) : toTerm (ofTerm t) = t := by
  induction t with
  | S => rfl
  | K => rfl
  | app a b iha ihb => simp [ofTerm, toTerm, iha, ihb]

theorem closedV_ofTerm (t : Term) : TermV.ClosedV (ofTerm t) := by
  induction t with
  | S => intro _; rfl
  | K => intro _; rfl
  | app a b iha ihb =>
    intro y
    simp [ofTerm, TermV.occurs, iha y, ihb y]

/-- `toTerm` inverts `ofTerm` exactly, so no two `Term`s are conflated. This
is all the faithfulness the bridge needs: everything transferred below starts
from a `Term`.

NOT claimed, deliberately: the stronger `ClosedV v → ofTerm (toTerm v) = v`
(that `toTerm` is faithful on EVERY variable-free `TermV`, not just on the
image of `ofTerm`). Its `var` case needs `(n == n) = true`, and every route to
that fact in this toolchain — `beq_self_eq_true`, or `simp` finding it —
drags in `Classical.choice`, which would be this tree's first use of it. The
lemma is decorative (nothing depends on it), so the claim was weakened to what
is needed rather than the axiom paid. See LAB_NOTEBOOK.md, Stage 9. -/
theorem ofTerm_injective {a b : Term} (h : ofTerm a = ofTerm b) : a = b := by
  have : toTerm (ofTerm a) = toTerm (ofTerm b) := by rw [h]
  simpa using this

-- ## Step transfer
-- No closedness hypothesis is needed: `StepV`'s rules are exactly `Step`'s,
-- `toTerm` is a homomorphism for application, and variables are inert on both
-- sides. So every variable-level step projects to a genuine `Term` step.

theorem step_toTerm {v w : TermV} (h : TermV.StepV v w) : toTerm v ⟶ toTerm w := by
  induction h with
  | K_red x y => exact Step.K_red (toTerm x) (toTerm y)
  | S_red f g x => exact Step.S_red (toTerm f) (toTerm g) (toTerm x)
  | appL _ ih => exact Step.appL ih
  | appR _ ih => exact Step.appR ih

theorem steps_toTerm {v w : TermV} (h : TermV.StepsV v w) : toTerm v ⟶* toTerm w := by
  induction h with
  | refl _ => exact Steps.refl _
  | tail s _ ih => exact Steps.tail (step_toTerm s) ih

-- ## Combinatory completeness, in the same language as the refutations
-- This is the point of the bridge. `F` below is a genuine `Term`, and the
-- reduction is genuine `Steps` — so for the first time the program's positive
-- calibration result and its negative ones are stated about the same system.

/-- **Combinatory completeness at the `Term` level.** For any single-variable
`TermV` body there is an actual SK `Term` `F` such that applying it to any
`Term` argument reduces to the body with that argument substituted. -/
theorem combinatory_completeness_Term (x : Nat) (t : TermV)
    (h : ∀ y, TermV.occurs y t = true → y = x) :
    ∃ F : Term, ∀ u : Term,
      Term.app F u ⟶* toTerm (TermV.subst x (ofTerm u) t) := by
  refine ⟨toTerm (TermV.bracket x t), fun u => ?_⟩
  have hstep : TermV.StepsV
      (TermV.app (TermV.bracket x t) (ofTerm u))
      (TermV.subst x (ofTerm u) t) :=
    TermV.bracket_beta x t (ofTerm u)
  have := steps_toTerm hstep
  simpa [toTerm] using this

-- (The `RS`-language restatement lives in `Universality/Calibration.lean`,
-- where it can sit beside the refutations it is meant to be comparable with —
-- this file deliberately stops at `Term`/`Step` so it need not import the
-- conservation-law layer.)

-- Sanity: the identity body `var 0` yields a combinator behaving as I.
#guard toTerm (TermV.bracket 0 (.var 0)) = app2 Term.S Term.K Term.K
#guard toTerm (TermV.bracket 0 (.var 0)) = I

-- ## Is the Stage 10 constraint satisfiable? (Stage 11)
-- Stage 10's prototype showed the adequacy abstraction breaks when reduction
-- desynchronises two copies that `S` duplicated, and that the fix is a design
-- constraint: **duplication must only ever hit normal forms.** Before building
-- pieces (ii)–(v) on top of that constraint, the obvious question is whether it
-- is satisfiable at all — and the first thing a machine duplicates is its own
-- CODE, via the self-application inside any fixpoint combinator.
--
-- All this program's code comes from `bracket`. So: are bracket outputs normal
-- forms? They are, and it is not an accident — bracket abstraction only ever
-- emits `K` applied to ONE argument and `S` applied to TWO, and neither is a
-- redex. Three small lemmas about those shapes, then the result.

theorem normalForm_S : NormalForm Term.S := by rintro ⟨u, h⟩; cases h

theorem normalForm_K : NormalForm Term.K := by rintro ⟨u, h⟩; cases h

/-- `K` applied to one argument is stuck: a K-redex needs two. -/
theorem normalForm_app_K {X : Term} (hX : NormalForm X) :
    NormalForm (Term.app Term.K X) := by
  rintro ⟨u, h⟩
  cases h with
  | appL hl => cases hl
  | appR hr => exact hX ⟨_, hr⟩

/-- `S` applied to one argument is stuck: an S-redex needs three. -/
theorem normalForm_app_S_one {A : Term} (hA : NormalForm A) :
    NormalForm (Term.app Term.S A) := by
  rintro ⟨u, h⟩
  cases h with
  | appL hl => cases hl
  | appR hr => exact hA ⟨_, hr⟩

/-- `S` applied to two arguments is stuck too — still one short of a redex.
This is the shape bracket abstraction emits for every application node. -/
theorem normalForm_app_S_two {A B : Term} (hA : NormalForm A) (hB : NormalForm B) :
    NormalForm (Term.app (Term.app Term.S A) B) := by
  rintro ⟨u, h⟩
  cases h with
  | appL hl => exact absurd ⟨_, hl⟩ (normalForm_app_S_one hA)
  | appR hr => exact hB ⟨_, hr⟩

/-- **Bracket abstraction emits only normal forms.** Every combinator this
program builds by abstraction is therefore safe to duplicate: the Stage 10
desynchronisation failure cannot touch code, only data.

This is the first half of the answer to "is the Stage 10 constraint
satisfiable?". The second half — that the DATA a driver duplicates is normal
at the moment of duplication — is not a theorem about `bracket` and remains an
obligation on piece (v)'s design. -/
theorem normalForm_bracket (x : Nat) (t : TermV) :
    NormalForm (toTerm (TermV.bracket x t)) := by
  induction t with
  | S => exact normalForm_app_K normalForm_S
  | K => exact normalForm_app_K normalForm_K
  | var y =>
    by_cases hy : y = x
    · simp only [TermV.bracket, hy, if_pos]
      exact normalForm_app_S_two normalForm_K normalForm_K
    · simp only [TermV.bracket, hy, if_neg]
      exact normalForm_app_K normalForm_S
  | app a b iha ihb =>
    exact normalForm_app_S_two iha ihb

-- Concretely: the combinator for the identity body is `I`, and it is normal.
theorem normalForm_I : NormalForm I := normalForm_app_S_two normalForm_K normalForm_K
#guard toTerm (TermV.bracket 0 (.var 0)) = I
