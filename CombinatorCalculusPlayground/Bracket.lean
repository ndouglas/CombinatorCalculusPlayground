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

/-- `(n == n) = true`, by a route that provably avoids `Classical.choice` — Stage 9's trap, and
Stage 76's sixth leak (which had been hiding in THIS FILE since `occurs_bracket` was proved by
`grind`; see the notebook). -/
private theorem beqSelf (n : Nat) : (n == n) = true := by
  first
    | exact Nat.beq_refl n
    | exact decide_eq_true rfl

-- The abstraction really binds: x is gone, other variables survive.
-- (Stage 76: the `var` case was `grind`, and `grind` was this development's sixth
-- `Classical.choice` leak — pre-existing, found when new code imitated it. Now explicit.)
theorem occurs_bracket (x y : Nat) (t : TermV) :
    occurs y (bracket x t) = (occurs y t && !(y == x)) := by
  induction t with
  | S => simp [bracket, occurs]
  | K => simp [bracket, occurs]
  | var z =>
    show occurs y (if z = x then app2 .S .K .K else .app .K (.var z))
      = (occurs y (.var z) && !(y == x))
    by_cases hz : z = x
    · rw [if_pos hz]
      show ((false || false) || false) = ((z == y) && !(y == x))
      by_cases hy : y = x
      · rw [show (y == x) = true from by rw [hy]; exact beqSelf x,
            show (z == y) = true from by rw [hz, hy]; exact beqSelf x]
        rfl
      · rw [show (z == y) = false from
          beq_eq_false_iff_ne.mpr (fun h => hy (hz.symm.trans h).symm)]
        rfl
    · rw [if_neg hz]
      show (false || (z == y)) = ((z == y) && !(y == x))
      by_cases hy : y = x
      · rw [show (y == x) = true from by rw [hy]; exact beqSelf x,
            show (z == y) = false from beq_eq_false_iff_ne.mpr (fun h => hz (h.trans hy))]
        rfl
      · rw [show (y == x) = false from beq_eq_false_iff_ne.mpr hy]
        cases (z == y) <;> rfl
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
    rw [beqSelf]
    cases occurs y t <;> rfl
  · rw [show occurs y t = false from by
      cases hocc : occurs y t
      · rfl
      · exact absurd hocc hy]
    rfl

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
    (_h : ∀ y, TermV.occurs y t = true → y = x) :
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
    · simp only [TermV.bracket, hy]
      exact normalForm_app_K normalForm_S
  | app a b iha ihb =>
    exact normalForm_app_S_two iha ihb

-- Concretely: the combinator for the identity body is `I`, and it is normal.
theorem normalForm_I : NormalForm I := normalForm_app_S_two normalForm_K normalForm_K
#guard toTerm (TermV.bracket 0 (.var 0)) = I

-- ## Piece (ii): two-variable abstraction (Stage 12)
-- Stage 10 found that iterating `bracket` needs substitution to commute with
-- bracketing, and that it only does so UP TO REDUCTION. Two design choices cut
-- that down to one manageable lemma.
--
-- FIRST: n-variable abstraction is not needed. A driver takes a fixpoint's
-- self-reference and a state, and its data can be TUPLED, so two nested
-- abstractions suffice — `bracket self (bracket state body)`. Two is exactly
-- the case the commutation lemma handles in one application, with no iteration.
--
-- SECOND: the substituted argument is always ENCODED DATA, i.e. in the image of
-- `ofTerm`. Stating the lemmas for `ofTerm p` rather than for an abstract
-- `ClosedV u` removes the `var` case entirely — which also dodges the
-- `Classical.choice` trap Stage 9 hit, since that trap lives precisely in
-- deriving a contradiction from `ClosedV (var n)`.

/-- Substituting into encoded data does nothing: it has no variables. -/
theorem subst_ofTerm (x : Nat) (v : TermV) (p : Term) :
    TermV.subst x v (ofTerm p) = ofTerm p := by
  induction p with
  | S => rfl
  | K => rfl
  | app a b iha ihb => simp [ofTerm, TermV.subst, iha, ihb]

/-- **The commutation lemma, in applied form.** Substituting encoded data for
`x` inside `[y]t` and then applying to `v` gives the same result as doing both
substitutions directly. This is what makes nested abstraction work: the two
combinators are NOT equal, but applied to any argument they reach the same
term, and applied is the only way they are ever used. -/
theorem bracket_subst_applied {x y : Nat} (hxy : x ≠ y) (p : Term) (t v : TermV) :
    TermV.StepsV
      (TermV.app (TermV.subst x (ofTerm p) (TermV.bracket y t)) v)
      (TermV.subst y v (TermV.subst x (ofTerm p) t)) := by
  induction t with
  | S =>
    -- [y]S = K S, substitution inert, (K S) v → S
    exact TermV.StepsV.tail (TermV.StepV.K_red .S v) (TermV.StepsV.refl _)
  | K =>
    exact TermV.StepsV.tail (TermV.StepV.K_red .K v) (TermV.StepsV.refl _)
  | var z =>
    by_cases hzy : z = y
    · -- [y](var y) = S K K, which is closed; (S K K) v →* v, and both
      -- substitutions leave `var y` as `v` since y ≠ x.
      subst hzy
      have hzx : z ≠ x := fun h => hxy h.symm
      simp only [TermV.bracket, TermV.subst, hzx, ite_false, ite_true]
      exact TermV.StepsV.tail (TermV.StepV.S_red .K .K v)
        (TermV.StepsV.tail (TermV.StepV.K_red v (.app .K v)) (TermV.StepsV.refl v))
    · -- [y](var z) = K (var z); the K-redex fires and both sides agree
      by_cases hzx : z = x
      · subst hzx
        simp only [TermV.bracket, TermV.subst, hzy, ite_false, ite_true,
          subst_ofTerm]
        exact TermV.StepsV.tail (TermV.StepV.K_red (ofTerm p) v) (TermV.StepsV.refl _)
      · simp only [TermV.bracket, TermV.subst, hzy, hzx, ite_false]
        exact TermV.StepsV.tail (TermV.StepV.K_red (.var z) v) (TermV.StepsV.refl _)
  | app a b iha ihb =>
    -- [y](a b) = S ([y]a) ([y]b); the S-redex fires and the two IHs finish
    exact TermV.StepsV.tail (TermV.StepV.S_red _ _ v) (TermV.StepsV.congApp iha ihb)

/-- Two-variable abstraction: `[x][y]t`. -/
def abs2 (x y : Nat) (t : TermV) : TermV := TermV.bracket x (TermV.bracket y t)

/-- **Two-variable combinatory completeness.** `[x][y]t` applied to encoded
data and then to any argument performs both substitutions. This is the form
piece (v)'s driver needs: `x` is the fixpoint's self-reference, `y` the state. -/
theorem abs2_beta {x y : Nat} (hxy : x ≠ y) (p : Term) (t v : TermV) :
    TermV.StepsV
      (TermV.app (TermV.app (abs2 x y t) (ofTerm p)) v)
      (TermV.subst y v (TermV.subst x (ofTerm p) t)) :=
  TermV.StepsV.trans
    (TermV.StepsV.congL (TermV.bracket_beta x (TermV.bracket y t) (ofTerm p)))
    (bracket_subst_applied hxy p t v)

/-- The two-variable combinator is closed data too, hence a normal form —
so it is safe to duplicate, per Stage 11. -/
theorem normalForm_abs2 (x y : Nat) (t : TermV) :
    NormalForm (toTerm (abs2 x y t)) :=
  normalForm_bracket x (TermV.bracket y t)

-- Sanity: [x][y] y is the "return the second argument" combinator, and it does.
#guard toTerm (abs2 0 1 (.var 1)) = toTerm (TermV.bracket 0 (TermV.app2 .S .K .K))

-- ## Stage 62: the occurs-check optimisation, added when it finally paid
-- `bracket` above says why it is naive: "Terms come out bigger, proofs come out smaller; for calibration
-- the proofs win (YAGNI)." That was right for calibration and it is exactly what blocks the tag driver.
-- Stage 62 compiled a fold-list toolkit with it and got `TAIL` at 14100 leaves, on which the tree's own
-- evaluator ABORTS — so the naive algorithm makes the driver not merely large but uncomputable.
--
-- The missing rule is the standard one: if `x` does not occur, do not distribute, just protect with `K`.

namespace TermV

/-- `subst` is the identity when the variable is absent — the fact the new rule needs. -/
theorem subst_of_not_occurs (x : Nat) (u : TermV) :
    ∀ {t : TermV}, occurs x t = false → subst x u t = t := by
  intro t
  induction t with
  | S => intro _; rfl
  | K => intro _; rfl
  | var y =>
      intro h
      simp only [occurs, beq_eq_false_iff_ne, ne_eq] at h
      simp [subst, h]
  | app a b iha ihb =>
      intro h
      simp only [occurs, Bool.or_eq_false_iff] at h
      simp [subst, iha h.1, ihb h.2]

/-- Bracket abstraction with the occurs check. Same specification as `bracket`, smaller output. -/
def bracketOpt (x : Nat) : TermV → TermV
  | .var y => if y = x then app2 .S .K .K else .app .K (.var y)
  | .app a b =>
      if occurs x (.app a b) then app2 .S (bracketOpt x a) (bracketOpt x b)
      else .app .K (.app a b)
  | .S => .app .K .S
  | .K => .app .K .K

/-- **Same beta property as `bracket`.** The extra branch is discharged by `subst_of_not_occurs`. -/
theorem bracketOpt_beta (x : Nat) (t u : TermV) :
    StepsV (.app (bracketOpt x t) u) (subst x u t) := by
  induction t with
  | S => exact StepsV.tail (StepV.K_red .S u) (StepsV.refl _)
  | K => exact StepsV.tail (StepV.K_red .K u) (StepsV.refl _)
  | var y =>
      by_cases hy : y = x
      · simp [bracketOpt, subst, hy]
        exact StepsV.tail (StepV.S_red .K .K u)
          (StepsV.tail (StepV.K_red u (.app .K u)) (StepsV.refl u))
      · simp [bracketOpt, subst, hy]
        exact StepsV.tail (StepV.K_red (.var y) u) (StepsV.refl _)
  | app a b iha ihb =>
      by_cases hocc : occurs x (.app a b) = true
      · simp only [bracketOpt, hocc, if_pos]
        exact StepsV.tail (StepV.S_red (bracketOpt x a) (bracketOpt x b) u)
          (StepsV.congApp iha ihb)
      · have hf : occurs x (TermV.app a b) = false := by simpa using hocc
        simp only [bracketOpt, if_neg hocc]
        rw [subst_of_not_occurs x u hf]
        exact StepsV.tail (StepV.K_red (.app a b) u) (StepsV.refl _)

end TermV

/-- The `Term`-level statement, matching `combinatory_completeness_Term`. -/
theorem combinatory_completeness_opt (x : Nat) (t : TermV) (u : Term) :
    toTerm (.app (TermV.bracketOpt x t) (ofTerm u)) ⟶* toTerm (TermV.subst x (ofTerm u) t) :=
  steps_toTerm (TermV.bracketOpt_beta x t (ofTerm u))

-- The optimisation is not cosmetic. `λx.λy.λz. x` distributes through three abstractions naively and
-- collapses to almost nothing with the check.
-- The optimisation compounds with nesting: negligible on `λx.λy.λz. x` (15 vs 9), decisive on real code.
-- Stage 62's fold-list toolkit: `CONS` 414 → 66, `TAIL` 14100 → 192, which is the difference between a term
-- the evaluator aborts on and one it handles in a third of a second.
#guard leafCount (toTerm (TermV.bracket 2 (TermV.bracket 1 (TermV.bracket 0 (.var 2))))) = 15
#guard leafCount (toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 (.var 2))))) = 9

-- ## Stage 64: substitution commutes with the optimised abstraction
-- Multi-argument application of compiled code needs the fact the NAIVE algorithm got in
-- `bracket_subst_applied` — substituting encoded data under an inner abstraction — but for `bracketOpt`.
-- The optimised statement is stronger: an EQUALITY rather than "up to reduction", because encoded data is
-- closed, so it can neither contain nor create an occurrence and the occurs check never changes its verdict.

/-- Encoded data is invisible to the occurs check: substituting it changes no occurrence of any OTHER
variable. (`y = x` is excluded — that occurrence is exactly what the substitution consumes.) -/
theorem occurs_subst_ofTerm {x y : Nat} (hyx : y ≠ x) (p : Term) (t : TermV) :
    TermV.occurs y (TermV.subst x (ofTerm p) t) = TermV.occurs y t := by
  induction t with
  | S => rfl
  | K => rfl
  | var z =>
      by_cases hz : z = x
      · subst hz
        have hne : (z == y) = false := beq_eq_false_iff_ne.mpr (fun h => hyx h.symm)
        simp [TermV.subst, TermV.occurs, closedV_ofTerm p y, hne]
      · simp [TermV.subst, hz]
  | app a b iha ihb => simp [TermV.subst, TermV.occurs, iha, ihb]

/-- Abstracting a variable out of encoded data only protects it with `K`: the occurs check sees nothing. -/
theorem bracketOpt_ofTerm (y : Nat) (p : Term) :
    TermV.bracketOpt y (ofTerm p) = .app .K (ofTerm p) := by
  cases p with
  | S => rfl
  | K => rfl
  | app a b =>
      have h : TermV.occurs y (ofTerm (Term.app a b)) = false := closedV_ofTerm _ y
      simp only [ofTerm] at h ⊢
      simp [TermV.bracketOpt, h]

/-- **Substituting encoded data commutes with the optimised abstraction, as an equality.** This is what
makes iterated application of multi-variable compiled code work: each argument's β-step leaves a genuine
`bracketOpt` for the next argument to consume. -/
theorem bracketOpt_subst_ofTerm {x y : Nat} (hxy : x ≠ y) (p : Term) (t : TermV) :
    TermV.subst x (ofTerm p) (TermV.bracketOpt y t)
      = TermV.bracketOpt y (TermV.subst x (ofTerm p) t) := by
  induction t with
  | S => rfl
  | K => rfl
  | var z =>
      by_cases hzy : z = y
      · subst hzy
        -- `[y](var y) = S K K` is closed, and the substitution leaves `var y` alone since `y ≠ x`.
        simp [TermV.bracketOpt, TermV.app2, TermV.subst, Ne.symm hxy]
      · by_cases hzx : z = x
        · subst hzx
          -- the substitution fires; both sides are `K` protecting the data.
          simp [TermV.bracketOpt, TermV.subst, hzy, bracketOpt_ofTerm]
        · simp [TermV.bracketOpt, TermV.subst, hzy, hzx]
  | app a b iha ihb =>
      have hos : TermV.occurs y (TermV.subst x (ofTerm p) (.app a b)) = TermV.occurs y (.app a b) :=
        occurs_subst_ofTerm (Ne.symm hxy) p _
      by_cases hocc : TermV.occurs y (.app a b) = true
      · have hocc' := hos.trans hocc
        simp only [TermV.subst] at hocc' ⊢
        simp only [TermV.bracketOpt, hocc, hocc', if_true]
        simp only [TermV.app2, TermV.subst, iha, ihb]
      · have hf : TermV.occurs y (TermV.app a b) = false := by simpa using hocc
        have hf' := hos.trans hf
        simp only [TermV.subst] at hf' ⊢
        simp [TermV.bracketOpt, hf, hf', TermV.subst]

-- ## The β-ladder at the `Term` level
-- Stage 63's plan needs compiled combinators of one to four arguments reasoned about at the lambda level.
-- Each rung applies one argument by `bracketOpt_beta`, then uses the commutation above to expose a genuine
-- abstraction for the next argument. Variables are numbered outermost-first: an n-argument combinator is
-- `[n-1](…([0] body))`.

/-- One argument: `Term`-level β for the optimised abstraction. -/
theorem bracketOpt_beta_Term (x : Nat) (t : TermV) (u : Term) :
    Term.app (toTerm (TermV.bracketOpt x t)) u ⟶* toTerm (TermV.subst x (ofTerm u) t) := by
  have h := steps_toTerm (TermV.bracketOpt_beta x t (ofTerm u))
  simpa [toTerm] using h

/-- Two arguments. -/
theorem bracketOpt_beta2_Term (b : TermV) (u v : Term) :
    Term.app (Term.app (toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))) u) v
      ⟶* toTerm (TermV.subst 0 (ofTerm v) (TermV.subst 1 (ofTerm u) b)) := by
  have h1 : Term.app (toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))) u
      ⟶* toTerm (TermV.bracketOpt 0 (TermV.subst 1 (ofTerm u) b)) := by
    have h := bracketOpt_beta_Term 1 (TermV.bracketOpt 0 b) u
    rwa [bracketOpt_subst_ofTerm (by decide) u b] at h
  exact Steps.trans (Steps.congL h1) (bracketOpt_beta_Term 0 _ v)

/-- Three arguments. -/
theorem bracketOpt_beta3_Term (b : TermV) (u v w : Term) :
    Term.app (Term.app (Term.app
        (toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b)))) u) v) w
      ⟶* toTerm (TermV.subst 0 (ofTerm w) (TermV.subst 1 (ofTerm v) (TermV.subst 2 (ofTerm u) b))) := by
  have h1 : Term.app (toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b)))) u
      ⟶* toTerm (TermV.bracketOpt 1 (TermV.bracketOpt 0 (TermV.subst 2 (ofTerm u) b))) := by
    have h := bracketOpt_beta_Term 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b)) u
    rwa [bracketOpt_subst_ofTerm (by decide) u (TermV.bracketOpt 0 b),
         bracketOpt_subst_ofTerm (by decide) u b] at h
  exact Steps.trans (Steps.congL (Steps.congL h1)) (bracketOpt_beta2_Term _ v w)

/-- Four arguments — `CONS`'s arity, the largest the toolkit uses. -/
theorem bracketOpt_beta4_Term (b : TermV) (u v w z : Term) :
    Term.app (Term.app (Term.app (Term.app
        (toTerm (TermV.bracketOpt 3 (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))))) u) v) w) z
      ⟶* toTerm (TermV.subst 0 (ofTerm z) (TermV.subst 1 (ofTerm w)
            (TermV.subst 2 (ofTerm v) (TermV.subst 3 (ofTerm u) b)))) := by
  have h1 : Term.app (toTerm (TermV.bracketOpt 3
        (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))))) u
      ⟶* toTerm (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 (TermV.subst 3 (ofTerm u) b)))) := by
    have h := bracketOpt_beta_Term 3 (TermV.bracketOpt 2 (TermV.bracketOpt 1 (TermV.bracketOpt 0 b))) u
    rwa [bracketOpt_subst_ofTerm (by decide) u (TermV.bracketOpt 1 (TermV.bracketOpt 0 b)),
         bracketOpt_subst_ofTerm (by decide) u (TermV.bracketOpt 0 b),
         bracketOpt_subst_ofTerm (by decide) u b] at h
  exact Steps.trans (Steps.congL (Steps.congL (Steps.congL h1))) (bracketOpt_beta3_Term _ v w z)

-- ## Stage 69: reduction is congruent under substitution contexts
-- The word-drift work needs to reduce INSIDE a hole of a compiled term: if the data in a
-- substitution position advances, the whole substituted term advances. Generic, one induction.

/-- If `M ⟶* M'`, then substituting `M` and substituting `M'` into the same context are related by
reduction — the context contributes only congruence steps, one path per occurrence of the hole. -/
theorem steps_toTerm_subst {y : Nat} {M M' : Term} (h : M ⟶* M') : ∀ (C : TermV),
    toTerm (TermV.subst y (ofTerm M) C) ⟶* toTerm (TermV.subst y (ofTerm M') C) := by
  intro C
  induction C with
  | S => exact Steps.refl _
  | K => exact Steps.refl _
  | var z =>
      by_cases hz : z = y
      · simpa [TermV.subst, hz] using h
      · simp [TermV.subst, hz]
        exact Steps.refl _
  | app a b iha ihb =>
      simp only [TermV.subst, toTerm]
      exact Steps.congApp iha ihb

-- ## Stage 76: the N-ary abstraction — toward the any-alphabet tag theorem
-- The tag `Simulation` (Stage 75) is for a two-symbol alphabet; known-universal tag systems need
-- more symbols, and the ONLY alphabet-dependent piece of the whole construction is dispatch. The
-- β-ladder above stops at arity 4; this section builds the list-indexed version — abstraction over
-- `k` variables, application to `k` arguments, β in one theorem — plus the SELECTORS
-- `λx₁…xₖ. xᵢ` that make an n-way dispatch, with their β, closed forms, and normality. All generic:
-- nothing here mentions tag systems.

/-- Apply a function to a list of arguments, left to right. -/
def appArgs (f : Term) : List Term → Term
  | [] => f
  | a :: as => appArgs (Term.app f a) as

theorem appArgs_congL : ∀ (args : List Term) {f f' : Term},
    (f ⟶* f') → appArgs f args ⟶* appArgs f' args
  | [], _, _, h => h
  | _ :: as, _, _, h => appArgs_congL as (Steps.congL h)

/-- Abstract the variables `k-1, …, 1, 0`, outermost first — the list-indexed `o1`/`o3`/`o4`. -/
def absArgs : Nat → TermV → TermV
  | 0, b => b
  | k + 1, b => TermV.bracketOpt k (absArgs k b)

/-- Substitute a list of arguments: the FIRST argument replaces the HIGHEST index, so the index of
each substitution is the length of the remaining suffix. -/
def substArgs : List Term → TermV → TermV
  | [], b => b
  | a :: as, b => substArgs as (TermV.subst as.length (ofTerm a) b)

/-- Substitution from above commutes past the whole abstraction block. -/
theorem subst_absArgs {j : Nat} (u : Term) : ∀ (k : Nat), k ≤ j → ∀ (b : TermV),
    TermV.subst j (ofTerm u) (absArgs k b) = absArgs k (TermV.subst j (ofTerm u) b)
  | 0, _, _ => rfl
  | k + 1, hk, b => by
      show TermV.subst j (ofTerm u) (TermV.bracketOpt k (absArgs k b)) = _
      rw [bracketOpt_subst_ofTerm (by omega) u (absArgs k b),
          subst_absArgs u k (by omega)]
      rfl

theorem substArgs_ofTerm : ∀ (args : List Term) (t : Term),
    substArgs args (ofTerm t) = ofTerm t
  | [], _ => rfl
  | _ :: as, t => by
      show substArgs as (TermV.subst as.length (ofTerm _) (ofTerm t)) = _
      rw [subst_ofTerm]
      exact substArgs_ofTerm as t

/-- **N-ary β.** The `k`-variable abstraction applied to `k` arguments performs all `k`
substitutions — `bracketOpt_beta2/3/4_Term`, for every arity at once. -/
theorem absArgs_beta : ∀ (args : List Term) (b : TermV),
    appArgs (toTerm (absArgs args.length b)) args ⟶* toTerm (substArgs args b)
  | [], _ => Steps.refl _
  | a :: as, b => by
      show appArgs (Term.app (toTerm (absArgs (as.length + 1) b)) a) as ⟶* _
      refine Steps.trans (appArgs_congL as ?_) (absArgs_beta as (TermV.subst as.length (ofTerm a) b))
      have h := bracketOpt_beta_Term as.length (absArgs as.length b) a
      rwa [subst_absArgs a as.length (Nat.le_refl _)] at h

-- ### Selectors: `λx₁…xₖ. xᵢ`, the dispatch primitives

/-- The argument at position `|pre|` has variable index `|post|` — substituting the whole list into
that variable returns exactly that argument. -/
theorem substArgs_select : ∀ (pre : List Term) (x : Term) (post : List Term),
    substArgs (pre ++ x :: post) (.var post.length) = ofTerm x := by
  intro pre
  induction pre with
  | nil =>
      intro x post
      show substArgs post (TermV.subst post.length (ofTerm x) (.var post.length)) = _
      rw [show TermV.subst post.length (ofTerm x) (.var post.length) = ofTerm x from by
        show (if post.length = post.length then ofTerm x else .var post.length) = ofTerm x
        rw [if_pos rfl]]
      exact substArgs_ofTerm post x
  | cons p pre ih =>
      intro x post
      show substArgs (pre ++ x :: post)
        (TermV.subst (pre ++ x :: post).length (ofTerm p) (.var post.length)) = _
      have hne : post.length ≠ (pre ++ x :: post).length := by
        simp only [List.length_append, List.length_cons]
        omega
      rw [show TermV.subst (pre ++ x :: post).length (ofTerm p) (.var post.length)
          = .var post.length from by
        show (if post.length = (pre ++ x :: post).length then ofTerm p else .var post.length) = _
        rw [if_neg hne]]
      exact ih x post

/-- The `i`-th selector on `k` arguments. -/
def selArgs (k i : Nat) : Term := toTerm (absArgs k (.var i))

/-- **Selector β**: applied to any argument list, the selector with index `|post|` returns the
argument sitting between `pre` and `post`. -/
theorem selArgs_correct (pre : List Term) (x : Term) (post : List Term) :
    appArgs (selArgs (pre ++ x :: post).length post.length) (pre ++ x :: post) ⟶* x := by
  have h := absArgs_beta (pre ++ x :: post) (.var post.length)
  rwa [substArgs_select, toTerm_ofTerm] at h

-- ### Closed forms and normality
-- A selector is `K`-wraps around an `S (K K)`-chain ending in `I` — every layer a shape the Stage
-- 11 lemmas cover, so selectors are NORMAL, generically in `k` and `i`.

/-- The occurs identity for the OPTIMISED algorithm — `occurs_bracket`'s twin. -/
theorem occurs_bracketOpt (x y : Nat) (t : TermV) :
    TermV.occurs y (TermV.bracketOpt x t) = (TermV.occurs y t && !(y == x)) := by
  induction t with
  | S => simp [TermV.bracketOpt, TermV.occurs]
  | K => simp [TermV.bracketOpt, TermV.occurs]
  | var z =>
      show TermV.occurs y (if z = x then TermV.app2 .S .K .K else .app .K (.var z))
        = (TermV.occurs y (.var z) && !(y == x))
      by_cases hz : z = x
      · rw [if_pos hz]
        show ((false || false) || false) = ((z == y) && !(y == x))
        by_cases hy : y = x
        · rw [show (y == x) = true from by rw [hy]; exact TermV.beqSelf x,
              show (z == y) = true from by rw [hz, hy]; exact TermV.beqSelf x]
          rfl
        · rw [show (z == y) = false from
            beq_eq_false_iff_ne.mpr (fun h => hy (hz.symm.trans h).symm)]
          rfl
      · rw [if_neg hz]
        show (false || (z == y)) = ((z == y) && !(y == x))
        by_cases hy : y = x
        · rw [show (y == x) = true from by rw [hy]; exact TermV.beqSelf x,
              show (z == y) = false from beq_eq_false_iff_ne.mpr (fun h => hz (h.trans hy))]
          rfl
        · rw [show (y == x) = false from beq_eq_false_iff_ne.mpr hy]
          cases (z == y) <;> rfl
  | app a b iha ihb =>
      by_cases hocc : TermV.occurs x (.app a b) = true
      · have hocc' : (TermV.occurs x a || TermV.occurs x b) = true := by
          simpa [TermV.occurs] using hocc
        simp only [TermV.bracketOpt, TermV.occurs, hocc', if_true, TermV.app2, iha, ihb]
        cases TermV.occurs y a <;> cases TermV.occurs y b <;> cases (y == x) <;> rfl
      · have hf : TermV.occurs x a = false ∧ TermV.occurs x b = false := by
          simpa [TermV.occurs, Bool.or_eq_false_iff] using hocc
        have hcond : (TermV.occurs x a || TermV.occurs x b) = false := by
          rw [hf.1, hf.2]; rfl
        simp only [TermV.bracketOpt, TermV.occurs, hcond, Bool.false_eq_true, if_false]
        by_cases hyx : y = x
        · subst hyx
          rw [hf.1, hf.2]
          rfl
        · rw [beq_eq_false_iff_ne.mpr hyx]
          cases TermV.occurs y a <;> cases TermV.occurs y b <;> rfl

/-- The optimised abstraction of a NON-OCCURRING variable is a bare `K`-protection, whatever the
body's shape. -/
theorem bracketOpt_not_occurs {x : Nat} {t : TermV} (h : TermV.occurs x t = false) :
    TermV.bracketOpt x t = .app .K t := by
  cases t with
  | S => rfl
  | K => rfl
  | var y =>
      show (if y = x then _ else _) = _
      rw [if_neg (beq_eq_false_iff_ne.mp h)]
  | app a b =>
      show (if TermV.occurs x (a.app b) = true then _ else _) = _
      rw [if_neg (fun hc => Bool.false_ne_true (h ▸ hc))]

/-- A tower of `K`-wraps. -/
def kTowerV : Nat → TermV → TermV
  | 0, t => t
  | k + 1, t => .app .K (kTowerV k t)

theorem occurs_kTowerV (y : Nat) (t : TermV) : ∀ (k : Nat),
    TermV.occurs y (kTowerV k t) = TermV.occurs y t
  | 0 => rfl
  | k + 1 => by
      show (TermV.occurs y .K || TermV.occurs y (kTowerV k t)) = _
      rw [occurs_kTowerV y t k]
      rfl

/-- The occurs-check, iterated through an abstraction block: variables at or above the block are
untouched. -/
theorem occurs_absArgs_var (i y : Nat) : ∀ (k : Nat), k ≤ y →
    TermV.occurs y (absArgs k (.var i)) = (i == y)
  | 0, _ => rfl
  | k + 1, hy => by
      show TermV.occurs y (TermV.bracketOpt k (absArgs k (.var i))) = _
      rw [occurs_bracketOpt, occurs_absArgs_var i y k (by omega),
          beq_eq_false_iff_ne.mpr (show y ≠ k by omega)]
      cases i == y <;> rfl

/-- Below the target variable, each abstraction layer is a bare `K`-wrap. -/
theorem absArgs_var_ge : ∀ (k i : Nat), k ≤ i → absArgs k (.var i) = kTowerV k (.var i)
  | 0, _, _ => rfl
  | k + 1, i, hk => by
      show TermV.bracketOpt k (absArgs k (.var i)) = .app .K (kTowerV k (.var i))
      rw [absArgs_var_ge k i (by omega)]
      exact bracketOpt_not_occurs (by
        rw [occurs_kTowerV]
        exact beq_eq_false_iff_ne.mpr (show i ≠ k by omega))

/-- Abstracting the variable a `K`-tower guards yields the `S (K K)`-chain, which is NORMAL. -/
theorem normalForm_bracketOpt_kTower (m : Nat) : ∀ (j : Nat),
    NormalForm (toTerm (TermV.bracketOpt m (kTowerV j (.var m))))
  | 0 => by
      show NormalForm (toTerm (TermV.bracketOpt m (.var m)))
      show NormalForm (toTerm (if m = m then TermV.app2 .S .K .K else .app .K (.var m)))
      rw [if_pos rfl]
      exact normalForm_I
  | j + 1 => by
      show NormalForm (toTerm (TermV.bracketOpt m (.app .K (kTowerV j (.var m)))))
      have hocc : TermV.occurs m (TermV.app .K (kTowerV j (.var m))) = true := by
        show (TermV.occurs m .K || TermV.occurs m (kTowerV j (.var m))) = true
        have hself : TermV.occurs m (TermV.var m) = true := by
          show (m == m) = true
          first
            | exact Nat.beq_refl m
            | exact decide_eq_true rfl
        rw [occurs_kTowerV, hself]
        rfl
      show NormalForm (toTerm (if TermV.occurs m (.app .K (kTowerV j (.var m))) = true
        then TermV.app2 .S (TermV.bracketOpt m .K) (TermV.bracketOpt m (kTowerV j (.var m)))
        else _))
      rw [if_pos hocc]
      exact normalForm_app_S_two (normalForm_app_K normalForm_K)
        (normalForm_bracketOpt_kTower m j)

/-- **Selectors are normal**, generically: safe to duplicate, safe to ship as symbols. -/
theorem selArgs_normal : ∀ (k i : Nat), i < k → NormalForm (selArgs k i)
  | k + 1, i, hik => by
      by_cases hi : i = k
      · subst hi
        show NormalForm (toTerm (TermV.bracketOpt i (absArgs i (.var i))))
        rw [absArgs_var_ge i i (Nat.le_refl i)]
        exact normalForm_bracketOpt_kTower i i
      · have hlt : i < k := by omega
        show NormalForm (toTerm (TermV.bracketOpt k (absArgs k (.var i))))
        rw [bracketOpt_not_occurs (by
          rw [occurs_absArgs_var i k k (Nat.le_refl k)]
          exact beq_eq_false_iff_ne.mpr (by omega))]
        exact normalForm_app_K (selArgs_normal k i hlt)

-- Anchors: the two-symbol dispatch of Stages 63–75 is the k = 2 instance, and the shapes are what
-- the closed forms say.
#guard selArgs 1 0 = I
#guard selArgs 2 1 = app2 Term.S (Term.app Term.K Term.K) I
#guard selArgs 2 0 = Term.app Term.K I
#guard selArgs 3 0 = Term.app Term.K (Term.app Term.K I)
#guard (List.range 5).all (fun i => leafCount (selArgs 5 i) < 20)

