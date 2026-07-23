--! # The iota combinator, first-order
-- Barker's ι is classically λx. x S K — famously a ONE-combinator basis
-- for the λ-calculus. Its first-order rewrite reading is the single rule
--     ι x  →  (x Sι) Kι
-- with Sι, Kι the fixed iota-terms below (the images of S and K).
-- EPISTEMIC STATUS: iota's universality is a λ-CALCULUS (higher-order,
-- erasing) fact — external, Barker 2001-era folklore — and is NOT
-- contradicted by anything in this repository. What THIS stage settles is
-- whether the first-order reading hosts SK under the pinned Simulation
-- (Universality/Calibration.lean: it cannot — the rule strictly grows
-- terms, and SK has reduction cycles).
import CombinatorCalculusPlayground.RS

inductive IotaTerm : Type
  | iota : IotaTerm
  | app : IotaTerm → IotaTerm → IotaTerm
deriving Repr, DecidableEq

namespace IotaTerm

/-- The image of K: ι(ι(ιι)). Behaviorally K in the λ-reading. -/
def Kiota : IotaTerm := .app .iota (.app .iota (.app .iota .iota))

/-- The image of S: ι Kiota. Behaviorally S in the λ-reading. -/
def Siota : IotaTerm := .app .iota Kiota

inductive IotaStep : IotaTerm → IotaTerm → Prop
  | iota_red (x : IotaTerm) :
      IotaStep (.app .iota x) (.app (.app x Siota) Kiota)
  | appL {t t' u : IotaTerm} : IotaStep t t' → IotaStep (.app t u) (.app t' u)
  | appR {t u u' : IotaTerm} : IotaStep u u' → IotaStep (.app t u) (.app t u')

def leafCount : IotaTerm → Nat
  | .iota => 1
  | .app t u => leafCount t + leafCount u

#guard leafCount Kiota = 4
#guard leafCount Siota = 5

-- Executable leftmost-outermost reducer, mirroring Census/Eval.lean.
def stepOnce : IotaTerm → Option IotaTerm
  | .app .iota x => some (.app (.app x Siota) Kiota)
  | .app t u =>
    match stepOnce t with
    | some t' => some (.app t' u)
    | none =>
      match stepOnce u with
      | some u' => some (.app t u')
      | none => none
  | _ => none

theorem stepOnce_sound : ∀ {t u : IotaTerm}, stepOnce t = some u → IotaStep t u := by
  intro t
  fun_induction stepOnce t with
  | case1 x =>
    intro u h
    cases h
    exact IotaStep.iota_red ..
  | case2 a b _ a' hstep ih =>
    intro u h
    injection h with h
    subst h
    exact IotaStep.appL (ih hstep)
  | case3 a b _ _ b' hstep _ ih =>
    intro u h
    injection h with h
    subst h
    exact IotaStep.appR (ih hstep)
  | _ =>
    intro u h
    simp_all

def trace (fuel : Nat) (t : IotaTerm) : List IotaTerm :=
  match stepOnce t, fuel with
  | none, _ => [t]
  | some _, 0 => [t]
  | some t', f + 1 => t :: trace f t'

-- ## CENSUS-FIRST PROBES (read before proving anything in Task 5)
-- The plan's central prediction: every iota_red strictly GROWS leaf count
-- (1 + |x| becomes |x| + 9), so first-order iota can never erase, and the
-- λ-level "Kι a b reduces to a" behavior is unreachable as first-order
-- reachability. These guards check that prediction empirically BEFORE any
-- proof effort. IF ANY PROBE FAILS: STOP — do not "fix" it; report
-- DONE_WITH_CONCERNS with the failing trace. The Task 5 plan would be
-- wrong and the stage must re-plan.

-- Sizes strictly increase along an observed trajectory of Kι ι ι.
#guard (let tr := trace 60 (.app (.app Kiota .iota) .iota)
        (tr.zip tr.tail).all fun (a, b) => leafCount a < leafCount b)
-- In particular Kι ι ι never reaches its first argument ι.
#guard (let tr := trace 60 (.app (.app Kiota .iota) .iota)
        tr.all (· != IotaTerm.iota))
-- And Sι ι ι ι never reaches (ι ι)(ι ι) — the S-behavior target.
#guard (let tr := trace 60 (.app (.app (.app Siota .iota) .iota) .iota)
        tr.all (· != IotaTerm.app (.app .iota .iota) (.app .iota .iota)))
-- The trajectory genuinely runs (never normalizes within fuel): 61 entries.
#guard (trace 60 (.app (.app Kiota .iota) .iota)).length = 61

end IotaTerm

/-- First-order iota as a rewriting system. -/
def RS.Iota : RS := ⟨IotaTerm, IotaTerm.IotaStep⟩
