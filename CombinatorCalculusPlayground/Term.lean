--! # Terms of combinatory logic
-- We define the S and K combinators and function application. This is the
-- raw syntax; how terms *reduce* lives in Step.lean.

-- `inductive` means "here are ALL the ways to build this thing, and nothing
-- else." A Term is like a LEGO set with exactly three kinds of brick.
--
-- `deriving Repr, DecidableEq` asks Lean to auto-generate the ability to print
-- Terms (`Repr`, used by `#eval`) and compare them for equality (`DecidableEq`).
inductive Term : Type
  | S : Term                   -- The S (substitution) combinator: S f g x = f x (g x)
  | K : Term                   -- The K (constant) combinator: K x y = x
  | app : Term → Term → Term   -- Sticks two terms together (function application)
deriving Repr, DecidableEq

-- `open` lets us write `S` instead of `Term.S`, etc. Just a convenience.
open Term

-- `def` defines a function or constant. `app` only takes two arguments, so
-- `app2` and `app3` are shortcuts to avoid deeply nested parentheses.
def app2 (f a b : Term) : Term :=
  app (app f a) b

def app3 (f a b c : Term) : Term :=
  app (app (app f a) b) c

-- The identity combinator: I x = x. Built from S and K because S K K x
-- reduces to K x (K x), which reduces to x. Proven in Step.lean (`I_reduces`).
def I : Term :=
  app2 S K K

-- ## Measures
-- Terms are binary trees; a tree with n leaves always has n - 1 internal
-- `app` nodes, so leaf count is the only size measure we need.

-- Number of combinator leaves (S's and K's) in a term.
def leafCount : Term → Nat
  | .S => 1
  | .K => 1
  | .app t u => leafCount t + leafCount u

-- Length of the left spine: how many arguments the head combinator has
-- been applied to. `S a b c` has spine length 3.
def spineLength : Term → Nat
  | .app t _ => spineLength t + 1
  | _ => 0

-- Standard combinator notation: application is left-associative and
-- implicit, so only right-nested applications need parentheses.
def render : Term → String
  | .S => "S"
  | .K => "K"
  | .app t u =>
    match u with
    | .app _ _ => render t ++ " (" ++ render u ++ ")"
    | _ => render t ++ " " ++ render u

-- `#guard` is a compile-time test: the build fails unless the expression
-- evaluates to `true`.
#guard leafCount I = 3
#guard spineLength I = 2
#guard spineLength S = 0
#guard render I = "S K K"
#guard render (app S (app K K)) = "S (K K)"
