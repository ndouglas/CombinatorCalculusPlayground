--! # Combinator Calculus Playground
-- We define the S and K combinators, the rules for how they simplify, and what
-- it means to take one or many simplification steps.

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

-- `#check` asks Lean "what type is this?" — a sanity check, not real code.
#check (app S K) -- Term

-- `def` defines a function or constant. `app` only takes two arguments, so
-- `app2` and `app3` are shortcuts to avoid deeply nested parentheses.
def app2 (f a b : Term) : Term :=
  app (app f a) b

def app3 (f a b c : Term) : Term :=
  app (app (app f a) b) c

#check app2 S K K -- Term

-- The identity combinator: I x = x. Built from S and K because S K K x
-- reduces to K x (K x), which reduces to x. We haven't *proven* that yet —
-- this just defines I as the expression S K K.
def I : Term :=
  app2 S K K

#check I -- Term

-- `#eval` actually computes and prints the value, unlike `#check` which only
-- reports the type. Here we can see I is stored as nested applications.
#eval I -- Term.app (Term.app (Term.S) (Term.K)) (Term.K)

-- Another `inductive`, but this time it defines a *relationship* between two
-- Terms, not a data structure. `Step a b` is a Prop (a proposition) meaning
-- "term `a` reduces to term `b` in exactly one step." The four constructors
-- are the only four ways a step can happen:
inductive Step : Term → Term → Prop
  | K_red (x y : Term) :
      Step (app2 K x y) x
      -- K grabs two args and returns the first: K x y → x
  | S_red (f g x : Term) :
      Step (app3 S f g x) (app (app f x) (app g x))
      -- S distributes the third arg to the first two: S f g x → (f x) (g x)
  | appL {t t' u : Term} :
      Step t t' → Step (app t u) (app t' u)
      -- If the left side of an application can step, so can the whole thing
  | appR {t u u' : Term} :
      Step u u' → Step (app t u) (app t u')
      -- Same idea, but for the right side

open Step

-- `infix` lets us write `a ⟶ b` instead of `Step a b`. The `50` is the
-- precedence (how tightly it binds compared to other operators).
-- We use `⟶` (\longrightarrow) instead of `→` to avoid shadowing Lean's
-- built-in function arrow.
infix:50 " ⟶ " => Step

#check (K_red (x := S) (y := K)) -- Step.K_red S K : Step (app2 K S K) S

-- `Steps` is zero or more reduction steps — the "can eventually become"
-- relation. Like `Step` it's a relationship (Prop), not data.
-- A path is either standing still (`refl`) or taking one step then a path
-- (`tail`).
inductive Steps : Term → Term → Prop
  | refl (t : Term) :
      Steps t t
      -- Zero steps: any term trivially reduces to itself
  | tail {t u v : Term} :
      Step t u → Steps u v → Steps t v
      -- One step from t to u, then a path from u to v, gives a path from t to v

-- The `*` is the conventional "zero or more" symbol, like in regex.
infix:50 " ⟶* " => Steps
