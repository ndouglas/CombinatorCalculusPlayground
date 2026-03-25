inductive Term : Type
  | S : Term
  | K : Term
  | app : Term → Term → Term
deriving Repr, DecidableEq

open Term

#check (app S K) -- Term

def app2 (f a b : Term) : Term :=
  app (app f a) b

def app3 (f a b c : Term) : Term :=
  app (app (app f a) b) c

#check app2 S K K -- Term

def I : Term :=
  app2 S K K

#check I -- Term

#eval I -- Term.app (Term.app (Term.S) (Term.K)) (Term.K)

inductive Step : Term → Term → Prop
  | K_red (x y : Term) :
      Step (app2 K x y) x
  | S_red (f g x : Term) :
      Step (app3 S f g x) (app (app f x) (app g x))
  | appL {t t' u : Term} :
      Step t t' → Step (app t u) (app t' u)
  | appR {t u u' : Term} :
      Step u u' → Step (app t u) (app t u')

open Step

infix:50 " → " => Step

#check (K_red (x := S) (y := K)) -- Step.K_red S K : Step (app2 K S K) S

inductive Steps : Term → Term → Prop
  | refl (t : Term) : Steps t t
  | tail {t u v : Term} : Step t u → Steps u v → Steps t v

infix:50 " →* " => Steps
