import CombinatorCalculusPlayground

open Term

-- Census over all pure-S terms with n = 1 .. maxLeaves leaves.
-- Usage: lake exe ccp [maxLeaves] [fuel]   (defaults: 8, 200)
def censusLine (fuel n : Nat) : String × List Term × List Term := Id.run do
  let mut term0 := 0  -- terminating
  let mut cyc : List Term := []
  let mut exhausted : List Term := []
  let mut maxSteps := 0
  let mut maxFinal := 0
  for t in sTerms n do
    match classify fuel t with
    | .terminating k _ =>
      term0 := term0 + 1
      if k > maxSteps then maxSteps := k
    | .cyclic _ _ => cyc := t :: cyc
    | .fuelExhausted fl =>
      exhausted := t :: exhausted
      if fl > maxFinal then maxFinal := fl
  let line := s!"n={n}: total={(sTerms n).length} terminating={term0} " ++
              s!"cyclic={cyc.length} exhausted={exhausted.length} " ++
              s!"maxSteps={maxSteps} maxFinalLeaves={maxFinal}"
  return (line, cyc, exhausted)

def main (args : List String) : IO Unit := do
  let maxLeaves := (args[0]?.bind String.toNat?).getD 8
  let fuel := (args[1]?.bind String.toNat?).getD 200
  IO.println s!"Pure-S census up to {maxLeaves} leaves, fuel {fuel}"
  IO.println "==========================================="
  let mut anyCycle := false
  let mut firstExhaustedReported := false
  for n in [1:maxLeaves+1] do
    let (line, cyc, exhausted) := censusLine fuel n
    IO.println line
    for t in cyc do
      anyCycle := true
      IO.println s!"  CYCLE FOUND: {render t}"
    if !exhausted.isEmpty && !firstExhaustedReported then
      firstExhaustedReported := true
      IO.println s!"  smallest fuel-exhausted terms (n={n}):"
      for t in exhausted.take 10 do
        IO.println s!"    {render t}"
  if !anyCycle then
    IO.println "No cycles found at any size (within fuel)."
