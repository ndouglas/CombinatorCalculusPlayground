# Conjectures

Census-generated claims, each with a status:
**open** / **proved** (link the theorem) / **refuted** (link the counterexample).
Census methodology: leftmost-outermost reduction (`stepOnce`), which is the
normalizing strategy; "exhausted" verdicts are fuel-outs, NOT divergence proofs.
As of Stage 1, SK reduction is proven confluent (`confluence`,
`Confluence.lean`) with unique normal forms (`nf_unique`), and
`normalize` is certified on both ends (`normalize_sound`,
`normalize_normal`): when the census reports a normal form, that term IS
the unique normal form of its input. (The classifier's step-counting and
cycle bookkeeping remain unverified census tooling.)

Runs behind this file (all `lake exe ccp <maxLeaves> <fuel>`, pure-S terms only,
no `K` leaves ever appear — `sTerms` enumerates over `Term.S` alone):

- `ccp 12 200` — full census, n = 1..12, fuel 200. (0.48s through n=8, ~10s
  through n=10, ~50s through n=11, completed n=12 in well under 10 minutes.)
- `ccp 9 1000` — fuel raised to 1000 at small n, to probe fuel-sensitivity of
  the exhausted-term growth rate. Ran 5 minutes, reached n=7 fully and stalled
  partway through n=8 (killed at the 5-minute mark, no full n=8/n=9 line).
- `ccp 10 1000` — attempted per the task brief; killed at the 10-minute mark
  with **zero** flushed output (stdout is fully block-buffered when redirected
  to a file, not a tty; the process never got far enough for even n=1's line
  to reach the file before it was killed). Reducing fuel to 200 (above) is
  what actually completed n=10 (and beyond). See LAB_NOTEBOOK.md for the
  runtime/tooling story.

## C1: Smallest non-normalizing pure-S term — status: open
Census (fuel N=200) finds all S-terms with ≤6 leaves normalize; at 7 leaves,
2 of 132 terms exhaust fuel. Candidates (rendered, standard combinator
notation, left-associative application):

```
S S S (S S) S S
S (S S) S S S S
```

Conjecture: `S S S (S S) S S` (equivalently, by the same evidence,
`S (S S) S S S S`) has no normal form under leftmost-outermost reduction —
i.e. `stepOnce` never reaches `none` from it.

Supporting (not proving) evidence: raising fuel from 200 to 1000 at n=7 does
not let either candidate normalize — instead the final term size at cutoff
explodes from 120112 leaves (fuel 200) to 25740409924 leaves (fuel 1000), a
~5-order-of-magnitude increase for a 5x fuel increase. That is consistent
with genuine unbounded/explosive growth along the trajectory, not with a
near-normal-form plateau that a little more fuel would resolve — but it
remains fuel-exhaustion, not a divergence proof.

## C2: No proper cycles in pure-S reduction — status: open
No S-term with ≤12 leaves revisits a previous term (leftmost-outermost,
fuel 200). Confirmed at every n = 1..12 (`No cycles found at any size (within
fuel).` printed by every run in this file's data). Conjecture: pure-S
leftmost-outermost trajectories never cycle. (NOTE: cycle-freedom under ALL
strategies is a stronger, separate claim; this census only ever runs
leftmost-outermost.)

## C3: Growth-pattern regularities observed — status: open
Two observations from the fuel=200, n=1..12 run:

1. **Head shape of the smallest exhausted terms.** Both n=7 candidates are a
   head `S` applied to exactly 5 arguments (`spineLength` 5) — two more than
   the 3 arguments an `S`-redex needs to fire. (`S S S (S S) S S` = `S`
   applied to `S, S, (S S), S, S`; `S (S S) S S S S` = `S` applied to
   `(S S), S, S, S, S`.) Sample size is only 2 terms, so this is a weak
   signal, not yet checked against the fuller n=8 exhausted set (41 terms;
   this census run does not print more than the first exhausted size's
   candidates, capped at 10 — see `Main.lean`'s `censusLine`).

2. **`maxFinalLeaves` plateaus once n ≥ 10 (fuel fixed at 200).** The largest
   final size any fuel-exhausted trajectory reaches, per n:

   | n  | maxFinalLeaves | maxSteps |
   |----|----------------|----------|
   | 7  | 120112         | 15       |
   | 8  | 390363         | 15       |
   | 9  | 2849113        | 86       |
   | 10 | 88163896       | 109      |
   | 11 | 88163897       | 173      |
   | 12 | 88163898       | 174      |

   From n=10 to n=12 `maxFinalLeaves` increases by exactly 1 leaf per unit of
   n, while at fixed fuel it had grown by roughly 30x from n=9 to n=10.
   Conjecture (tentative, unexplained): once n is large enough, the
   trajectory that saturates 200 fuel steps is essentially the same
   explosive expansion regardless of which (n-leaf) starting term achieves
   it, with the extra starting leaves surviving un-reduced off to the side —
   this is an observation about the fuel=200 cutoff, not a claim about
   unbounded fuel behavior, and it is not yet explained by any proved lemma.
