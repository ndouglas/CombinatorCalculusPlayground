# CombinatorCalculusPlayground

Attempting to kill five or six birds with one stone:
- learn and practice Lean
- deepen intuitions about computability
- determine whether S combinator is universal
- dispel a little ennui
- appear intelligent

## Where to look

**[STATUS.md](STATUS.md) — what is actually settled**, organised by the four
goals of the design spec. Start there; the two files below are chronological and
long.

- [CONJECTURES.md](CONJECTURES.md) — the ledger. Every claim with a status
  (`open` / `probed` / `weakened` / `external` / `proved` / `refuted`), plus a
  materiality and a prior-art line.
- [LAB_NOTEBOOK.md](LAB_NOTEBOOK.md) — the working notebook, one entry per
  session: what was attempted, what Lean resisted, what the estimates got wrong.
  A first-class deliverable per the spec, not a diary.
- [docs/superpowers/specs/](docs/superpowers/specs/) — the design spec, which is
  the authority on what this program is for.
- **[The Clockmaker's Shop](https://ndouglas.github.io/CombinatorCalculusPlayground/)**
  — a visual essay on what `{S,C}` reduction looks like, with both figures computed
  live in the browser by an engine the test suite checks against the Lean.

Zero dependencies (no Mathlib, no Batteries). No `sorry`, no `native_decide`, no
`Classical.choice`. `lake build` checks everything, including ~175 `#guard`s.

## The short version

Three of the spec's four goals are done, closed, or ongoing-by-design.
Reachability between pure S-terms is decidable. No one-combinator, single-rule
first-order system of any arity can host SK. Whether S alone is universal is
**not** resolved here — what is established is where the question lives: *if S
alone is universal, its encoding must be non-injective or must fail to preserve
reduction paths.*
