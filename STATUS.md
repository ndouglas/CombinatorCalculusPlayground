# Status, by spec goal

The stage-by-stage record lives in `CONJECTURES.md` (the ledger) and
`LAB_NOTEBOOK.md` (the working notebook). Both are chronological and now run to
several thousand lines, which means neither answers the question "what is
actually settled?" This file does, organised by the four goals of
`docs/superpowers/specs/2026-07-23-s-combinator-research-program-design.md`.

Everything below is machine-checked in Lean 4 with **no dependencies** (no
Mathlib, no Batteries), **no `sorry`**, **no `native_decide`**, and **no
`Classical.choice`**. Axiom footprint is `[propext, Quot.sound]` or less
throughout — `Quot.sound` rides core tactic machinery (`omega`/`simp`), a trail
inherited since Stage 0. As of Stage 76 this claim is **build-enforced**:
`Audit.lean` pins the headline theorems' exact footprints with `#guard_msgs`,
so any drift fails the build.

At time of writing (Stage 208 review): 36 modules, ~1,231 theorems, 437
build-enforced `#guard`s plus 241 `#guard_msgs`-pinned axiom footprints,
~25,400 lines of Lean, zero warnings, 478 commits. The run stands at 90
consecutive autonomous stages (119–208). Since the Stage 170 review the
program delivered: the persistence campaign's full resolution (the
persistent reader, the parking orbit, the fate machine and its universal
certificates); the floor ladder to n=14 (excess 12 → 44 → 69 → 86); the
frame ISA — READ, CALL, COMPILE, FETCH, BRANCH, EXPRESS, WRITE — with
the parity law C9 PROVED for all inputs; the reproduction stack (gene,
dynasty, tape: machines beget machines, words read one symbol per
generation); the counting chain (bounded odometers, axiom-free); and
two calibrated frontier questions — bounded intermediates and C10, the
regrowth question. Since the Stage 130 review the run
continued autonomously through Stage 159 (41 consecutive stages), delivering:
the FRONTIER EQUIVALENCE at all four ladder rungs (decidable ⟺ computably
bounded intermediates, generic engine + kits) with pinned floors and the
forced-march toolkit; the GLIDER (deterministic, normal-form-free, its whole
trajectory certified) and the COUNTER (an eight-leaf machine with fixed
member registers and a √step-height tower — spine-level data, probe-read);
and the FOLD CAMPAIGN: cell synthesis in one fire, the queue cell (C7
registered and refuted inside two stages), the biodegradable architecture
(zero-residue FIFO traversal — machinery built from the self-consuming
combinator), the fuel law and fuel blindness, the generation cycle (a tag
generation IS a `{S,C}` cycle), the attractor, the growth step, the
cell-armed pop (the arm is the program), and the Q-family's complete pinned
dynamics. The campaign's residue is ONE design problem, now named: THE
NONDESTRUCTIVE-READ PROBLEM (C8's kernel) — tag hosting lacks a marker that
survives its own firing; register hosting lacks a test that spares its
operand; both are "read without consuming" against non-erasure's grain.
Every mechanism beneath that problem is a pinned, axiom-free theorem.
Stages 161–164 then took the kernel apart: one-bit machines are generic
(66 pairs at n=8, 986 at n=9 — a single embedded `C ↔ C C` flips counter
↔ glider, but only at build time); the LOCKSTEP LAW (149/149 two-tower
machines at n ≤ 9 share one clock — copies are born equal); and finally
THE REGISTER DEMO (`sc_read_bitC`/`sc_read_bitB`, axiom-free, pinned):
`reg reg S (C C)` with `reg = S bit` — the bit alone selects between two
distinct normal forms, each still CONTAINING its application-ready
register. The nondestructive read EXISTS: read, diverge, survive. And Stage 165
pinned THE LATCH (`scLatch_run_C`/`_B` + the mode pulses, axiom-free):
an eight-leaf machine that STASHES a register copy (fire one), CONSULTS
the working copy (fire ten), and diverges into bit-dependent perpetual
five-beat pulses that carry the stashed register forever — the
Stage-163 paper design found executing in the wild, verified
fire-by-fire. `{S,C}`'s first pinned control primitive: a set-once
latch with a reusable source bit. Stages 166–167 then finished the
primitive set: the CONSULTATION LOOP (`S C C (S S C) scDup` consults its
register TWELVE times in 52 forced fires, register alive throughout —
kernel-certified via march-replay and the structural consultation
detector) and the WRITE (`sc_reg_write`, axiom-free: registers are
minted, not mutated — one S-fire with prefab `S S`). ALL FOUR CONTROL
PRIMITIVES of the nondestructive-read problem now exist as pinned or
build-enforced mechanisms: read, latch, looped read, write. C8's
remaining content is COMPOSITION alone — and Stages 168–171 built its
chassis: word-length registers already implement dec/test/inc (pop =
`scRun_step`, zero-test = marker promotion, inc = the growth step), and
TWO CLOCKS EXIST BY DESIGN (`sc_two_clocks`/`sc_independent_registers`,
axiom-free, pinned: member-held configurations reduce independently —
the lockstep law binds single-spine marches, not architectures, since
reachability quantifies over all schedules). Stage 172 then pinned THE
COUPLED ZERO-TEST (`sc_ztest_zero`/`sc_ztest_nonzero`, axiom-free):
registers as inert words, the branch read off the word's own head shape
— empty-marker versus cell — nondestructively, registers intact in both
distinct outcomes. The composition ledger is COMPLETE AS PARTS: dec
(`scRun_step`), test (the zero-test), inc (the growth step), four
control primitives, independent clocks, the branch. Stage 173 then pinned
TEST-AND-DECREMENT itself (`sc_testdec`, axiom-free): sixteen fires from
the nonzero register to a state carrying the DECREMENTED, RE-GUARDED
register, with marker provenance certified (`S S` dye, machinery-free by
`#guard` — three genuine machines out of 48 naive hits under the
provenance null). The Minsky HALF-STEP is a theorem — and Stage 174
proved IT CYCLES (`sc_testdec_twice`, axiom-free: the same machine takes
the two-cell register through the `#guard`ed intermediate to the doubly-
decremented register, twenty-six fires, marker provenance intact; the
Lean assembled programmatically from the trace). Stage 175 closed the seam
survey: the cycle machine is a BOUNDED COUNTER-READER (registers 0/1/2
reach unique, distinct normal forms — value-dependent halts, closures
complete), and the composition's sole remainder is THE PERSISTENCE
PROBLEM (C8-final): a machine that outlives its own step. The quine, the
constructor gap, and loop persistence were one wall met from three
sides — and Stage 176 breached it for read-only state: THE PERSISTENT
READER (`scReader_period`/`_step`/`_unbounded`, axiom-free, pinned). The
front `S P (C P) (C r)` reproduces itself VERBATIM every seven fires,
emitting one accounted junk block, with its register consulting twice
per period (#guarded: forced march, consultation count, presence); the
period lifts to every generation by congruence. A machine that outlives
its own step, unboundedly, while interacting with its state — found
inside the Stage-166 consultation loop by periodicity analysis. Stages 177–178 gave
the writer its final form: persistence is PARAMETRIC
(`sc_pulse_parametric` — five fires, any cargo, pinned), the reader's
state is its own engine (the consultation fires mint the next front),
and machines write FORWARD-ONLY — junk re-enters the fire zone only by
burning down to it. The writing reader is therefore a GROW/BURN
ALTERNATOR: Stage 116's boustrophedon, once an obstacle description,
returns as the blueprint — grow-phase emits computed junk (the reader's
mechanics), burn-phase re-reads it (the biodegradable machinery), the
carry rides parametric persistence. Every phase-mechanism is pinned; the
alternator is the last composition — and Stage 179 located its final
spec: THE JUNK IS STORAGE. The reader's junk blocks are C-headed
register complexes (pure-C junk is probe-dead: duplication-driven
persistence necessarily copies its engine into its junk) — the reader
appends one stored register per period, a write-only log; the burn
phase is the read head; a FUEL TOWER is the missing trigger that ends
the grow phase and burns the front into its own storage. Reader (176) +
fuel (137) + burn (148): three pinned phenomena, one splice. And Stage
180 solved persistence at the OTHER extreme: THE PARKING ORBIT
(`scOrb`, 21 leaves) is a forced period-5 limit cycle — inescapable,
kernel-checked — whose cargo slot is pure congruence, so any state
rides it verbatim forever at constant size (`sc_park_forever`), and a
9-leaf reader head parks an `S S bit` register on it in sixteen fires
with exactly one consultation, storing THE BIT IN THE PHASE
(`scPark_entry_C/CC`: phase 0 vs phase 4, equal wall-clock). Stage 182
closed the gap between the two persistence solutions with THE FATE
MACHINE (`scFate bit`, 12 leaves): bit `C` drops onto a period-7
bounded cycle that CONSULTS its register once per lap forever (the
duplicating fire re-mints the consumed register copy — regeneration,
pinned; runs of every length via `scFate_runs`), while bit `C C` sends
the SAME machine to a kernel-checked normal form in 36 fires
(`sc_fate`): the register's content decides whether the machine's
future is finite. Stage 183 made the halt half UNIVERSAL via the new
RANKED-CLOSURE certificate (`scRanked_bound` + the emitted 231-state
height-graded space): no schedule exceeds 36 fires — sharp, the
leftmost path reaches it — and every dead end is `scFateNf`
(`sc_fate_universal`), the program's first pinned
termination-of-all-paths result. Stage 184 made termination COMPOSE:
the pair chassis is inert, so member walls ADD (`scPair_bounded`) and
the two-register pair has four pinned futures (`sc_four_fates`: one C
bit = immortal; two CC bits = double normal form behind a sharp 72-fire
wall) — 53,361 virtual states handled by four lemmas, no product
space. Stage 185 pinned the campaign's outer boundary, axiom-free:
BITS ARE SOURCES (`sc_bits_are_sources` — every fire yields a double
application, so nothing ever reduces TO an atom or to `C C`): register
contents are inputs forever, outputs never, and fate in {S,C} is
decided strictly by initial conditions. The constructive complement,
`sc_relay_fates`/`sc_relay_wall`: the assembler `S S C M` houses any
machine with its shadow in one fire, and the housed halt dies behind a
compositional 73-fire wall. Stage 186 sealed the architecture question:
THE CHASSIS ISOLATES (`sc_pair_reachable_iff` — pair reachability is
exactly the product of member reachabilities, an iff; the housed shadow
drifts free, `sc_shadow_drifts`). Composition of certificates: yes.
Communication: never through the holder — only through fires, where the
cell-synthesis line lives — and Stage 188 pinned that channel in use:
METABOLIC ASSEMBLY (`sc_metabolic_assembly`, axiom-free): three dead
cells burn, the freed `S S` minter executes on the freed cargo, and
seven fires produce `S B (S S B)` — the chassis housing the cargo
beside its own minted register. The first producer→consumer handoff. And Stage 189 closed the loop:
scFate is verbatim a POP PRODUCT (head cell `S (S scDup)`, arm cell
`S S b`, cargo cell `C C`), so THE FATE MACHINE ASSEMBLES ITSELF from
three dead cells in six fires (`sc_fate_assembly`, axiom-free), with
the full dead-cells-to-fate pipeline schedule-universal via a second
ranked certificate (237 states, wall 42 = 6 + 36,
`sc_fate_assembly_universal`) and nested housing via
`sc_assembly_line`. Construction chooses fate; computation never does. Stage 190 widened
the switch to a spectrum: THE FRAME TRICHOTOMY (`sc_frame_trichotomy`
— `scFrame r = S (S scDup) r (C C)`, with `scFate b = scFrame (S S b)`
by `rfl`): register `C` halts behind a forced 11-fire universal wall,
`C S` rides a period-8 orbit forever inside nine terms, `S S S` grows
without bound on a period-7 front with exact size law 15 + 5n. HALT,
ORBIT, EXPLODE — one 8-leaf head, futures selected by register shape
(census: 1,168 / 336 / 1,661 over all registers ≤ 6 leaves). And Stage
191 delivered the program's first HOSTED PREDICATE (`sc_parity_hosted`):
the unary numeral `C^k S` in the frame HALTS for even k (11 + 2k fires)
and ORBITS FOREVER for odd k (period 7 + k) — parity decided by
eternity, pinned for k = 0..7, probe-verified to k = 10, and Stage 192
PROVED the all-k law (`sc_frame_parity_law`, conjecture C9 closed in
one stage): the prelude is register-universal (nine fires to the
triple `M M M`, axiom-free), `C` is flip (one constructor per strip),
and the two parametric closes give — for EVERY k — a normal form in
11 + 4j fires when k = 2j, and the N-tower orbit `Φ = M N₁ N₂` of
period 2j + 8 when k = 2j + 1. An infinite input family whose parity
is decided by eternity: the program's first complete hosting theorem.
Stage 193 added the second instruction: THE WRAPPER ISA
(`sc_frame_handoff`, axiom-free) — thirteen fires take the frame on
`W r` to `r X X`: two C's mean CALL, and the register becomes the
program (executing `S` halts, `sc_frame_shield`; executing the
duplicator orbits forever, `sc_wrapper_isa`). Registers are data AND
code — read by strips, called by handoff. Stage 194 completed the
triad: THE OMEGA INSTRUCTION (`sc_frame_omega`, axiom-free) — the
wrapper word `W·C·W` takes the frame to naked self-application `r r r`
in thirty fires, every register; at the duplicator the output is
verbatim the generation-loop seed (`sc_omega_to_loop`: frame → ω → loop
→ eternity, all axiom-free). READ, CALL, COMPILE — and Stage 195
added FETCH (`sc_addressed_fetch`, zero new fires — pure composition):
for register `C^m · p` the frame dispatches by address parity — even
puts the payload in control, odd parks it and runs dead material. The
numeral is an instruction pointer — and Stage 197 delivered SEQUENCING:
THE GENE (`scGene t`, 14 leaves — frame head in one cell, the child's
register in the other). `sc_reproduction`: twenty-nine fires take the
addressed parent to the assembled child `FH t t`, the gene choosing the
child's register; at `t = W` the child is verbatim `scFrame scW`
(`sc_machines_beget`) — MACHINES BEGET MACHINES, riders as stack. And
Stage 198 delivered ITERATION: verbatim quines are impossible (single-
slot genes force register = cargo) but the three-cell gene `scGene2`
gives THE LINEAGE LAW (`sc_lineage`, 21 fires, parametric — parent of
`scGene2 q` begets parent of `q`) and THE DYNASTY (`sc_dynasty`: every
generation-n ancestor reduces to a term carrying the founder in head
position). Machines beget machines to any depth — and Stage 199 added the fork:
THE BRANCH (`sc_branch_even/odd`, zero new fires): payload `C^k y z`
gives control to `y` or `z` by the numeral's parity, and
`sc_conditional_dynasty` splices it into reproduction — the machine
tree forks on a numeral. ISA: READ, CALL, COMPILE, FETCH,
EXPRESS/ASSEMBLE, BRANCH. And Stage 200 BUILT THE TAPE (`sc_tape_run`,
induction over every word and payload): a word over {even, odd} encoded
as nested branch-genes — linear size — is read ONE SYMBOL PER GENERATION
(22 fires each): even symbols beget the next machine (the gene fires
anywhere, `sc_gene_anywhere`, axiom-free), odd symbols park the head
(`sc_tape_stop`), and all-even words deliver the founder machine after
the whole tape is consumed. Stored program, instruction pointer,
fetch-decode-execute, reproduction, halting — all pinned. And Stage 201 found WRITE-BACK: THE SUCCESSOR
(`sc_successor`, axiom-free) — `S_red` with middle argument `C` is the
calculus's only C-chain extender, minting the incremented numeral
beside any continuation (the routed variant delivers it in operator
position, ready to branch). The tape reads, the successor writes, the
gene copies, the branch decides: tag hosting's parts list is complete.
Stage 204 closed the frame's instruction algebra (all thirty
wrapper-words ≤ 4 mapped; two new pinned instructions — the cheap omega
`C·W`, self-application in 17 fires, and the successor call `W·C·W·C`:
`r (C r) (C r)`, the register executed on its own increment).
Stage 202 mapped the integration wall and registered it: C10, THE
ODOMETER QUESTION — self-application (omega) plus the successor does
NOT yield a self-incrementing counter (154k bodies, zero), consistent
with the calculus's conservation laws; hosting so far pre-builds its
recursion (dynasty depth, tape symbols), and whether {S,C} admits any
live self-modifying counter is now the program's sharpest open
question — and Stage 205 calibrated it as hard from BOTH sides:
~245k configurations across five architectures (including the
successor-call route) find no odometer, while the S-farm observation
(S-stock is duplicable, as the persistent reader demonstrates) blocks
every counting-invariant refutation. C10 sits at equilibrium beside
bounded intermediates as the program's twin frontier questions — and
Stage 206 gave it final form: THE COUNTING CHAIN (`sc_bounded_odometer`,
axiom-free) delivers `C^(k+n) S` to any continuation in 2n fires at
three leaves per increment, so counting is FREE in {S,C}; C10 is
exactly the regrowth question — can a machine refuel its own prefab
stock? Stage 209 fixed the search language: odometers are CONTEXT
FAMILIES (the reader's front holds five register copies), and the
corrected family sweep finds zero through seven-leaf contexts (3,337,323
families through eight leaves — the completed sweep — all zero) — while the reader's
consultation does mint `C²r` each period, its unwrapping is
load-bearing for front restoration. Stage 211 opened the invariant
program with THE SPINE DICHOTOMY (`sc_spine_dichotomy`, [propext]):
every step is a MUTATION (one argument steps in place) or a CALL (the
first argument becomes the program) — reduction is a call-stack
discipline whose return stack is the leftmost branch, all five walls
share one explanation, and C10 becomes: can a machine place an
incremented copy of its own address into its own return stack? Stage
212 iterated the dichotomy (`sc_head_provenance`, [propext]): over any
reduction the head either survives or is supplied by a first argument
of a reachable state — no third source of control exists. Provenance
is pinned; C10 is now an address-flow question on supply chains — and
Stage 213 added WALL SIX, the first quantitative one: NUMERALS ARE
SOURCES at every depth (`sc_numerals_are_sources`, no step ever
produces one) and the NUMERAL SPEED LIMIT (`sc_numeral_speed_limit`)
caps address advance at one depth per fire. Any odometer is
fire-paced; C10's endgame is a lap-budget accounting: fires per period
versus mints plus prefab regrowth (analyzed: neither depth-counting
nor atom-counting closes it — a positional invariant is required).
Stage 214 added the dichotomy's positional corollary, THE CARGO LAW
(`sc_cargo_law`, [propext]): the rightmost spine argument survives
every fire — displaced only by a BOTTOM CALL at arity exactly three.
FIFO is the geometry of the spine, and the tag step's architecture is
now forced: burn down, bottom-call the production, rebuild. Stage 215
unified the mint family as THE STAMP (`sc_stamp`/`sc_cell_mint`,
axiom-free): the S-fire's g-seat stamps the x-seat with any prefab —
`C` mints successors, `C C` mints cells. The identity-tag rotation is
three-quarters pinned (read half: the Stage 148 traversal; write half:
the cell mint); what remains is THE WALK that folds stamped cells back
into a word chain — and Stage 216 recorded its resistance: no
parametric walker within nine-leaf heads (a nine-leaf phantom was
caught by the placeholder discipline), and the visible convergence that
THE WALK AND C10'S REGROWTH ARE THE SAME SPECIES OF PROBLEM: progress
through material interleaved with preservation of machinery — the
interleaving the six walls constrain. Stage 217 made it seven: THE
SUFFIX LAW (`sc_suffix_law`, [propext]) — argument suffixes beyond the
call frame survive every step; products never overtake surviving
material. The tag step is forced onto the scBWord chassis and its
remaining freedom is one dimension: the arm supply — which Stage 218
CLOSED with the PASS-THROUGH CELL (`sc_passthrough`, axiom-free):
`C M W · A ⟶ M A W`, the arm conserved, one fire per symbol
(`sc_cword_run` — optimal, versus the old chassis's seven fires and an
arm consumed per symbol), symbols emerging in rotation order. The
identity tag machine lacks exactly one mechanism: the loop closure —
and Stage 219 recorded its resistance (six-leaf repackers are
symbol-dependent phantoms; parametric repacking needs a GROWING
prefab, which fixed shapes cannot supply). Loop closure, the walk, and
C10's regrowth are one problem in three costumes: output-paced
machinery growth — solved in this calculus only by the reader's
growing front. The recorded suspicion: the tag machine is a
reader-variant, not a cycle. Stage 220 certified the suspicion's
foundation: THE BURN (`sc_junk_ignition`/`sc_junk_is_cell`, axiom-free)
— the reader's junk blocks are live pass-through cells that ignite on
each other, re-exposing and CONSULTING their stored registers in four
fires; probe-traced, the stream metabolizes (second-order cells,
reader-like growth). Grow and burn are two behaviors of one junk
medium, and the alternator, the tag loop closure, and C10's regrowth
all now live there: the program's central object is the medium. Stage 221 took its pulse:
the burn is a PERIOD-12 GROWTH WAVE (+67 leaves per period, no verbatim
front — periodic drift, a fourth recurrence kind beyond the toolkit's
verbatim/cyclic/graded three), and pinning it wants C9-style trace
templates. At the 103-stage mark the run stands: seven walls (five as
theorems), the ISA complete, hosting three-quarters built, the floor
ladder at four rungs, C9 proved, C10 hard-open, one medium under it
all. Behind the alternator stand tag/Minsky hosting,
undecidability, and the frontier equivalence's negative resolution. Since the Stage 114 review, one autonomous run
(Stages 119–129) delivered two threads: the DECIDABILITY KIT for `{S,C}`
(confluence and unique normal forms transported from the SK Takahashi
template; normal forms characterized; bounded reachability DECIDABLE with a
verified successor function; exact C-fragment conservation; the two-sided
speed limit) and the MEMBER CALCULUS made machine-checked theory
(`SCMembers.lean`: the member-action characterization, count monotonicity and
the squeeze, the crossing configuration, the last-variable invariant, the
funnel, stuckness-is-forever) — culminating in **`scv_no_pair`** (Stage 129):
ARRIVAL-ORDER PAIRING IS IMPOSSIBLE IN `{S,C}`, closing a conjecture open
since Stage 103 and turning its census bound into a theorem at every machine
size. That is the program's first standing conjecture closed from the hosting
thread's negative side, and it hardens the interrogation wall: `{S,C}` hosts
data, branching, and self-regenerating traversal, but no machine can
reorder-and-apply its arguments selector-style. Earlier milestones (Stage 114
review and before): the acyclicity ladder complete with the h-/w-cycle
classification, the hosting stack through `tailInSC` and the one-tag-step
(axiom-free throughout).

---

## Goal 1 — a self-contained formalization deep enough to state the prize question precisely

**Status: DONE.**

| Result | Theorem | Where |
|---|---|---|
| SK reduction is confluent, with unique normal forms | `confluence`, `nf_unique` | `Confluence.lean` |
| `normalize` certified on both ends | `normalize_sound`, `normalize_normal` | `Census/Eval.lean` |
| K-freeness closed under reduction; no erasure | `KFree.of_step`, `leafCount_le_of_steps` | `SFragment.lean` |
| K-free normal forms are exactly the spine-≤2 shapes | `SNF_iff` | `SFragment.lean` |
| {S,K} combinatory completeness | `combinatory_completeness` | `Bracket.lean` |
| ...restated in the same language as the refutations | `combinatory_completeness_RS` | `Universality/Calibration.lean` |
| Abstract rewriting systems, with SK / pure S / tag instances | `RS`, `RS.SK`, `RS.PureS`, `RS.Tag` | `RS.lean` |

The prize question is stated precisely as a property of a pinned encoding class
over abstract rewriting systems — see Goal 2.

---

## Goal 2 — a machine-checked taxonomy of universality definitions

**Status: DONE — taxonomy built, calibrated in both directions, and the open
item CLOSED (Stages 75–79): a genuine tag system is hosted by a machine-checked
`Simulation`, generalised to EVERY finite-alphabet 2-tag system. See "the open
item" below for the route.**

Three observation modes, all quantifying over a pinned encoding class:
`UniversalReach` / `UniversalNorm` / `UniversalConv` (`Universality/Defs.lean`).

**The encoding classes, and why there are two.** Negative claims strengthen as
the class grows; positive claims strengthen as it shrinks. So refutations are
stated for the weaker `PathEncoding` (injective + path-preserving, nothing else)
and certifications for the stronger `Simulation` (adds a decoder and backward
reflection). `Simulation.toPathEncoding` gives the inclusion;
`pathEncoding_strictly_weaker` proves it is proper, so the direction is
substantive rather than bookkeeping.

| Result | Theorem |
|---|---|
| One refutation mechanism for all acyclic hosts | `PathEncoding.refute_of_acyclic` |
| ...from a strictly-growing measure | `RS.Acyclic.of_strict_measure` |
| pure S cannot host SK | `no_pathEncoding_SK_pureS` |
| first-order ι cannot host SK | `no_pathEncoding_SK_iota` |
| **no one-combinator one-rule system of any arity can (C4)** | `no_pathEncoding_SK_poly` |
| `bwd` from a stuttering abstraction (adequacy) | `RS.bwd_of_abstraction`, `Simulation.ofAbstraction` |
| a `Simulation` whose source is known-universal | `universalReach_extend` |
| **a `Simulation` of a genuine multi-step machine INSIDE SK** | `countdownInSK` |
| **a `Simulation` of a genuine TAG SYSTEM inside SK — the open item, closed** | `tagABInSK`, `universalReach_tagAB_SK` |
| **...generalised: EVERY finite-alphabet 2-tag system is hosted** | `tagTInSK`, `finTagInSK`, `universalReach_finTag` |

**Negative controls** — what the definitions would collapse to if loosened:
`bareEncNorm_trivial` (an oracle encoder witnesses unpinned normalization-based
universality for *any* source) and `universalReach_self` / `universalNorm_self` /
`universalConv_self` (all three modes are trivially true on the diagonal, so a
ledger cell carries information only when reference ≠ host).

**Adequacy — the blocker, now cleared (Stages 45–48).** `bwd` was the risky
piece from Stage 8. Stage 10 found the failure (duplicated arguments drift),
Stage 13 refuted the first two fixes (constrain the encoding: impossible, since
transient duplicates are unavoidable; abstract up to joinability: too coarse,
`joinable_abs_not_functional`), Stage 45 found the third — read a term's
**K-normal form**, so doomed subterms and any drift inside them are invisible —
Stage 46 made that denote (`knf_unique`, `IsKNF.of_kstep`), and Stages 47–48
proved the S-step half via a commutation square (`sk_square`, `itower_sStep`).
The result is `countdownInSK`, a `Simulation` into `RS.SK` with a genuinely
multi-step encoding rather than an inclusion.

Stages 49–58 then produced a **second, independent** adequacy proof for the
same machine (`countdownInSK'`), via the *trajectory relation* rather than
K-normal forms, sharing nothing with the first but the encoding. Getting there
lifted four inherited pure-S restrictions from Goal 3's decidability layer
(`enumAt`, `smallTerms`, `deficit`, `boundedClosure_isSome`) and produced
`reachableWithin_correct` — **bounded-region reachability is decidable for full
SK** — plus `RS.bwd_of_abstraction_path`, which lets an abstraction advance by a
source *path* rather than a single step.

Its limit, stated plainly: the countdown is **not** universal, so this
discharges the *mechanism* criterion (a) was blocked on, not criterion (a).

**The tag-step driver — spec piece (v) — now exists and its forward half is
proved (Stages 59–64).** `STEPc` computes one step of a genuine two-symbol
m = 2 tag system (`a ↦ [b]`, `b ↦ [a,b]`) literally on fold-encoded words
(`STEPc_mkWord`), and `tagAB_fwd` gives `fwd` end to end: every source step is
simulated by actual SK reduction on the encoded word, via Stage 61's
fixpoint-free driver.

**Stage 65: the decoder is done (`decTag_encTag`), and the tag system
PATH-ENCODES into SK, machine-checked (`tagABPathEncoding`)** — the weaker
certificate class, but the one every refutation here is stated over, now
inhabited by a genuine dispatch machine. For the full `Simulation`, `bwd`
remains — and Stage 65 proved it is **false for the current encoding**
(`tagAB_bwd_false`): the tag step is partial, the compiled step function is
total, so the host keeps computing where the source has halted
(`encTag [b] ⟶* encTag [a,b]` with `[b]` a tag normal form). The driver needs
a length guard (Stage 66 design item). Both of the countdown's adequacy
templates are also provably inapplicable, for reasons that survive the guard:
the trajectory relation assumes a loop-free source and `tagAB` has a fixed
point (`onSegment_habs_fails_of_selfLoop`); the K-normal-form abstraction
demands intermediates that K-normalise to encodings, and the driver's first
self-application step already violates that (`tagDriver_knf_hstep_fails`).
A third abstraction, plus a characterisation of the guarded driver's
reachable set, is the remaining research obligation.

**Stage 66: the guarded driver is built and proved** (`STEPg`, 936 leaves):
stuck words are literally fixed (`STEPg_stuck`), `fwd` re-proved with the
Stage 64 lemmas untouched (`tagABg_fwd`), decoder and `PathEncoding`
retargeted (`tagABgPathEncoding`), and Stage 65's falsifier repaired
(`encTagG_stuck_returns`). `bwd` is now open rather than false; the
reachable-set characterisation is the whole of the remaining distance.

**Stages 67–68: the rigidity audit and the clean rebuild.** Shipped code was
NOT normal (Stage 11's `normalForm_bracket` does not cover `bracketOpt` over
bodies embedding applied constants); the audit accounted for every live
position and the rebuild (`TAILZn`/`TAILn`/`HASTWOn`/`STEPgn`, 870 leaves —
smaller than before) removed all non-word redexes, build-enforced. The final
encoding is `encTagN` / `tagABnPathEncoding`. Code drift now equals data
drift: ONE species, the reducts of `mkWord w`. That word-drift family, the
machine phases composed over it, and the third abstraction are what remain
for `bwd`.

**Stage 69: the word-drift family is DONE, by behaviour rather than
enumeration.** Every word reaches a canonical normal form
(`wordNF`/`mkWord_to_wordNF`), and every drifted copy still reaches it
(`mkWord_drift_complete` — confluence joins, normality pins), so drift can
always be completed and never conflates words (`mkWord_drift_functional`).
What remains for `bwd`: injectivity of `wordNF` (syntactic), and the phase
layer — where the checkpoints are not normal, so completion must come from
the driver's structure instead of `nf_unique`.

**Stages 70–73: the identity layer is done and the route is forced.**
Injectivity (`encWord_drift_pins`, Stage 70); drift-input step-correctness
with literal outputs — the fold restores literalness (`STEPgn_drift`,
`encTagN_drift_fwd`, Stage 71); the corrected frame — completion cannot see
order, so `bwd` needs a per-step tracking relation (Stage 72); and the
landscape closed by two more machine-checked refutations (Stage 73):
segment relations are inherently second proofs (`segRel_habs_iff`), and the
driver's region is UNBOUNDED (`driver_region_unbounded` — the shell
pre-unfolds future cycles, `selfRep_nests`), killing bounded-region
decidability. Four mechanisms refuted in total; the one remaining route is
a per-step tracking abstraction over the interior factorization: an
inductive family of shell contexts (closed under nesting) over data holes
(handled by the Stage 69–71 suite).

**Stage 74: the interior factorization EXISTS** (`DriverShell.lean`): a
12-kind inductive family, generic in the step function, proved closed under
reduction (`Sh.closed`), with `driver_interior_invariant` instantiating it
for the tag driver — every reduct of `encTagN w` is shell machinery over
data holes. The data layer is abstract behind two Step-closed predicates;
instantiating it, then reading the tracking abstraction off the factored
shape, is what remains for `bwd`.

**Calibration criteria, from the spec.** (b) discharged in Stage 3. (c)
discharged by the definitions ledger plus the `PathEncoding` scoping. (a) — see
Stage 16 in the ledger — is **unsatisfiable as written**, because its
"including one-combinator bases" clause is refuted in first-order scope by C4;
in its satisfiable restatement (certify at least one known-universal system via
a `Simulation` inhabitant) it is **discharged**.

---

## Goal 3 — is reachability between pure S-terms decidable?

**Status: CLOSED. Yes, for K-free sources.**

`stepsDecidable` / `steps_decidable_of_kFree` (`Decidability.lean`). Stage 2
monotonicity confines every path inside a finite universe; `enum_complete`
(`Census/Completeness.lean`) proves that universe is exhaustively enumerable; a
`deficit` measure then bounds how long saturation can take, so the certified
per-instance procedure `reachable?` always returns a verdict.

Honest framing, also in the module header: on paper this is folklore-adjacent —
"monotone size ⇒ bounded search" is two lines given Stage 2. The machine-checked
version is the claim.

---

## Goal 4 — how far this setup pushes Lean on genuine research mathematics

**Status: ONGOING BY DESIGN — it is a deliverable, not a target.** The spec says
plainly: *"if Stage 5 never terminates, the notebook is the result."*
`LAB_NOTEBOOK.md` is that deliverable. Its most transferable content:

- **Nine `Classical.choice` leaks** (the fifth in Stage 69 — Stage 9's `BEq`
  trap again, sixty stages later, in a file that quotes it; the SIXTH in
  Stage 76 was PRE-EXISTING — `occurs_bracket`'s `grind` had leaked since it
  was written, tainting `combinatory_completeness`, and was found only when
  new code imitated the old tactic). Five caught by a per-stage
  `#print axioms`; the sixth showed per-stage auditing certifies stages, not
  the tree — so the claim is now BUILD-ENFORCED (`Audit.lean` pins every
  headline theorem's exact footprint with `#guard_msgs`). The SEVENTH leak
  (Stage 79) was caught by that audit one stage after it was built, and came
  through a new door: `omega` aimed at a non-arithmetic goal routes through
  `Classical.choice`; the EIGHTH (Stage 93) was the same door again —
  the mechanism recurs because contradictory-hypothesis branches invite it; the
  NINTH (Stage 101) is a new variant of the same door: `omega` proving a
  CONJUNCTION-INSIDE-DISJUNCTION goal routes through choice even though plain
  disjunctions of equalities are clean (verified by experiment)
  audit and none by review, all originating in core's `BEq`/instance layer or in
  `omega` discharging a non-arithmetic goal. Three were fixed by rewriting; the
  fourth was resolved by *weakening a decorative claim* rather than paying the
  axiom.
- **A difficulty-estimate tally**: four under-estimates, one over-estimate,
  with the same cause in both directions — estimating from the first
  representation that came to mind rather than from the problem.
- **Four prototypes that found bad news**, each cheap, each preventing a larger
  rewrite. Naming the risky piece has been reliable; rating its difficulty has
  not.

---

## The conjectures

`C1`–`C6` were census output, not goals. Current standing:

| | Claim | Status |
|---|---|---|
| C1(a) | some pure-S term has no normal form | **PROVED** `c1a` — `Recurrence.lean`, via a regular-tree-language certificate |
| C1(b) | none with ≤ 6 leaves does, so 7 is the floor | **PROVED** `no_small_divergence` |
| C2 | no proper cycles in pure-S reduction | **PROVED** `no_pure_S_cycle` (probably external too) |
| C3 | growth-pattern regularities | **RETIRED** as a census artifact |
| C4 | no one-rule first-order basis hosts SK | **PROVED** `no_pathEncoding_SK_poly` |
| C5 | conservation for pure S (WN ⇒ SN) | **PROVED** `conservation` — *not* an import; proved from Stages 1, 2, 6 and C2 |
| C6 | divergence density → 1 | **probed**, open, low materiality |

C1(a) is proved by a **recurrence set** (Endrullis–Zantema 2014): a
six-state deterministic tree automaton whose accepted language is non-empty,
closed under reduction, and contains no normal forms. Witness:
`S S S (S S S) (S S S (S S S))`, twelve leaves. C5 supplies the last step —
"admits an infinite reduction" ⟹ "has no normal form" is not automatic for
pure S, it *is* the conservation theorem.

The certificate is not tight: C1(b) proves the true divergence floor is **seven**
leaves, and the automaton rejects both seven-leaf candidates, so `c1` and `c2`
remain individually open.

C1(a)'s **loop route** (Stages 37–42) is closed off and was prior art —
Waldmann 2000 proved CL(S) admits no ground loops. What survives from those
stages is reusable machinery (`Subterm`, `Step.subterm_split'`,
`step_growth_eq`, `selfEmbed_imp_halfShape`) and one live pointer: the
**open-term** version, `t ⟶* C[tσ]`, is open in the literature. Everything
here is ground.

Every entry carries a **materiality** and a **prior-art** line in the ledger.
Those two fields were added in Stage 7 after nine stages went into C1, whose
materiality was low from the start and whose prior art was discoverable in an
hour.

---

## The relaxation ladder — an ACYCLICITY ladder (spec Stage 5, second component)

The spec's Stage 5 has **two** components. The north star — reachability
decidability — is Goal 3 above and is closed. The other is the *bracketing
program*: "classify universality of bases between {S} and {S,K} — e.g., {S,I},
{S,B}, {S,C} — each rung a publishable partial result that narrows where
universality is lost." Sixteen stages engaged only with the first; the ladder was
opened in Stage 17.

**THE LADDER IS COMPLETE** (Stage 96): every rung settled, the two two-combinator
bases split in opposite directions.

**WHAT THIS LADDER ANSWERS, AND WHAT IT DOES NOT.** The spec says "classify
**universality** of bases." What this program can answer per rung is
**acyclicity** — and acyclicity only bounds *refutability*: an acyclic basis can
be refuted as a host of SK by the existing mechanism, a cyclic one cannot be
touched by it. **No rung below settles universality.** Rung one does *not* say
`{S,I}` is or is not universal; it says the program's refutation tool cannot
reach it. Stated here because rung one otherwise reads like a universality
result, which would be the same misreading the `Tag → Tag` result was scoped
against in Stage 16.

| rung | basis | acyclicity verdict |
|---|---|---|
| 0 | `{S}` | **acyclic** (`no_pure_S_cycle`); hence refuted as a host of SK |
| 1 | `{S,I}` | **cyclic** (`omegaSI_cycle`). NO monotone measure exists in either direction (`SI_no_strict_measure`, `SI_no_decreasing_measure`) — so the mechanism is not merely unhelpful here, it is provably inapplicable |
| 2 | `{S,B}` | **CLOSED — ACYCLIC (Stage 83: `SB_acyclic`), hence CANNOT HOST SK (`no_pathEncoding_SK_SB`).** The right-spine depth never decreases along any step and strictly increases at root steps; Stage 81's localization supplies the root step on every cycle. Subsumes all fragment results and census bounds. The route: 80 typechecked (termination dead), 81 localized (root steps forced), 82 dichotomized, 83 closed | No counting measure is monotone (`no_monotone_counting_measure`). No cycle under **any** strategy up to 8 leaves within a 30-leaf cap, cap-insensitive to 120 (`onCycleAny`); the cap is not liftable by brute force. **τ strictly drops on every B-reduction and every τ-light S-reduction, so the τ-light fragment is ACYCLIC** (`sbLight_acyclic`) — hence any cycle must fire an S-reduction duplicating a τ-**heavy** argument (`sbCycle_needs_heavy_S`) |
| 3 | `{S,C}` | **CLOSED — CYCLIC (Stage 96: `SC_cycle`, `SC_not_acyclic`, axiom-free witness).** With `h = C S C`: `S (C h) C h ⟶ C h h (C h) ⟶ h (C h) h ⟶ S (C h) C h` — a 3-cycle, 9 leaves, found by CHASING THE SURVIVING BRANCH of the impossibility hunt. Minimal cycle length is EXACTLY 3 (`sc_minimal_cycle_length`); the minimal cycle is NOT unique (Stage 99: the 13-leaf w-cycle, `C (w w) w w`, `w = S (C C)`); and the CLASSIFICATION is a theorem (Stage 101, `sc_root_three_cycle_classified`): every root 3-cycle is the h-cycle at basepoint A or B, or the w-cycle. `{S,C}` closes OPPOSITE to `{S,B}`; `PathEncoding.refute_of_acyclic` can never apply. The census stopped at 6 leaves; the witness sits at 9. Hosting: see THE HOSTING THREAD section below |
| top | `{S,K}` | **cyclic** — by the Ω ↔ M cycle, and independently by inheritance from rung one (`SK_not_acyclic_via_rung1`) |

**A standing caveat on census evidence here.** Cycle hunts based on a single
reduction strategy are **leftmost-outermost only**. Stage 0 flagged that for pure S; Stage 21
gave it a concrete witness — rung one's cycle is *kernel-proved to exist* and
leftmost-outermost reduction provably never returns to it (`omegaSI` grows
6,8,7,10,9,8,12,… forever). So "no cycle found" at any rung bounds LO cycles only,
never the reduction relation. Pure S is unaffected because C2 *proved* acyclicity by
a measure, not by the census. **Stage 22 replaced the rung-two hunt with a
strategy-independent one** (`onCycleAny`, all one-step successors, validated by
finding rung one's cycle) — so rung two's evidence is no longer subject to this
caveat, only to a size cap.

**The rungs are not independent — the ladder is a hierarchy.** Cycles propagate
along path encodings (`not_acyclic_of_pathEncoding`, axiom-free), so a cyclic
basis makes every system it path-encodes into cyclic as well. Rung one is
therefore an **upward-closed family**, not a point: any basis with a definable
`I` inherits its cycle. `siInSK` witnesses this at the top of the ladder, and
`SK_not_acyclic_via_rung1` re-derives SK's non-acyclicity by that route —
independent of the Ω ↔ M cycle, so the two agree.

### What each rung has ESTABLISHED

The spec's purpose for a rung is *"a publishable partial result that narrows where
universality is lost"* — not a full acyclicity proof. Every rung is now SETTLED
(rungs 2 and 3 closed in opposite directions, Stages 83 and 96); here is what each
has delivered.

- **Rung 0 `{S}`** — acyclicity PROVED (`no_pure_S_cycle`), and refuted as an SK host.
  Also a genuine decision procedure for reachability, because monotonicity confines
  every path.
- **Rung 1 `{S,I}`** — cyclic, PROVED, and **upward-closed**: any basis with a
  definable `I` inherits the cycle (`not_acyclic_of_pathEncoding`, `siInSK`). Also the
  witness that erasure-freeness does *not* explain rung 0's acyclicity, and that
  **arity** is the discriminator.
- **Rung 2 `{S,B}`** — **CLOSED at Stage 83: ACYCLIC (`SB_acyclic`), hence not an SK
  host (`no_pathEncoding_SK_SB`)** — by right-spine-depth monotonicity composed with
  Stage 81's cycle localization. Everything below is subsumed, and kept as the record
  of the route (and of the six-stage miss the closure exposed — see the Stage 83
  notebook entry):
  - no counting measure is monotone (`no_monotone_counting_measure`);
  - the τ-light fragment is ACYCLIC (`sbLight_acyclic`), so a cycle must fire an
    S-reduction on a τ-**heavy** argument — threshold bootstrapped from τ ≥ 4 to an
    *average* of τ ≥ 14, with the argument family's cap recorded at τ ≈ 24;
  - the **S-only fragment is ACYCLIC** (`sbSOnly_acyclic`), so a cycle must contain a
    **B-reduction** (`sbCycle_needs_B`) — C2's squeeze transplanted, since S-only
    {S,B} is pure S over a two-symbol alphabet;
  - no I-like combinator AT ANY SIZE (`sb_no_I_like`, Stage 98 — upgraded from the
    7-leaf census: every step result is an application, so `t S ⟶* S` is a nonempty
    path ending at a leaf, impossible), closing the transport route unconditionally;
  - censused clean to 8 leaves under *any* strategy, cap-insensitive to 120.

  - the **no-B-duplication fragment is ACYCLIC** (`sbNoBDup_acyclic`) — a three-level
    squeeze on `#B`, then `leafCount`, then τ — so a cycle must contain an S-reduction
    whose duplicated argument **contains a `B`** (`sbCycle_needs_B_duplication`). This
    fragment strictly contains the S-only one, so it *subsumes* `sbSOnly_acyclic`.

  Composed, these give a **proved syntactic** necessary condition: a cycle requires an
  S-reduction whose third argument has ≥ 3 leaves, and an S-reduction whose third
  argument contains a `B`. (Measured: this does *not* prune a seed-filtered search —
  99.6% of 8-leaf terms survive — because it constrains a cycle's *steps*, not a
  search's *seeds*. Pruning during exploration is also unavailable: it would need a
  localizable unreachability certificate, and these constraints are global sums.)
- **Rung 3 `{S,C}`** — **CLOSED at Stage 96: CYCLIC (`SC_cycle`, `SC_not_acyclic` —
  axiom-free witness; minimal cycle length EXACTLY 3, `sc_minimal_cycle_length`).**
  With `h = C S C`, the 3-cycle is
  `S (C h) C h ⟶S C h h (C h) ⟶C h (C h) h ⟶C·appL S (C h) C h` — nine leaves,
  three above the census horizon, found by chasing the surviving branch of the
  impossibility hunt: Stage 95's budgets forced any S-rooted 3-cycle to carry two
  root fires, and the single consistent assignment through the injections is
  inhabited. The rung closes OPPOSITE to `{S,B}`; the acyclicity route to refuting
  `{S,C}` as an SK host (`PathEncoding.refute_of_acyclic`) is permanently closed.
  Everything below is the route that cornered the witness — six necessary
  conditions and two impossibility sweeps, every one satisfied by the cycle:
  two impossibility sweeps: the τ-light fragment is acyclic (`scLight_acyclic`); the
  S-only fragment is acyclic (`scSOnly_acyclic`); the no-C-duplication fragment is
  acyclic (`scNoCDup_acyclic`), so any cycle needs a C-duplicating S-reduction
  (`scCycle_needs_C_duplication`); any cycle passes through a root redex
  (`sc_acyclic_of_no_root_cycle`, Stage 81); any cycle fires a FLATTENING `C`
  (`scCycle_needs_flat_C`, Stage 84); and any root cycle's return path reaches a
  SECOND root redex, at the root or immediately left of it
  (`scCycle_second_redex`, Stage 88 — cycles cannot avoid the top-left spine). The
  collapse escape is narrowed (Stage 89): leaf-headed collapse is dead
  (`sc_no_leaf_collapse`) and every collapse fires a root redex from a right-nested
  subterm (`sc_collapse_needs_root`), and leaf-headed terms can never reach a root
  redex (`sc_leafLeft_no_root_reach`), giving the CYCLE ANATOMIES (Stage 90): a root
  S-cycle returns through a whole-term root step or `f` is an application and both
  projections carry root fires (`sc_root_S_anatomy`); a root C-cycle returns through
  a whole-term root step or `x` is an application with the left projection firing
  and `y ⟶* z` (`sc_root_C_anatomy`). Leaf-headed-argument root cycles must return
  through whole-term root steps. The frontier invariant is ROTATE OR DESCEND
  (`scCycle_rotate_or_descend`, Stage 91): every cycle carries a root cycle that
  either contains another root cycle on itself (through its return's whole-term
  root fire) or has an app-headed head argument whose `app head last` projection
  fires a root redex on a strictly smaller term. The well-foundedness scaffold is in
  place (Stage 92): length-indexed paths (`RS.StepsN`), a choice-free descent engine
  (`RS.acyclic_of_cycle_descent` — strictly-shortening cycle surgery proves
  acyclicity), and the conservation fact that rotation preserves total cycle length
  (`scRootCycle_rotate_same_length`) — rotation cannot escape a length descent.
  First purchase (Stage 93): the dichotomy and localization redone with lengths
  (`sc_stepsN_facts`, `sc_cycle_needs_root_length`), so MINIMAL CYCLES ARE ROOT
  CYCLES exactly (`sc_minimal_cycle_is_root`), no step is a self-loop
  (`scStep_irrefl`), and minimal cycles have length ≥ 2
  (`sc_cycle_length_ge_two`). Second purchase (Stage 94): a root fire is never
  undone in one step (`sc_no_root_two_cycle` — the live branch dies on the frozen
  left), so there are no 2-cycles and MINIMAL CYCLE LENGTH ≥ 3
  (`sc_cycle_length_ge_three`). Third purchase (Stage 95): collapse costs at least
  two steps (`sc_no_step_collapse`, `sc_collapse_length_ge_two`), and the return
  dichotomies carry exact budgets (`sc_root_S_return_length`,
  `sc_root_C_return_length`: sandwiches account for every step, projections split
  it, the S-side collapse costs ≥ 2) — so an S-rooted root cycle with a rootless
  return has cycle length ≥ 4 (`sc_root_S_projection_length`); short cycles must be
  C-rooted or carry second fires — and Stage 96's witness carries exactly the two
  fires the budget demanded. Termination routes were provably dead
  (`SC_not_normalizing`), positional measures provably insufficient (C permutes),
  the τ×ρ braid provably failed (Stage 85, witnessed), and the spine calculus
  (`scSpine_S_root`, `scSpine_C_root`, `sc_no_leaf_self_embed`) supplied the
  frozen-left theorem that closed the case analyses. The census stopped at 6 leaves;
  the witness sits at 9. The necessary conditions stand as theorems ABOUT the
  cycle space of `{S,C}` — no longer steps toward an acyclicity proof, but the
  sharpest published description of what its cycles must look like, verified against
  the one now known to exist.

**Shared machinery.** Every acyclic-fragment result above — and C2's original argument —
is an instance of one lemma, `RS.Acyclic.of_three_level`: three measures where each level
pins the next (`m1` never rises; when it holds still `m2` never falls; when that holds
still too `m3` strictly drops). Written by hand four times before being abstracted.

### The rung procedure

Order is load-bearing. Rung one ran this before it was written down.

```
0. PRECONDITION: the basis {S, X} and X's rule as a rewrite schema.

1. Compute each rule's leafCount delta at minimal instantiation.
   -> know whether leafCount is monotone up, down, or neither.  [arithmetic]

2. IF every rule strictly increases: RS.Acyclic.of_strict_measure -> refuted.
   STOP. [one line -- where iota and all of C4 land]

3. ELSE hunt for a cycle. Canonical attempt: Omega = (S X X)(S X X).
   -> a cycle KILLS every monotone measure in both directions, so step 4
      becomes provably futile; or the attempt terminates, weak evidence
      toward acyclic. [small; absence of a cycle is not proof of none]

4. ONLY IF no cycle: hunt a combined measure -- lexicographic, since by
   step 1 no single component is monotone. [a full slice, as C2 was]

5. Record the rung, and say which question was answered (acyclicity,
   not universality).
```

**Step 3 must precede step 4**, because a cycle makes step 4 provably
impossible. At rung one that ordering saved the expensive step entirely — by
luck rather than design, which is why it is written down now. Steps 1 and 3 are
independent and can run together.

**Stage 96 postscript — step 3 has a second form.** The census (bounded cycle
hunt) is step 3's cheap form and it can miss: rung 3's cycle sits at 9 leaves,
three above where the census stopped. The expensive form is PROOF-GUIDED
SEARCH: run step 4's impossibility machinery with EXACT accounting (budgets,
not bounds), and when a branch refuses to die, its constraints are a
construction recipe -- unification either kills the branch or builds the
witness. Rung 3 fell to that form: sixteen stages of necessary conditions
specified the cycle up to one assignment. The procedure gains a step 4-prime:
if step 4 stalls with one surviving branch, instantiate it.

**What rung 1 establishes.** The program's entire negative apparatus routes
through one mechanism, `RS.Acyclic.of_strict_measure` — and that mechanism
**stops dead at the first rung**. It covers `{S}`, first-order ι, and every
one-combinator one-rule system (C4); it provably cannot touch `{S,I}`. Also:
erasure-freeness is *not* what keeps pure S acyclic, since `{S,I}` erases nothing
either and still cycles. Higher rungs need positive constructions or new
mechanisms.

## The hosting thread — SK ≤ `{S,C}`, the constructive half (Stages 98–113)

Rung 3's closure (cyclic) killed the refutation route and opened the opposite
question: can `{S,C}` — no erasure, no identity, no selectors — host
computation? Sixteen stages later the answer is a machine-checked stack, ALL OF
IT AXIOM-FREE (pure constructions, no `propext`, no `Quot.sound`):

| Capability | Theorem(s) | Stage |
|---|---|---|
| No I-like combinator, at any size (both `{S,B}` and `{S,C}`) | `sc_no_I_like`, `sb_no_I_like` | 98 |
| `{S,C}` path-encodes into SK (upward closure complete) | `scInSK` | 100 |
| Unbounded convergence (C-towers shred to `C C C`) — the naive erasure-impossibility is false | `sc_unbounded_convergence` | 102 |
| No one-application selector; the cyclic ROTATOR exists (`C C u v w ⟶* v w u`) | `scv_no_single_selector`, `scRot_beta` | 103 |
| Branching WITHOUT selectors: tags `C`/`C C` head-promote an arm under one uniform protocol, the untaken arm parked not erased | `scTagA_dispatch`, `scTagB_dispatch` | 104 |
| The word layer: normal, stable two-symbol words with per-symbol traversal (swap parity selects the arm) | `scWord_step_false/true`, `scWord_normal` | 105 |
| The re-launcher and the recycling arm: the parked arm is the next first arm | `scRelaunch_beta`, `scArm_step`, `scTraversal_step_*` | 106 |
| Payload regeneration: `scDup = S (C C) (C C)` (the w-cycle seed applied to a tag) duplicates the parked arm; UNBOUNDED TRAVERSAL; **the first machine hosted on any upper rung** | `scDup_step`, `scRun`, **`tailInSC : PathEncoding RS.TailB RS.SC`** | 107 |
| Production-carrying cells (differentiation is free at encoding time); the 3-arg driver protocol | `scPCell_step`, `scPCell_step_acc` | 108 |
| Runtime cons: the accumulator is writable, four fires, zero residue | `scCons_beta`, `scQCell_step` | 109 |
| **THE ONE-TAG-STEP**: read the cell, append its wrapper to the pile, advance, arms regenerated | `scTCell_step`, **`scTWord_step`** | 112 |
| Multi-symbol productions by cell layering | `scTCell2_step` | 113 |

**The method that carried it** — model, bound, edge, construct: Stage 110's
searches found mid-spine insertion census-dead across three protocols;
Stage 111 PROVED the bound in the searched model (opaque literals freeze the
spine at head — `scv_varHead2_step` — so at most one literal lands behind the
last atom) and located its edge (real cells are C-headed compounds, exempt);
Stage 112 constructed past it in two fires (`scTCell W rest = C (C rest scDup)
W` — the arms are CONSTANTS, so the cell supplies a fresh literal arm and
demotes a spare to accounted pile-junk).

**The member calculus** (the thread's working theory of `{S,C}` interrogation):
three moves — prefix-edit, passenger-step-back, z-nest — one terminator (an
atom reaching the head freezes the spine), one permanence (the last member is
immovable, so piles are LIFO by law; LIFO fold of LIFO pile restores FIFO).
MACHINE-CHECKED as of Stages 123–125 (`SCMembers.lean`): `scvStep_members`
(the member-action characterization — every step is an S-fire or C-fire on
the first three members, or one member stepping in place), the count laws
(`scvSteps_countVar_mono`, the squeeze), and `scv_cross_last` — THE CROSSING
CONFIGURATION: on count-preserving steps, moving a member behind a
last-position variable forces the three-member C-fire shape. Stage 126 lifted
it to paths (`scv_lastVar_step`, `scv_lastVar_steps`, pinned): along any
count-preserving reduction, a last-position variable RIDES THE TAIL until the
one configuration that can consume it — handed back with its full sandwich
(the path to it, the step out, the path onward). Stage 127 assembled THE
FUNNEL (`scv_pair_funnel`, pinned, with `scv_varHead_frozen` — vars freeze at
the head — and `scv_pair_pred` — the ONLY step into `s a b` is the root
C-fire from `C s b a`): every pairing path `P a b s ⟶* s a b` threads the
crossing configuration `C x y s` (`x` machine-headed, `s`-free on both
members, payload variables split one-each across `x` and `y`) and then the
canonical predecessor. Stages 128–129 CLOSED THE DEADLOCK: with `Stuck`
(a variable heading the term or a compound member — forever, by
`scv_stuck_steps`) supplying the dead ends, the invariant `Ahead` (both
payload variables ahead of `s` in the member list) is inductive on
count-preserving steps — the only fire that could break it needs `s` third
and both payloads in the two slots ahead, promoting one of them — and so
**ARRIVAL-ORDER PAIRING IS IMPOSSIBLE IN `{S,C}`** (`scv_no_pair`, pinned):
no machine `P`, however large, reduces `P a b s` to `s a b` on opaque
arguments. Open since Stage 103; the census bound (≤ 9 leaves) is now a
theorem at every size. This is the program's second complete impossibility
at the interrogation level (after the one-application selector, Stage 103)
and its first CLOSED standing conjecture from the hosting thread's
negative side. Stage 131 completed the FAMILY: the swapped order is
impossible too (`scv_no_pair_swapped`, via the generic predecessor
`scv_sel_pred`), while payload-headed rearrangement is TWO FIRES
(`scv_swap_reachable`, axiom-free: `C C a b s ⟶* (b s) a`). The wall is
exactly about `s` reaching the head — `{S,C}` shuffles arguments freely
but never hands control to the one that arrived last.
Non-erasure forbids UNACCOUNTED waste, not waste: every surviving gadget gives
each forced passenger a job.

**What remains for a full tag `Simulation` into `{S,C}`**: the FOLD phase —
and Stage 144 SPLIT IT IN HALF. Its production step FELL: `sc_cell_synth` /
`scv_cell_synth` (pinned, axiom-free) — a traversal cell is all constant
except its wrapper, so ONE S-fire mints `scTCell w rest` at runtime from the
prefab `scCellPrefab rest`, even for an opaque `w`; the genetic-closure law
(Stage 115) stands, but its documented seam (S-fires nest spine members into
elements) does the work its prose had written off. Stage 145 conjectured
the accumulation half impossible (C7, the mid-insertion obstruction);
Stage 146 REFUTED C7 in a day: the obstruction is real about moves but
assumed `scTCell`'s child order. THE QUEUE CELL (`scQCell acc W =
C (C scDup acc) W`, children in stream order, constants only at heads) is
runtime-synthesizable in three one-fire nests (`sc_qcell_synth₁–₃`) and
delivers the IDENTICAL one-tag-step protocol in seven fires
(`scQCell_fire`; word layer `scQWord`/`scQWord_step` — all axiom-free,
pinned). The fold ledger: production ✓, accumulation ✓, protocol ✓. Full
tag hosting — and with it the undecidability side of the rung-3
equivalence — hangs on ONE remaining design problem: C8, DRIVER
SELF-REGENERATION (the quine). The stakes are now explicit: a quine
driver ⟹ tag `Simulation` into `{S,C}` ⟹ rung-3 reachability
undecidable ⟹ the frontier equivalence resolves negative. Stage 147
mapped C8's first wall (THE ARM-JUNK BARRIER — spent arms are
non-erasable and block the synthesis position; 2,286 end-markers, zero)
and Stage 148's co-design DISSOLVED it: THE BIODEGRADABLE ARCHITECTURE
(`scBCell acc W = C (C C acc) W`, arms `C C`) makes every auxiliary leaf
pure C, so exact C-conservation burns all machinery — five-fire protocol
(`scBCell_fire`), and a two-cell word ends at literally `E W₂ W₁`
(`scBWord_two`, axiom-free, pinned): ZERO RESIDUE and the wrappers in
FIFO ORDER — the tag queue's append order, free. Two of the three
architectural walls (arm junk, LIFO piles) were scDup-era artifacts. C8
now reads concretely: from `E W₂ W₁`, erect the next word with a working
accumulator and re-armed driver (re-erection is live — `scDup W₂ W₁`
runs a cell in two fires — but mints a junk accumulator). Stages 149–152
measured the remaining gap exactly: THE FUEL LAW (`scBWord_run` — leading
wrappers burn as arms; only the final two arrive) and FUEL BLINDNESS
(`scBCell_fuel_blind` — all fuels deliver bitwise-identical states: the
furnace reads nothing); and on the positive side THE GENERATION CYCLE
(`sc_generation_cycle` — the one-symbol self-tag hosts as a five-fire
`{S,C}` CYCLE, the end marker acting as return address) and THE ATTRACTOR
(`sc_words_decay` — every `scDup`-ended word pops to empty then pulses in
that cycle forever; the naive multi-symbol loop is dead). All axiom-free,
pinned. C8, final form after Stages 153–156: THE
CONSTRUCTOR GAP. The growth step exists (`sc_growth_step` — four fires,
word +1 cell, marker and arms surviving verbatim, via the co-designed
`scQuine`), a third protocol moves information inward instead of burning
it (`sc_cellArm_pop` — cell-arms hand their CONTENTS forward; the arm is
the program), and the Q-family's complete law is pinned
(`sc_spiral_pop`/`sc_spiral_descends` into a universal 14-cycle). But the
books cannot balance: pops strip arm depth, growth restores arms flat, so
the family caps at tower-3 (measured from both directions). What remains
is a self-reproducing CONSTRUCTOR — a marker that mints for the word and
deepens both arms while surviving. Everything below that one design
object is pinned theorem. The boustrophedon framing was itself corrected (Stage 116): front-push and
front-pop INTERLEAVE, so the induced dynamics are PREFIX REWRITING — a
deterministic stack process with a finite wrapper alphabet, pushdown-flavored,
and generational separation would need a mid-spine barrier that cannot exist.
THE FRONTIER QUESTION REFRAMED: is `{S,C}`-reachability DECIDABLE? Formal
transport (Stage 116, `Simulation.steps_iff` + `Simulation.transferDecidable`,
axiom-free): reachability is equivalent across a Simulation, so deciding the
host decides the source — a Simulation of SK into a reachability-decidable
host would decide SK-reachability (undecidable, external). Decidability of
`{S,C}` would therefore close the negative half at the Simulation class. The
C-FRAGMENT is settled (Stage 117, `scStepsC_conservation`, `SCC_acyclic`,
pinned): every C-fire loses exactly one leaf, so the fragment obeys EXACT
CONSERVATION (a length-`n` path loses exactly `n` leaves), terminates, is
acyclic (every full-system cycle fires an S — the dual of `scSOnly_acyclic`,
closing the fragment square), and has finite reachable sets (fragment
reachability decidable in principle). The dichotomy
(`scStep_leafCount_dichotomy`) pins the escape: the non-decreasing steps are
exactly the S-fires. Full-`{S,C}` decidability = whether S-fires can be
accounted — and the accounting now has its exact laws (Stage 118,
`scSteps_shrink_le`, `scSteps_growth_le`, pinned): the TWO-SIDED SPEED LIMIT —
no step loses more than one leaf (the anti-erasure law quantified; SK's K
erases mountains in one step, `{S,C}` pays retail) and no step more than
doubles. Every `{S,C}` path is metered on both sides. The member-sequence
abstraction collapses under S-compounding and non-erasing TRSs are
Turing-complete in general, so the question is genuinely about these rules;
SC-CONFLUENCE is now IN PLACE (Stage 119, `SC_confluence`, `sc_nf_unique`,
pinned at `[propext]` — matching SK's footprint): the Takahashi proof
transported arm for arm, with both redex inversions at depth three since
neither `{S,C}` rule erases. Normal forms are characterized (Stage 120, `SCNF_iff`, pinned — axiom-free):
exactly the spine-width-≤-2 shapes. BOUNDED REACHABILITY IS DECIDABLE
(Stage 121, `scReachFrom_iff`, `scReachWithin_decidable`, pinned): a verified
successor function and its n-step closure compute exactly the ≤-n-step cone.
The single remaining piece for full decidability is the BOUNDED-INTERMEDIATE
question — an intermediate bound plus the shrink limit would bound path
lengths, and `scReachWithin` would then decide `t ⟶* u` outright. The
question is now STATED PRECISELY (`RS.StepsLe`, Stage 132) and has its first
hard datum: THE MINIMAL MOUNTAIN (`sc_no_max_bound`, pinned) — a six-leaf
term whose only step climbs to seven on its way to a six-leaf target, so any
bounding function exceeds the identity; probe data (all starts ≤ 8 leaves)
force `f(8,8) ≥ 31`, an explosive trend consistent with the doubling speed
limit and with genuine computation happening between the endpoints. THE
BACKBONE IS A THEOREM (Stages 133–134, `sc_decidable_of_bound`, pinned): if
ANY computable `f` bounds witnessing paths' intermediates, `{S,C}`
reachability is decidable — via a verified capped-universe enumerator,
constructive pigeonhole (over a hand-rolled `listRemove`; core's
`List.erase` lemmas carry `Classical.choice` — the tenth leak, first found
in the library rather than a tactic), and saturation of the capped engine;
CAPPED reachability is decidable unconditionally (`scStepsLe_decidable`).
The rung-3 frontier is now one sharp alternative: a computable bound
(decidable, negative Simulation half closes) or mountains beyond every
bound (undecidable — and the hosting thread is the reduction's raw
material). The program's two research threads have converged. Stage 139
made the alternative an EQUIVALENCE (`sc_decidable_iff_bound`, pinned):
`{S,C}` reachability is decidable IF AND ONLY IF a computable function of
the endpoint sizes bounds witnessing paths' intermediates — the converse
assembles the bound from any decision procedure via a hand-rolled
choice-free find (core has no `Nat.find`; `Acc.rec` eliminates into data).
The one open goal-level question is now a single well-posed sentence, and
it has PINNED QUANTITATIVE FLOORS (Stages 140/142/181, `sc_bound_floor_6`/
`_44`/`_25`/`_186`): every valid `f` obeys `f(6,6) ≥ 7`, `f(8,32) ≥ 44`,
`f(9,10) ≥ 25`, `f(10,142) ≥ 186`, `f(12,234) ≥ 291`, and
`f(12,18) ≥ 87` — via the TALL, STEEP, n=10, and two n=12 MOUNTAINS
(forced prefixes of 49, 13, 300, 400, and 400 steps; the n=10 rung from
an exhaustive census of all 4,978,688 ten-leaf terms, the n=12 rungs
from its graft neighborhood and a 1.5M random sweep — two different
mountain species: tall-peak/big-endpoint and modest-peak/tiny-endpoint).
Best-witness excess reads 12 → 44 → 69 → 86 at n = 8 → 10 → 12 → 14
(the n=14 rung: `f(14,280) ≥ 366`, forced march-500, graft-found in 352
tries) — the scaling evidence leans ever harder against bounded
intermediates, i.e. toward undecidability, and the witnesses form one
structural family of climbers. All certified by the forced-march toolkit
(`scForcedMarch`/`scForced_mountain`/`scChained_steps`: chains computed by
the verified successor, certificates linear in the path; the n=9 census
found 13,721 such mountains, exhaustively). And the equivalence is now
GENERIC (Stage 142, `RS.SuccKit.decidable_iff_bound`, pinned): any rung
with a verified successor function and bounded enumeration gets it —
instantiated at RUNG 0 (`sk_decidable_iff_bound`, pinned): SK faces the
IDENTICAL question with the opposite expected answer (its reachability is
externally undecidable, so no computable bound exists there). Stage 143
equipped rungs 1 and 2 as well (`si_decidable_iff_bound`,
`sb_decidable_iff_bound`, pinned): the relaxation ladder — built to
compare acyclicity — now compares the reachability frontier uniformly at
all four rungs with one generic instrument. THE GLIDER
(Stage 135, `sc_glider`, pinned; pump axiom-free): an eight-leaf term whose
reachable set is infinite — `p p p` with `p = S (C (S S))` reproduces
itself under a wrapper every three fires, growing five leaves per loop,
traced 1500 steps without ever branching. Non-cyclic divergence at eight
leaves: `{S,C}` runs deterministic unbounded computation from tiny seeds,
and only CONTROL (halting on a condition — the fold problem, seen from the
other side) separates that from an undecidability reduction. Stage 136
CERTIFIED the march: the trajectory is exactly five shapes with singleton
successor lists (`GliderTraj`, `scSucc_wrap`), so reduction from the seed
is deterministic (`scGlider_deterministic`, pinned) and the seed has NO
NORMAL FORM (`scGlider_no_normal_form`, pinned) — the first
machine-checked normal-form-free `{S,C}` term. Stage 137 gave the engine
FIXPOINT DETECTION (`scReachCapped_excludes`, pinned): a decidable
stable-round check certifies unreachability under a cap — the minimal
mountain re-certified purely by `decide` — and the verified control probe
found 164 FUELED MOUNTAINS (machines that burn a `C C`-tower into linear
peak work, then strongly normalize to 5–7 leaves): halting-on-fuel exists
in `{S,C}`; what remains open is whether fuel can encode arbitrary
computation. Stage 115
also corrected Stage 111's prose invariant (atoms CAN sit at member heads via
S-fires, witnessed in-file; the freeze theorem and one-behind bound survive).
Negative standing results shaping any route: arm-level differentiation
homogenizes, arrival-order pairing IMPOSSIBLE (Stage 129, `scv_no_pair` —
formerly a ≤ 9 census conjecture), opaque mid-spine insertion impossible.

## The open item — CLOSED (Stage 75)

**Does SK certifiably host a genuine tag system?** Concretely: is there a
`Simulation (RS.Tag T) RS.SK`?

**YES — `tagABInSK : Simulation (RS.Tag tagAB) RS.SK`** (`DriverShell.lean`,
Stage 75): a genuine two-symbol, deletion-number-two tag system —
inspect, dispatch, append, guarded on its halting condition — hosted inside
SK in the demanding encoding class, encoder/decoder/`fwd`/`bwd` all
machine-checked, axioms `[propext, Quot.sound]`. The route, Stages 65–75:
`bwd` proved FALSE for the unguarded driver (65); the guard (66); the
rigidity audit and clean rebuild (67–68); the word-drift layer by
completion — canonical forms, injectivity, literalness restoration
(69–71); the frame corrections (72–73, four mechanisms refuted); the shell
factorization invariant (74); and the semantic data layer, under which
`bwd` is an INVERSION rather than a tracking argument (75) — the order was
in the slots, not the steps.

Honest scope, unchanged in kind since Stage 16: `tagAB` belongs to the
Cocke–Minsky universal CLASS (m = 2), but this two-symbol instance is not
itself proven universal and no such claim is made. Spec piece (v) — a
tag-step driver with a real `Simulation` — is discharged in full.

**Stages 76–79 completed the scaling**: `tagTInSK` (any m = 2 system, given
a four-hypothesis dispatch interface) and `finTagInSK` (the interface
discharged for every `Fin n` alphabet via selectors). Every concrete
known-universal 2-tag system in the literature is an instance of a
machine-checked theorem; universality of any particular table remains
EXTERNAL knowledge, cited not checked, as the repository has always
scoped it.

The original framing follows, for the record.

This is the one substantive thing left, and Stage 29 upgraded it from
"research-blocked" to a **stated structural obstruction**: the two candidate
abstractions fail for *opposite* reasons. The syntactic one is too **fine** — `S f g x`
duplicates `x`, the copies drift, and it loses track (`naiveAbs_not_stuttering`). The
joinability one is too **coarse** — it relates every trajectory state to every other, so
it is never functional on `enc`'s image (`RS.joinable_abs_not_functional`), which is
exactly the hypothesis the relational adequacy lemma needs. A workable abstraction must
sit strictly between, and neither obvious construction does.

Infrastructure in place for any future attempt: `RS.bwd_of_abstraction_rel` (adequacy
from a *relational* abstraction, with Stage 8's function version as a special case).

The older framing follows. The obstruction is `bwd`, and it is load-bearing: a positive
certification must be made in the demanding class (Stage 7's asymmetry), so it
cannot be weakened away. Stage 8 reduced `bwd` to supplying a stuttering
abstraction, which makes the obligation standard rather than open-ended — but
Stages 10 and 13 then showed the obvious abstraction fails, because `S f g x`
duplicates `x` and the copies drift, and transient duplicates are unavoidable in
SK (moving a value past another costs a copy). The abstraction must therefore be
insensitive to doomed subterms — up to `Joinable`, or reading only the live
spine. That is a research obligation.

Infrastructure already in place for it: pieces (i) and (ii) of the decomposition
(`ofTerm`/`toTerm` bridge, `abs2`/`abs2_beta`), plus `normalForm_bracket` (all
machine code is normal, so a fixpoint's self-application is safe).

## What this program does not claim

- It does not resolve the Wolfram prize question. What it establishes is where
  the question lives: **if S alone is universal, its encoding must be
  non-injective or must fail to preserve reduction paths.**
- It does not claim priority on C1, C2, or C5 — all are external or probably so.
- It does not claim `Simulation` is the right definition of universality. It
  claims the definition is *pinned*, *calibrated in both directions*, and that
  the unpinned alternatives provably measure nothing.
