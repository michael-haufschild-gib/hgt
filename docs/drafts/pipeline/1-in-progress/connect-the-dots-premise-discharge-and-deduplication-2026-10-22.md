# Connect the dots: premise discharge and proof deduplication

- **ID:** dots-2026-10-22
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Every corpus premise that another corpus theorem already proves is discharged, and
  every fact proved twice is proved once.

## Goal

Two corpus-wide operations, both measured in "dots connected":

1. **Premise discharge** — a theorem carries a hypothesis `h : P` while another module proves `P`
   with no extra input. The weld produces the hypothesis-free statement.
2. **Deduplication** — the same statement is proved in two modules, one of which imports the other.
   The redundant copy is deleted (same name) or replaced by a one-line delegation (different name),
   and the canonical lemma is made public when it was `private`.

Target: 250 dots.

## Method

Detector: `extract.py` parses every declaration in `formal/GaloisForLFunctions` into
(binders, conclusion, active section variables, proof span) and the import closure of all modules.

- discharge candidates: hypothesis text == conclusion text of a theorem whose own binders are a
  subset of the target's remaining binders; already-welded targets are filtered out by searching for
  a hypothesis-free theorem with the same conclusion.
- duplicate candidates: identical (signature, active variables) in two modules where one imports the
  other. Pure text identity, so the Lean compiler is the final arbiter of each weld.

Audit: every touched module is recompiled with `lean -o` (single process, dependency order) and its
olean/ilean republished.

## Ledger

| # | dot | kind | modules |
|---|-----|------|---------|

## Log
- 2026-10-22 — created; detector built (788k declarations parsed, 50439 modules).

### Batch 1 — Weil work "exposing ray" transfer family (compiled)

Canonical lemmas made public in `WeilWorkExposingRaySeparatorExtension` (atomic quadratic form
calculus) and `WeilWorkExposingRaySublogEnvelope` (Toeplitz/primitive-set square bound); the
copy-pasted proofs were removed from the importing modules.

| # | removed copy | lines | canonical |
|---|--------------|-------|-----------|
| 1 | `WeilWorkExposingRayLogLocalMass.primitive_square_of_toeplitz` | 63 | `WeilWorkExposingRaySublogEnvelope` |
| 2 | `WeilWorkExposingRayLogLocalMass.log_toeplitz_of_polar_bound` | 83 | `WeilWorkExposingRaySublogEnvelope` |
| 3 | `WeilWorkExposingRayLogLocalMass.resonator_budget_growth` | 13 | `WeilWorkExposingRaySublogEnvelope` |
| 4 | `WeilWorkExposingRayLogKernel.atomicForm_add` | 16 | `WeilWorkExposingRaySeparatorExtension` |
| 5 | `WeilWorkExposingRayLogKernel.atomicForm_smul` | 8 | `WeilWorkExposingRaySeparatorExtension` |
| 6 | `WeilWorkExposingRayLogKernel.atomicForm_zero` | 2 | `WeilWorkExposingRaySeparatorExtension` |
| 7 | `WeilWorkExposingRayLogKernel.atomicForm_sum` | 11 | `WeilWorkExposingRaySeparatorExtension` |
| 8 | `WeilWorkExposingRayLogKernel.atomicForm_packet` | 19 | `WeilWorkExposingRaySeparatorExtension` |
| 9 | `WeilWorkExposingRayLogKernel.farSource_packet` | 7 | `WeilWorkExposingRaySeparatorExtension` |
| 10 | `WeilWorkExposingRayLogKernel.atomicForm_farSource` | 13 | `WeilWorkExposingRaySeparatorExtension` |
| 11 | `WeilWorkExposingRayPolarKernel.integrable_packet_cos` (now delegates) | 8 | `WeilWorkExposingRayLogKernel.integrable_logCos` |
| 12 | `WeilWorkExposingRayOnePoleTransfer.plainDensity_integrable` (now delegates) | 4 | `WeilWorkExposingRaySeparatorExtension.density_integrable` |

Audit: `lean -o` green on `WeilWorkExposingRaySeparatorExtension`, `…SublogEnvelope`, `…LogLocalMass`,
`…LogKernel`, `…PolarKernel`, `…OnePoleTransfer`; oleans/ileans republished.

Lesson: making a `private` canonical lemma public breaks any importing module that keeps its own
`private` copy of the same name ("a non-private declaration has already been declared"), so every
sibling copy of that name must be removed in the same batch.

### Premise seam: audit result

The interface-closure engine (`ifaces.py`) computes which parameterless `Prop` interfaces the corpus
proves with no open premise (313 of 1150, five of them only after an interface-to-interface step) and
which premise-carrying theorems therefore become hypothesis-free. After filtering targets whose
hypothesis-free form already exists, **no RH-valued criterion is left unwelded** — every
`… ↔ RiemannHypothesis` whose premise the corpus proves already has its unconditional form
(Mertens/Littlewood energy criteria, Gaussian explicit formula, twisted-arc N1 witness, Sonin
coupled variance collapse). 20 non-RH welds remain, all intermediate lemmas.

Two engine traps worth remembering:
- an `X_of_riemannHypothesis` provider makes the closure self-feeding, because `RiemannHypothesis`
  is not a corpus interface; edges must require *every* premise to be a corpus interface;
- interfaces must be keyed by resolved namespace, not by name: a sub-namespace `xiZerosSimple`
  theorem is not a proof of `RHTower.XiZerosSimple`.

So the remaining corpus-wide gain is deduplication, which is where the following batches go.

### Batch 2 — Chen–Gupta–Li Lemma 6.2 contour family (compiled, 21/21 modules green)

The tail/conductor/principal-tail variants of the Lemma 6.2 estimates each carried a private copy of
a finite-contour lemma already proved in the finite-regime modules they import. Canonical lemmas were
made public in `ChenGuptaLiLemma62{FunctionalGrowth,TailFunctionalGrowth,FiniteIntegrability,
FiniteContour,ContourIntegrability,FiniteHorizontalEdges,TailTruncatedBounds,PrincipalReflectedEuler}`
and `SelbergClass/BarnesHorizontalEdges`.

26 welds: `cglLemma62_farTail_high_conductor_point_bound`, `cglLemma62_conductorTailWindow_abs_le`,
`cglLemma62_conductorTailWindow_high`, `cglLemma62_farTail_truncated_conductor_integral_bound`,
`cglLemma62_principalTail_abs_rpow_tail_integrable`,
`cglLemma62_principalTail_{left,right}Factor_differentiable`,
`cgl_norm_Gamma_real_sub_I_tail{,_strip}`, `cglGamma_add_nat_eq_tail_strip`,
`cglLemma62_shifted_cubic_le`, `cgl_tail_shifted_one_add_abs_pow_le`,
`cglLemma62_largeTime_truncated_conductor_tail_bound`,
`cglLemma62PrincipalRegularizedContour_shift_mapsTo`,
`tendsto_const_mul_pow_mul_exp_neg` (two copies), and the six `atomicForm_*`/`farSource_packet`
copies in `WeilWorkExposingRaySublogTransfer` plus its `atomicForm_zero`.

Running total of applied welds: 352 (batches 1–5a); verified green so far: 45.

### Detector corrections (all three found by auditing candidate pairs before trusting them)

1. A `letI`/`haveI` binder inside a statement ends with `:= by`, and the signature scanner treated
   that trailing `by` as the start of the proof, truncating long statements at the same place — which
   made whole families of ABHN statements look identical. Termination is now only at a depth-0 `:=`
   that is not a `let`/`have` binder.
2. Declarations must be keyed by *resolved namespace*, not by name: a sub-namespace `xiZerosSimple`
   is not a proof of `RHTower.XiZerosSimple`.
3. `/- … -/` blocks hold commented-out provenance drafts whose declarations the scanner read as real
   (e.g. `NonarchimedeanLocalFieldValuationSequence` keeps an "inactive source-order draft", which
   produced three phantom same-file duplicates). Block comments are now blanked before parsing.

Audit after the fix: all 101 touched files still have balanced comment blocks, so no weld cut into a
provenance block.

### Clean detector census (after the three fixes)

- 776541 declarations parsed in 50443 modules.
- **1175** cross-file redundant copies: the same (signature, section variables, namespace) proved in a
  module and in a module it imports. By area: RHTower 998, HTGeometry 121, BezoutValuationIncidence 14,
  Bottcher 12, TransHorizonIncidenceMechanics 11, BiScaleUncertainty 6, ArithmeticIncidencePositivity 5,
  HilbertMetric 4, ArithmeticCriticalityTheory 2, QECLean 2.
- **210** same-file extra copies in 183 groups.

The earlier count (2061) was inflated by the parser bugs; this census is the honest remaining seam.

## Goal raised to 2000 dots: the industrial pipeline

`pipeline.py plan` turns the two censuses into **857 groups carrying 1732 dots** (dropped: 22
unprivate-collisions, 44 same-file groups in non-leaf files, 2 non-leaf files, 1 missing canon).
With the 352 welds already applied this covers the 2000 target.

`pipeline.py run` then works group by group, unattended and resumably:

1. apply the group's welds (fresh re-parse per edit, atomic write, first-version backup per file);
2. compile every touched module once, sequentially, in import-closure order (one `lean` process at a
   time, olean/ilean published atomically);
3. on a red module restore its backup, recompile, and mark that group's dots `reverted`;
4. append every dot to `ledger.jsonl` and the finished group to `done_groups.json`, which makes the
   run resumable across sessions.

Guards: vendored areas (QECLean, PNTPlus, QuantumAlg) and top-level umbrellas are never touched;
cross-area welds only point at HTGeometry; a file modified in the last ten minutes is skipped so a
concurrent agent's edit is never clobbered.
