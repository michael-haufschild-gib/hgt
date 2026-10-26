# Kernel-checked first-atom quadrature

- **ID:** kernel-checked-first-atom-quadrature
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User request: replace native decision proofs in PA order-24 quadrature and rank-four Milnor-to-Steinberg surjectivity.
- **Statement:** Preserve all existing theorem statements, without added assumptions or axioms, using kernel-checked arithmetic.

## Approach

The finite-index complement follows from cardinality: three distinct elements cannot exhaust
`Fin 4`. Rational quadrature uses integer intervals with denominator `10^30`. Every arithmetic,
polynomial, rounding, and integration operation has a proved containment theorem. Equality
certificates normalize endpoints, polynomial coefficients, and cell integrals separately;
`norm_num` and proof-producing `cbv` retain kernel-checkable proofs. The five final comparisons
factor out the common denominator before summing certified integer numerators.

Original rational definitions moved unchanged from `PrimeArchThetaFirstAtomHighOrderMomentBounds`
to `PrimeArchThetaFirstAtomQuadratureEnclosures`. The original rational-bounds theorem now invokes
`RHTower.ThetaRationalQuadrature.firstAtom_bounds`; its analytic consequence is unchanged.

## Completed checks

- [x] Final direct check of `HTGeometry/MilnorKTwoSteinbergSurjective.lean` (session 26180, exit 0).
- [x] HT axiom audits: `exists_fin4_fourth`, `fin4_steinbergSymbol_index_independent`,
  `milnorKTwoToFin4SteinbergKTwoCenter_surjective`, and
  `milnorKTwoQuotientKerEquivFin4SteinbergKTwoCenter` have only
  `propext, Classical.choice, Quot.sound`.
- [x] The stale HT target olean/ilean from October 23 were removed after rechecking their exact
  timestamps and sizes. No HT target rebuild is needed unless a file being written imports it.
- [x] Enclosures, Seeds, and Certificates have current valid olean/ilean artifacts.
- [x] Width certificates are literal integers: the zero case explicitly unfolds `Enclosure.pow`;
  width 57 is `[0,1]` over `10^30` with standard axioms (Seeds session 79079, exit 0).
- [x] Two- and eight-coefficient integration tails pass (56556, exit 0).
- [x] All five rows at cell 63 pass, including every integration tail and final numerator axiom
  audit (26748, exit 0). Every audit has only the three standard axioms above.
- [x] `PrimeArchThetaFirstAtomQuadratureCells0` (cells 0–3) built successfully
  (53008, exit 0); its current olean/ilean are valid. Olean size is 617 MB.
- [x] `PrimeArchThetaFirstAtomQuadratureCells4` (cells 4–7) built successfully
  (19298, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells8` (cells 8–11) built successfully
  (67465, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells12` (cells 12–15) built successfully
  (29417, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells16` (cells 16–19) built successfully
  (9111, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells20` (cells 20–23) built successfully
  (36728, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells24` (cells 24–27) built successfully
  (5304, exit 0); its current olean/ilean are valid.
- [x] `PrimeArchThetaFirstAtomQuadratureCells28` (cells 28–31) built successfully
  (86031, exit 0, recovered from the completed-command record); current artifacts are valid.
- [x] All twenty production helpers are imported by the RHTower umbrella. Do not compile umbrellas.
- [x] Production-source scans find no native decision tactic, placeholders, added axioms, raised
  limits, or temporary diagnostics. `git diff --check` passes.
- [x] All standalone probes, including `HgtFirstAtomPolynomialProbe` and
  `HgtFirstAtomCompactProbe`, and their sources/audit files/olean/ilean artifacts are removed.
  A source-wide check found no remaining Lean references to either probe.

## Current process and remaining work

**Active owned Lean session: 55140**, building
`RHTower/PrimeArchThetaFirstAtomQuadratureCells32.lean` (cells 32–35).
Wait for this session before starting another Lean process.

The isolated `reduce` replacement probe failed at the default recursion limit (57280, exit 1),
with downstream incomplete-value errors. No limits were changed. Production Certificates
was never modified; all existing table checks remain valid. The probe source, audit file,
and any probe artifacts have been removed. Continue the validated `cbv` certificates.

Then build, separately and in the foreground:

1. The remaining `PrimeArchThetaFirstAtomQuadratureCells<N>` modules, with
   `N = 36, 40, 44, 48, 52, 56, 60`.
   Each certifies exactly four cells, from `N` through `N + 3`.
2. `PrimeArchThetaFirstAtomQuadratureArithmetic` (all five sums).

Use `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.ilean GaloisForLFunctions/RHTower/<Module>.lean`
from `formal/`, one process at a time. These oleans are required by the next source file being
written. Only the cells 0–31 tables have passed; do not mistake the last-cell probe for all-cell validation.

Finally check the actual PA target directly with
`lake --old env lean GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean`.
Temporarily append axiom-print commands for
`RHTower.ThetaRationalQuadrature.firstAtom_bounds`,
`RHTower.thetaRationalQuadrature_firstAtom_bounds`, and
`RHTower.thetaCuspFirstAtom_highOrder_five_bounds`; remove only those diagnostics afterward.
The HT target already passed its final direct check and needs no repetition absent changes.

After the PA audit succeeds, remove its stale original-target olean/ilean pair. Both still date
October 22, with mtime `1792702343` and sizes `1813872` / `130207`, respectively. They predate this
task and contain the old native proof. The HT stale pair is already removed. Do not rebuild targets
unless another file being written imports them. Preserve unrelated work.
Rewrite this card as a concise formalized record and move it to `3-formalized` only after all
remaining checks pass.

## Implementation notes

- Integration must normalize `List.drop` before applying `Enclosure.mass.eq_2`. Normalize the
  cached next-tail equation identically, then rewrite cached width powers before scalar `cbv`.
- The initial width-zero branch omitted `rw [Enclosure.pow]`; its equality certificates were
  valid but retained nested unevaluated arithmetic. This is fixed and audited. Do not raise limits.
- The production macro stages Horner composition, multiplication rows, and integration blocks of
  at most eight coefficients. All five cell-63 rows now validate this exact implementation.
- Automatic repository snapshots have sometimes committed intermediate work. Preserve others'
  changes; `git diff` alone does not enumerate everything done by this task.
- The original sixteen-cell batch occupied 18 GB, including 17 GB of compressed memory. Its owned
  process was terminated and exit 143 confirmed before restarting. Tables now contain four cells
  each; certificate mathematics and the cell generator are unchanged. No artifact from that
  interrupted batch remains.
