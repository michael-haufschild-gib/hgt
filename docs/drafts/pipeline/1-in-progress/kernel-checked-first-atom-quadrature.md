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
- [x] Enclosures, Seeds, and Certificates have current valid olean/ilean artifacts.
- [x] Width certificates are literal integers: the zero case explicitly unfolds `Enclosure.pow`;
  width 57 is `[0,1]` over `10^30` with standard axioms (Seeds session 79079, exit 0).
- [x] Two- and eight-coefficient integration tails pass (56556, exit 0).
- [x] All five rows at cell 63 pass, including every integration tail and final numerator axiom
  audit (26748, exit 0). Every audit has only the three standard axioms above.
- [x] All eight production helpers are imported by the RHTower umbrella. Do not compile umbrellas.
- [x] Production-source scans find no native decision tactic, placeholders, added axioms, raised
  limits, or temporary diagnostics. `git diff --check` passes.
- [x] All standalone probes and the temporary `HgtFirstAtomPolynomialProbe` source/olean/ilean
  have been removed. No scratch file is needed to continue.

## Current process and remaining work

**Active owned Lean session: 31851**, building
`RHTower/PrimeArchThetaFirstAtomQuadratureCells0.lean` (cells 0–15). No errors have been emitted.
Wait for this session before starting another Lean process.

Then build, separately and in the foreground:

1. `PrimeArchThetaFirstAtomQuadratureCells16` (cells 16–31).
2. `PrimeArchThetaFirstAtomQuadratureCells32` (cells 32–47).
3. `PrimeArchThetaFirstAtomQuadratureCells48` (cells 48–63).
4. `PrimeArchThetaFirstAtomQuadratureArithmetic` (all five sums).

Use `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.ilean GaloisForLFunctions/RHTower/<Module>.lean`
from `formal/`, one process at a time. These oleans are required by the next source file being
written. No table olean has passed yet; do not mistake the last-cell probe for all-cell validation.

Finally check the actual PA target directly with
`lake --old env lean GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean`.
Temporarily append axiom-print commands for
`RHTower.ThetaRationalQuadrature.firstAtom_bounds`,
`RHTower.thetaRationalQuadrature_firstAtom_bounds`, and
`RHTower.thetaCuspFirstAtom_highOrder_five_bounds`; remove only those diagnostics afterward.
The HT target already passed its final direct check and needs no repetition absent changes.

After success, remove the stale original-target olean/ilean pairs: PA artifacts date October 22,
HT artifacts October 23, both predating this task and still containing the old native proofs.
Do not rebuild targets unless another file being written imports them. Preserve unrelated work.
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
