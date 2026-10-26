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
- [x] `PrimeArchThetaFirstAtomQuadratureCells0` (cells 0–3) built successfully
  (53008, exit 0); its current olean/ilean are valid. Olean size is 617 MB.
- [x] `PrimeArchThetaFirstAtomQuadratureCells4` (cells 4–7) built successfully
  (19298, exit 0); its current olean/ilean are valid.
- [x] All twenty production helpers are imported by the RHTower umbrella. Do not compile umbrellas.
- [x] Production-source scans find no native decision tactic, placeholders, added axioms, raised
  limits, or temporary diagnostics. `git diff --check` passes.
- [x] Earlier standalone probes and the temporary `HgtFirstAtomPolynomialProbe` source/olean/ilean
  have been removed. The new, uncompiled reduction probe is listed below and still needs cleanup.

## Current process and remaining work

**Active owned Lean session: 67465**, building
`RHTower/PrimeArchThetaFirstAtomQuadratureCells8.lean` (cells 8–11). No errors have been emitted.
Wait for this session before starting another Lean process.

Before building further tables, check the prepared smaller-proof experiment below. The large
olean size warrants checking whether definitional reduction can avoid explicit reduction traces.
Production Certificates is unchanged; the existing table checks remain valid.

### Prepared reduction probe

- Corpus searches for kernel normalization and `conv reduce` found no relevant project precedent.
  Mathlib search was performed afterward. Lean's `Lean/Elab/Tactic/Conv/Basic.lean:95` confirms
  `reduce` calls `changeLhs (reduce lhs)`, so it uses definitional equality without new axioms.
- `formal/HgtFirstAtomCompactProbe.lean` is a copy of Certificates with the command renamed to
  `first_atom_cell_reduce`, every terminal `cbv` replaced by `reduce`, and one complete cell 63
  appended. It has NOT been compiled yet. No limits are changed.
- `/tmp/hgt_first_atom_reduce_audit.lean` imports that probe and audits all five raw numerators.
  Thus an olean for the probe is needed by an actual file being checked.
- After session 67465 exits, build the probe explicitly with `lake --old env lean -o
  .lake/build/lib/lean/HgtFirstAtomCompactProbe.olean -i
  .lake/build/lib/lean/HgtFirstAtomCompactProbe.ilean HgtFirstAtomCompactProbe.lean`, from `formal/`.
  If it succeeds, check `/tmp/hgt_first_atom_reduce_audit.lean` with the same foreground Lean
  command and inspect the probe artifact size. Adopt the change only if the full cell and axiom
  audits pass without limit changes. Remove probe source/audit/artifacts afterward.
- If `reduce` fails at default limits, preserve the checked production method and resume tables.
  Do not confuse failures in this isolated probe with production failures.

Then build, separately and in the foreground:

1. The remaining `PrimeArchThetaFirstAtomQuadratureCells<N>` modules, with
   `N = 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60`.
   Each certifies exactly four cells, from `N` through `N + 3`.
2. `PrimeArchThetaFirstAtomQuadratureArithmetic` (all five sums).

Use `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.ilean GaloisForLFunctions/RHTower/<Module>.lean`
from `formal/`, one process at a time. These oleans are required by the next source file being
written. Only the cells 0–7 tables have passed; do not mistake the last-cell probe for all-cell validation.

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
- The original sixteen-cell batch occupied 18 GB, including 17 GB of compressed memory. Its owned
  process was terminated and exit 143 confirmed before restarting. Tables now contain four cells
  each; certificate mathematics and the cell generator are unchanged. No artifact from that
  interrupted batch remains.
