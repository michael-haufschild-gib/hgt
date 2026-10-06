# Complete signed kinetic source tensor (C82)

- **ID:** tt-complete-kinetic-source-tensor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route TT; tt-kinetic-contraction-source
- **Statement:** The entire cleared source has an exact twenty-by-ten reduced kinetic/drift expansion; all block and cofactor input cells and their support laws are audited.

## Goal

Expose every signed input to the full finite-clock source inequality.
This is an exact algebraic representation. No source-value or control sign
is asserted, and the two hundred source cells have not all been individually
normalized.

## Gates

- [x] Full literal source retained, with no added source-sign premise.
- [x] Dependency-closed algebraic proof below, [PROVED HERE].
- [x] Twelve direct production leaves;997 imported declaration audits.
- [ ] Standalone publication.

## Proof

The complete moment of order n has drift degree at most n/2, uniformly in
its kinetic index. The corresponding full flow block has drift degree at
most n/2+1. The five signed cofactors have respective drift bounds8,7,6,5,4;
their matching block bounds are2,3,4,5,6. Exact two-index convolution gives
drift bound10 for each product and hence for their complete signed sum.

C81 proved that every kinetic coefficient has zero constant drift term.
Its exact `divX` quotient therefore has degree at most9. Expanding that
quotient and the complete degree19 kinetic source gives, for all complex
h,v,z, including zero clock and zero drift,

`clearSlope(h,v,z) = v * sum_(j<20) (sum_(b<10) sourceCell(h,j,b+1)*v^b)*z^j`.

All220 block cells and475 cofactor cells are produced from the original
moment/flow identities. All105 drift rows have complete arbitrary-index
reconstructions, and all ten families have arbitrary-kinetic selectors.
Support laws prove that omitted indices vanish. No sign is discarded.

## Lean certificate

Namespace `HTGeometry.ThetaRatioKineticContraction`.

- `ThetaCuspRatioKineticDriftSupport`: uniform moment/cofactor support,
  exact cofactor forms and kinetic degree bounds;33 declarations.
- `ThetaCuspRatioKineticDriftBlocks2/4/6/8/10`: complete block cells,
  rows, selectors and support;350 declarations.
- `ThetaCuspRatioKineticDriftCofactors2/4/6/8/10`: complete cofactor cells,
  rows and selectors;610 declarations.
- `ThetaCuspRatioKineticReducedTensor`: complete source support, reduced
  coefficient degree/expansion and full tensor identity;4 declarations.

Capstone: `completeKineticSlope_reduced_tensor`.
Every leaf passed direct `lake --old env lean -o ... <module>.lean`, with no
diagnostics, and is wired once into RHTower. No umbrella/full build was run.
The33-declaration support audit and964-declaration input/tensor audit contain
only `propext`, `Classical.choice`, and `Quot.sound`.

Audit records: `/tmp/tt_c82_production_manifest.json`,
`/tmp/tt_c82_cells_production_manifest.json`,
`/tmp/tt_c82_support_axioms.log`,
`/tmp/tt_c82_cells_production_axioms.log`,
`/tmp/tt_c82_final_audit_report.json`.

Global lint is not clean:24 unrelated errors, including23 missing umbrella
imports and proof debt in `VerticalProgressionSecondMomentLimit.lean`.
No C82 error; scoped forbidden declarations, raised limits, whitespace and
wiring checks pass. Full diagnostics: `/tmp/tt_c82_lint.log`.

## Learning and remaining frontier

Raw-cast cleanup alone left coefficients of `Polynomial.X` as atoms in some
earlier scalar witnesses. These identities were valid, but multiplying their
unreduced data caused artificial expression growth. Explicit
`Polynomial.coeff_X` simplification is now applied to every block/cofactor
cell before multiplication. The corrected production audits use default
limits. No mathematical sign conjecture was falsified by the earlier tactic
failures.

No hard finite-clock sign gap is closed. Next is the actual full reduced
control/source inequality, beginning with the complete first control.
Full source quadratic, fourth Schur gap, compact/adverse-ray join,
integrated/all-rank closure and RH remain open.

## Log

- 2026-10-06 — corrected production inputs and full tensor audited.
