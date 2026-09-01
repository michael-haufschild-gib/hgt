# Finite range-determinant holonomy as selector

- **ID:** `ULF-RDH-NOGO-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED AS SELECTION MECHANISM
- **Statement:** Put route gauges on canonical range determinant line and force RH by triviality of
  their finite holonomy.

## Exact killing theorem/mechanism

Canonical range determinant line exists and its gauge covariance is correct
(`RangeDeterminantFormation`). But finite determinant holonomy is already a downstream classifier:

- `ArithmeticXiStokesCentralRankPort` identifies literal Xi cyclic residue with determinant
  holonomy defect and proves zero iff critical-line support, while explicitly not proving global
  vanishing.
- `DeningerExponentGammaSixShellTransportRigidity` proves exceptional two-sheet reflection
  coefficient is a gauge coboundary, so reflection covariance has no invariant horizontal
  holonomy by itself.
- `ConstitutiveRecoveryCocycleHolonomy` proves finite cycle holonomy classifies gauge equivalence;
  it does not force the holonomy class to vanish.

Thus replacing route scalars by one finite range line improves carrier semantics but does not
narrow literal Xi responses. Assuming a global flat section or trivial holonomy inserts selection.

## Strongest positive survivor

Every injective finite-rank formation canonically factors through a one-dimensional determinant
line of its actual range; the embedded line equals ambient Pluecker span, Gram positivity is its
phase/orientation quotient, and source gauge changes act by determinant character. Paper theorem
`ULF-RDPD-001`; Lean module `RangeDeterminantFormation`.

## New insight

Any determinant-line selection obstruction must live beyond a globally framed finite line: in
cofinal/singular gluing, rank-changing relative determinant transport, or failure of a global
nonvanishing section. Finite route transition ratios are gauge data, not source selection.

## Status

- Finite-holonomy selection retired.
- Positive survivor paper-proved and Lean-certified.
- Next audit target: source-generated rank-changing/cofinal relative determinant system.

## Log

- 2026-09-01 — carrier theorem proved; determinant-holonomy corpus hostile audit completed; finite
  selection mechanism retired.
