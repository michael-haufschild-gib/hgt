# Matched CCM source as exact determinant-line shear crossing

- **ID:** `ccm-chiral-nodal-source-shear-crossing`
- **Stage:** 3-formalized
- **Type:** NEW SCIENTIFIC KNOWLEDGE
- **Source:** chiral nodal line × corpus Krein crossing × singular determinant-response/adjugate mechanisms
- **Lean module:** `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear`
- **Status:** closed and unconditional; not an RH proof

## Result

Let `Hₙ(ξ)` be the Hermitian `3 × 3` compression of the actual matched chiral Schatten operator,
with unique normalized null vector

`vₙ(ξ) = (aₙ, aₙSₙ(ξ), -1)`.

For the fixed Hermitian source shear

`B = [[0,1,0],[1,0,0],[0,0,0]]`,

Lean proves the exact null-line crossing form

`vₙ(ξ)* B vₙ(ξ) = 2 aₙ² Sₙ(ξ)`.

More strongly, the complete determinant polynomial of the affine Hermitian family is

`det(Hₙ(ξ) + tB) = -2 t aₙ² Sₙ(ξ)`.

It is exactly linear: there are no hidden higher-order terms. Its derivative at the nodal wall is
the same coefficient. At every nonzero-weight arithmetic atom, positivity of the signed matched
source is equivalent both to positive Krein crossing form and to negative determinant slope.
After totalized normalization by `2aₙ²`, the crossing reporter equals the intact source for every
natural index, and every finite actual matched prime--polar block is its spectral integral.

## Formal endpoints

- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear_isHermitian`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_eq`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_isHermitian`
- `det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily`
- `hasDerivAt_det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingForm_pos_iff`
- `det_ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingFamily_one_neg_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeNodalSourceCrossingReporter_eq`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_nodalSourceCrossing`

## New principle

Source orientation has acquired a linear spectral-flow receiver. It is no longer stored only as
a nonlinear ratio, positive covariance, or abstract exterior sign: it is the sign of a simple
determinant crossing of a fixed shear through a canonical operator-derived nodal wall. Gauge
magnitude contributes only the strictly positive factor `2aₙ²`, so it cannot alter orientation.

This is directly compatible with corpus crossing-sign, adjugate, Krein, residue-jump, and Stokes
machinery. Remaining problem is global: prove a source-independent constraint on the aggregate
determinant crossing current strong enough to select its allowed chamber. The local sign itself is
now coefficient-faithful and premise-free.

## Verification

- direct check: `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear.lean`
- exact leaf build: `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeNodalSourceShear`
- selected theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions/RHTower.lean`

## Research log

- 2026-08-21 — Broad receiver search found singular Jacobi/adjugate response, Puiseux simple-crossing sign, and Hankel Krein shear machinery.
- 2026-08-21 — Exact crossing form, full determinant polynomial, wall derivative, source-sign equivalence, normalized reporter, and finite-block identity proved and leaf-built.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
