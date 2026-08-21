# Chiral Schatten frame retains CCM orientation discarded by positive covariance

- **ID:** `ccm-projective-gauge-chiral-schatten-frame`
- **Stage:** 3-formalized
- **Type:** NEW SCIENTIFIC KNOWLEDGE
- **Source:** corpus weld: projective-gauge trace-class carrier × `InvolutiveProjectiveWedgeTransportLaw` × skew-adjoint rank-one calculus × Plücker orientation corpus
- **Lean module:** `GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralOperator`
- **Status:** closed and unconditional; not an RH proof

## Result

Let `w` and `s_xi` be the weight and matched-source columns of the actual CCM
projective gauge, and define

`A_xi = |w><s_xi| - |s_xi><w|`.

Lean proves that `A_xi` is a skew-adjoint Schatten-one operator of rank at most
two and that every matrix coefficient is the oriented minor

`w(a) conj(s_xi(b)) - s_xi(a) conj(w(b))`.

The anchor coefficients satisfy

- atom/weight anchor: `-a_n S_n(xi)`;
- atom/source anchor: `a_n`.

Their totalized negative ratio therefore recovers the intact signed matched
source `S_n(xi)`. Multiplication by `i` gives a self-adjoint Schatten-one
orientation observable with the same rank bound. Its spectral integral of
anchor-matrix ratios is exactly every finite actual matched prime--polar CCM
block.

## Formal endpoints

- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_skewAdjoint`
- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_hasRankLE_two`
- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralOperator_matrix`
- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralReporter_eq`
- `ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationOperator_isSelfAdjoint`
- `ccmActualHeadMatchedPhaseProjectiveGaugeHermitianOrientationReporter_eq`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_hermitianOrientationSchattenOperator`

## New principle

The positive covariance carrier stores the two feature rays but is invariant
under source-frame reversal. The antisymmetric exterior square is the minimal
rank-two trace-class carrier that retains ordered frame orientation. This
separates two previously conflated jobs: positive trace-class geometry controls
size and compactness; the chiral Schatten component carries source sign.

The result does not force the required orientation. It identifies the next
receiver problem precisely: find a corpus mechanism that acts on the signed
self-adjoint chiral observable rather than only on its positive square or Gram
covariance.

## Verification

- direct check: `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadMatchedPhaseProjectiveGaugeChiralOperator.lean`
- exact leaf build: `lake build GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralOperator`
- selected theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions/RHTower.lean`

## Research log

- 2026-08-21 — Bures and positive Markov welds rejected: covariance is orientation-blind, while Markov transport existence is already equivalent to RH.
- 2026-08-21 — Chiral operator, Hermitian orientation observable, exact source reporter, and finite actual-block identity proved in Lean and leaf-built.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
