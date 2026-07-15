# Finite involutive group average as an orthogonal projection

- **ID:** finite-involutive-group-average-orthogonal-projection
- **Stage:** 1-in-progress
- **Type:** source-level Lean formalization awaiting a targeted check
- **Source:** quantum group averaging and finite-group twirling
- **Usefulness gate:** discharges self-adjointness and idempotence premises for an existing RHTower scattering constraint

## Claim

Let `U` be a bounded operator on a real or complex Hilbert space.  If

`U† U = 1` and `U² = 1`,

then `U† = U`.  Consequently the finite `Z₂` average

`P = (1/2) (1 + U) = finiteCyclicGaugeAverage U 2`

is a self-adjoint idempotent, hence the orthogonal projection onto the fixed sector
`ker (U - 1)`.  Every state has the exact value decomposition

`‖P ψ‖² + ‖(1 - P) ψ‖² = ‖ψ‖²`.

This is a static constraint identity, not a time evolution.

## Physics sources

- D. Giulini, “Group Averaging and Refined Algebraic Quantization,” arXiv:gr-qc/0003040, reviews group averaging as a construction of the physical space for first-class quantum constraints.
- W. Kamiński, J. Lewandowski, and T. Pawłowski, “Quantum constraints, Dirac observables and evolution: group averaging versus Schrödinger picture in LQC,” arXiv:0907.4322, applies group averaging to physical Hilbert spaces in loop quantum cosmology.
- M. A. Graydon et al., “Real Randomized Benchmarking,” arXiv:1801.06121, states the finite-group normalized twirl is idempotent and self-adjoint and therefore the orthogonal projection onto the invariant commutant.  The present vector-state `Z₂` result is the corresponding orbit-average law.

## Direct corpus applications

1. `HTGeometry.FiniteConstraintGroupAverage` previously established only algebraic idempotence for the general finite cyclic average.  The new involutive-isometry theorem constructs self-adjointness rather than accepting it as a downstream hypothesis.
2. `RHTower.soninLogFourierScattering` was already involutive.  Its existing exact logarithmic-unitary model also proves norm preservation, so the new generic theorem identifies it as self-adjoint.
3. `RHTower.soninLogFourierInvariantAverage` is now the explicit orthogonal projection onto the physical fixed sector of `soninLogFourierScattering - 1`.
4. `norm_finiteInvolutiveGaugeAverage_sq_add_complement_sq` now proves the invariant/gauge-variant energy partition once in the general HT constraint layer, directly from `U†U = 1` and `U² = 1`.
5. `norm_soninLogFourierInvariantAverage_sq_add_complement_sq` is a direct consumer of that theorem.  Its former proof through two-projection supersymmetry and an artificial zero projection has been removed, so the logarithmic scattering module no longer rebuilds a generic group-average fact locally.
6. On an invariant state, `soninLogFourierInvariantAverage_additiveTranslation_of_fixed` turns a single physical dilation into the exact forward/backward logarithmic-translation pair.  This exposes the cosine channel already implicit in the Mellin/dilation corpus.

## Formalization

- `formal/GaloisForLFunctions/HTGeometry/FiniteConstraintGroupAverage.lean`
  - `finiteCyclicGaugeSum_isSelfAdjoint`
  - `finiteCyclicGaugeAverage_isSelfAdjoint`
  - `isSelfAdjoint_of_adjoint_mul_self_of_sq_eq_one`
  - `finiteInvolutiveGaugeAverage_isSelfAdjoint`
  - `finiteInvolutiveGaugeAverage_isIdempotentElem`
  - `norm_finiteInvolutiveGaugeAverage_sq_add_complement_sq`
- `formal/GaloisForLFunctions/RHTower/SoninLogCoordinateScattering.lean`
  - `soninLogFourierScattering_norm`
  - `soninLogFourierScattering_adjoint_mul_self`
  - `soninLogFourierScattering_sq_eq_one`
  - `soninLogFourierScattering_isSelfAdjoint`
  - `soninLogFourierInvariantAverage`
  - fixed-sector equivalence, exact norm partition, and forward/backward translation symmetrizer

## Status

[SOURCE FORMALIZED, NOT CHECKED] The declarations have been added source-first.  No Lean command,
build, linter, numerical experiment, or other computation was run, in accordance with the active
research constraint.  Promotion to Stage 3 requires one targeted module check in a later authorized
session; it does not require a full build.
