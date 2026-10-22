# Xi complex-heat source-contour vertical-bound universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `exists_admissible_gaussianSource_contour_approximates_heatMoment`, which realizes real-time
  Gaussian heat moments as limits of normalized continued prime--archimedean source contours; and
- `summable_norm_xiGaussianHeatTermC_of_rh` plus
  `norm_xiGaussianHeatTraceC_le_of_rh`, which under RH control the complex-time Gaussian trace on
  every vertical line of the open right half-plane.

The real-time contour theorem did not cover complex heat time, while the vertical bound had no
prime--archimedean contour realization.

## Universal law

Assume RH. For every complex heat time `τ` with `Re τ>0` and every `ε>0`, there is an admissible
rectangle such that its normalized continued prime--archimedean contour at the test

`z ↦ exp(-τ z²)`

is within `ε` of the complex-time Xi heat trace. Moreover the same contour approximant obeys

`‖normalized contour‖ < xiGaussianHeatTraceReal(Re τ) + ε`.

Thus RH's vertical cancellation bound is inherited, up to arbitrary accuracy, by arithmetic
source contours rather than existing only on the divisor side.

## Dependency-closed paper proof

1. The complex Gaussian `g_τ(z)=exp(-τz²)` is entire.
2. At a centered Xi spectral point `w_q`, `g_τ(w_q)=exp(-τw_q²)`, exactly the complex heat term.
3. Under RH and `Re τ>0`, the existing vertical theorem gives absolute summability of these terms.
4. Choose a finite divisor packet whose sum is within `ε` of the full complex heat trace.
5. Apply the general admissible-rectangle synthesis law to that packet and `g_τ`. The normalized
   contour equals the sum over all copies enclosed by the resulting rectangle; cofinality preserves
   the finite-sum approximation.
6. RH also gives `‖heatTraceC τ‖ ≤ heatTraceReal(Re τ)`.
7. Triangle inequality combines steps 5 and 6 to give the source-contour norm bound with error
   `ε`.

No spectral truncation is treated as exact, no numerical computation enters, and the only RH use
is the existing absolute-summability and vertical-cancellation theorem.

## Formal targets

- `xiGaussianComplexTestC`
- `analyticOnNhd_xiGaussianComplexTestC`
- `xiGaussianComplexTestC_spectralPoint`
- `exists_admissible_complexGaussianSource_contour_approximates_heatTraceC_of_rh`
- `xi_complexHeat_sourceContourVerticalBoundUniversality`

## Novelty audit

Post-proof searches found classical Guinand--Weil explicit-formula treatments, real heat-flow
evolution of Xi, Fourier optimization with explicit formulas, and finite Weil dictionaries. They
did not reveal the exact conditional law that complex-time Xi heat traces throughout
`Re τ>0` are approximated by continued prime--archimedean rectangles whose norms inherit the RH
vertical cancellation bound with the same arbitrary error.

The exact source-contour vertical law remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/1904.12438
- https://doi.org/10.1093/qmath/haab037
- https://arxiv.org/abs/2607.02828

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/XiComplexHeatSourceContourVerticalBoundUniversalityLaw.lean`

with declarations:

- `xiGaussianComplexTestC`
- `differentiable_xiGaussianComplexTestC`
- `analyticOnNhd_xiGaussianComplexTestC`
- `xiGaussianComplexTestC_spectralPoint`
- `exists_admissible_complexGaussianSource_contour_approximates_heatTraceC_of_rh`
- `xi_complexHeat_sourceContourVerticalBoundUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/XiComplexHeatSourceContourVerticalBoundUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` beside the real-time Gaussian rectangle and
complex-time vertical-bound modules.
