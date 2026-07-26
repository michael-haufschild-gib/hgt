# LAW475 — Xi prime–Gamma contour Turán bottom-shell universality

## Status

- Pipeline stage: 3 — formalized
- Conjecture label: `LAW475`
- Discovery mode: theorem-generated Xi heat/source-contour closure
- Mathematical computations used: none
- Novelty status: `[NOVELTY UNVERIFIED]`

## Corpus parents

1. `XiGaussianExplicitFormulaRectangle.
   exists_admissible_rectIntegral_gaussianSource_eq_xiZeroCopy_sum`
   realizes any finite divisor packet by an arithmetic prime–Gamma contour for each
   Gaussian–Hermite test.
2. `XiGaussianExplicitFormulaRectangle.
   exists_admissible_gaussianSource_contour_approximates_heatMoment`
   proves individual cofinal approximation of each Gaussian heat moment.
3. `XiGaussianHeatTuranDefect.xiHeatTuranDefect_nonneg_of_riemannHypothesis`
   makes the exact order-two Gaussian Hankel determinant nonnegative under RH.
4. `XiHeatTuranBottomDetection.exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair`
   makes it eventually negative when the bottom squared shell is one off-critical conjugate pair.

No existing theorem uses one common rectangle for the full order-two moment packet or transfers
the Turán sign to the arithmetic contour determinant.

## Universal law

For every positive heat time and every accuracy, one admissible arithmetic rectangle
simultaneously approximates the three Gaussian heat moments `M₀(t), M₁(t), M₂(t)` through the
normalized continued prime–Gamma source contours

`Cₙ(t; R) = (2πi)⁻¹ ∮_R z^(2n) exp(-t z²) S_PA(z) dz`.

Define the contour Turán determinant

`D_R(t) = Re C₀(t;R) · Re C₂(t;R) - (Re C₁(t;R))²`.

Then:

1. under RH, for every `ε > 0` one can choose `R` with `D_R(t) > -ε`;
2. if the bottom squared Xi shell is a single off-critical conjugate pair, then for every
   sufficiently large `t` one can choose `R` with `D_R(t) < 0`.

Thus one finite prime–Gamma contour, not three unrelated contours, carries the order-two Xi heat
Hankel sign and detects the off-critical bottom shell.

## Dependency-closed paper proof

For each `n = 0,1,2`, summability of the Gaussian heat monomial terms makes the net of finite
partial sums converge to `Mₙ(t)`. The intersection of these three eventual conditions is still
eventual. Choose one finite divisor packet beyond that joint threshold, then apply the general
rectangle-synthesis theorem once. The resulting rectangle contains the common packet, so all
three normalized contour sums lie within the requested accuracy of their moments.

The polynomial map

`T(A) = Re A₀ · Re A₂ - (Re A₁)²`

on `Fin 3 → ℂ` is continuous and sends the exact heat-moment packet to
`xiHeatTuranDefect t`.

Under RH, that exact value is nonnegative. The inverse image of `(-ε, ∞)` is therefore an open
neighborhood of the heat packet. Joint contour approximation places one source-contour packet in
that neighborhood, giving `D_R(t) > -ε`.

For a single off-critical conjugate bottom shell, the bottom-detection theorem supplies `T₀` such
that the exact Turán defect is negative for every `t > T₀`. The inverse image of `(-∞,0)` is then
an open neighborhood of the exact heat packet. Joint contour approximation again places one
source-contour packet inside it, giving `D_R(t) < 0`.

No quantitative experiment, numerical zero data, RH assumption in the off-critical direction,
or unproved interchange is used.

## Strength boundary

The off-critical conclusion assumes the proved simple bottom-shell shape: one conjugate class.
The corpus does not yet prove eventual Turán negativity for arbitrary multi-class bottom shells.
The theorem also asserts existence of a sign-detecting cofinal rectangle, not that every
sufficiently large rectangle has that sign.

## Lean target

File:
`formal/GaloisForLFunctions/RHTower/XiPrimeGammaContourTuranBottomShellUniversalityLaw.lean`

Planned declarations:

- `xiGaussianSourceContourMoment`
- `xiGaussianHeatMomentPacket`
- `xiGaussianSourceContourMomentPacket`
- `xiGaussianMomentPacketTuran`
- `exists_admissible_gaussianSource_contour_approximates_heatMomentPacket`
- `exists_primeGammaContourTuran_gt_neg_epsilon_of_rh`
- `exists_eventually_negative_primeGammaContourTuran_of_bottom_conjugate_pair`
- `xi_primeGammaContourTuran_bottomShellUniversality`

## Verification log

- Paper proof: dependency-closed
- Lean exact check: passed with
  `lake env lean GaloisForLFunctions/RHTower/XiPrimeGammaContourTuranBottomShellUniversalityLaw.lean`
- Axiom audit: pending final audit
- Final targeted module build: pending final audit
- Umbrella wiring: complete in `GaloisForLFunctions/RHTower.lean`

## Novelty audit

Primary-source searches were run only after paper proof and direct Lean elaboration. Nearby
literature studies de Bruijn–Newman heat flow, effective Xi heat approximation, real-zero
dynamics, and general explicit-formula/Weil positivity:

- https://arxiv.org/abs/1904.12438
- https://arxiv.org/abs/1801.05914
- https://arxiv.org/abs/2005.05142
- https://arxiv.org/abs/1910.14368

No located source states the exact common-rectangle law: three Gaussian–Hermite moments
simultaneously reconstructed from one continued prime–Gamma contour, with its finite Turán
determinant nearly nonnegative under RH and eventually negative for a simple off-critical bottom
shell. Search coverage cannot prove absence from all literature, so status remains
`[NOVELTY UNVERIFIED]`.
