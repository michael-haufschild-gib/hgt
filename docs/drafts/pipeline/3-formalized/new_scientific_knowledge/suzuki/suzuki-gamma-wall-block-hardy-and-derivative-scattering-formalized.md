# Gamma-wall block Hardy transfer and the derivative scattering obstruction, formalized

- **ID:** `suzuki-gamma-wall-block-hardy-and-derivative-scattering`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-gamma-wall-block-hardy-and-derivative-scattering.md`
- **Lean (principal modules):**
  - `formal/GaloisForLFunctions/HTGeometry/WeightedHardyInequality.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaStripCarrierTwoSided.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaForcedStripHardy.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaWallHardyBoundary.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaWallCutoffCommutator.lean`
  - `formal/GaloisForLFunctions/RHTower/WallOneBlockEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/WallBlockSeries.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpMultiplier.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpBinetFormula.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpMultiplierAction.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpNearDiagonalLipschitz.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpCommutatorFourierKernel.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpCommutatorH1Bound.lean`
  - `formal/GaloisForLFunctions/RHTower/ShiftedSymbolWeightedDifference.lean`
  - `formal/GaloisForLFunctions/RHTower/ShiftedJumpCommutatorH1Bound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/InverseFamilyThirdDerivative.lean`
  - `formal/GaloisForLFunctions/HTGeometry/InverseFamilyContinuityFromResolvent.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PhaseGeneratorThirdIntegrationByParts.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PowerTailBochnerBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PowerTailBochnerBoundInward.lean`
  - `formal/GaloisForLFunctions/RHTower/WallThirdIntegrationByParts.lean`
  - `formal/GaloisForLFunctions/RHTower/WallThirdRemainderTail.lean`
  - `formal/GaloisForLFunctions/RHTower/WallFinitePart.lean`
  - `formal/GaloisForLFunctions/RHTower/WallThirdBlockDecomposition.lean`
  - `formal/GaloisForLFunctions/RHTower/WallTailOperatorRegularity.lean`
  - `formal/GaloisForLFunctions/RHTower/WallFrequencyFirstBoundary.lean`
  - `formal/GaloisForLFunctions/RHTower/WallFrequencySecondBoundary.lean`
  - `formal/GaloisForLFunctions/RHTower/WallFrequencyThirdBoundary.lean`
  - `formal/GaloisForLFunctions/RHTower/WallVectorDerivativeWall.lean`
  - `formal/GaloisForLFunctions/RHTower/WallScatteringCharge.lean`
  - `formal/GaloisForLFunctions/RHTower/WallScatteringCriterion.lean`
  - `formal/GaloisForLFunctions/RHTower/WallInwardThirdTail.lean`
  - `formal/GaloisForLFunctions/RHTower/WallInwardScatteringCharge.lean`
  - `formal/GaloisForLFunctions/RHTower/WallInwardScatteringCriterion.lean`
  - `formal/GaloisForLFunctions/RHTower/WallScatteringCriterionLine.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCutoffForcingIdentity.lean`

## Formal content

| Card | Lean |
|---|---|
| `(3)` two-sided strip carrier bound | `exists_twoSided_suzukiGammaStripNormSq` |
| `(7)`, `(8)` physical block norm and the wall transfer | `gammaWallBlockNorm`, `gammaWallBlockNorm_lt_top_of_exp_wall` |
| Theorem 1, `(11)` one-block Gamma Hardy estimate | `exists_bound_lintegral_sq_forcedProfile_oneBlock` |
| `(13)` variation of constants on a shifted ray | `forcedStripRay`, `forcedProfile`, `forcedProfile_split` |
| Theorem 2, `(24)` block series convergence | `summable_blockSolutions` |
| Theorem 2, `(25)` the block norm is the angular transform's | `eLpNorm_vectorAngularTransform_eq` |
| `(26)`, `(27)` the jump multiplier and its Binet series | `gammaJumpMultiplier`, `gammaJumpWeight_eq_tsum`, `gammaJumpOperator_freqSuperposition` |
| Theorem 3, `(28)`–`(31)` literal cutoff commutator and its exponential wall | `norm_gammaWallCommutator_le_exp`, `norm_gammaWallCommutator_le`, `gammaWallBlockNorm_gammaWallCommutator_lt_top`, `gammaWallCommutator_integrand` |
| `(33)` the commutator's Fourier kernel | `gammaJump_commutator_kernel` |
| `(34)` derivative decay of the symbol | `exists_deriv_gammaJumpMultiplier_bound`, `abs_gammaJumpMultiplier_le` |
| `(35)` weighted near-diagonal Lipschitz bound | `exists_bound_gammaJump_nearDiagonal`, `abs_gammaJump_farRegion_le`, `exists_bound_gammaJump_global` |
| `(32)` order minus one, real line | `exists_bound_lintegral_sq_gammaJumpCommutatorDensity` |
| `(35a)` order minus one, shifted line | `exists_bound_wallSymbol_global`, `exists_bound_lintegral_sq_shiftedJumpCommutatorDensity` |
| Theorem 4, `(36) ⟹ (37)` | `lintegral_enorm_sq_forcedStripRay_lt_top` |
| `(39)` Hilbert-valued weighted Hardy inequality (and its sharpness) | `lintegral_enorm_hardyAverage_sq_le`, `lintegral_hardyAverage_sq_eq_top_of_le_half` |
| `(41)`, `(42)` the derivative carrier and the sharp wall | `suzukiGammaStripDerivativeNormSq`, `not_integrable_suzukiGammaStripDerivativeNormSq` |
| `(44)` the amplitude recursion `D_{j+1} = C⁻¹∂D_j` | `invFamily`, `invFamilyProduct`, `invFamilyProduct2`, `invFamilyProduct2Deriv` |
| `(45)` the three-fold expansion | `phase_ibp_thrice_of_continuousOn`, `wall_phase_ibp_thrice` |
| `(46)` the finite part and the two charges | `wallFinitePart`, `wall_phase_finitePart_decomposition`, `wallScatteringCharge`, `wallScatteringChargeNeg` |
| `(47)` Theorem 5, outward ray | `lintegral_sq_freq_forcedProfile_ray_ne_top_iff` |
| `(47)` Theorem 5, inward ray | `lintegral_sq_freq_forcedProfile_negRay_ne_top_iff` |
| `(47)` Theorem 5, whole line | `lintegral_sq_freq_forcedProfile_line_ne_top_iff` |
| `(48)` the transported remainder is `O(x^{-2})` | `norm_wallThirdTail_transported_le`, `norm_wallThirdTailNeg_transported_le` |
| `(51)` the exact cutoff forcing identity | `cutoff_forcing_identity`, `cutoff_forcing_identity_commutator` |

## Notes

**The vector form of the wall.**  `(42)` as the card states it is scalar.  What Theorem 5 needs is
the vector statement: `xH(x+iσ)v` is square integrable on a ray only when `v = 0`.  That does not
need the sharp asymptotics at all.  The inverse propagator grows at most like `(1+|x|)^{1/2+σ}`, so
`‖H(x)v‖ ≥ ‖v‖/(K₂(1+|x|)^{1/2+σ})` and the frequency-weighted density dominates `|x|^{1−2σ}`,
whose exponent exceeds `−1` for every `σ < 1`.  `lintegral_sq_freq_stripPropagator_eq_top` and
`lintegral_sq_freq_stripPropagator_negRay_eq_top` are the two rays.

**Why the frequency variable needed its own continuity chain.**  The charges `(46)` are block
averages of a *ray* integral of the three-fold remainder, so that integral must depend measurably on
the frequency.  The corpus's amplitude-continuity lemmas are keyed on `HasDerivAt C (C₁ t) t`, which
is a statement about the position; in the frequency variable the symbol jets are constants and that
hypothesis fails.  `InverseFamilyContinuityFromResolvent.lean` restates the whole chain keyed on
`ContinuousOn (invFamily C) S` alone — the amplitudes are polynomial in the resolvent — and then
`continuousOn_of_dominated` gives frequency-continuity of the ray remainder, the dominating power
tail being frequency-free.

**Both rays, and why only the endpoint changes.**  Every estimate the expansion uses is even: the
amplitude bounds are in `|t|`, and both propagator bounds are in `|y|`.  So the inward statements are
the outward ones with the endpoint reflected, and the only sign that genuinely changes is the
orientation of the moving interval — on the inward side `∫_W^x = ∫_{(-∞,x]} − ∫_{(-∞,W]}`, the
opposite of the outward `∫_Y^x = ∫_{(Y,∞)} − ∫_{(x,∞)}`.

**The shifted commutator.**  `(35a)` is the same convolution estimate with `r(ξ)` replaced by
`r(ξ+iσ) = wallSymbol σ ξ`.  The two facts it consumes are the derivative decay
`‖r_σ′(t)‖ ≤ C₀/(1+|t|)` — the corpus polygamma jet bound past the unit radius, continuity on the
collar inside it — and linear growth, which the mean value theorem then supplies.  The logarithm the
card's `(34)` displays is never needed: the far region is already controlled by the separation.

**What is not claimed.**  The card's last gates — realizing `(51)` on every completed support-pruned
carrier state, `SUZUKI-TRACE-ZERO-H1`, corona no-return, raw Evans injectivity, and RH — remain open
route statements, not theorems of this card.
