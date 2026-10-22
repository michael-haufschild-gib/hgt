# Trace zero forces `H¹` under analytic forcing, formalized

- **ID:** `suzuki-scalar-analytic-forcing-trace-zero-h1`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-scalar-analytic-forcing-trace-zero-h1.md`
- **Lean (built for this card):**
  - `formal/GaloisForLFunctions/HTGeometry/LogNormalDifferentiatedEquation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaCutoffDifferentiatedIdentity.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaCutoffIdentityBounds.lean`
  - `formal/GaloisForLFunctions/HTGeometry/EndpointGermAnalytic.lean`
  - `formal/GaloisForLFunctions/HTGeometry/EndpointGermDerivative.lean`
  - `formal/GaloisForLFunctions/HTGeometry/LogChartEnergyExtended.lean`
  - `formal/GaloisForLFunctions/RHTower/ShiftedGammaConjugation.lean`
  - `formal/GaloisForLFunctions/RHTower/ShiftedGammaJumpDerivative.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaTestPairingMajorant.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaJumpTranspose.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaCutoffCommutatorBridge.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaCompactSupportWall.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaWallTerminalBlockSource.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaWallBlockTransfer.lean`
  - `formal/GaloisForLFunctions/RHTower/ScalarAnalyticForcingH1.lean`
- **Lean (inherited from the four input cards, all stage 3):**
  - `formal/GaloisForLFunctions/HTGeometry/LogNormalEquationTrace.lean`,
    `GammaTransportKernel.lean`, `HalfLogCesaroAverage.lean`, `LogChartEnergyTransfer.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiForcedStripGluing.lean`,
    `SuzukiForcedStripDatum.lean`, `SuzukiGammaStripGluing.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaWallCutoffCommutator.lean`,
    `WallOneBlockEstimate.lean`, `WallBlockSeries.lean`, `WallForcedProfileMemLp.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaWeightedTailCoercivity.lean`,
    `SuzukiGammaShiftKappa.lean`, `SuzukiGammaMollifiedEquation.lean`,
    `SuzukiGammaWeakDomainUpgrade.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` the operators `P` and `R_full` | `fullLogDirichlet`, `fullPrimitive`, `gammaTransport`, `secondDifference`, `gammaTransportKernel` |
| `(3)` the analytic endpoint germ | `hasSum_endpointGerm`, `summable_norm_endpointGerm` |
| `(5)` the signed half-log trace exists | `tendsto_halfLogTrace_mollified`, `tendsto_halfLogTrace_of_equation` |
| `(9)` the differentiated equation | `hasDerivAt_gammaTransport`, `hasDerivAt_fullPrimitive`, `hasDerivAt_source_of_logNormalEquation` |
| `(10)` the differentiated germ's rate | `exists_bound_deriv_endpointGerm`, `exists_bound_deriv_endpointGerm'` |
| `(11)` the Fourier multiplier `r` | `wallSymbol`, `gammaJumpMultiplier` |
| `(12)` the frequency ODE | `forcedStripLine`, `stripSolution`, `forcedParticular` |
| `(13)` trace zero ⟹ upper-strip gluing | `forcedGlue_iff_halfLogScatter_eq_zero`, `halfLogScatter_eq_zero_iff` |
| `(14)` the exact differentiated cutoff identity | `gammaCutoff_differentiated_identity`, `gammaCutoff_differentiated_identity_of_bounds` |
| the commutator of `(14)` is the corpus wall commutator | `gammaCommutator_eq_gammaWallCommutator`, `norm_gammaWallCommutator_le_exp` |
| the `χ′`-terms of `(14)` are exponentially walled | `norm_le_exp_of_compactSupport`, `abs_gammaTransport_le_exp_of_compactSupport` |
| `(15)` the block source space, and membership | `gammaWallBlockNorm`, `gammaWallBlockNorm_lt_top_of_exp_wall`, `gammaWallBlockNorm_lt_top_of_terminal_exp_wall` |
| `(16)` the block Hardy transfer | `summable_gammaWallBlockPiece_norm`, `summable_blockSolutions_of_gammaWallBlockNorm`, with `eLpNorm_vectorAngularTransform_eq` the Plancherel half |
| conjugation by `e^{σL}` | `shiftedSecondDifference_exp_mul`, `shiftedGammaJump_exp_mul` |
| `R_σ` commutes with `d/dL`; `R_σᵀ = R_{−σ}` | `hasDerivAt_shiftedGammaJump`, `deriv_shiftedGammaJump`, `integral_shiftedGammaJump_mul_test` |
| `(17)` the shifted numerical range | `suzukiGammaShiftKappa`, `neg_suzukiGammaShiftKappa_le_integral`, `neg_suzukiGammaShiftKappa_mul_le_shiftedGammaForm` |
| `(18)`, `(7)` the weighted derivative and `H¹` | `suzukiGamma_weakDomain_upgrade`, `suzukiGamma_profile_H1`, `scalarAnalyticForcing_physical_H1` |
| `(19)` the chart energy identity, extended | `integral_sq_spatial_eq_integral_exp_weighted`, `lintegral_sq_spatial_eq_lintegral_exp_weighted` |
| `(8)` the physical `H¹` conclusion | `lintegral_sq_spatial_ne_top_of_weighted`, `lintegral_sq_spatial_ne_top_of_weightedDeriv`, `lintegral_sq_logTransport_ne_top` |
| `(20)` every exponential polynomial has an analytic germ | `differentiable_expPolynomial`, `hasSum_endpointGerm_expPolynomial` |

## Notes

**Why `(9)` costs nothing beyond a Lipschitz derivative.**  The primitive inside `P` cancels one copy
of the profile, and the transport commutes with differentiation because its kernel does not see the
evaluation point.  The domination for differentiating under the integral sign is the kernel's *first
moment*: a Lipschitz derivative makes the differentiated second difference `O(s)` uniformly in the
base point, and `s·k(s)` is integrable on the whole positive ray — at the origin because the factor
`s` cancels the pole, at infinity because the kernel decays.  No second-derivative bound enters.

**`(14)` is pure algebra.**  With `W = χF` the product rule gives `W′ = χ′F + χF′`, additivity splits
the transport, and `([R,χ]F)′ = [R,χ′]F + [R,χ]F′` — itself the product rule plus `R∘d/dL = d/dL∘R` —
removes the derivative of `F` from inside the commutator.  Substituting `(9)` gives the display.

**The three walls that put `(14)`'s right side in the block class.**  `χG′` is supported on a
terminal ray and decays at rate `δ`, so its block norm is a geometric series whenever `σ < δ`; a
one-sided source has only finitely many nonzero negative blocks, which is why the two-sided rate-one
condition of `gammaWallBlockNorm_lt_top_of_exp_wall` is not needed.  The commutator terms are the
corpus's `gammaWallCommutator`, whose two-sided `O(e^{-|L|})` wall is already proved.  The
`χ′`-terms are compactly supported, and so are exponentially walled trivially; their *transports*
are walled for a different reason — past the support the diagonal term vanishes and the translates
can only reach the support at scale `s ≥ |L| − R − 1`, where the kernel has already decayed.

**`(19)` had to be restated in extended form.**  The chart identity
`∫‖∂_r u‖²dr = ∫e^{L}‖F′‖²dL` is an equality of Bochner integrals and therefore says nothing about
finiteness.  For `ℝ≥0∞` it does, and then `e^{2σL}` with `σ > 1/2` dominates the chart's own `e^{L}`
on the terminal ray.  That is exactly the card's choice `1/2 < σ < min(1,δ)`.

**What is not claimed.**  `(21)` is explicitly an `[OPEN SOURCE CONNECTOR]`, and the card's last four
gates — prime-seam/Feshbach forcing, application to every completed trace-zero mode, raw Evans
injectivity, RH — are route statements, not theorems of this card.
