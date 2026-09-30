# Ξ is Laguerre-positive on a positive proportion of the line (explicit off-line moment)

- **ID:** xi-laguerre-positive-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** rh-goal-loop-opus-2026-09-29 cycle 31; LA receivers F0240/F0269; corpus chain
  `ZetaGateProductAFE*` (unconditional gate with an existential constant), `XiLaguerreShadow`,
  `ZetaTwoThirdsOffLineMomentConstant`, `Sieve/SelbergDiagonalUpperAsymptotic`, `HighBlockChiModulus`.
- **Statement:** for all large `V`, the first Laguerre inequality `Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` and the
  vertical monotonicity of `y ↦ |Ξ(x+iy)|` on `y ≥ 0` hold on a subset of `[0, V]` of measure
  `≥ (29/50)V − 21/100`; the input is the unconditional explicit off-line moment
  `Σ_{0<Im ρ≤V} m_ρ (Re ρ − ½)⁺ ≤ (21/100)V`.

## Goal
A density partial producer for the LA receivers F0240 (Laguerre–Pólya) and F0269 (vertical
monotonicity): both fail only on the shadow `⋃ (γ − (β−½), γ + (β−½))` of the off-line zeros, whose
measure is at most twice the off-line first moment. The corpus proves the moment is `O(V)` with an
existential constant; an explicit constant `< ½` gives positive density.

## Approach
The corpus gate constant is `c₀ = 200·M_R/R`, `M_R = 128e·C_L²·e^{R/25}·e^{4R}`, crude in four places:
the Barban–Vehov gcd form (`64 C_L²`), the `χ`-pair weight (`e`, and `U^{2d} ≤ 2e^{4R}`), the
logarithm of the mollifier length (`400/log U`), and the displacement range `d log U ≤ 2R`.
Sharp replacements, all from owned results:
1. `J_s(e) ≤ e^{2(s−1)} φ(e)` for squarefree `e`, so the gcd form is `≤ N^{4d}·D(N)` with
   `D(N) = Σ φ(e) (Σ_{e|m} w_m/m)²` the Selberg diagonal, `D(N)/log N → 1` (corpus).
2. `‖χ(½−d+iτ)‖ = (τ/2π)^d e^{e}`, `|e| ≤ d(π/τ + 5/τ²)` (corpus).
3. `log N / log U → 1/100`, `d log U ≤ R log U/log(U−1) → R`.
Then the block main term tends to `(50/R)·e^{2R + R/25}`; the dyadic law, gate and the two-thirds
ceiling give `4π·M(V) ≤ (log c − 5R/3 + η)V`. At `R = 3`, `η = 1/5`: `log(50/3) + 1.12 + 0.2 ≤ 4.1 log 2 + 1.32 ≈ 4.162 < 4π/3`, so `M(V) ≤ V/3`.
With each conjugate pair's shadow counted once, `vol(S ∩ [0,V]) ≤ 2M(V+½) ≤ (2V+1)/3`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Lean
- `RHTower/Sieve/BarbanVehovGcdFormSharp.lean`: `gcdPowKernel_le_rpow_mul_totient` (`J_s(e) ≤ e^{2(s−1)}φ(e)`,
  squarefree `e`), `sum_barbanVehov_gcd_rpow_div_le_diagonal`.
- `RHTower/ZetaGateProductAFESharpHighBlock.lean`: `gcdSum₂_hbReal_le_diagonal`,
  `norm_chiPairWeight_le_sharp`, `norm_integral_window_chiPairWeight_le_sharp`, `mollLong`, `sharpBlockConst`,
  `tendsto_sharpBlockFactor`, `sharp_mainTerm_le`, `exists_highBlock_bound_sharp`.
- `RHTower/ZetaGateProductAFEZetaBlock.lean`: `exists_zetaBlock_meanSquare_le` (`∫_a^v|ζ|² ≪ a log U`).
- `RHTower/ZetaOffLineMomentExplicit.lean`: `integral_normSq_zeta_mul_edPoly_le_sq_mul`, `integral_normSq_zeta_mul_edPoly_convexity`,
  `lowBlock_power_le`, `zetaDyadicMeanSquareLaw_long`, `zetaMollifiedMeanSquareGate_sharp`,
  `eventually_offLineMoment_le`.
- `RHTower/XiLaguerreShadowDensity.lean`: `exists_boxZero_of_mem_xiShadow`,
  `volume_xiShadow_inter_Icc_le_offLineMoment`, `eventually_volume_xiShadow_inter_Icc_le`,
  `eventually_volume_laguerre_monotone_ge`.
- `RHTower/XiHadamardSignDensity.lean`: `exists_boxZero_of_hadamard_fail`, `volume_hadamardFail_le`,
  `eventually_volume_hadamardSign_ge` (Hadamard sign F0242 on a third of the right half-strip area).
- `RHTower/XiCriticalScaleDiscSeamExplicitDensity.lean`: `mul_card_badCriticalScaleDiscs_le_offLineMoment`,
  `exists_card_goodCriticalScaleDiscs_ge` (TG seam contraction on `≥ 31%` of right discs, every scale).
- `RHTower/XiSliceCoeffDensity.lean`: `xiSliceCoeff_nonneg_of_not_mem_xiShadow`,
  `eventually_volume_sliceCoeff_nonneg_ge` (all-order slice positivity on heights of measure `≥ 0.54V`).
- `RHTower/ZetaFixedSigmaDensity.lean`: `exists_zeroCount_fixedShift_le`, `eventually_zeroCount_fixedSigma_le`,
  `eventually_volume_hadamardFail_line_le` (Hadamard sign at almost every height of each line `σ > ½`).
All `lake env lean` clean, `--old` leaf builds, axioms `propext, Classical.choice, Quot.sound`,
wired in `RHTower.lean` after `DeBruijnStrictLaguerre`, collision scan clean.

## Log
- 2026-09-30 — created; interfaces verified in Lean sources.
- 2026-09-30 — middle regime by the trivial-mollifier block mean square (`ZetaGateProductAFEZetaBlock`):
  mollifier `U^{1/15}`, high blocks from `U^{5/6}`, `R = 3/2`, moment `≤ 0.21V`, densities 58%, TG 37%.
- 2026-09-30 — mollifier lengthened to `U^{1/25}` (high blocks `a ≥ U^{1/2}`, low blocks by the
  convexity bound): constant `(25/(2R))e^{2R+4R/25}`, `R = 2`, moment `≤ 0.23V`, densities 54%.
- 2026-09-30 — formalized. Sharpening the four crude factors of the corpus gate needed no new analytic
  input beyond the Jordan-kernel comparison: the Selberg diagonal limit and the exact `χ` modulus were
  owned. The mollifier length `U^{1/100}` stays; the constant `50/R` is `1/(2Rθ)` at `θ = 1/100`.
  Improving `θ` toward `½` (BCHB off-diagonal) would raise the density toward `1 − (log(1+1/θ) − …)/2π`.
