# Hardy's theorem is Lean-proved unconditionally (2026-08-18)

`RHTower.exists_Xi_zero_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ Xi t = 0`
axioms: [propext, Classical.choice, Quot.sound].

## Module chain (all wired into `GaloisForLFunctions.RHTower`)

1. `RHTower/JacobiThetaBoundaryLimits.lean`
   - `jacobiTheta_eq_cpow_mul` (S-transform), `norm_jacobiTheta_eq`, `jacobiTheta_one_add`
     (θ(1+w) = 2θ(4w) − θ(w)), `jacobiThetaTailConstant = 2/(1−e^{−π})`,
     `norm_jacobiTheta_sub_one_le'` (tail bound at height ≥ 1),
     `le_norm_jacobiTheta` (cusp blow-up `½‖w‖^{−1/2} ≤ ‖θ(w)‖`),
     `norm_jacobiTheta_one_add_le` (vanishing at the even cusp).
2. `RHTower/HardyThetaSource.lean`
   - `hardyStrip = {u | |Im u| < π/2}`, `hardySource u = (e^{u/4}(θ(i e^u) − 1) − e^{−u/4})/2`,
     evenness, holomorphy on the strip, `norm_hardySource_le` (≤ C_c e^{−|Re u|/4} for |Im u| ≤ c),
     `integrable_hardySource_line`, and `xiThetaLogSource_eq_hardySource` linking it to the corpus
     theta trace.
3. `RHTower/HardyThetaFourier.lean`
   - `fourier_hardySource : 𝓕 hardySource (t/4π) = Λ(1/2+it)`,
     `norm_completedZeta_critical_le` (exponential decay on the critical line at every rate < π/4,
     by contour shift `integral_horizontal_shift_of_decay`),
     `completedZetaFourier w = Λ(1/2 + 4πw i)`, `fourier_hardySource_line`
     (line transform = `e^{−2πyw}` times the axis transform),
     `hardySource_line_eq_integral` (Fourier inversion on every horizontal line),
     `norm_hardySource_line_le`.
4. `RHTower/HardyTheorem.lean`
   - `completedRiemannZeta_critical_eq_Xi : Λ(1/2+it) = −2Ξ(t)/(t²+1/4)`,
     `hardyXiDensity w = −2Ξ(4πw)/((4πw)²+1/4)` (even, continuous),
     `norm_hardySource_axis_le` (≤ 17 near the boundary, via `norm_jacobiTheta_one_add_le`),
     `tendsto_norm_hardySource_logTwo_atTop` (blow-up at `log 2 + iπ/2`, via `le_norm_jacobiTheta`
     and period 2),
     `integrable_exp_pi_sq_mul_abs_hardyXiDensity` (Fatou in the height y ↑ π/2),
     `false_of_hardyXiDensity_tail_sign`, `exists_Xi_zero_gt`,
     `exists_two_distinct_positive_real_XiC_zeros`,
     `exists_pole_suzukiXiCharacteristicTarget`,
     `not_analyticOnNhd_suzukiXiCharacteristicTarget` (unconditional card-D endgame).

## Technique notes worth reusing

- Fourier inversion on horizontal lines replaces analytic continuation of the inversion integral:
  the contour shift gives `𝓕 (hardySource(· + iy)) = e^{−2πyw} 𝓕 hardySource`, so
  `Integrable.fourierInv_fourier_eq` yields the value at every point of the strip with no
  differentiation under the integral sign.
- Fatou (`lintegral_liminf_le`) runs directly over the filter `𝓝[<] (π/2)` — it is countably
  generated — so no sequence of heights is needed.
- Monotone convergence would be circular here (the Bochner version needs the limit integrable);
  Fatou in `ℝ≥0∞` is the right tool.
- Evenness of the density (`integral_neg_eq_self`) converts `e^{−2πyw}` moments into `cosh`
  moments, which are monotone in the height and nonnegative on the tail.

## Card

`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/`
`suzuki-screw-characteristic-meromorphic-limit-correction.md` — Hardy gate closed; the literal
"target has an unconditional real pole" claim is now Lean-internal.
