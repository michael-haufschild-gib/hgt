import GaloisForLFunctions.RHTower.ModularArcDyadicScaleLimitHilbertConvergence
import GaloisForLFunctions.RHTower.ModularArcDyadicCriticalLinePowerSeries

/-!
# All-Orders Oscillatory Mellin Power Series, Logarithmic-Cosine Moment Hierarchy, and Height-Uniform Critical-Line Curvature

In `ModularArcDyadicCriticalLinePowerSeries` (Cycle 47), we established the all-orders Taylor
polynomial hierarchy and real-analytic power-series convergence for the **quadratic** strip-weighted
Hilbert energy `E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx` and origin–infinity energy imbalance
`Δ_k(l)` around the critical line `l = 0`.

In this module we develop the corresponding **all-orders real-analytic horizontal Taylor and
power-series theory for the two-variable oscillatory Mellin transform**
$$M_k(l, \tau) = \int_0^\infty x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
  = \int_{\mathbb{R}} e^{lv} \cos(\tau v)\,\Phi_k(v)\,dv
  = \int_{\mathbb{R}} \cosh(lv) \cos(\tau v)\,\Phi_k(v)\,dv$$
and its **origin–infinity oscillatory Mellin imbalance**
$$\Delta_k^{\mathrm{Mellin}}(l, \tau)
  = \int_1^\infty x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
    - \int_0^1 x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
  = \int_0^\infty 2\sinh(lv) \cos(\tau v)\,\Phi_k(v)\,dv$$
uniformly across **all vertical frequencies `τ ∈ ℝ`** and **all dyadic scales `k ≥ 2`**:

1. **All-Orders Logarithmic-Cosine Moment Hierarchy (`Section 1`):**
   - Pointwise factorial-exponential envelope
     `|v|^n · |Φ_k(v)| ≤ 825 · ν.real univ · n! · 8^n · exp(−|v|/8)`
     (`abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth`).
   - All-orders integrability of `v^n cos(τv) Φ_k(v)` on `ℝ` and on `(0, ∞)`, and exact
     multiplicative-to-additive log-scale bridges on `(0, ∞)`, `(1, ∞)`, and `(0, 1]`
     (`setIntegral_Ioi_log_pow_mul_cos_log_mul_rpow_neg_half_eq`,
     `setIntegral_Ioi_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq`,
     `setIntegral_Ioc_zero_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq`).
   - Height- and scale-independent factorial upper bound
     `|∫_ℝ v^n cos(τv) Φ_k(v) dv| ≤ 13200 · ν.real univ · n! · 8^n`
     (`abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_le`).
   - Identical vanishing of all odd-order logarithmic-cosine moments on `ℝ`:
     `∫_ℝ v^{2m+1} cos(τv) Φ_k(v) dv = 0` for all `m ∈ ℕ` and `τ ∈ ℝ`
     (`integral_odd_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_zero`).
   - Exact `(0, 1]` vs `(1, ∞)` critical-line equipartition of all absolute and even-order
     logarithmic-cosine moments (`integral_abs_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi`,
     `integral_even_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi`).
   - Quantitative height-uniform `O(n! · 8^n / cosh((log k)/4))` `k → ∞` convergence of all
     logarithmic-cosine moments to the modular arc Poisson profile moments
     `∫_ℝ v^n cos(τv) arcPoissonProfile ν v dv`
     (`abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le`,
     `tendsto_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_atTop`).

2. **Height-Uniform All-Orders Even Taylor Expansion & Power-Series Convergence for `M_k(l, τ)` (`Section 2`):**
   - Factorial-to-geometric absorption `(|l| |v|)^N / N! ≤ (8|l|)^N · exp(|v|/8)`
     (`abs_mul_pow_div_factorial_le_eight_pow_mul_exp_eighth`) and pointwise Taylor remainder
     envelope (`taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le`).
   - Scale- and height-independent geometric `O((8|l|)^{2M} / (1/8 − |l|))` Taylor remainder bound
     across `|l| < 1/8` and all `τ ∈ ℝ`:
     `|M_k(l, τ) − ∑_{m < M} (l^{2m} / (2m)!) ∫_ℝ v^{2m} cos(τv) Φ_k(v) dv| ≤
       (1650 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M}`
     (`abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le`).
   - Unconditional `M → ∞` power-series convergence on `|l| < 1/8` for all `τ ∈ ℝ`
     (`tendsto_sum_range_even_pow_div_factorial_mul_cos_moment_atTop`).

3. **Critical-Line Horizontal Stationarity (`∂_l M_k(0, τ) = 0`) and Second-Order Curvature (`Section 3`):**
   - Height-uniform quadratic `O(l²)` stationary bound on `|l| < 1/8`:
     `|M_k(l, τ) − M_k(0, τ)| ≤ (105600 · ν.real univ / (1/8 − |l|)) · l²`
     (`abs_oscillatoryMellin_sub_criticalLine_le_sq`), proving vanishing first-order horizontal
     derivative `(M_k(l, τ) − M_k(0, τ)) / l → 0` as `l → 0` at every vertical height `τ ∈ ℝ`
     (`tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero`).
   - Height-uniform quartic `O(l⁴)` second-order Taylor remainder on `|l| < 1/8`:
     `|M_k(l, τ) − M_k(0, τ) − (l² / 2) ∫_ℝ v² cos(τv) Φ_k(v) dv| ≤
       (6758400 · ν.real univ / (1/8 − |l|)) · l⁴`
     (`abs_oscillatoryMellin_sub_criticalLine_sub_quadratic_le_pow_four`), proving the exact
     second-order horizontal curvature limit
     `(M_k(l, τ) − M_k(0, τ)) / l² → (1/2) ∫_ℝ v² cos(τv) Φ_k(v) dv` as `l → 0` at every `τ ∈ ℝ`
     (`tendsto_div_sq_oscillatoryMellin_sub_criticalLine_nhds_zero`).

4. **Height-Uniform All-Orders Odd Taylor Expansion & Transversal Derivative for `Δ_k^{\mathrm{Mellin}}(l, τ)` (`Section 4`):**
   - Scale- and height-independent geometric `O((8|l|)^{2M+1} / (1/8 − |l|))` Taylor remainder bound
     across `|l| < 1/8` and all `τ ∈ ℝ`:
     `|Δ_k^{\mathrm{Mellin}}(l, τ) − 2 ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} cos(τv) Φ_k(v) dv| ≤
       (3300 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M+1}`
     (`abs_oscillatoryMellin_imbalance_sub_two_mul_sum_range_odd_le`) and `M → ∞` power-series
     convergence (`tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_cos_moment_atTop`).
   - Height-uniform cubic `O(|l|³)` linear-Taylor remainder (`abs_oscillatoryMellin_imbalance_sub_two_mul_linear_le_cubic`)
     and exact horizontal transversal derivative on the critical line:
     `Δ_k^{\mathrm{Mellin}}(l, τ) / l → 2 ∫_{v > 0} v cos(τv) Φ_k(v) dv` as `l → 0` for all `τ ∈ ℝ`
     (`tendsto_div_oscillatoryMellin_imbalance_nhds_zero`,
     `exists_dyadic_oscillatoryMellin_powerSeries_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: All-Orders Logarithmic-Cosine Moment Hierarchy across `τ ∈ ℝ` -/

/-- **Factorial-exponential upper bound `|v|^n ≤ n! · 8^n · exp((1/8)|v|)` (`n ∈ ℕ`, `v ∈ ℝ`).** -/
theorem abs_pow_le_factorial_mul_eight_pow_mul_exp_eighth (n : ℕ) (v : ℝ) :
    |v| ^ n ≤ (n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|) := by
  have h := pow_le_factorial_mul_exp_nonneg (by positivity : 0 ≤ (1 / 8 : ℝ) * |v|) n
  have hmul := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (8 : ℝ) ^ n)
  calc |v| ^ n
      = ((1 / 8 : ℝ) * |v|) ^ n * (8 : ℝ) ^ n := by rw [← mul_pow]; ring
    _ ≤ ((n.factorial : ℝ) * Real.exp ((1 / 8 : ℝ) * |v|)) * (8 : ℝ) ^ n := hmul
    _ = (n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|) := by ring

/-- **Pointwise factorial-exponential envelope for `|v|^n · |Φ_k(v)|` (`k ≥ 2`, `n ∈ ℕ`):**
For all `v ∈ ℝ`,
`|v|^n · |arcLineInfiniteDyadicProfile k ν v| ≤ 825 · ν.real univ · n! · 8^n · exp(−(1/8)|v|)`. -/
theorem abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (v : ℝ) :
    |v| ^ n * |arcLineInfiniteDyadicProfile k ν v| ≤
      825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n * Real.exp (-((1 / 8 : ℝ) * |v|)) := by
  have hv := abs_pow_le_factorial_mul_eight_pow_mul_exp_eighth n v
  have hprof := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  calc |v| ^ n * |arcLineInfiniteDyadicProfile k ν v|
      ≤ ((n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|)) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul hv hprof (abs_nonneg _) (by positivity)
    _ = 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n *
          (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n *
          Real.exp (-((1 / 8 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **All-orders integrability of `v ↦ |v|^n · |arcLineInfiniteDyadicProfile k ν v|` on `ℝ` (`k ≥ 2`).** -/
theorem integrable_abs_pow_mul_abs_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    Integrable (fun v : ℝ => |v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  refine ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 8)).const_mul B).mono'
    ((continuous_abs.pow n).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν).abs).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hnn : 0 ≤ |v| ^ n * |arcLineInfiniteDyadicProfile k ν v| :=
    mul_nonneg (pow_nonneg (abs_nonneg v) n) (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v

/-- **All-orders integrability of `v ↦ |v|^n cos(τv) Φ_k(v)` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrable_abs_pow_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    Integrable (fun v : ℝ => |v| ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  refine (integrable_abs_pow_mul_abs_arcLineInfiniteDyadicProfile hk hν n).mono'
    (((continuous_abs.pow n).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg v) n)]
  have hcos : |v| ^ n * |Real.cos (τ * v)| ≤ |v| ^ n := by
    calc |v| ^ n * |Real.cos (τ * v)|
        ≤ |v| ^ n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg v) n)
      _ = |v| ^ n := mul_one _
  exact mul_le_mul_of_nonneg_right hcos (abs_nonneg _)

/-- **All-orders integrability of `v ↦ v^n cos(τv) Φ_k(v)` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    Integrable (fun v : ℝ => v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  refine (integrable_abs_pow_mul_abs_arcLineInfiniteDyadicProfile hk hν n).mono'
    (((continuous_id.pow n).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have hcos : |v| ^ n * |Real.cos (τ * v)| ≤ |v| ^ n := by
    calc |v| ^ n * |Real.cos (τ * v)|
        ≤ |v| ^ n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg v) n)
      _ = |v| ^ n := mul_one _
  exact mul_le_mul_of_nonneg_right hcos (abs_nonneg _)

/-- **All-orders half-line integrability of `v ↦ v^n cos(τv) Φ_k(v)` on `(0, ∞)` (`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrableOn_Ioi_zero_pow_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    IntegrableOn
      (fun v : ℝ => v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) :=
  (integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν n τ).integrableOn

/-- **Multiplicative `(0, ∞)` vs additive `ℝ` bridge for the `n`-th signed logarithmic-cosine moment
(`k ≥ 1`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_{x > 0} (log x)^n cos(τ log x) x^{−1/2} V_k(x) dx = ∫_ℝ v^n cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_log_pow_mul_cos_log_mul_rpow_neg_half_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        (Real.log x) ^ n * Real.cos (τ * Real.log x) * x ^ (-(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν x) =
      ∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ n * Real.cos (τ * v) * Real.exp (v * -(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = v ^ n * Real.cos (τ * v) * ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
    _ = v ^ n * Real.cos (τ * v) * (Real.exp (v / 2) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [hexp]

/-- **Multiplicative `(0, ∞)` vs additive `ℝ` bridge for the `n`-th absolute logarithmic-cosine moment
(`k ≥ 1`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_{x > 0} |log x|^n cos(τ log x) x^{−1/2} V_k(x) dx = ∫_ℝ |v|^n cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        |Real.log x| ^ n * Real.cos (τ * Real.log x) * x ^ (-(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν x) =
      ∫ v : ℝ, |v| ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp v * (|v| ^ n * Real.cos (τ * v) * Real.exp (v * -(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = |v| ^ n * Real.cos (τ * v) * ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
    _ = |v| ^ n * Real.cos (τ * v) * (Real.exp (v / 2) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [hexp]

/-- **Infinity-sector (`x > 1`) log-scale bridge for the `n`-th logarithmic-cosine moment
(`k ≥ 1`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_{x > 1} |log x|^n cos(τ log x) x^{−1/2} V_k(x) dx = ∫_{v > 0} v^n cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) (τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        |Real.log x| ^ n * Real.cos (τ * Real.log x) * x ^ (-(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ), v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, abs_of_pos hv,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ n * Real.cos (τ * v) * Real.exp (v * -(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = v ^ n * Real.cos (τ * v) * ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
    _ = v ^ n * Real.cos (τ * v) * (Real.exp (v / 2) *
          arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [hexp]

/-- **Origin-sector (`x ∈ (0, 1]`) log-scale bridge for the `n`-th logarithmic-cosine moment
(`k ≥ 1`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_{x ∈ (0, 1]} |log x|^n cos(τ log x) x^{−1/2} V_k(x) dx = ∫_{v > 0} v^n cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioc_zero_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) (τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        |Real.log x| ^ n * Real.cos (τ * Real.log x) * x ^ (-(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ), v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [Real.rpow_def_of_pos (Real.exp_pos (-v)), Real.log_exp, abs_neg, abs_of_pos hv,
    mul_neg, Real.cos_neg]
  have hprof : Real.exp ((-v) / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)) =
      arcLineInfiniteDyadicProfile k ν v := by
    rw [exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v), arcLineInfiniteDyadicProfile_neg]
  have hexp : Real.exp (-v) * Real.exp (-v * -(1 / 2 : ℝ)) = Real.exp ((-v) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-v) * (v ^ n * Real.cos (τ * v) * Real.exp (-v * -(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v)))
      = v ^ n * Real.cos (τ * v) * ((Real.exp (-v) * Real.exp (-v * -(1 / 2 : ℝ))) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v))) := by ring
    _ = v ^ n * Real.cos (τ * v) * (Real.exp ((-v) / 2) *
          arcLineInfiniteDyadicVector k ν (Real.exp (-v))) := by rw [hexp]
    _ = v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by rw [hprof]

/-- **All-orders full-line vs half-line absolute logarithmic-cosine moment identity
(`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_ℝ |v|^n cos(τv) Φ_k(v) dv = 2 ∫_{v > 0} v^n cos(τv) Φ_k(v) dv`. -/
theorem integral_abs_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    (∫ v : ℝ, |v| ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      2 * ∫ v in Ioi (0 : ℝ), v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hk1 : 1 ≤ k := by omega
  have hg : IntegrableOn
      (fun x : ℝ =>
        |Real.log x| ^ n * Real.cos (τ * Real.log x) * x ^ (-(1 / 2 : ℝ)) *
          arcLineInfiniteDyadicVector k ν x)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_abs_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν n τ).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
      ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |v| ^ n * Real.cos (τ * v) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v))
        = |v| ^ n * Real.cos (τ * v) *
            ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
              arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [← hexp]
      _ = Real.exp v * (|v| ^ n * Real.cos (τ * v) * Real.exp (v * -(1 / 2 : ℝ)) *
            arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
  have hsum := setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg
  rw [setIntegral_Ioc_zero_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq hk1 ν n τ,
    setIntegral_Ioi_one_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq hk1 ν n τ,
    setIntegral_Ioi_abs_log_pow_mul_cos_log_mul_rpow_neg_half_eq hk1 ν n τ] at hsum
  linarith

/-- **Even-order full-line vs half-line logarithmic-cosine moment equipartition
(`k ≥ 2`, `m ∈ ℕ`, `τ ∈ ℝ`):**
`∫_ℝ v^{2m} cos(τv) Φ_k(v) dv = 2 ∫_{v > 0} v^{2m} cos(τv) Φ_k(v) dv`. -/
theorem integral_even_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (m : ℕ) (τ : ℝ) :
    (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      2 * ∫ v in Ioi (0 : ℝ),
        v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [← integral_abs_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν (2 * m) τ]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  have hev : |v| ^ (2 * m) = v ^ (2 * m) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [hev]

/-- **Identical vanishing of all odd-order logarithmic-cosine moments on `ℝ` (`k, ν, m ∈ ℕ`, `τ ∈ ℝ`):**
For every odd power `2m + 1` and every vertical frequency `τ ∈ ℝ`,
`∫_ℝ v^{2m+1} cos(τv) Φ_k(v) dv = 0`. -/
theorem integral_odd_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_zero
    (k : ℕ) (ν : Measure ArcParam) (m : ℕ) (τ : ℝ) :
    (∫ v : ℝ, v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
  have hneg := integral_neg_eq_self
    (fun v : ℝ => v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) volume
  have hfun :
      (fun v : ℝ => (-v) ^ (2 * m + 1) * Real.cos (τ * -v) * arcLineInfiniteDyadicProfile k ν (-v)) =
      fun v : ℝ => -(v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v
    rw [Odd.neg_pow (⟨m, rfl⟩ : Odd (2 * m + 1)) v, mul_neg, Real.cos_neg,
      arcLineInfiniteDyadicProfile_neg]
    ring
  rw [hfun, integral_neg] at hneg
  linarith

/-- **Height- and scale-independent factorial upper bound on the `n`-th logarithmic-cosine moment
(`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`|∫_ℝ v^n cos(τv) Φ_k(v) dv| ≤ 13200 · ν.real univ · n! · 8^n`. -/
theorem abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    |∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      13200 * ν.real univ * (n.factorial : ℝ) * 8 ^ n := by
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hc8 : (0 : ℝ) < 1 / 8 := by norm_num
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc8).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ => v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc8] at h1
    calc |∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v|
        ≤ B * (2 / (1 / 8 : ℝ)) := h1
      _ = 13200 * ν.real univ * (n.factorial : ℝ) * 8 ^ n := by dsimp [B]; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hcos : |v| ^ n * |Real.cos (τ * v)| ≤ |v| ^ n := by
      calc |v| ^ n * |Real.cos (τ * v)|
          ≤ |v| ^ n * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg v) n)
        _ = |v| ^ n := mul_one _
    calc |v| ^ n * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ |v| ^ n * |arcLineInfiniteDyadicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
      _ ≤ B * Real.exp (-((1 / 8 : ℝ) * |v|)) :=
          abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v

/-- **All-orders integrability of `v ↦ v^n cos(τv) arcPoissonProfile ν v` on `ℝ` (`n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrable_pow_mul_cos_mul_arcPoissonProfile
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    Integrable (fun v : ℝ => v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v) := by
  set B := 5 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hc8 : (0 : ℝ) < 1 / 8 := by norm_num
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc8).const_mul B
  refine hdom.mono'
    (((continuous_id.pow n).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcPoissonProfile ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have hcos : |v| ^ n * |Real.cos (τ * v)| ≤ |v| ^ n := by
    calc |v| ^ n * |Real.cos (τ * v)|
        ≤ |v| ^ n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg v) n)
      _ = |v| ^ n := mul_one _
  have hv := abs_pow_le_factorial_mul_eight_pow_mul_exp_eighth n v
  have hB := abs_arcPoissonProfile_le_exp_mul hν (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  calc |v| ^ n * |Real.cos (τ * v)| * |arcPoissonProfile ν v|
      ≤ |v| ^ n * |arcPoissonProfile ν v| :=
        mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
    _ ≤ ((n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|)) *
          (5 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul hv hB (abs_nonneg _) (by positivity)
    _ = B * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
        dsimp [B]; ring
    _ = B * Real.exp (-((1 / 8 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Quantitative height-uniform `O(n! · 8^n / cosh((log k)/4))` `k → ∞` convergence bound for the
`n`-th logarithmic-cosine moment (`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`|(∫_ℝ v^n cos(τv) Φ_k(v) dv) − ∫_ℝ v^n cos(τv) arcPoissonProfile ν v dv| ≤
  (66240 · ν.real univ · n! · 8^n) · (1 / cosh((log k)/4))`. -/
theorem abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    |(∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
        ∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v| ≤
      (66240 * ν.real univ * (n.factorial : ℝ) * 8 ^ n) *
        (1 / Real.cosh (Real.log k / 4)) := by
  rw [← integral_sub
    (integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν n τ)
    (integrable_pow_mul_cos_mul_arcPoissonProfile hν n τ)]
  set B := (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * (n.factorial : ℝ) * 8 ^ n
  have hc8 : (0 : ℝ) < 1 / 8 := by norm_num
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc8).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc8] at h1
    calc |∫ v : ℝ,
            (v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v)|
        ≤ B * (2 / (1 / 8 : ℝ)) := h1
      _ = (66240 * ν.real univ * (n.factorial : ℝ) * 8 ^ n) *
            (1 / Real.cosh (Real.log k / 4)) := by dsimp [B]; ring
  · rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hcos : |v| ^ n * |Real.cos (τ * v)| ≤ |v| ^ n := by
      calc |v| ^ n * |Real.cos (τ * v)|
          ≤ |v| ^ n * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg v) n)
        _ = |v| ^ n := mul_one _
    have hv := abs_pow_le_factorial_mul_eight_pow_mul_exp_eighth n v
    have hdiff := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter hk hν v
    calc |v| ^ n * |Real.cos (τ * v)| *
            |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v|
        ≤ |v| ^ n * |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| :=
          mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
      _ ≤ ((n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|)) *
            ((4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul hv hdiff (abs_nonneg _) (by positivity)
      _ = B * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 8 : ℝ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Unconditional `k → ∞` convergence of the `n`-th logarithmic-cosine moment (`n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_ℝ v^n cos(τv) Φ_k(v) dv → ∫_ℝ v^n cos(τv) arcPoissonProfile ν v dv` as `k → ∞`. -/
theorem tendsto_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    Tendsto
      (fun k : ℕ => ∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      atTop
      (nhds (∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C := 66240 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have ht : Tendsto (fun k : ℕ => C * (1 / Real.cosh (Real.log k / 4))) atTop (nhds 0) := by
    simpa using tendsto_inv_cosh_quarter_log_atTop.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop 2] with k hk
  rw [Real.norm_eq_abs]
  exact abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le hk hν n τ


/-! ## Section 2: Height-Uniform All-Orders Even Taylor Expansion & Power Series for `M_k(l, τ)` -/

/-- **Factorial-to-geometric absorption for `(|l| · |v|)^N / N!`:**
For every `N ∈ ℕ` and `l, v ∈ ℝ`,
`(|l| * |v|) ^ N / (N.factorial : ℝ) ≤ (8 * |l|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|)`. -/
theorem abs_mul_pow_div_factorial_le_eight_pow_mul_exp_eighth (N : ℕ) (l v : ℝ) :
    (|l| * |v|) ^ N / (N.factorial : ℝ) ≤
      (8 * |l|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) := by
  have hfac_pos : (0 : ℝ) < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have h0 := abs_pow_le_factorial_mul_eight_pow_mul_exp_eighth N v
  have h1 : |v| ^ N / (N.factorial : ℝ) ≤ (8 : ℝ) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) := by
    rw [div_le_iff₀ hfac_pos]
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (abs_nonneg l) N)
  calc (|l| * |v|) ^ N / (N.factorial : ℝ)
      = |l| ^ N * (|v| ^ N / (N.factorial : ℝ)) := by rw [mul_pow, mul_div_assoc]
    _ ≤ |l| ^ N * ((8 : ℝ) ^ N * Real.exp ((1 / 8 : ℝ) * |v|)) := h2
    _ = (8 * |l|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) := by
        rw [← mul_assoc, ← mul_pow, mul_comm |l| 8]

/-- **Pointwise Taylor remainder envelope for `Φ_k` (`k ≥ 2`, `N ∈ ℕ`, `l, v ∈ ℝ`):**
`((|l| * |v|) ^ N / N!) * exp(|l| * |v|) * |Φ_k(v)| ≤
  825 * ν.real univ * (8 * |l|) ^ N * exp(−((1/8 − |l|) * |v|))`. -/
theorem taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (N : ℕ) (l v : ℝ) :
    ((|l| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp (|l| * |v|) *
        |arcLineInfiniteDyadicProfile k ν v| ≤
      825 * ν.real univ * (8 * |l|) ^ N *
        Real.exp (-((1 / 8 - |l|) * |v|)) := by
  have h1 := abs_mul_pow_div_factorial_le_eight_pow_mul_exp_eighth N l v
  have h2 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h1_exp :
      ((|l| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp (|l| * |v|) ≤
        (8 * |l|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (|l| * |v|) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have hprod := mul_le_mul h1_exp h2 (abs_nonneg _) (by positivity)
  refine hprod.trans_eq ?_
  have hexp :
      Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (|l| * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|)) =
        Real.exp (-((1 / 8 - |l|) * |v|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (8 * |l|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (|l| * |v|) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)))
      = 825 * ν.real univ * (8 * |l|) ^ N *
          (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (|l| * |v|) *
            Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 825 * ν.real univ * (8 * |l|) ^ N *
          Real.exp (-((1 / 8 - |l|) * |v|)) := by rw [hexp]

/-- **Integrability of `cosh(lv) cos(τv) Φ_k(v)` on `ℝ` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have e : (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => (1 / 2 : ℝ) *
        (Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          Real.exp ((-l) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v; rw [Real.cosh_eq, neg_mul]; ring
  rw [e]
  exact ((integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ).add
    (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ)).const_mul _

/-- **Full-line integral linearity for the `M`-term even Taylor polynomial against `cos(τv) Φ_k(v)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l, τ ∈ ℝ`, and `M ∈ ℕ`,
`∫_ℝ (∑_{m < M} (lv)^{2m} / (2m)!) cos(τv) Φ_k(v) dv =
  ∑_{m < M} (l^{2m} / (2m)!) ∫_ℝ v^{2m} cos(τv) Φ_k(v) dv`. -/
theorem integral_sum_range_even_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M : ℕ) :
    (∫ v : ℝ,
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∑ m ∈ Finset.range M,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow]
    ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact integral_const_mul _ _
  · intro m _
    exact (integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν (2 * m) τ).const_mul _

/-- **Scale- and height-independent geometric `O((8|l|)^{2M} / (1/8 − |l|))` Taylor remainder bound
for the two-variable oscillatory Mellin transform `M_k(l, τ)` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∑_{m < M} (l^{2m} / (2m)!) ∫_ℝ v^{2m} cos(τv) Φ_k(v) dv| ≤
  (1650 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M}`. -/
theorem abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) (M : ℕ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∑ m ∈ Finset.range M,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| := sub_pos.mpr hl
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ,
    ← integral_sum_range_even_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq hk hν l τ M]
  have hInt_cosh : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν (2 * m) τ).const_mul _)
  rw [← integral_sub hInt_cosh hInt_sum]
  set B := 825 * ν.real univ * (8 * |l|) ^ (2 * M)
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
        ≤ B * (2 / (1 / 8 - |l|)) := h1
      _ = (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M) := by
          dsimp [B]; ring
  · have hsub :
        Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v =
        (Real.cosh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    have hnonneg :
        0 ≤ Real.cosh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ) :=
      sub_nonneg.mpr (sum_range_even_pow_div_factorial_le_cosh M (l * v))
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul, abs_of_nonneg hnonneg]
    have habs_u : |l * v| = |l| * |v| := abs_mul l v
    have hev_u : (l * v) ^ (2 * M) = (|l| * |v|) ^ (2 * M) := by
      rw [← habs_u, pow_mul, pow_mul, sq_abs]
    have hrem := cosh_sub_sum_range_even_pow_div_factorial_le M (l * v)
    rw [hev_u, habs_u] at hrem
    have hcos :
        (Real.cosh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          |Real.cos (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (|l| * |v|) := by
      calc (Real.cosh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
              |Real.cos (τ * v)|
          ≤ (Real.cosh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hnonneg
        _ = Real.cosh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ) := mul_one _
        _ ≤ ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (|l| * |v|) := hrem
    calc (Real.cosh (l * v) -
            ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (|l| * |v|) *
            |arcLineInfiniteDyadicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hcos (abs_nonneg _)
      _ ≤ B * Real.exp (-((1 / 8 - |l|) * |v|)) :=
          taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * M) l v

/-- **Unconditional `M → ∞` real-analytic power-series convergence for the two-variable oscillatory
Mellin transform `M_k(l, τ)` across `|l| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`∑_{m < M} (l^{2m} / (2m)!) ∫_ℝ v^{2m} cos(τv) Φ_k(v) dv →
  ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx` as `M → ∞`. -/
theorem tendsto_sum_range_even_pow_div_factorial_mul_cos_moment_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun M : ℕ =>
        ∑ m ∈ Finset.range M,
          (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h64_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have h8l_lt : 8 * |l| < 1 := by linarith
  have h64_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have hgeom : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h64_nonneg h64_lt
    exact h.congr (fun M => by rw [pow_mul])
  have hmaj : Tendsto
      (fun M : ℕ => (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (1650 * ν.real univ / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le hk hν hl τ M


/-! ## Section 3: Critical-Line Horizontal Stationarity & Second-Order Curvature across `τ ∈ ℝ` -/

/-- **Height- and scale-independent quadratic `O(l²)` stationary bound for `M_k(l, τ)` around the
critical line `l = 0` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx| ≤ (105600 · ν.real univ / (1/8 − |l|)) · l²`. -/
theorem abs_oscillatoryMellin_sub_criticalLine_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x| ≤
      (105600 * ν.real univ / (1 / 8 - |l|)) * l ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hM1 := abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le hk hν hl τ 1
  have hterm0 :
      ∑ m ∈ Finset.range 1,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
    rw [Finset.sum_range_one]
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    rw [← setIntegral_Ioi_rpow_zero_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector,
      setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν 0 τ]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only; rw [zero_mul, Real.exp_zero, one_mul]
  rw [hterm0] at hM1
  refine hM1.trans_eq ?_
  have hsq : (8 * |l|) ^ (2 * 1) = 64 * l ^ 2 := by
    calc (8 * |l|) ^ 2 = 64 * |l| ^ 2 := by ring
      _ = 64 * l ^ 2 := by rw [sq_abs]
  rw [hsq]
  ring

/-- **Vanishing first-order horizontal derivative of `M_k(l, τ)` on the critical line `l = 0` at
every vertical height `τ ∈ ℝ` (`k ≥ 2`):**
`((∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx) / l → 0` as `l → 0`. -/
theorem tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l)
      (nhds 0) (nhds 0) := by
  set C := 1689600 * ν.real univ
  have hmaj : Tendsto (fun l : ℝ => C * |l|) (nhds 0) (nhds 0) := by
    simpa using (continuous_abs.tendsto 0).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-1 / 16 : ℝ) (1 / 16) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hmem] with l hl_mem
  have hl16 : |l| < 1 / 16 := abs_lt.mpr ⟨by linarith [hl_mem.1], hl_mem.2⟩
  have hl8 : |l| < 1 / 8 := by linarith
  rw [sub_zero, Real.norm_eq_abs, abs_div]
  rcases eq_or_ne l 0 with rfl | hl_ne
  · simp [C]
  · have hl_pos : 0 < |l| := abs_pos.mpr hl_ne
    have h1 := abs_oscillatoryMellin_sub_criticalLine_le_sq hk hν hl8 τ
    have hdenom : (1 / 16 : ℝ) ≤ 1 / 8 - |l| := by linarith
    have hinv : 1 / (1 / 8 - |l|) ≤ 16 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hdenom
      linarith
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    have h2 : (105600 * ν.real univ / (1 / 8 - |l|)) * l ^ 2 ≤ C * |l| * |l| := by
      rw [← sq_abs]
      calc (105600 * ν.real univ / (1 / 8 - |l|)) * |l| ^ 2
          = (1 / (1 / 8 - |l|)) * (105600 * ν.real univ * |l| ^ 2) := by ring
        _ ≤ 16 * (105600 * ν.real univ * |l| ^ 2) :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
        _ = C * |l| * |l| := by dsimp [C]; ring
    exact (div_le_iff₀ hl_pos).mpr (h1.trans h2)

/-- **Height- and scale-independent quartic `O(l⁴)` second-order Taylor remainder bound for
`M_k(l, τ)` around `l = 0` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    (∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx) −
    (l² / 2) ∫_ℝ v² cos(τv) Φ_k(v) dv| ≤ (6758400 · ν.real univ / (1/8 − |l|)) · l⁴`. -/
theorem abs_oscillatoryMellin_sub_criticalLine_sub_quadratic_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (l ^ 2 / 2) *
        (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (6758400 * ν.real univ / (1 / 8 - |l|)) * l ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hM2 := abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le hk hν hl τ 2
  have hterm0 :
      (∫ v : ℝ, Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
    rw [← setIntegral_Ioi_rpow_zero_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector,
      setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν 0 τ]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only; rw [zero_mul, Real.exp_zero, one_mul]
  have hsum2 :
      ∑ m ∈ Finset.range 2,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (l ^ 2 / 2) *
        (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      mul_one, Nat.factorial_two, Nat.cast_ofNat]
    rw [hterm0]
  rw [hsum2, sub_add_eq_sub_sub] at hM2
  refine hM2.trans_eq ?_
  have hpow4 : (8 * |l|) ^ (2 * 2) = 4096 * l ^ 4 := by
    have habs4 : |l| ^ 4 = l ^ 4 := by
      calc |l| ^ 4 = (|l| ^ 2) ^ 2 := by ring
        _ = (l ^ 2) ^ 2 := by rw [sq_abs]
        _ = l ^ 4 := by ring
    calc (8 * |l|) ^ (2 * 2) = 4096 * |l| ^ 4 := by ring
      _ = 4096 * l ^ 4 := by rw [habs4]
  rw [hpow4]
  ring

/-- **Exact second-order horizontal curvature limit of `M_k(l, τ)` on the critical line `l = 0`
at every vertical height `τ ∈ ℝ` (`k ≥ 2`):**
`((∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∫_{x > 0} x^{−1/2} cos(τ log x) V_k(x) dx) / l² →
  (1/2) ∫_ℝ v² cos(τv) Φ_k(v) dv` as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_sub_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) /
          l ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds ((1 / 2 : ℝ) *
        ∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set C := 108134400 * ν.real univ
  have hmaj : Tendsto (fun l : ℝ => C * l ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun l : ℝ => C * l ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-1 / 16 : ℝ) (1 / 16) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem, self_mem_nhdsWithin] with l hl_mem hl_ne
  simp only [mem_compl_singleton_iff] at hl_ne
  have hl16 : |l| < 1 / 16 := abs_lt.mpr ⟨by linarith [hl_mem.1], hl_mem.2⟩
  have hl8 : |l| < 1 / 8 := by linarith
  have hsq_pos : 0 < l ^ 2 := sq_pos_of_ne_zero hl_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) /
        l ^ 2 -
      (1 / 2 : ℝ) * (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (l ^ 2 / 2) *
          (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / l ^ 2 := by
    have hne2 : l ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_oscillatoryMellin_sub_criticalLine_sub_quadratic_le_pow_four hk hν hl8 τ
  have hdenom : (1 / 16 : ℝ) ≤ 1 / 8 - |l| := by linarith
  have hinv : 1 / (1 / 8 - |l|) ≤ 16 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hdenom
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (l ^ 2 / 2) *
          (∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (6758400 * ν.real univ / (1 / 8 - |l|)) * l ^ 4 := h1
    _ = (1 / (1 / 8 - |l|)) * (6758400 * ν.real univ * l ^ 4) := by ring
    _ ≤ 16 * (6758400 * ν.real univ * l ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * l ^ 2 * l ^ 2 := by dsimp [C]; ring


/-! ## Section 4: All-Orders Odd Taylor Expansion & Transversal Derivative for `Δ_k^{\mathrm{Mellin}}(l, τ)` -/

/-- **Integrability of `2 sinh(lv) cos(τv) Φ_k(v)` on `(0, ∞)` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) := by
  have e : (fun v : ℝ =>
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ =>
        Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.exp ((-l) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    funext v; rw [Real.sinh_eq, neg_mul]; ring
  rw [e]
  exact (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ).integrableOn.sub
    (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ).integrableOn

/-- **Half-line integral linearity for the `M`-term odd Taylor polynomial against `cos(τv) Φ_k(v)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l, τ ∈ ℝ`, and `M ∈ ℕ`,
`∫_{v > 0} 2 (∑_{m < M} (lv)^{2m+1} / (2m+1)!) cos(τv) Φ_k(v) dv =
  2 ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} cos(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_zero_two_mul_sum_range_odd_pow_mul_cos_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M : ℕ) :
    (∫ v in Ioi (0 : ℝ),
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      2 * ∑ m ∈ Finset.range M,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ),
            v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => 2 *
        ((∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v; ring
  rw [hfun, integral_const_mul]
  congr 1
  have hfun2 :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow]; ring
  rw [hfun2, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact integral_const_mul _ _
  · intro m _
    exact (integrableOn_Ioi_zero_pow_mul_cos_mul_arcLineInfiniteDyadicProfile
      hk hν (2 * m + 1) τ).const_mul _

/-- **Scale- and height-independent geometric `O((8|l|)^{2M+1} / (1/8 − |l|))` Taylor remainder bound
for the origin–infinity oscillatory Mellin imbalance `Δ_k^{\mathrm{Mellin}}(l, τ)`
(`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`, `M ∈ ℕ`):**
`|Δ_k^{\mathrm{Mellin}}(l, τ) −
    2 ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} cos(τv) Φ_k(v) dv| ≤
  (3300 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M+1}`. -/
theorem abs_oscillatoryMellin_imbalance_sub_two_mul_sum_range_odd_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) (M : ℕ) :
    |((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * ∑ m ∈ Finset.range M,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ),
              v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (3300 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| := sub_pos.mpr hl
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ,
    ← setIntegral_Ioi_zero_two_mul_sum_range_odd_pow_mul_cos_mul_profile_eq hk hν l τ M]
  have hInt_sinh : IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          (2 * (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ))) *
            (v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [mul_assoc, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrableOn_Ioi_zero_pow_mul_cos_mul_arcLineInfiniteDyadicProfile
        hk hν (2 * m + 1) τ).const_mul _)
  rw [← integral_sub hInt_sinh hInt_sum]
  set B := 2 * 825 * ν.real univ * (8 * |l|) ^ (2 * M + 1)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l|) * |v|))) =
          (3300 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hsub :
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v =
        2 * ((Real.sinh (l * v) -
            ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have habs_u : |l * v| = |l| * |v| := abs_mul l v
    have hrem := abs_sinh_sub_sum_range_odd_pow_div_factorial_le M (l * v)
    rw [habs_u] at hrem
    have hcos :
        |Real.sinh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
          |Real.cos (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) := by
      calc |Real.sinh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
              |Real.cos (τ * v)|
          ≤ |Real.sinh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |Real.sinh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| :=
            mul_one _
        _ ≤ ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) :=
            hrem
    have htay := taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * M + 1) l v
    calc 2 * (|Real.sinh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
            |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|)
        ≤ 2 * (((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp (|l| * |v|) * |arcLineInfiniteDyadicProfile k ν v|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcos (abs_nonneg _)) (by positivity)
      _ ≤ 2 * (825 * ν.real univ * (8 * |l|) ^ (2 * M + 1) *
            Real.exp (-((1 / 8 - |l|) * |v|))) :=
          mul_le_mul_of_nonneg_left htay (by positivity)
      _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
          dsimp [B]; ring

/-- **Unconditional `M → ∞` real-analytic power-series convergence for the origin–infinity
oscillatory Mellin imbalance `Δ_k^{\mathrm{Mellin}}(l, τ)` across `|l| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`2 ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} cos(τv) Φ_k(v) dv →
  Δ_k^{\mathrm{Mellin}}(l, τ)` as `M → ∞`. -/
theorem tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_cos_moment_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun M : ℕ =>
        2 * ∑ m ∈ Finset.range M,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ),
              v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h64_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have h8l_lt : 8 * |l| < 1 := by linarith
  have h64_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have hgeom_even : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h64_nonneg h64_lt
    exact h.congr (fun M => by rw [pow_mul])
  have hgeom : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M + 1)) atTop (nhds 0) := by
    have h := hgeom_even.mul_const (8 * |l|)
    rw [zero_mul] at h
    exact h.congr (fun M => (pow_succ (8 * |l|) (2 * M)).symm)
  have hmaj : Tendsto
      (fun M : ℕ => (3300 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (3300 * ν.real univ / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_oscillatoryMellin_imbalance_sub_two_mul_sum_range_odd_le hk hν hl τ M

/-- **Height- and scale-independent cubic `O(|l|³)` linear-Taylor remainder bound for
`Δ_k^{\mathrm{Mellin}}(l, τ)` around `l = 0` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`|Δ_k^{\mathrm{Mellin}}(l, τ) − 2 l ∫_{v > 0} v cos(τv) Φ_k(v) dv| ≤
  (1689600 · ν.real univ / (1/8 − |l|)) · |l|³`. -/
theorem abs_oscillatoryMellin_imbalance_sub_two_mul_linear_le_cubic
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * l *
          (∫ v in Ioi (0 : ℝ),
            v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1689600 * ν.real univ / (1 / 8 - |l|)) * |l| ^ 3 := by
  have hM1 := abs_oscillatoryMellin_imbalance_sub_two_mul_sum_range_odd_le hk hν hl τ 1
  have hsum1 :
      2 * ∑ m ∈ Finset.range 1,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ),
            v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      2 * l *
        (∫ v in Ioi (0 : ℝ),
          v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [Finset.sum_range_one]
    simp only [mul_zero, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    ring
  rw [hsum1] at hM1
  refine hM1.trans_eq ?_
  ring

/-- **Exact first-order horizontal transversal derivative of the origin–infinity oscillatory
Mellin imbalance `Δ_k^{\mathrm{Mellin}}(l, τ)` on the critical line `l = 0` at every vertical
height `τ ∈ ℝ` (`k ≥ 2`):**
`Δ_k^{\mathrm{Mellin}}(l, τ) / l → 2 ∫_{v > 0} v cos(τv) Φ_k(v) dv` as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_oscillatoryMellin_imbalance_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (2 * ∫ v in Ioi (0 : ℝ),
        v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set C := 27033600 * ν.real univ
  have hmaj : Tendsto (fun l : ℝ => C * l ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun l : ℝ => C * l ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-1 / 16 : ℝ) (1 / 16) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem, self_mem_nhdsWithin] with l hl_mem hl_ne
  simp only [mem_compl_singleton_iff] at hl_ne
  have hl16 : |l| < 1 / 16 := abs_lt.mpr ⟨by linarith [hl_mem.1], hl_mem.2⟩
  have hl8 : |l| < 1 / 8 := by linarith
  have hl_pos : 0 < |l| := abs_pos.mpr hl_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l -
      2 * (∫ v in Ioi (0 : ℝ),
        v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      (((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * l * (∫ v in Ioi (0 : ℝ),
          v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / l := by
    field_simp
  rw [hdiff_eq, abs_div, div_le_iff₀ hl_pos]
  have h1 := abs_oscillatoryMellin_imbalance_sub_two_mul_linear_le_cubic hk hν hl8 τ
  have hdenom : (1 / 16 : ℝ) ≤ 1 / 8 - |l| := by linarith
  have hinv : 1 / (1 / 8 - |l|) ≤ 16 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hdenom
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        2 * l * (∫ v in Ioi (0 : ℝ),
          v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (1689600 * ν.real univ / (1 / 8 - |l|)) * |l| ^ 3 := h1
    _ = (1 / (1 / 8 - |l|)) * (1689600 * ν.real univ * |l| ^ 3) := by ring
    _ ≤ 16 * (1689600 * ν.real univ * |l| ^ 3) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |l| ^ 2 * |l| := by dsimp [C]; ring
    _ = C * l ^ 2 * |l| := by rw [sq_abs]

/-- **Master All-Orders Oscillatory Mellin Power-Series & Logarithmic-Cosine Moment Witness Theorem:**
There exists a non-zero finite Borel measure `ν` on `ArcParam` symmetric under `arcNeg` such
that for every integer scale `k ≥ 2` and every vertical frequency `τ ∈ ℝ`:
1. **Logarithmic-Cosine Moment Hierarchy & Scale-Limit Convergence (`∀ n ∈ ℕ`):**
   - `∫_{x > 0} (log x)^n cos(τ log x) x^{−1/2} V_k(x) dx = ∫_ℝ v^n cos(τv) Φ_k(v) dv`,
   - `|∫_ℝ v^n cos(τv) Φ_k(v) dv| ≤ 13200 · ν.real univ · n! · 8^n`,
   - `∫_ℝ v^{2m+1} cos(τv) Φ_k(v) dv = 0` and
     `∫_ℝ v^{2m} cos(τv) Φ_k(v) dv = 2 ∫_{v > 0} v^{2m} cos(τv) Φ_k(v) dv`,
   - `∫_ℝ v^n cos(τv) Φ_k(v) dv → ∫_ℝ v^n cos(τv) arcPoissonProfile ν v dv` as `k → ∞` at rate
     `O(n! · 8^n / cosh((log k)/4))`;
2. **Height-Uniform Even Taylor Remainder & Power-Series Convergence for `M_k(l, τ)` (`|l| < 1/8`):**
   - `|M_k(l, τ) − ∑_{m < M} (l^{2m} / (2m)!) ∫_ℝ v^{2m} cos(τv) Φ_k(v) dv| ≤
       (1650 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M} → 0` as `M → ∞`;
3. **Critical-Line Horizontal Stationarity & Second-Order Curvature (`l → 0`):**
   - `(M_k(l, τ) − M_k(0, τ)) / l → 0` as `l → 0`,
   - `(M_k(l, τ) − M_k(0, τ)) / l² → (1/2) ∫_ℝ v² cos(τv) Φ_k(v) dv` as `l → 0` (`l ≠ 0`);
4. **Height-Uniform Odd Taylor Remainder, Power-Series Convergence, and Transversal Derivative
   for `Δ_k^{\mathrm{Mellin}}(l, τ)` (`|l| < 1/8`):**
   - `|Δ_k^{\mathrm{Mellin}}(l, τ) − 2 ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} cos(τv) Φ_k(v) dv| ≤
       (3300 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M+1} → 0` as `M → ∞`,
   - `Δ_k^{\mathrm{Mellin}}(l, τ) / l → 2 ∫_{v > 0} v cos(τv) Φ_k(v) dv` as `l → 0` (`l ≠ 0`). -/
theorem exists_dyadic_oscillatoryMellin_powerSeries_arcWitness :
    ∃ (ν : Measure ArcParam),
      ∃ (_ : IsFiniteMeasure ν),
        ν ≠ 0 ∧
        ν.map arcNeg = ν ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ n : ℕ, ∀ τ : ℝ,
          |∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
            13200 * ν.real univ * (n.factorial : ℝ) * 8 ^ n) ∧
        (∀ k m : ℕ, ∀ τ : ℝ,
          (∫ v : ℝ, v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ m : ℕ, ∀ τ : ℝ,
          (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
            2 * ∫ v in Ioi (0 : ℝ),
              v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ∧
        (∀ n : ℕ, ∀ τ : ℝ,
          Tendsto
            (fun k : ℕ => ∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
            atTop
            (nhds (∫ v : ℝ, v ^ n * Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 → ∀ τ : ℝ, ∀ M : ℕ,
          |(∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∑ m ∈ Finset.range M,
              (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
            (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun M : ℕ =>
              ∑ m ∈ Finset.range M,
                (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ τ : ℝ,
          Tendsto
            (fun l : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) / l)
            (nhds 0) (nhds 0)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ τ : ℝ,
          Tendsto
            (fun l : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) / l ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds ((1 / 2 : ℝ) *
              ∫ v : ℝ, v ^ 2 * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun M : ℕ =>
              2 * ∑ m ∈ Finset.range M,
                (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ),
                    v ^ (2 * m + 1) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                  arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ τ : ℝ,
          Tendsto
            (fun l : ℝ =>
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) / l)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (2 * ∫ v in Ioi (0 : ℝ),
              v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  obtain ⟨ν, hfin, hν_ne, hν_sym, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν_ne, hν_sym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk n τ
    exact abs_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_le hk hν_sym n τ
  · intro k m τ
    exact integral_odd_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_zero k ν m τ
  · intro k hk m τ
    exact integral_even_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_two_mul_Ioi hk hν_sym m τ
  · intro n τ
    exact tendsto_integral_pow_mul_cos_mul_arcLineInfiniteDyadicProfile_atTop hν_sym n τ
  · intro k hk l hl τ M
    exact abs_setIntegral_Ioi_rpow_mul_cos_log_sub_sum_range_even_le hk hν_sym hl τ M
  · intro k hk l hl τ
    exact tendsto_sum_range_even_pow_div_factorial_mul_cos_moment_atTop hk hν_sym hl τ
  · intro k hk τ
    exact tendsto_div_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν_sym τ
  · intro k hk τ
    exact tendsto_div_sq_oscillatoryMellin_sub_criticalLine_nhds_zero hk hν_sym τ
  · intro k hk l hl τ
    exact tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_cos_moment_atTop hk hν_sym hl τ
  · intro k hk τ
    exact tendsto_div_oscillatoryMellin_imbalance_nhds_zero hk hν_sym τ

end

end RHTower
