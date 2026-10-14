import GaloisForLFunctions.RHTower.ModularArcDyadicJointTwoVariablePowerSeries

/-!
# Conjugate Sine Oscillatory Mellin Transform, Global Cauchy–Riemann Equations, and Joint Odd-Odd Power Series

In `ModularArcDyadicStripOscillatoryMellin`, `ModularArcDyadicOscillatoryMellinPowerSeries`, and
`ModularArcDyadicJointTwoVariablePowerSeries`, we established the analytic theory of the real-part
two-variable oscillatory Mellin transform
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx = ∫_ℝ cosh(lv) cos(τv) Φ_k(v) dv`
of the infinite-horizon dyadic modular arc line vector `V_k = arcLineInfiniteDyadicVector k ν` and
profile `Φ_k = arcLineInfiniteDyadicProfile k ν`.

In complex coordinates `s = 1/2 + l + iτ`, the full complex Mellin transform of `V_k` is
`∫_{x > 0} x^{l − 1/2 + iτ} V_k(x) dx = M_k(l, τ) + i N_k(l, τ)`, where the conjugate imaginary
part is the **sine oscillatory Mellin transform**
`N_k(l, τ) := ∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx`.

In this module we build the complete unconditional analytic, functional-equation, Cauchy–Riemann,
and two-variable power-series infrastructure for `N_k(l, τ)` and the pair `(M_k, N_k)`:

1. **Log-Scale Change of Variables, `sinh(lv) sin(τv)` Representation, Critical-Line Vanishing,
   and Doubly-Odd Functional Equation (`Section 1`):**
   - Exact log-scale change of variables (`k ≥ 1`, `l, τ ∈ ℝ`):
     `∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_ℝ e^{lv} sin(τv) Φ_k(v) dv`
     (`setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile`).
   - Exact `sinh(lv) sin(τv)` representation across the full open critical strip `|l| < 1/2`:
     `∫_ℝ e^{lv} sin(τv) Φ_k(v) dv = ∫_ℝ sinh(lv) sin(τv) Φ_k(v) dv`
     (`integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh`).
   - Identical vanishing on the critical line `l = 0` (`setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero`,
     proving that the complex Mellin transform of `V_k` is purely real on `Re(s) = 1/2`) and on the
     real axis `τ = 0` (`setIntegral_Ioi_rpow_mul_sin_zero_eq_zero`).
   - Doubly-odd functional equation on `(0, ∞)`:
     `N_k(−l, τ) = −N_k(l, τ)`, `N_k(l, −τ) = −N_k(l, τ)`, and `N_k(−l, −τ) = N_k(l, τ)`
     (`setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg`,
     `setIntegral_Ioi_rpow_mul_sin_neg_log_eq_neg`,
     `setIntegral_Ioi_rpow_neg_mul_sin_neg_log_eq`).
   - Origin–infinity `(0, 1]` vs `(1, ∞)` sector decomposition:
     `∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_{v > 0} e^{lv} sin(τv) Φ_k(v) dv` and
     `∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx = −∫_{v > 0} e^{−lv} sin(τv) Φ_k(v) dv`,
     yielding `N_k(l, τ) = ∫_{v > 0} 2 sinh(lv) sin(τv) Φ_k(v) dv`
     (`setIntegral_Ioi_rpow_mul_sin_log_eq_two_mul_setIntegral_Ioi_zero_sinh`).

2. **All-Orders Logarithmic-Sine Moment Hierarchy & Height-Uniform Odd Taylor Series (`Section 2`):**
   - For every `n ∈ ℕ` and `τ ∈ ℝ`, the `n`-th logarithmic-sine moment
     `∫_{x > 0} (log x)^n sin(τ log x) x^{−1/2} V_k(x) dx = ∫_ℝ v^n sin(τv) Φ_k(v) dv`
     is integrable and satisfies the height- and scale-independent bound
     `|∫_ℝ v^n sin(τv) Φ_k(v) dv| ≤ 13200 · ν.real univ · n! · 8^n`
     (`abs_integral_pow_mul_sin_mul_arcLineInfiniteDyadicProfile_le`), with even-order vanishing
     `∫_ℝ v^{2m} sin(τv) Φ_k(v) dv = 0` (`integral_even_pow_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_zero`).
   - Scale- and height-independent geometric `O((8|l|)^{2M+1} / (1/8 − |l|))` Taylor remainder
     bound (`abs_setIntegral_Ioi_rpow_mul_sin_log_sub_sum_range_odd_le`) and `M → ∞` power-series
     convergence (`tendsto_sum_range_odd_pow_div_factorial_mul_sin_moment_atTop`) across `|l| < 1/8`
     and all `τ ∈ ℝ`.
   - Height-uniform cubic `O(|l|³)` linear-Taylor remainder (`abs_sineMellin_sub_linear_le_cubic`)
     and exact horizontal transversal derivative on the critical line:
     `N_k(l, τ) / l → ∫_ℝ v sin(τv) Φ_k(v) dv` as `l → 0` for all `τ ∈ ℝ`
     (`tendsto_div_sineMellin_nhds_zero`).

3. **Global Cauchy–Riemann Partial Derivative Equations Across `|l| < 1/8`, `τ ∈ ℝ` (`Section 3`):**
   - Pointwise quadratic shift remainder bounds for `cosh((l+h)v)`, `sinh((l+h)v)`, `cos((τ+h)v)`,
     and `sin((τ+h)v)` (`abs_cosh_add_sub_cosh_sub_mul_sinh_le`,
     `abs_sinh_add_sub_sinh_sub_mul_cosh_le`, `abs_cos_add_sub_cos_add_mul_sin_le`,
     `abs_sin_add_sub_sin_sub_mul_cos_le`).
   - Quantitative `O(h²)` first-order Taylor remainder bounds and exact partial derivative limits
     at **every** point `(l, τ)` with `|l| < 1/8` and `τ ∈ ℝ`:
     `∂_l M_k(l, τ) = ∂_τ N_k(l, τ) = ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv`
     (`tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero`,
     `tendsto_div_sineMellin_vert_shift_nhds_zero`) and
     `∂_l N_k(l, τ) = −∂_τ M_k(l, τ) = ∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv`
     (`tendsto_div_sineMellin_horiz_shift_nhds_zero`,
     `tendsto_div_oscillatoryMellin_vert_shift_nhds_zero`), together with quadratic `O(h²)`
     Cauchy–Riemann finite-difference cancellation bounds
     (`abs_cauchyRiemann_first_defect_le_sq`, `abs_cauchyRiemann_second_defect_le_sq`).

4. **Joint Two-Variable Odd-Odd Taylor Expansion & Power Series for `N_k(l, τ)` on `|l| + |τ| < 1/8` (`Section 4`):**
   - Scale-independent additive geometric remainder bound for the `(M, J)` joint odd-odd Taylor
     polynomial of `N_k(l, τ)` in terms of the pure critical-line real even logarithmic moments
     `∫_ℝ v^{2m+2j+2} Φ_k(v) dv`:
     `|N_k(l, τ) − ∑_{m < M} ∑_{j < J} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j+1} / (2j+1)!) ∫_ℝ v^{2m+2j+2} Φ_k(v) dv| ≤
       (1650 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M+1} + (8|τ|)^{2J+1})`
     (`abs_sineMellin_sub_double_sum_range_odd_le`) and `N → ∞` diagonal power-series convergence
     (`tendsto_double_sum_range_odd_pow_div_factorial_atTop`,
     `exists_dyadic_conjugateSine_cauchyRiemann_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: The Conjugate Sine Oscillatory Mellin Transform, Critical-Line Vanishing, and Doubly-Odd Functional Equation -/

/-- **Exact log-scale change of variables for the sine oscillatory Mellin integral of
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} sin(τ log x) · arcLineInfiniteDyadicVector k ν x dx =
  ∫_ℝ e^{lv} sin(τv) · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ v : ℝ, Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) * Real.sin (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- **Odd reflection symmetry `v ↦ −v` (`l ↦ −l`) for the sine Fourier-Laplace transform of
`arcLineInfiniteDyadicProfile k ν`:**
`∫_ℝ e^{(−l)v} sin(τv) Φ_k(v) dv = −∫_ℝ e^{lv} sin(τv) Φ_k(v) dv`. -/
theorem integral_exp_neg_mul_sin_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ v : ℝ, Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      -(∫ v : ℝ, Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have h := integral_neg_eq_self
    (fun v : ℝ => Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) volume
  have hfun :
      (fun v : ℝ =>
        Real.exp (l * -v) * Real.sin (τ * -v) * arcLineInfiniteDyadicProfile k ν (-v)) =
      fun v : ℝ =>
        -(Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v
    rw [arcLineInfiniteDyadicProfile_neg, mul_neg, mul_neg, Real.sin_neg, neg_mul]
    ring
  rw [hfun, integral_neg] at h
  linarith

/-- **Odd reflection symmetry `τ ↦ −τ` for the sine Fourier-Laplace transform of
`arcLineInfiniteDyadicProfile k ν`:**
`∫_ℝ e^{lv} sin((−τ)v) Φ_k(v) dv = −∫_ℝ e^{lv} sin(τv) Φ_k(v) dv`. -/
theorem integral_exp_mul_sin_neg_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ v : ℝ, Real.exp (l * v) * Real.sin ((-τ) * v) * arcLineInfiniteDyadicProfile k ν v) =
      -(∫ v : ℝ, Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ => Real.exp (l * v) * Real.sin ((-τ) * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => -(Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v
    rw [neg_mul, Real.sin_neg]
    ring
  rw [hfun, integral_neg]

/-- **Integrability of `e^{lv} sin(τv) Φ_k(v)` on `ℝ` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Integrable
      (fun v : ℝ => Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hdom : Integrable (fun v : ℝ => Real.exp (l * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_exp_mul_arcLineInfiniteDyadicProfile_of_abs_lt_half hk hν hl
  refine hdom.norm.mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
    calc |Real.exp (l * v)| * |Real.sin (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ |Real.exp (l * v)| * 1 * |arcLineInfiniteDyadicProfile k ν v| := by
          gcongr
      _ = |Real.exp (l * v)| * |arcLineInfiniteDyadicProfile k ν v| := by ring

/-- **Integrability of `sinh(lv) sin(τv) Φ_k(v)` on `ℝ` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have e : (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ =>
        (Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) / 2 := by
    funext v; rw [Real.sinh_eq, neg_mul]; ring
  rw [e]
  exact ((integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).sub
    (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ)).div_const 2

/-- **Exact `sinh(lv) sin(τv)` representation of the sine Fourier-Laplace transform of
`arcLineInfiniteDyadicProfile k ν` across `|l| < 1/2` and `τ ∈ ℝ` (`k ≥ 2`):**
`∫_ℝ e^{lv} sin(τv) Φ_k(v) dv = ∫_ℝ sinh(lv) sin(τv) Φ_k(v) dv`. -/
theorem integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ v : ℝ, Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hIl : Integrable
      (fun v : ℝ => Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ
  have hIneg : Integrable
      (fun v : ℝ => Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ
  have heq :
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ =>
        (Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) / 2 := by
    funext v; rw [Real.sinh_eq, neg_mul]; ring
  rw [heq, integral_div, integral_sub hIl hIneg,
    integral_exp_neg_mul_sin_mul_arcLineInfiniteDyadicProfile]
  ring

/-- **Critical-line vanishing (`l = 0`) of the sine oscillatory Mellin transform (`k ≥ 1`, `τ ∈ ℝ`):**
On the critical line `Re(s) = 1/2` (`l = 0`), the imaginary part of the complex Mellin transform
of `arcLineInfiniteDyadicVector k ν` vanishes identically at every vertical height `τ ∈ ℝ`:
`∫_{x > 0} x^{−1/2} sin(τ log x) V_k(x) dx = 0`. -/
theorem setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
  have h0 : (-(1 / 2 : ℝ)) = 0 - 1 / 2 := by ring
  rw [h0, setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν 0 τ]
  have hsym := integral_exp_neg_mul_sin_mul_arcLineInfiniteDyadicProfile k ν 0 τ
  simp only [neg_zero] at hsym
  linarith

/-- **Real-axis vanishing (`τ = 0`) of the sine oscillatory Mellin transform (`l ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} sin(0 · log x) V_k(x) dx = 0`. -/
theorem setIntegral_Ioi_rpow_mul_sin_zero_eq_zero
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (0 * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
  simp [Real.sin_zero]

/-- **Horizontal odd functional equation `l ↦ −l` for the sine oscillatory Mellin transform
(`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{−l − 1/2} sin(τ log x) V_k(x) dx =
  −∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν (-l) τ,
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l τ,
    integral_exp_neg_mul_sin_mul_arcLineInfiniteDyadicProfile]

/-- **Vertical odd functional equation `τ ↦ −τ` for the sine oscillatory Mellin transform
(`k ∈ ℕ`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} sin((−τ) log x) V_k(x) dx =
  −∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioi_rpow_mul_sin_neg_log_eq_neg
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
  have hfun :
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      fun x : ℝ =>
        -(x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) := by
    funext x
    rw [neg_mul, Real.sin_neg]
    ring
  rw [hfun, integral_neg]

/-- **Joint inversion invariance `(l, τ) ↦ (−l, −τ)` for the sine oscillatory Mellin transform
(`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{−l − 1/2} sin((−τ) log x) V_k(x) dx =
  ∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx`. -/
theorem setIntegral_Ioi_rpow_neg_mul_sin_neg_log_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (-l - 1 / 2) * Real.sin ((-τ) * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk ν l (-τ),
    setIntegral_Ioi_rpow_mul_sin_neg_log_eq_neg k ν l τ, neg_neg]

/-- **Half-line `(1, ∞)` log-scale identity for the sine oscillatory Mellin transform (`k ≥ 1`):**
`∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_{v > 0} e^{lv} sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_one_rpow_mul_sin_log_eq_setIntegral_Ioi_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        Real.exp (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_one_eq_setIntegral_Ioi_zero_exp_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) * Real.sin (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) * Real.sin (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- **Origin-sector `(0, 1]` log-scale identity for the sine oscillatory Mellin transform (`k ≥ 1`):**
`∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx = −∫_{v > 0} e^{−lv} sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_zero
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      -(∫ v in Ioi (0 : ℝ),
        Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  rw [setIntegral_Ioc_zero_one_eq_setIntegral_Ioi_zero_exp_neg_mul]
  have hfun :
      (fun v : ℝ =>
        Real.exp (-v) *
          ((Real.exp (-v)) ^ (l - 1 / 2) * Real.sin (τ * Real.log (Real.exp (-v))) *
            arcLineInfiniteDyadicVector k ν (Real.exp (-v)))) =
      fun v : ℝ =>
        -(Real.exp ((-l) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v
    rw [Real.rpow_def_of_pos (Real.exp_pos (-v)), Real.log_exp,
      ← arcLineInfiniteDyadicProfile_neg k ν v,
      ← exp_half_mul_arcLineInfiniteDyadicVector hk ν (-v)]
    have hexp : Real.exp (-v) * Real.exp (-v * (l - 1 / 2)) =
        Real.exp ((-l) * v) * Real.exp (-v / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsin : Real.sin (τ * -v) = -Real.sin (τ * v) := by
      rw [mul_neg, Real.sin_neg]
    calc Real.exp (-v) * (Real.exp (-v * (l - 1 / 2)) * Real.sin (τ * -v) *
            arcLineInfiniteDyadicVector k ν (Real.exp (-v)))
        = (Real.exp (-v) * Real.exp (-v * (l - 1 / 2))) * Real.sin (τ * -v) *
            arcLineInfiniteDyadicVector k ν (Real.exp (-v)) := by ring
      _ = (Real.exp ((-l) * v) * Real.exp (-v / 2)) * (-Real.sin (τ * v)) *
            arcLineInfiniteDyadicVector k ν (Real.exp (-v)) := by rw [hexp, hsin]
      _ = -(Real.exp ((-l) * v) * Real.sin (τ * v) *
            (Real.exp (-v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp (-v)))) := by ring
  rw [hfun, integral_neg]

/-- **Half-line `2 sinh(lv) sin(τv)` representation of the sine oscillatory Mellin transform across
`|l| < 1/2` (`k ≥ 2`, `τ ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx = ∫_{v > 0} 2 sinh(lv) sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_rpow_mul_sin_log_eq_two_mul_setIntegral_Ioi_zero_sinh
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v in Ioi (0 : ℝ),
        2 * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hk1 : 1 ≤ k := by omega
  have hnl : |-l| < 1 / 2 := by simpa using hl
  have hg : IntegrableOn
      (fun x : ℝ =>
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)
      (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_iff_integrable_exp_mul]
    refine (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).congr
      (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
      ← exp_half_mul_arcLineInfiniteDyadicVector hk1 ν v]
    have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
        Real.exp (l * v) * Real.exp (v / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (l * v) * Real.sin (τ * v) *
            (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v))
        = (Real.exp (l * v) * Real.exp (v / 2)) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
      _ = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [← hexp]
      _ = Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.sin (τ * v) *
            arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
  have hI_pos := (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl τ).integrableOn
    (s := Ioi (0 : ℝ))
  have hI_neg := (integrable_exp_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hnl τ).integrableOn
    (s := Ioi (0 : ℝ))
  rw [← setIntegral_Ioc_zero_one_add_setIntegral_Ioi_one hg,
    setIntegral_Ioc_zero_one_rpow_mul_sin_log_eq_neg_setIntegral_Ioi_zero hk1 ν l τ,
    setIntegral_Ioi_one_rpow_mul_sin_log_eq_setIntegral_Ioi_zero hk1 ν l τ,
    neg_add_eq_sub, ← integral_sub hI_pos hI_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  rw [Real.sinh_eq, neg_mul]
  ring


/-! ## Section 2: Logarithmic-Sine Moment Hierarchy and Height-Uniform Odd Taylor Series of `N_k(l, τ)` -/

/-- **Log-scale change of variables for the `n`-th logarithmic-sine moment (`k ≥ 1`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`∫_{x > 0} (log x)^n sin(τ log x) x^{−1/2} V_k(x) dx = ∫_ℝ v^n sin(τv) Φ_k(v) dv`. -/
theorem setIntegral_Ioi_log_pow_mul_sin_log_mul_rpow_neg_half_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (n : ℕ) (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        (Real.log x) ^ n * Real.sin (τ * Real.log x) *
          x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) =
      ∫ v : ℝ, v ^ n * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * -(1 / 2 : ℝ)) = Real.exp (v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp v * (v ^ n * Real.sin (τ * v) *
          Real.exp (v * -(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν (Real.exp v))
      = v ^ n * Real.sin (τ * v) *
          ((Real.exp v * Real.exp (v * -(1 / 2 : ℝ))) *
            arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring
    _ = v ^ n * Real.sin (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by rw [hexp]

/-- **All-orders integrability of `v^n sin(τv) Φ_k(v)` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`).** -/
theorem integrable_pow_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    Integrable (fun v : ℝ => v ^ n * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 8)).const_mul B
  refine hdom.mono'
    (((continuous_id.pow n).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
  calc |v| ^ n * |Real.sin (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      ≤ |v| ^ n * 1 * |arcLineInfiniteDyadicProfile k ν v| := by gcongr
    _ = |v| ^ n * |arcLineInfiniteDyadicProfile k ν v| := by ring
    _ ≤ B * Real.exp (-((1 / 8 : ℝ) * |v|)) := h1

/-- **Height- and scale-independent factorial upper bound for the `n`-th logarithmic-sine moment
(`k ≥ 2`, `n ∈ ℕ`, `τ ∈ ℝ`):**
`|∫_ℝ v^n sin(τv) Φ_k(v) dv| ≤ 13200 · ν.real univ · n! · 8^n`. -/
theorem abs_integral_pow_mul_sin_mul_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) (τ : ℝ) :
    |∫ v : ℝ, v ^ n * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v| ≤
      13200 * ν.real univ * (n.factorial : ℝ) * 8 ^ n := by
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 8)).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ => v ^ n * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul,
      integral_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 8)] at h1
    calc |∫ v : ℝ, v ^ n * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v|
        ≤ B * (2 / (1 / 8 : ℝ)) := h1
      _ = 13200 * ν.real univ * (n.factorial : ℝ) * 8 ^ n := by dsimp [B]; ring
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hp := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
    have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
    calc |v| ^ n * |Real.sin (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ |v| ^ n * 1 * |arcLineInfiniteDyadicProfile k ν v| := by gcongr
      _ = |v| ^ n * |arcLineInfiniteDyadicProfile k ν v| := by ring
      _ ≤ B * Real.exp (-((1 / 8 : ℝ) * |v|)) := hp

/-- **Even-order full-line vanishing for the logarithmic-sine moments (`m ∈ ℕ`, `τ ∈ ℝ`):**
Because `v^{2m} sin(τv) Φ_k(v)` is odd on `ℝ`,
`∫_ℝ v^{2m} sin(τv) Φ_k(v) dv = 0`. -/
theorem integral_even_pow_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_zero
    (k : ℕ) (ν : Measure ArcParam) (m : ℕ) (τ : ℝ) :
    (∫ v : ℝ, v ^ (2 * m) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
  have h := integral_neg_eq_self
    (fun v : ℝ => v ^ (2 * m) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) volume
  have hodd :
      (fun v : ℝ =>
        (-v) ^ (2 * m) * Real.sin (τ * -v) * arcLineInfiniteDyadicProfile k ν (-v)) =
      fun v : ℝ => -(v ^ (2 * m) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v
    have hev : (-v) ^ (2 * m) = v ^ (2 * m) := by
      rw [pow_mul, pow_mul, neg_sq]
    rw [hev, mul_neg, Real.sin_neg, arcLineInfiniteDyadicProfile_neg]
    ring
  rw [hodd, integral_neg] at h
  linarith

/-- **Full-line integral linearity for the `M`-term odd Taylor polynomial against `sin(τv) Φ_k(v)`:**
`∫_ℝ (∑_{m < M} (lv)^{2m+1} / (2m+1)!) sin(τv) Φ_k(v) dv =
  ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_ℝ v^{2m+1} sin(τv) Φ_k(v) dv`. -/
theorem integral_sum_range_odd_pow_mul_sin_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M : ℕ) :
    (∫ v : ℝ,
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∑ m ∈ Finset.range M,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow]; ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact integral_const_mul _ _
  · intro m _
    exact (integrable_pow_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν (2 * m + 1) τ).const_mul _

/-- **Scale- and height-independent geometric `O((8|l|)^{2M+1} / (1/8 − |l|))` Taylor remainder
bound for `N_k(l, τ)` across `|l| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`, `M ∈ ℕ`):**
`|(∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) −
    ∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_ℝ v^{2m+1} sin(τv) Φ_k(v) dv| ≤
  (1650 · ν.real univ / (1/8 − |l|)) · (8|l|)^{2M+1}`. -/
theorem abs_setIntegral_Ioi_rpow_mul_sin_log_sub_sum_range_odd_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) (M : ℕ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∑ m ∈ Finset.range M,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ,
    ← integral_sum_range_odd_pow_mul_sin_mul_profile_eq hk hν l τ M]
  have hInt_sinh : Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrable_pow_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν (2 * m + 1) τ).const_mul _)
  rw [← integral_sub hInt_sinh hInt_sum]
  set B := 825 * ν.real univ * (8 * |l|) ^ (2 * M + 1)
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
        ≤ B * (2 / (1 / 8 - |l|)) := h1
      _ = (1650 * ν.real univ / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
          dsimp [B]; ring
  · have hsub :
        Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v =
        (Real.sinh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul]
    have hrem := abs_sinh_sub_sum_range_odd_pow_div_factorial_le M (l * v)
    rw [abs_mul] at hrem
    have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
    have hprod1 :
        |Real.sinh (l * v) -
          ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
          |Real.sin (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) := by
      calc |Real.sinh (l * v) -
              ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
              |Real.sin (τ * v)|
          ≤ ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) * Real.exp (|l| * |v|)) * 1 :=
            mul_le_mul hrem hsin (abs_nonneg _) (by positivity)
        _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) := by ring
    have hprof := taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * M + 1) l v
    exact (mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)).trans hprof

/-- **Unconditional `M → ∞` power-series convergence for the sine oscillatory Mellin transform
`N_k(l, τ)` on `|l| < 1/8` across all `τ ∈ ℝ` (`k ≥ 2`):**
`∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_ℝ v^{2m+1} sin(τv) Φ_k(v) dv →
  ∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx` as `M → ∞`. -/
theorem tendsto_sum_range_odd_pow_div_factorial_mul_sin_moment_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun M : ℕ =>
        ∑ m ∈ Finset.range M,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have hr_sq_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have hr_sq_lt_one : (8 * |l|) ^ 2 < 1 := by
    nlinarith [abs_nonneg l]
  have hpow2 : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr_sq_nonneg hr_sq_lt_one).congr fun M => by
      rw [pow_mul]
  have hpow : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M + 1)) atTop (nhds 0) := by
    have hmul := hpow2.mul_const (8 * |l|)
    rw [zero_mul] at hmul
    exact hmul.congr fun M => by rw [pow_succ]
  set C := 1650 * ν.real univ / (1 / 8 - |l|)
  have hmaj : Tendsto (fun M : ℕ => C * (8 * |l|) ^ (2 * M + 1)) atTop (nhds 0) := by
    simpa using hpow.const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_setIntegral_Ioi_rpow_mul_sin_log_sub_sum_range_odd_le hk hν hl τ M

/-- **Height-uniform cubic `O(|l|³)` linear-Taylor remainder bound for `N_k(l, τ)` near the
critical line `l = 0` (`k ≥ 2`, `|l| < 1/8`, `τ ∈ ℝ`):**
`|(∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) − l ∫_ℝ v sin(τv) Φ_k(v) dv| ≤
  (844800 · ν.real univ / (1/8 − |l|)) · |l|³`. -/
theorem abs_sineMellin_sub_linear_le_cubic
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      l * (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (844800 * ν.real univ / (1 / 8 - |l|)) * |l| ^ 3 := by
  have hM1 := abs_setIntegral_Ioi_rpow_mul_sin_log_sub_sum_range_odd_le hk hν hl τ 1
  simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one] at hM1
  refine hM1.trans_eq ?_
  ring

/-- **Exact horizontal transversal derivative of `N_k(l, τ)` on the critical line `l = 0` across
all `τ ∈ ℝ` (`k ≥ 2`):**
`(∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) / l → ∫_ℝ v sin(τv) Φ_k(v) dv`
as `l → 0` (`l ≠ 0`). -/
theorem tendsto_div_sineMellin_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun l : ℝ =>
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set C := 16 * 844800 * ν.real univ
  have hmaj : Tendsto (fun l : ℝ => C * l ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun l : ℝ => C * l ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-(1 / 16 : ℝ)) (1 / 16) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem, self_mem_nhdsWithin] with l hl_mem hl_ne
  simp only [mem_compl_singleton_iff] at hl_ne
  have hl16 : |l| < 1 / 16 := abs_lt.mpr hl_mem
  have hl8 : |l| < 1 / 8 := by linarith
  have hl_pos : 0 < |l| := abs_pos.mpr hl_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / l -
        (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        l * (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / l := by
    field_simp
  rw [hdiff_eq, abs_div, div_le_iff₀ hl_pos]
  have h1 := abs_sineMellin_sub_linear_le_cubic hk hν hl8 τ
  have hdenom : (1 / 16 : ℝ) ≤ 1 / 8 - |l| := by linarith
  have hinv : 1 / (1 / 8 - |l|) ≤ 16 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hdenom
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        l * (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (844800 * ν.real univ / (1 / 8 - |l|)) * |l| ^ 3 := h1
    _ = (1 / (1 / 8 - |l|)) * (844800 * ν.real univ * |l| ^ 3) := by ring
    _ ≤ 16 * (844800 * ν.real univ * |l| ^ 3) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |l| ^ 2 * |l| := by dsimp [C]; ring
    _ = C * l ^ 2 * |l| := by rw [sq_abs]


/-! ## Section 3: Global Cauchy–Riemann Partial Derivative Equations Across `|l| < 1/8`, `τ ∈ ℝ` -/

/-- Elementary hyperbolic sine envelope `|sinh u| ≤ exp |u|` for all `u ∈ ℝ`. -/
theorem abs_sinh_le_exp_abs (u : ℝ) : |Real.sinh u| ≤ Real.exp |u| := by
  have h1 : |Real.sinh u| ≤ Real.cosh u := by
    rw [Real.sinh_eq, Real.cosh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htri := abs_sub (Real.exp u) (Real.exp (-u))
    rw [abs_of_pos (Real.exp_pos u), abs_of_pos (Real.exp_pos (-u))] at htri
    linarith
  exact h1.trans (cosh_le_exp_abs u)

/-- **Uniform quadratic bound `|sinh u − u| ≤ (u² / 2) · exp |u|` for all `u ∈ ℝ`.** -/
theorem abs_sinh_sub_self_le_sq_div_two_mul_exp (u : ℝ) :
    |Real.sinh u - u| ≤ (u ^ 2 / 2) * Real.exp |u| := by
  have hsplit : Real.sinh u - u =
      ((Real.exp u - (1 + u)) - (Real.exp (-u) - (1 + -u))) / 2 := by
    rw [Real.sinh_eq]; ring
  have h1 := abs_exp_sub_sum_range_le_factorial_tail 2 u
  have h2 := abs_exp_sub_sum_range_le_factorial_tail 2 (-u)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_ofNat,
    abs_neg] at h1 h2
  rw [hsplit, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htri := (abs_sub (Real.exp u - (1 + u)) (Real.exp (-u) - (1 + -u))).trans
    (add_le_add h1 h2)
  have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
  rw [hsq] at htri
  linarith

/-- **Uniform quadratic bound `|sin u − u| ≤ (u² / 2) · exp |u|` for all `u ∈ ℝ`.** -/
theorem abs_sin_sub_self_le_sq_div_two_mul_exp (u : ℝ) :
    |Real.sin u - u| ≤ (u ^ 2 / 2) * Real.exp |u| := by
  have h1 := abs_sin_sub_sum_range_le_sinh_abs_sub_sum 1 u
  simp only [Finset.sum_range_one, mul_zero, zero_add, pow_zero, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one, one_mul] at h1
  have hnonneg : 0 ≤ Real.sinh |u| - |u| := by
    have hh := sum_range_odd_pow_div_factorial_le_sinh_nonneg 1 (abs_nonneg u)
    simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one,
      Nat.factorial_one, Nat.cast_one, div_one] at hh
    linarith
  have h2 := abs_sinh_sub_self_le_sq_div_two_mul_exp |u|
  rw [abs_of_nonneg hnonneg, sq_abs, abs_abs] at h2
  exact h1.trans h2

/-- **Pointwise quadratic shift remainder bound for `cosh((l + h)v) − cosh(lv) − (hv) sinh(lv)`:**
For all `l, h, v ∈ ℝ`,
`|cosh((l + h)v) − cosh(lv) − (hv) sinh(lv)| ≤ h² v² · exp((|l| + |h|)|v|)`. -/
theorem abs_cosh_add_sub_cosh_sub_mul_sinh_le (l h v : ℝ) :
    |Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)| ≤
      h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
  have hsplit :
      Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v) =
        Real.cosh (l * v) * (Real.cosh (h * v) - 1) +
          Real.sinh (l * v) * (Real.sinh (h * v) - h * v) := by
    rw [add_mul, Real.cosh_add]; ring
  have hcosh_l : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have hsinh_l : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
  have hcosh_h : |Real.cosh (h * v) - 1| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    have h0 : 0 ≤ Real.cosh (h * v) - 1 := sub_nonneg.mpr (Real.one_le_cosh (h * v))
    rw [abs_of_nonneg h0, ← abs_mul]
    have h1 := cosh_sub_sum_range_even_pow_div_factorial_le 1 (h * v)
    simpa [Finset.sum_range_one] using h1
  have hsinh_h : |Real.sinh (h * v) - h * v| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_sinh_sub_self_le_sq_div_two_mul_exp (h * v)
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
  have ht1 : Real.cosh (l * v) * |Real.cosh (h * v) - 1| ≤
      Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul hcosh_l hcosh_h (abs_nonneg _) (Real.exp_nonneg _)
  have ht2 : |Real.sinh (l * v)| * |Real.sinh (h * v) - h * v| ≤
      Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul hsinh_l hsinh_h (abs_nonneg _) (Real.exp_nonneg _)
  calc Real.cosh (l * v) * |Real.cosh (h * v) - 1| +
          |Real.sinh (l * v)| * |Real.sinh (h * v) - h * v|
      ≤ Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) +
          Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
        add_le_add ht1 ht2
    _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
    _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise quadratic shift remainder bound for `sinh((l + h)v) − sinh(lv) − (hv) cosh(lv)`:**
For all `l, h, v ∈ ℝ`,
`|sinh((l + h)v) − sinh(lv) − (hv) cosh(lv)| ≤ h² v² · exp((|l| + |h|)|v|)`. -/
theorem abs_sinh_add_sub_sinh_sub_mul_cosh_le (l h v : ℝ) :
    |Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)| ≤
      h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
  have hsplit :
      Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v) =
        Real.sinh (l * v) * (Real.cosh (h * v) - 1) +
          Real.cosh (l * v) * (Real.sinh (h * v) - h * v) := by
    rw [add_mul, Real.sinh_add]; ring
  have hcosh_l : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have hsinh_l : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
  have hcosh_h : |Real.cosh (h * v) - 1| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    have h0 : 0 ≤ Real.cosh (h * v) - 1 := sub_nonneg.mpr (Real.one_le_cosh (h * v))
    rw [abs_of_nonneg h0, ← abs_mul]
    have h1 := cosh_sub_sum_range_even_pow_div_factorial_le 1 (h * v)
    simpa [Finset.sum_range_one] using h1
  have hsinh_h : |Real.sinh (h * v) - h * v| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_sinh_sub_self_le_sq_div_two_mul_exp (h * v)
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
  have ht1 : |Real.sinh (l * v)| * |Real.cosh (h * v) - 1| ≤
      Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul hsinh_l hcosh_h (abs_nonneg _) (Real.exp_nonneg _)
  have ht2 : Real.cosh (l * v) * |Real.sinh (h * v) - h * v| ≤
      Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul hcosh_l hsinh_h (abs_nonneg _) (Real.exp_nonneg _)
  calc |Real.sinh (l * v)| * |Real.cosh (h * v) - 1| +
          Real.cosh (l * v) * |Real.sinh (h * v) - h * v|
      ≤ Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) +
          Real.exp (|l| * |v|) * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
        add_le_add ht1 ht2
    _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
    _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise quadratic shift remainder bound for `cos((τ + h)v) − cos(τv) + (hv) sin(τv)`:**
For all `τ, h, v ∈ ℝ`,
`|cos((τ + h)v) − cos(τv) + (hv) sin(τv)| ≤ h² v² · exp(|h| |v|)`. -/
theorem abs_cos_add_sub_cos_add_mul_sin_le (τ h v : ℝ) :
    |Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)| ≤
      h ^ 2 * v ^ 2 * Real.exp (|h| * |v|) := by
  have hsplit :
      Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v) =
        Real.cos (τ * v) * (Real.cos (h * v) - 1) -
          Real.sin (τ * v) * (Real.sin (h * v) - h * v) := by
    rw [add_mul, Real.cos_add]; ring
  have hcos_h : |Real.cos (h * v) - 1| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    have h1 := abs_cos_sub_sum_range_even_pow_div_factorial_le 1 (h * v)
    simpa [Finset.sum_range_one] using h1
  have hsin_h : |Real.sin (h * v) - h * v| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_sin_sub_self_le_sq_div_two_mul_exp (h * v)
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have ht1 : |Real.cos (τ * v)| * |Real.cos (h * v) - 1| ≤
      1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_cos_le_one _) hcos_h (abs_nonneg _) (by positivity)
  have ht2 : |Real.sin (τ * v)| * |Real.sin (h * v) - h * v| ≤
      1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_sin_le_one _) hsin_h (abs_nonneg _) (by positivity)
  calc |Real.cos (τ * v)| * |Real.cos (h * v) - 1| +
          |Real.sin (τ * v)| * |Real.sin (h * v) - h * v|
      ≤ 1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) +
          1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
        add_le_add ht1 ht2
    _ = h ^ 2 * v ^ 2 * Real.exp (|h| * |v|) := by ring

/-- **Pointwise quadratic shift remainder bound for `sin((τ + h)v) − sin(τv) − (hv) cos(τv)`:**
For all `τ, h, v ∈ ℝ`,
`|sin((τ + h)v) − sin(τv) − (hv) cos(τv)| ≤ h² v² · exp(|h| |v|)`. -/
theorem abs_sin_add_sub_sin_sub_mul_cos_le (τ h v : ℝ) :
    |Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)| ≤
      h ^ 2 * v ^ 2 * Real.exp (|h| * |v|) := by
  have hsplit :
      Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v) =
        Real.sin (τ * v) * (Real.cos (h * v) - 1) +
          Real.cos (τ * v) * (Real.sin (h * v) - h * v) := by
    rw [add_mul, Real.sin_add]; ring
  have hcos_h : |Real.cos (h * v) - 1| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    have h1 := abs_cos_sub_sum_range_even_pow_div_factorial_le 1 (h * v)
    simpa [Finset.sum_range_one] using h1
  have hsin_h : |Real.sin (h * v) - h * v| ≤ ((h * v) ^ 2 / 2) * Real.exp (|h| * |v|) := by
    rw [← abs_mul]
    exact abs_sin_sub_self_le_sq_div_two_mul_exp (h * v)
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have ht1 : |Real.sin (τ * v)| * |Real.cos (h * v) - 1| ≤
      1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_sin_le_one _) hcos_h (abs_nonneg _) (by positivity)
  have ht2 : |Real.cos (τ * v)| * |Real.sin (h * v) - h * v| ≤
      1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
    mul_le_mul (Real.abs_cos_le_one _) hsin_h (abs_nonneg _) (by positivity)
  calc |Real.sin (τ * v)| * |Real.cos (h * v) - 1| +
          |Real.cos (τ * v)| * |Real.sin (h * v) - h * v|
      ≤ 1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) +
          1 * (((h * v) ^ 2 / 2) * Real.exp (|h| * |v|)) :=
        add_le_add ht1 ht2
    _ = h ^ 2 * v ^ 2 * Real.exp (|h| * |v|) := by ring

/-- **Integrability of `v^n sinh(lv) cos(τv) Φ_k(v)` on `ℝ` across `|l| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (n : ℕ) (τ : ℝ) :
    Integrable
      (fun v : ℝ => v ^ n * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hc : 0 < 1 / 8 - |l| := by linarith
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  refine hdom.mono'
    ((((continuous_id.pow n).mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
  have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
  have hcos : |Real.cos (τ * v)| ≤ 1 := Real.abs_cos_le_one (τ * v)
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  have hsc : |Real.sinh (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc |Real.sinh (l * v)| * |Real.cos (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 := mul_le_mul hsinh hcos (abs_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|l| * |v|) := by ring
  calc |v| ^ n * |Real.sinh (l * v)| * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      = (|Real.sinh (l * v)| * |Real.cos (τ * v)|) *
          (|v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul hsc h1 (by positivity) (Real.exp_nonneg _)
    _ = B * (Real.exp (|l| * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Integrability of `v^n cosh(lv) sin(τv) Φ_k(v)` on `ℝ` across `|l| < 1/8` and `τ ∈ ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (n : ℕ) (τ : ℝ) :
    Integrable
      (fun v : ℝ => v ^ n * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hc : 0 < 1 / 8 - |l| := by linarith
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  refine hdom.mono'
    ((((continuous_id.pow n).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.cosh_pos _)]
  have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have hsin : |Real.sin (τ * v)| ≤ 1 := Real.abs_sin_le_one (τ * v)
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  have hcs : Real.cosh (l * v) * |Real.sin (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc Real.cosh (l * v) * |Real.sin (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 := mul_le_mul hcosh hsin (abs_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (|l| * |v|) := by ring
  calc |v| ^ n * Real.cosh (l * v) * |Real.sin (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      = (Real.cosh (l * v) * |Real.sin (τ * v)|) *
          (|v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul hcs h1 (by positivity) (Real.exp_nonneg _)
    _ = B * (Real.exp (|l| * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Pointwise quadratic shift envelope multiplied by `|Φ_k(v)|` (`k ≥ 2`):**
For all `l, h, v ∈ ℝ`,
`(h² v² · exp((|l| + |h|)|v|)) · |Φ_k(v)| ≤
  (105600 · ν.real univ · h²) · exp(−(1/8 − |l| − |h|)|v|)`. -/
theorem quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l h v : ℝ) :
    (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) *
      |arcLineInfiniteDyadicProfile k ν v| ≤
      (105600 * ν.real univ * h ^ 2) * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
  have hp := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν 2 v
  rw [sq_abs] at hp
  simp only [Nat.factorial_two, Nat.cast_ofNat] at hp
  calc (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) *
          |arcLineInfiniteDyadicProfile k ν v|
      = (h ^ 2 * Real.exp ((|l| + |h|) * |v|)) *
          (v ^ 2 * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ (h ^ 2 * Real.exp ((|l| + |h|) * |v|)) *
          (825 * ν.real univ * 2 * 8 ^ 2 * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (105600 * ν.real univ * h ^ 2) *
          (Real.exp ((|l| + |h|) * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = (105600 * ν.real univ * h ^ 2) * Real.exp (-((1 / 8 - |l| - |h|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Height-uniform quadratic `O(h²)` horizontal first-order Taylor remainder for `M_k(l + h, τ)`
across `|l| + |h| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`|(∫_{x > 0} x^{l + h − 1/2} cos(τ log x) V_k(x) dx) −
    (∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    h ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv| ≤
  (211200 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_oscillatoryMellin_horiz_shift_sub_linear_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl8 : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_half : |l + h| < 1 / 2 := (abs_add_le l h).trans_lt (by linarith)
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l + h) τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hlh_half τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ,
    ← integral_const_mul]
  have hInt1 : Integrable
      (fun v : ℝ => Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hlh_half τ
  have hInt2 : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt3 : Integrable
      (fun v : ℝ =>
        h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    simpa [pow_one] using
      (integrable_pow_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl8 1 τ).const_mul h
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.sub hInt2
  rw [← integral_sub hInt1 hInt2, ← integral_sub hInt12 hInt3]
  set B := 105600 * ν.real univ * h ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by dsimp [B]; ring
  · have hsub :
        Real.cosh ((l + h) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        (Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)) *
          Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul]
    have hrem := abs_cosh_add_sub_cosh_sub_mul_sinh_le l h v
    have hcos := Real.abs_cos_le_one (τ * v)
    have hprod :
        |Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)| *
          |Real.cos (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.cosh ((l + h) * v) - Real.cosh (l * v) - (h * v) * Real.sinh (l * v)| *
              |Real.cos (τ * v)|
          ≤ (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hrem hcos (abs_nonneg _) (by positivity)
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by ring
    exact (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
      (quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Height-uniform quadratic `O(h²)` horizontal first-order Taylor remainder for `N_k(l + h, τ)`
across `|l| + |h| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`|(∫_{x > 0} x^{l + h − 1/2} sin(τ log x) V_k(x) dx) −
    (∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) −
    h ∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv| ≤
  (211200 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_sineMellin_horiz_shift_sub_linear_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl8 : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hlh_half : |l + h| < 1 / 2 := (abs_add_le l h).trans_lt (by linarith)
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν (l + h) τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hlh_half τ,
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ,
    ← integral_const_mul]
  have hInt1 : Integrable
      (fun v : ℝ => Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hlh_half τ
  have hInt2 : Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt3 : Integrable
      (fun v : ℝ =>
        h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    simpa [pow_one] using
      (integrable_pow_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl8 1 τ).const_mul h
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.sub hInt2
  rw [← integral_sub hInt1 hInt2, ← integral_sub hInt12 hInt3]
  set B := 105600 * ν.real univ * h ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by dsimp [B]; ring
  · have hsub :
        Real.sinh ((l + h) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        (Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)) *
          Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul]
    have hrem := abs_sinh_add_sub_sinh_sub_mul_cosh_le l h v
    have hsin := Real.abs_sin_le_one (τ * v)
    have hprod :
        |Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)| *
          |Real.sin (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.sinh ((l + h) * v) - Real.sinh (l * v) - (h * v) * Real.cosh (l * v)| *
              |Real.sin (τ * v)|
          ≤ (h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|)) * 1 :=
            mul_le_mul hrem hsin (abs_nonneg _) (by positivity)
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by ring
    exact (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
      (quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Height-uniform quadratic `O(h²)` vertical first-order Taylor remainder for `M_k(l, τ + h)`
across `|l| + |h| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`|(∫_{x > 0} x^{l − 1/2} cos((τ + h) log x) V_k(x) dx) −
    (∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) +
    h ∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv| ≤
  (211200 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_oscillatoryMellin_vert_shift_add_linear_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl8 : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ + h),
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half (τ + h),
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ,
    ← integral_const_mul]
  have hInt1 : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ + h)
  have hInt2 : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt3 : Integrable
      (fun v : ℝ =>
        h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    simpa [pow_one] using
      (integrable_pow_mul_cosh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl8 1 τ).const_mul h
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.sub hInt2
  rw [← integral_sub hInt1 hInt2, ← integral_add hInt12 hInt3]
  set B := 105600 * ν.real univ * h ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
        h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
              h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by dsimp [B]; ring
  · have hsub :
        Real.cosh (l * v) * Real.cos ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v +
          h * (v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        Real.cosh (l * v) *
          (Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
    have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
    have hrem := abs_cos_add_sub_cos_add_mul_sin_le τ h v
    have hprod :
        Real.cosh (l * v) *
          |Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc Real.cosh (l * v) *
              |Real.cos ((τ + h) * v) - Real.cos (τ * v) + (h * v) * Real.sin (τ * v)|
          ≤ Real.exp (|l| * |v|) * (h ^ 2 * v ^ 2 * Real.exp (|h| * |v|)) :=
            mul_le_mul hcosh hrem (abs_nonneg _) (Real.exp_nonneg _)
        _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    exact (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
      (quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **Height-uniform quadratic `O(h²)` vertical first-order Taylor remainder for `N_k(l, τ + h)`
across `|l| + |h| < 1/8` and all `τ ∈ ℝ` (`k ≥ 2`):**
`|(∫_{x > 0} x^{l − 1/2} sin((τ + h) log x) V_k(x) dx) −
    (∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) −
    h ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv| ≤
  (211200 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_sineMellin_vert_shift_sub_linear_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl8 : |l| < 1 / 8 := by linarith [abs_nonneg h]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |h| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l (τ + h),
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half (τ + h),
    setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ,
    ← integral_const_mul]
  have hInt1 : Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half (τ + h)
  have hInt2 : Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt3 : Integrable
      (fun v : ℝ =>
        h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
    simpa [pow_one] using
      (integrable_pow_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl8 1 τ).const_mul h
  have hInt12 : Integrable
      (fun v : ℝ =>
        Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    hInt1.sub hInt2
  rw [← integral_sub hInt1 hInt2, ← integral_sub hInt12 hInt3]
  set B := 105600 * ν.real univ * h ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |h|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))|
        ≤ B * (2 / (1 / 8 - |l| - |h|)) := h1
      _ = (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by dsimp [B]; ring
  · have hsub :
        Real.sinh (l * v) * Real.sin ((τ + h) * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          h * (v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        Real.sinh (l * v) *
          (Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul]
    have hsinh : |Real.sinh (l * v)| ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact abs_sinh_le_exp_abs (l * v)
    have hrem := abs_sin_add_sub_sin_sub_mul_cos_le τ h v
    have hprod :
        |Real.sinh (l * v)| *
          |Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)| ≤
        h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
      calc |Real.sinh (l * v)| *
              |Real.sin ((τ + h) * v) - Real.sin (τ * v) - (h * v) * Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * (h ^ 2 * v ^ 2 * Real.exp (|h| * |v|)) :=
            mul_le_mul hsinh hrem (abs_nonneg _) (Real.exp_nonneg _)
        _ = h ^ 2 * v ^ 2 * (Real.exp (|l| * |v|) * Real.exp (|h| * |v|)) := by ring
        _ = h ^ 2 * v ^ 2 * Real.exp ((|l| + |h|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    exact (mul_le_mul_of_nonneg_right hprod (abs_nonneg _)).trans
      (quadratic_shift_envelope_mul_abs_arcLineInfiniteDyadicProfile_le hk hν l h v)

/-- **First Cauchy–Riemann finite-difference cancellation bound across `|l| + |h| < 1/8` and `τ ∈ ℝ`:**
`|(M_k(l + h, τ) − M_k(l, τ)) − (N_k(l, τ + h) − N_k(l, τ))| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_cauchyRiemann_first_defect_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have h1 := abs_oscillatoryMellin_horiz_shift_sub_linear_le_sq hk hν hlh τ
  have h2 := abs_sineMellin_vert_shift_sub_linear_le_sq hk hν hlh τ
  set DM_l := (∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set DN_τ := (∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set L := h * ∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v
  have hsplit : DM_l - DN_τ = (DM_l - L) - (DN_τ - L) := by ring
  rw [hsplit]
  refine ((abs_sub (DM_l - L) (DN_τ - L)).trans (add_le_add h1 h2)).trans_eq ?_
  ring

/-- **Second Cauchy–Riemann finite-difference cancellation bound across `|l| + |h| < 1/8` and `τ ∈ ℝ`:**
`|(M_k(l, τ + h) − M_k(l, τ)) + (N_k(l + h, τ) − N_k(l, τ))| ≤
  (422400 · ν.real univ / (1/8 − |l| − |h|)) · h²`. -/
theorem abs_cauchyRiemann_second_defect_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l h : ℝ} (hlh : |l| + |h| < 1 / 8) (τ : ℝ) :
    |((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)| ≤
      (422400 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := by
  have h1 := abs_oscillatoryMellin_vert_shift_add_linear_le_sq hk hν hlh τ
  have h2 := abs_sineMellin_horiz_shift_sub_linear_le_sq hk hν hlh τ
  set DM_τ := (∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set DN_l := (∫ x in Ioi (0 : ℝ),
      x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
    ∫ x in Ioi (0 : ℝ),
      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set L := h * ∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v
  have hsplit : DM_τ + DN_l = (DM_τ + L) + (DN_l - L) := by ring
  rw [hsplit]
  refine ((abs_add_le (DM_τ + L) (DN_l - L)).trans (add_le_add h1 h2)).trans_eq ?_
  ring

/-- **Exact horizontal partial derivative `∂_l M_k(l, τ)` at any `(l, τ)` with `|l| < 1/8` (`k ≥ 2`):**
`(M_k(l + h, τ) − M_k(l, τ)) / h → ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 211200 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hh_pos : 0 < |h| := abs_pos.mpr hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h -
      (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / h := by
    field_simp
  rw [hdiff_eq, abs_div, div_le_iff₀ hh_pos]
  have h1 := abs_oscillatoryMellin_horiz_shift_sub_linear_le_sq hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (211200 * ν.real univ * h ^ 2) := by ring
    _ ≤ (1 / δ) * (211200 * ν.real univ * h ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |h| ^ 2 := by rw [sq_abs]; dsimp [C]; ring
    _ = C * |h| * |h| := by ring

/-- **Exact vertical partial derivative `∂_τ N_k(l, τ) = ∂_l M_k(l, τ)` at any `(l, τ)` with
`|l| < 1/8` (`k ≥ 2`):**
`(N_k(l, τ + h) − N_k(l, τ)) / h → ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sineMellin_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 211200 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hh_pos : 0 < |h| := abs_pos.mpr hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h -
      (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / h := by
    field_simp
  rw [hdiff_eq, abs_div, div_le_iff₀ hh_pos]
  have h1 := abs_sineMellin_vert_shift_sub_linear_le_sq hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (211200 * ν.real univ * h ^ 2) := by ring
    _ ≤ (1 / δ) * (211200 * ν.real univ * h ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |h| ^ 2 := by rw [sq_abs]; dsimp [C]; ring
    _ = C * |h| * |h| := by ring

/-- **Exact horizontal partial derivative `∂_l N_k(l, τ)` at any `(l, τ)` with `|l| < 1/8` (`k ≥ 2`):**
`(N_k(l + h, τ) − N_k(l, τ)) / h → ∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sineMellin_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 211200 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hh_pos : 0 < |h| := abs_pos.mpr hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h -
      (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / h := by
    field_simp
  rw [hdiff_eq, abs_div, div_le_iff₀ hh_pos]
  have h1 := abs_sineMellin_horiz_shift_sub_linear_le_sq hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (211200 * ν.real univ * h ^ 2) := by ring
    _ ≤ (1 / δ) * (211200 * ν.real univ * h ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |h| ^ 2 := by rw [sq_abs]; dsimp [C]; ring
    _ = C * |h| * |h| := by ring

/-- **Exact vertical partial derivative `∂_τ M_k(l, τ) = −∂_l N_k(l, τ)` at any `(l, τ)` with
`|l| < 1/8` (`k ≥ 2`):**
`(M_k(l, τ + h) − M_k(l, τ)) / h → −∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_oscillatoryMellin_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 211200 * ν.real univ / δ
  have hmaj : Tendsto (fun h : ℝ => C * |h|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * |h|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh_lt : |h| < δ := abs_lt.mpr hh_mem
  have hlh : |l| + |h| < 1 / 8 := by dsimp [δ] at hh_lt; linarith
  have hh_pos : 0 < |h| := abs_pos.mpr hh_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h -
      (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / h := by
    field_simp
    ring
  rw [hdiff_eq, abs_div, div_le_iff₀ hh_pos]
  have h1 := abs_oscillatoryMellin_vert_shift_add_linear_le_sq hk hν hlh τ
  have hdenom : δ ≤ 1 / 8 - |l| - |h| := by dsimp [δ] at hh_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |h|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        h * (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (211200 * ν.real univ / (1 / 8 - |l| - |h|)) * h ^ 2 := h1
    _ = (1 / (1 / 8 - |l| - |h|)) * (211200 * ν.real univ * h ^ 2) := by ring
    _ ≤ (1 / δ) * (211200 * ν.real univ * h ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * |h| ^ 2 := by rw [sq_abs]; dsimp [C]; ring
    _ = C * |h| * |h| := by ring


/-! ## Section 4: Joint Two-Variable Odd-Odd Taylor Expansion & Power Series for `N_k(l, τ)` on `|l| + |τ| < 1/8` -/

/-- **Pointwise additive joint Taylor remainder bound for `sinh(lv) sin(τv)`:**
For every `M, J ∈ ℕ` and `l, τ, v ∈ ℝ`,
`|sinh(lv) sin(τv) −
    (∑_{m < M} (lv)^{2m+1} / (2m+1)!) · (∑_{j < J} (−1)^j (τv)^{2j+1} / (2j+1)!)| ≤
  ((|l| |v|)^{2M+1} / (2M+1)! + (|τ| |v|)^{2J+1} / (2J+1)!) · exp((|l| + |τ|) |v|)`. -/
theorem abs_sinh_mul_sin_sub_double_sum_range_le (M J : ℕ) (l τ v : ℝ) :
    |Real.sinh (l * v) * Real.sin (τ * v) -
        (∑ m ∈ Finset.range M,
            (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))| ≤
      ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
        (|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
        Real.exp ((|l| + |τ|) * |v|) := by
  set S_M := ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)
  set S_J := ∑ j ∈ Finset.range J,
    (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)
  have hsplit :
      Real.sinh (l * v) * Real.sin (τ * v) - S_M * S_J =
        (Real.sinh (l * v) - S_M) * Real.sin (τ * v) +
          S_M * (Real.sin (τ * v) - S_J) := by ring
  have habs_lv : |l * v| = |l| * |v| := abs_mul l v
  have hSM_abs_le :
      |S_M| ≤ ∑ m ∈ Finset.range M,
        (|l| * |v|) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hfac0 : (0 : ℝ) ≤ ((2 * m + 1).factorial : ℝ) := Nat.cast_nonneg _
    rw [abs_div, abs_pow, habs_lv, abs_of_nonneg hfac0]
  have hsinh_le_exp : Real.sinh (|l| * |v|) ≤ Real.exp (|l| * |v|) := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (|l| * |v|)
    have := Real.exp_pos (-(|l| * |v|))
    linarith
  have hSM_le_exp : |S_M| ≤ Real.exp (|l| * |v|) :=
    (hSM_abs_le.trans (sum_range_odd_pow_div_factorial_le_sinh_nonneg M (by positivity))).trans
      hsinh_le_exp
  have hrem_sinh :
      |Real.sinh (l * v) - S_M| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) := by
    have h := abs_sinh_sub_sum_range_odd_pow_div_factorial_le M (l * v)
    rwa [habs_lv] at h
  have hrem_sin :
      |Real.sin (τ * v) - S_J| ≤
        ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) * Real.exp (|τ| * |v|) := by
    have h := abs_sin_sub_sum_range_odd_pow_div_factorial_le J (τ * v)
    have habs : |τ * v| = |τ| * |v| := abs_mul τ v
    rwa [habs] at h
  have hterm1 :
      |(Real.sinh (l * v) - S_M) * Real.sin (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul]
    have hsin_le_exp : |Real.sin (τ * v)| ≤ Real.exp (|τ| * |v|) :=
      (Real.abs_sin_le_one _).trans (Real.one_le_exp (by positivity))
    calc |Real.sinh (l * v) - S_M| * |Real.sin (τ * v)|
        ≤ (((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|)) *
            Real.exp (|τ| * |v|) :=
          mul_le_mul hrem_sinh hsin_le_exp (abs_nonneg _) (by positivity)
      _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hterm2 :
      |S_M * (Real.sin (τ * v) - S_J)| ≤
        ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul]
    calc |S_M| * |Real.sin (τ * v) - S_J|
        ≤ Real.exp (|l| * |v|) *
            (((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) * Real.exp (|τ| * |v|)) :=
          mul_le_mul hSM_le_exp hrem_sin (abs_nonneg _) (Real.exp_nonneg _)
      _ = ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  calc |(Real.sinh (l * v) - S_M) * Real.sin (τ * v)| + |S_M * (Real.sin (τ * v) - S_J)|
      ≤ ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) +
          ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) :=
        add_le_add hterm1 hterm2
    _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
          (|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by ring

/-- **Full-line integral linearity for the `(M, J)` joint two-variable odd-odd Taylor polynomial
against `Φ_k(v)` (`k ≥ 2`):**
`∫_ℝ (∑_{m < M} (lv)^{2m+1} / (2m+1)!) · (∑_{j < J} (−1)^j (τv)^{2j+1} / (2j+1)!) Φ_k(v) dv =
  ∑_{m < M} ∑_{j < J} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j+1} / (2j+1)!) ∫_ℝ v^{2m+1+2j+1} Φ_k(v) dv`. -/
theorem integral_double_sum_range_odd_pow_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M J : ℕ) :
    (∫ v : ℝ,
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) *
          (v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      exact integral_const_mul _ _
    · intro j _
      exact (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν
        (2 * m + 1 + (2 * j + 1))).const_mul _
  · intro m _
    exact integrable_finsetSum _ (fun j _ =>
      (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν
        (2 * m + 1 + (2 * j + 1))).const_mul _)

/-- **Scale-independent additive geometric remainder bound for the `(M, J)` joint two-variable
odd-odd Taylor polynomial of `N_k(l, τ)` across `|l| + |τ| < 1/8` (`k ≥ 2`, `M, J ∈ ℕ`):**
`|(∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx) −
    ∑_{m < M} ∑_{j < J} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j+1} / (2j+1)!) ∫_ℝ v^{2m+1+2j+1} Φ_k(v) dv| ≤
  (1650 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M+1} + (8|τ|)^{2J+1})`. -/
theorem abs_sineMellin_sub_double_sum_range_odd_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) (M J : ℕ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
        ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J + 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg τ]
  have hc : 0 < 1 / 8 - |l| - |τ| := by linarith
  rw [setIntegral_Ioi_rpow_mul_sin_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_sin_mul_arcLineInfiniteDyadicProfile_eq_sinh hk hν hl_half τ,
    ← integral_double_sum_range_odd_pow_mul_profile_eq hk hν l τ M J]
  have hInt_sinh : Integrable
      (fun v : ℝ => Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_sinh_mul_sin_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
          ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) *
            (v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, mul_pow, pow_add]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun j _ =>
        (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν
          (2 * m + 1 + (2 * j + 1))).const_mul _))
  rw [← integral_sub hInt_sinh hInt_sum]
  set B := 825 * ν.real univ * ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J + 1))
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                (∑ j ∈ Finset.range J,
                  (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
                arcLineInfiniteDyadicProfile k ν v)|
        ≤ B * (2 / (1 / 8 - |l| - |τ|)) := h1
      _ = (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
            ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J + 1)) := by
          dsimp [B]; ring
  · have hsub :
        Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v =
        (Real.sinh (l * v) * Real.sin (τ * v) -
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul]
    have hrem := abs_sinh_mul_sin_sub_double_sum_range_le M J l τ v
    have ht1 := joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le
      hk hν (2 * M + 1) l l τ v
    have ht2 := joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le
      hk hν (2 * J + 1) τ l τ v
    calc |Real.sinh (l * v) * Real.sin (τ * v) -
            (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
              (∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))| *
            |arcLineInfiniteDyadicProfile k ν v|
        ≤ (((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
              (|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|)) *
            |arcLineInfiniteDyadicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hrem (abs_nonneg _)
      _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| +
          ((|τ| * |v|) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| := by ring
      _ ≤ 825 * ν.real univ * (8 * |l|) ^ (2 * M + 1) * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) +
          825 * ν.real univ * (8 * |τ|) ^ (2 * J + 1) * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) :=
        add_le_add ht1 ht2
      _ = B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by dsimp [B]; ring

/-- **Unconditional `N → ∞` joint two-variable odd-odd Taylor power-series convergence for
`N_k(l, τ)` on `|l| + |τ| < 1/8` (`k ≥ 2`):**
`∑_{m < N} ∑_{j < N} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j+1} / (2j+1)!) ∫_ℝ v^{2m+1+2j+1} Φ_k(v) dv →
  ∫_{x > 0} x^{l − 1/2} sin(τ log x) V_k(x) dx` as `N → ∞`. -/
theorem tendsto_double_sum_range_odd_pow_div_factorial_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have hl_sq_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have hl_sq_lt_one : (8 * |l|) ^ 2 < 1 := by
    have : 8 * |l| < 1 := by linarith [abs_nonneg τ]
    nlinarith [abs_nonneg l]
  have hpow_l2 : Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hl_sq_nonneg hl_sq_lt_one).congr fun N => by
      rw [pow_mul]
  have hpow_l : Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N + 1)) atTop (nhds 0) := by
    have hmul := hpow_l2.mul_const (8 * |l|)
    rw [zero_mul] at hmul
    exact hmul.congr fun N => by rw [pow_succ]
  have hτ_sq_nonneg : 0 ≤ (8 * |τ|) ^ 2 := sq_nonneg _
  have hτ_sq_lt_one : (8 * |τ|) ^ 2 < 1 := by
    have : 8 * |τ| < 1 := by linarith [abs_nonneg l]
    nlinarith [abs_nonneg τ]
  have hpow_τ2 : Tendsto (fun N : ℕ => (8 * |τ|) ^ (2 * N)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hτ_sq_nonneg hτ_sq_lt_one).congr fun N => by
      rw [pow_mul]
  have hpow_τ : Tendsto (fun N : ℕ => (8 * |τ|) ^ (2 * N + 1)) atTop (nhds 0) := by
    have hmul := hpow_τ2.mul_const (8 * |τ|)
    rw [zero_mul] at hmul
    exact hmul.congr fun N => by rw [pow_succ]
  set C := 1650 * ν.real univ / (1 / 8 - |l| - |τ|)
  have hmaj :
      Tendsto (fun N : ℕ => C * ((8 * |l|) ^ (2 * N + 1) + (8 * |τ|) ^ (2 * N + 1)))
        atTop (nhds 0) := by
    simpa using (hpow_l.add hpow_τ).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_sineMellin_sub_double_sum_range_odd_le hk hν hlτ N N

/-- **Master Conjugate Sine & Cauchy–Riemann Witness Theorem for the Infinite-Horizon Dyadic
Modular Arc Tower:**
There exists a symmetric finite non-zero Borel measure `ν` on `ArcParam` such that for every
integer generator `k ≥ 2`:
1. (**Critical-line reality and doubly-odd functional equation**):
   For all `l, τ ∈ ℝ`, `N_k(0, τ) = 0`, `N_k(l, 0) = 0`, `N_k(−l, τ) = −N_k(l, τ)`, and
   `N_k(l, −τ) = −N_k(l, τ)`.
2. (**Height-uniform odd Taylor power series for `N_k(l, τ)`**):
   For all `|l| < 1/8` and `τ ∈ ℝ`,
   `∑_{m < M} (l^{2m+1} / (2m+1)!) ∫_ℝ v^{2m+1} sin(τv) Φ_k(v) dv → N_k(l, τ)` as `M → ∞`.
3. (**Global Cauchy–Riemann partial derivative equations across `|l| < 1/8`, `τ ∈ ℝ`**):
   At every `(l, τ)` with `|l| < 1/8` and `τ ∈ ℝ`,
   - `(M_k(l + h, τ) − M_k(l, τ)) / h → ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv` and
     `(N_k(l, τ + h) − N_k(l, τ)) / h → ∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv`,
   - `(N_k(l + h, τ) − N_k(l, τ)) / h → ∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv` and
     `(M_k(l, τ + h) − M_k(l, τ)) / h → −∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv`.
4. (**Joint two-variable odd-odd Taylor power-series convergence on `|l| + |τ| < 1/8`**):
   `∑_{m < N} ∑_{j < N} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j+1} / (2j+1)!) ∫_ℝ v^{2m+1+2j+1} Φ_k(v) dv → N_k(l, τ)`
   as `N → ∞`. -/
theorem exists_dyadic_conjugateSine_cauchyRiemann_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ τ : ℝ,
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) ∧
        (∀ l τ : ℝ,
          (∫ x in Ioi (0 : ℝ),
            x ^ (-l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
          -(∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun M : ℕ =>
              ∑ m ∈ Finset.range M,
                (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m + 1) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ∧
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ∧
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ∧
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) ∧
        (∀ ⦃l τ : ℝ⦄, |l| + |τ| < 1 / 8 →
          Tendsto
            (fun N : ℕ =>
              ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
                (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  ((-1 : ℝ) ^ j * τ ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m + 1 + (2 * j + 1)) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  refine ⟨fun τ => setIntegral_Ioi_rpow_neg_half_mul_sin_log_eq_zero hk1 ν τ,
    fun l τ => setIntegral_Ioi_rpow_neg_mul_sin_log_eq_neg hk1 ν l τ,
    fun l hl τ => tendsto_sum_range_odd_pow_div_factorial_mul_sin_moment_atTop hk hν hl τ,
    fun l hl τ =>
      ⟨tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ,
       tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ,
       tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ,
       tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ⟩,
    fun l τ hlτ => tendsto_double_sum_range_odd_pow_div_factorial_atTop hk hν hlτ⟩

end

end RHTower

