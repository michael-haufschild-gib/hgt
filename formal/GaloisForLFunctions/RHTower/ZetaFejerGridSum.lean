import GaloisForLFunctions.RHTower.ZetaFejerWeight

/-!
# Grid character sums of the Fejér window

The Fejér window `W` of `[s₀, s₁]` with band `b` decays quadratically outside the interval
(`fejerWindow_le_sq_right`, `fejerWindow_le_sq_left`) and its transform vanishes beyond the band.  On the Gabor grid
`τ_k = T + k·2π/L`, Poisson summation therefore gives

`Σ_{k∈ℤ} W(τ_k) e^{iyτ_k} = 0`   whenever `|jL − y| ≥ b` for every `j ∈ ℤ`

(`hasSum_fejer_grid_char_eq_zero`): the weighted grid sees a frequency `y` only through its aliases `y ≡ 0 mod L`, up
to the band.  For the weighted trace of the zeta Gram matrix this removes every prime frequency `log n` with
`b ≤ log n ≤ L − b`.
-/

open Complex MeasureTheory Real Set Filter Asymptotics
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b s₀ s₁ : ℝ}

/-- To the right of the interval the window decays quadratically. -/
theorem fejerWindow_le_sq_right (hb : 0 < b) (h01 : s₀ ≤ s₁) {s : ℝ} (hs : s₁ < s) :
    fejerWindow b s₀ s₁ s ≤ (fejerMass b)⁻¹ * ((s₁ - s₀) * (4 / ((s - s₁) ^ 2 * b))) := by
  have hk := fejerMass_pos hb
  unfold fejerWindow
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hk.le)
  have hle : s - s₁ ≤ s - s₀ := by linarith
  have hbd : ∀ v ∈ Icc (s - s₁) (s - s₀), fejerBandProfile b v ≤ 4 / ((s - s₁) ^ 2 * b) := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le (by linarith) hv.1
    refine (fejerBandProfile_le_inv hb hv0.ne').trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : (s - s₁) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by linarith) hv.1 2
    nlinarith
  calc ∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v
      ≤ ∫ v in (s - s₁)..(s - s₀), 4 / ((s - s₁) ^ 2 * b) :=
        intervalIntegral.integral_mono_on hle
          ((continuous_fejerBandProfile hb).intervalIntegrable _ _) intervalIntegrable_const hbd
    _ = (s₁ - s₀) * (4 / ((s - s₁) ^ 2 * b)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- To the left of the interval the window decays quadratically. -/
theorem fejerWindow_le_sq_left (hb : 0 < b) (h01 : s₀ ≤ s₁) {s : ℝ} (hs : s < s₀) :
    fejerWindow b s₀ s₁ s ≤ (fejerMass b)⁻¹ * ((s₁ - s₀) * (4 / ((s₀ - s) ^ 2 * b))) := by
  have hrefl : fejerWindow b s₀ s₁ s = fejerWindow b (-s₁) (-s₀) (-s) := by
    unfold fejerWindow
    congr 1
    have h := intervalIntegral.integral_comp_neg (a := s - s₁) (b := s - s₀) (fejerBandProfile b)
    simp only [fejerBandProfile_neg] at h
    rw [h]
    congr 1 <;> ring
  rw [hrefl]
  have h := fejerWindow_le_sq_right hb (s₀ := -s₁) (s₁ := -s₀) (by linarith) (s := -s) (by linarith)
  rw [show -s₀ - -s₁ = s₁ - s₀ by ring, show -s - -s₀ = s₀ - s by ring] at h
  exact h

variable {L : ℝ}

/-- The window sampled along `x ↦ T + x·2π/L`, twisted by `e^{iy(·)}`. -/
def gridChar (b s₀ s₁ L T y x : ℝ) : ℂ :=
  ((fejerWindow b s₀ s₁ (T + x * (2 * π / L)) : ℝ) : ℂ) * cexp (I * y * ((T + x * (2 * π / L) : ℝ) : ℂ))

theorem continuous_fejerWindow (hb : 0 < b) : Continuous (fejerWindow b s₀ s₁) := by
  unfold fejerWindow
  refine continuous_const.mul ?_
  have hF := continuous_fejerBandProfile hb
  have : (fun s => ∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v)
      = fun s => (∫ v in (0 : ℝ)..(s - s₀), fejerBandProfile b v)
        - ∫ v in (0 : ℝ)..(s - s₁), fejerBandProfile b v := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  rw [this]
  have hP : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..u, fejerBandProfile b v :=
    continuous_iff_continuousAt.mpr fun u => (hF.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  exact (hP.comp (continuous_id.sub continuous_const)).sub (hP.comp (continuous_id.sub continuous_const))

theorem norm_gridChar (hb : 0 < b) (h01 : s₀ ≤ s₁) (T y x : ℝ) :
    ‖gridChar b s₀ s₁ L T y x‖ = fejerWindow b s₀ s₁ (T + x * (2 * π / L)) := by
  unfold gridChar
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerWindow_nonneg hb h01 _),
    show I * (y : ℂ) * ((T + x * (2 * π / L) : ℝ) : ℂ) = ((y * (T + x * (2 * π / L))) : ℝ) * I by
      push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_gridChar (hb : 0 < b) (T y : ℝ) : Continuous (gridChar b s₀ s₁ L T y) := by
  have := continuous_fejerWindow (s₀ := s₀) (s₁ := s₁) hb
  unfold gridChar
  fun_prop

/-- The sampled window decays like `|x|⁻²`. -/
theorem gridChar_isBigO (hb : 0 < b) (h01 : s₀ ≤ s₁) (hL : 0 < L) (T y : ℝ) :
    gridChar b s₀ s₁ L T y =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  have hk := fejerMass_pos hb
  set C : ℝ := (fejerMass b)⁻¹ * ((s₁ - s₀) * (16 / (h ^ 2 * b))) with hC
  set R : ℝ := 2 * (|s₁ - T| + |s₀ - T| + 1) / h with hR
  refine IsBigO.of_bound C ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)] with x hx
  rw [Real.norm_eq_abs] at hx
  rw [norm_gridChar hb h01, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hxR : 2 * (|s₁ - T| + |s₀ - T| + 1) ≤ |x| * h := by
    rw [hR, div_le_iff₀ hh0] at hx; linarith
  have hx0 : 0 < |x| := by
    have : 0 < 2 * (|s₁ - T| + |s₀ - T| + 1) := by positivity
    by_contra h0; push Not at h0
    have : |x| * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 hh0.le
    linarith
  have hs₁ := abs_nonneg (s₁ - T)
  have hs₀ := abs_nonneg (s₀ - T)
  rcases le_or_gt 0 x with hxp | hxn
  · rw [abs_of_nonneg hxp] at hxR hx0
    have hgap : x * h / 2 ≤ T + x * h - s₁ := by linarith [le_abs_self (s₁ - T)]
    have hgap0 : 0 < x * h / 2 := by positivity
    have hW := fejerWindow_le_sq_right hb h01 (s := T + x * h) (by linarith)
    refine hW.trans ?_
    rw [hC, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [show 16 / (h ^ 2 * b) * (x ^ 2)⁻¹ = 4 / ((x * h / 2) ^ 2 * b) by field_simp; ring]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgap0.le hgap 2) hb.le
  · rw [abs_of_neg hxn] at hxR hx0
    have hgap : -x * h / 2 ≤ s₀ - (T + x * h) := by linarith [neg_abs_le (s₀ - T)]
    have hgap0 : 0 < -x * h / 2 := by nlinarith
    have hW := fejerWindow_le_sq_left hb h01 (s := T + x * h) (by linarith)
    refine hW.trans ?_
    rw [hC, mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [show 16 / (h ^ 2 * b) * (x ^ 2)⁻¹ = 4 / ((-x * h / 2) ^ 2 * b) by field_simp; ring]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgap0.le hgap 2) hb.le

/-- The transform of the sampled window vanishes at every `w` with `|wL − y| ≥ b`. -/
theorem fourier_gridChar_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) (hL : 0 < L) (T y : ℝ) {w : ℝ}
    (hw : b ≤ |w * L - y|) : 𝓕 (gridChar b s₀ s₁ L T y) w = 0 := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  set G : ℝ → ℂ := fun s => cexp (I * ((w * L * T : ℝ) : ℂ))
      * (((fejerWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (-(I * ((w * L - y : ℝ) : ℂ) * s))) with hG
  have hpt : ∀ x : ℝ, Real.fourierChar (-(x * w)) • gridChar b s₀ s₁ L T y x = G (T + h * x) := by
    intro x
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, gridChar, hG]
    rw [show T + x * (2 * π / L) = T + h * x by rw [hh]; ring]
    have e1 : cexp (((2 * π * -(x * w) : ℝ) : ℂ) * I) * cexp (I * (y : ℂ) * ((T + h * x : ℝ) : ℂ))
        = cexp (I * ((w * L * T : ℝ) : ℂ)) * cexp (-(I * ((w * L - y : ℝ) : ℂ) * ((T + h * x : ℝ) : ℂ))) := by
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hh]
      push_cast
      field_simp
      ring
    linear_combination ((fejerWindow b s₀ s₁ (T + h * x) : ℝ) : ℂ) * e1
  rw [Real.fourier_real_eq]
  simp_rw [hpt]
  have h1 := Measure.integral_comp_mul_left (fun z => G (T + z)) h
  rw [h1, integral_add_left_eq_self G T, hG, integral_const_mul,
    integral_fejerWindow_mul_cexp_eq_zero hb h01 hw, mul_zero, smul_zero]

/-- **Weighted grid character sums vanish off the aliases:** if `|jL − y| ≥ b` for every `j ∈ ℤ`, then
`Σ_{k∈ℤ} W(τ_k) e^{iyτ_k} = 0` on the grid `τ_k = T + k·2π/L`. -/
theorem hasSum_fejer_grid_char_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) (hL : 0 < L) (T y : ℝ)
    (hy : ∀ j : ℤ, b ≤ |j * L - y|) :
    HasSum (fun k : ℤ => gridChar b s₀ s₁ L T y k) 0 := by
  have hc := continuous_gridChar (s₀ := s₀) (s₁ := s₁) (L := L) hb T y
  have hgO := gridChar_isBigO hb h01 hL T y
  have hFO : 𝓕 (gridChar b s₀ s₁ L T y) =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop ((|y| + b) / L))]
      with w hw
    rw [Real.norm_eq_abs, div_le_iff₀ hL] at hw
    rw [fourier_gridChar_eq_zero hb h01 hL T y (w := w)]
    · simp
    · have h1 : |w * L| - |y| ≤ |w * L - y| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h1
      linarith
  have hsum : Summable (fun k : ℤ => gridChar b s₀ s₁ L T y k) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) (hgO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two hgO hFO 0
  simp only [zero_add] at key
  have h0 : ∀ n : ℤ, 𝓕 (gridChar b s₀ s₁ L T y) n * fourier n ((0 : ℝ) : UnitAddCircle) = 0 := by
    intro n
    rw [fourier_gridChar_eq_zero hb h01 hL T y (hy n), zero_mul]
  simp_rw [h0, tsum_zero] at key
  rw [← key]
  exact hsum.hasSum

end FejerWeight

end RHTower
