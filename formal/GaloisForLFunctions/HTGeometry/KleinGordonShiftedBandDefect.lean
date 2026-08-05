import GaloisForLFunctions.HTGeometry.KleinGordonShiftedGroupLaw

/-!
# The shifted propagator on a band

Below a fixed frequency the shifted frequency is bounded, `Ω² ≤ 1 + R² + b`, so the Taylor estimates
of the circle become uniform: the shifted cosine propagator is the identity to second order and the
shifted sine propagator is multiplication by the elapsed time to third order,

`‖(cos(τΩ) − 1)P_R‖ ≤ τ²(1 + R² + b)/2`,   `‖(sin(τΩ)/Ω − τ)P_R‖ ≤ |τ|³(1 + R² + b)/6`.

These are the shifted counterparts of the free band estimates, and they are what makes the shifted
propagator differentiable in operator norm on a band — the step that turns the shifted symbols into an
actual solution operator.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section BandDefect

variable {v : E → ℝ} {b : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Below a fixed frequency the shifted frequency is bounded.** -/
theorem kgShiftedFreq_sq_le (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b) {R : ℝ} {ξ : E}
    (hξ : ‖ξ‖ ≤ R) : kgShiftedFreq v ξ ^ 2 ≤ 1 + R ^ 2 + b := by
  rw [kgShiftedFreq_sq hb1 hvb ξ]
  have hfreq : kgFreq ξ ^ 2 ≤ 1 + R ^ 2 := by
    rw [kgFreq, Real.sq_sqrt (by positivity)]
    nlinarith [norm_nonneg ξ]
  have hv : v ξ ≤ b := le_of_abs_le (hvb ξ)
  linarith

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem band_bound_nonneg (hb0 : 0 ≤ b) (R : ℝ) : (0 : ℝ) ≤ 1 + R ^ 2 + b := by
  nlinarith [sq_nonneg R]

/-! ## The cosine defect -/

/-- The symbol of `cos(τΩ) − 1`, cut to the frequencies below `R`. -/
def kgShiftedCosDefectLow (v : E → ℝ) (τ R : ℝ) (ξ : E) : ℂ :=
  (kgShiftedCos v τ ξ - 1) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedCosDefectLow (hv : Measurable v) (τ R : ℝ) :
    Measurable (kgShiftedCosDefectLow v τ R) :=
  ((measurable_kgShiftedCos hv τ).sub measurable_const).mul (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgShiftedCosDefectLow_le (hb0 : 0 ≤ b) (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b)
    (τ R : ℝ) (ξ : E) :
    ‖kgShiftedCosDefectLow v τ R ξ‖ ≤ τ ^ 2 * (1 + R ^ 2 + b) / 2 := by
  have hband := band_bound_nonneg hb0 R
  have hB0 : (0 : ℝ) ≤ τ ^ 2 * (1 + R ^ 2 + b) / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg τ) hband) (by norm_num)
  rw [kgShiftedCosDefectLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, kgShiftedCos, show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos (τ * kgShiftedFreq v ξ) - 1| ≤ (τ * kgShiftedFreq v ξ) ^ 2 / 2 :=
      abs_cos_sub_one_le _
    have h2 : (τ * kgShiftedFreq v ξ) ^ 2 / 2 = τ ^ 2 * kgShiftedFreq v ξ ^ 2 / 2 := by ring
    have h3 : kgShiftedFreq v ξ ^ 2 ≤ 1 + R ^ 2 + b := kgShiftedFreq_sq_le hb1 hvb hξ
    have h4 : τ ^ 2 * kgShiftedFreq v ξ ^ 2 / 2 ≤ τ ^ 2 * (1 + R ^ 2 + b) / 2 := by
      nlinarith [sq_nonneg τ]
    rw [h2] at h1
    linarith
  · simpa using hB0

set_option maxHeartbeats 1000000 in
/-- **The shifted cosine propagator is the identity to second order, below a fixed frequency.** -/
theorem norm_kgShiftedCosOp_lowPass_sub_le (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (τ R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgShiftedCosOp hv τ (kgLowPassOp R x) - kgLowPassOp R x‖
      ≤ τ ^ 2 * (1 + R ^ 2 + b) / 2 * ‖x‖ := by
  have hband := band_bound_nonneg hb0 R
  have hB0 : (0 : ℝ) ≤ τ ^ 2 * (1 + R ^ 2 + b) / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg τ) hband) (by norm_num)
  have hprod : Measurable fun ξ : E => kgShiftedCos v τ ξ * kgLowPass R ξ :=
    (measurable_kgShiftedCos hv τ).mul (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgShiftedCos v τ ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le v τ ξ) (norm_nonneg _) (norm_kgLowPass_le R ξ)
  have hcomp : (kgShiftedCosOp (E := E) hv τ).comp (kgLowPassOp R)
      = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Eventually.of_forall fun _ => rfl)
  have hdiff : fourierMulCLM (measurable_kgShiftedCosDefectLow hv τ R) hB0
      (norm_kgShiftedCosDefectLow_le hb0 hb1 hvb τ R)
      = fourierMulCLM hprod zero_le_one hprodb - kgLowPassOp R := by
    rw [kgLowPassOp_eq]
    refine fourierMulCLM_sub _ _ _ zero_le_one hprodb zero_le_one (norm_kgLowPass_le R) hB0
      (norm_kgShiftedCosDefectLow_le hb0 hb1 hvb τ R) (Eventually.of_forall fun ξ => ?_)
    rw [kgShiftedCosDefectLow]
    ring
  have hval : kgShiftedCosOp (E := E) hv τ (kgLowPassOp R x) - kgLowPassOp R x
      = fourierMulCLM (measurable_kgShiftedCosDefectLow hv τ R) hB0
        (norm_kgShiftedCosDefectLow_le hb0 hb1 hvb τ R) x := by
    rw [hdiff, sub_apply, ← ContinuousLinearMap.comp_apply, hcomp]
  rw [hval]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_fourierMulCLM_le _ _ _) x

/-! ## The sine defect -/

/-- The symbol of `sin(τΩ)/Ω − τ`, cut to the frequencies below `R`. -/
def kgShiftedSinDefectLow (v : E → ℝ) (τ R : ℝ) (ξ : E) : ℂ :=
  (kgShiftedSinOverFreq v τ ξ - (τ : ℂ)) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgShiftedSinDefectLow (hv : Measurable v) (τ R : ℝ) :
    Measurable (kgShiftedSinDefectLow v τ R) :=
  ((measurable_kgShiftedSinOverFreq hv τ).sub measurable_const).mul (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgShiftedSinDefectLow_le (hb0 : 0 ≤ b) (hb1 : b < 1) (hvb : ∀ ξ : E, |v ξ| ≤ b)
    (τ R : ℝ) (ξ : E) :
    ‖kgShiftedSinDefectLow v τ R ξ‖ ≤ |τ| ^ 3 * (1 + R ^ 2 + b) / 6 := by
  have hband := band_bound_nonneg hb0 R
  have hB0 : (0 : ℝ) ≤ |τ| ^ 3 * (1 + R ^ 2 + b) / 6 :=
    div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg τ) 3) hband) (by norm_num)
  rw [kgShiftedSinDefectLow, kgLowPass]
  split
  · rename_i hξ
    have hpos := kgShiftedFreq_pos hb1 hvb ξ
    rw [mul_one, kgShiftedSinOverFreq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    have hrw : Real.sin (τ * kgShiftedFreq v ξ) / kgShiftedFreq v ξ - τ
        = (Real.sin (τ * kgShiftedFreq v ξ) - τ * kgShiftedFreq v ξ) / kgShiftedFreq v ξ := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : |Real.sin (τ * kgShiftedFreq v ξ) - τ * kgShiftedFreq v ξ|
        ≤ |τ * kgShiftedFreq v ξ| ^ 3 / 6 := abs_sin_sub_self_le _
    have habs : |τ * kgShiftedFreq v ξ| ^ 3 = |τ| ^ 3 * kgShiftedFreq v ξ ^ 3 := by
      rw [abs_mul, abs_of_pos hpos, mul_pow]
    have h3 : kgShiftedFreq v ξ ^ 2 ≤ 1 + R ^ 2 + b := kgShiftedFreq_sq_le hb1 hvb hξ
    rw [habs] at h1
    have hstep : kgShiftedFreq v ξ ^ 2 * kgShiftedFreq v ξ
        ≤ (1 + R ^ 2 + b) * kgShiftedFreq v ξ := mul_le_mul_of_nonneg_right h3 hpos.le
    have habs3 : (0 : ℝ) ≤ |τ| ^ 3 := pow_nonneg (abs_nonneg τ) 3
    have h4 : |τ| ^ 3 * kgShiftedFreq v ξ ^ 3 / 6
        ≤ |τ| ^ 3 * (1 + R ^ 2 + b) / 6 * kgShiftedFreq v ξ := by
      have hmul := mul_le_mul_of_nonneg_left hstep habs3
      have hcube : kgShiftedFreq v ξ ^ 3
          = kgShiftedFreq v ξ ^ 2 * kgShiftedFreq v ξ := by ring
      rw [hcube]
      linarith
    linarith
  · simpa using hB0

set_option maxHeartbeats 1000000 in
/-- **The shifted sine propagator is multiplication by the elapsed time to third order, below a
fixed frequency.** -/
theorem norm_kgShiftedSinFreqOp_lowPass_sub_le (hv : Measurable v) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hvb : ∀ ξ : E, |v ξ| ≤ b) (τ R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgShiftedSinFreqOp hv τ (kgLowPassOp R x) - (τ : ℂ) • kgLowPassOp R x‖
      ≤ |τ| ^ 3 * (1 + R ^ 2 + b) / 6 * ‖x‖ := by
  have hband := band_bound_nonneg hb0 R
  have hB0 : (0 : ℝ) ≤ |τ| ^ 3 * (1 + R ^ 2 + b) / 6 :=
    div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg τ) 3) hband) (by norm_num)
  have hprod : Measurable fun ξ : E => kgShiftedSinOverFreq v τ ξ * kgLowPass R ξ :=
    (measurable_kgShiftedSinOverFreq hv τ).mul (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgShiftedSinOverFreq v τ ξ * kgLowPass R ξ‖ ≤ |τ| := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgShiftedSinOverFreq_le v τ ξ
    have h2 := norm_kgLowPass_le R ξ
    calc ‖kgShiftedSinOverFreq v τ ξ‖ * ‖kgLowPass R ξ‖
        ≤ |τ| * 1 := mul_le_mul h1 h2 (norm_nonneg _) (abs_nonneg τ)
      _ = |τ| := mul_one _
  have hscal : Measurable fun ξ : E => (τ : ℂ) * kgLowPass R ξ :=
    measurable_const.mul (measurable_kgLowPass R)
  have hscalb : ∀ ξ : E, ‖(τ : ℂ) * kgLowPass R ξ‖ ≤ |τ| := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := norm_kgLowPass_le R ξ
    calc |τ| * ‖kgLowPass R ξ‖ ≤ |τ| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg τ)
      _ = |τ| := mul_one _
  have hcomp : (kgShiftedSinFreqOp (E := E) hv τ).comp (kgLowPassOp R)
      = fourierMulCLM hprod (abs_nonneg τ) hprodb := by
    rw [kgShiftedSinFreqOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ (abs_nonneg τ) hprodb
      (Eventually.of_forall fun _ => rfl)
  have hsmul : fourierMulCLM hscal (abs_nonneg τ) hscalb = (τ : ℂ) • kgLowPassOp (E := E) R := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hscal zero_le_one (norm_kgLowPass_le R) (abs_nonneg τ) hscalb
      (τ : ℂ) (Eventually.of_forall fun _ => rfl)
  have hdiff : fourierMulCLM (measurable_kgShiftedSinDefectLow hv τ R) hB0
      (norm_kgShiftedSinDefectLow_le hb0 hb1 hvb τ R)
      = fourierMulCLM hprod (abs_nonneg τ) hprodb - fourierMulCLM hscal (abs_nonneg τ) hscalb := by
    refine fourierMulCLM_sub _ _ _ (abs_nonneg τ) hprodb (abs_nonneg τ) hscalb hB0
      (norm_kgShiftedSinDefectLow_le hb0 hb1 hvb τ R) (Eventually.of_forall fun ξ => ?_)
    rw [kgShiftedSinDefectLow]
    ring
  have hval : kgShiftedSinFreqOp (E := E) hv τ (kgLowPassOp R x) - (τ : ℂ) • kgLowPassOp R x
      = fourierMulCLM (measurable_kgShiftedSinDefectLow hv τ R) hB0
        (norm_kgShiftedSinDefectLow_le hb0 hb1 hvb τ R) x := by
    rw [hdiff, hsmul, sub_apply, ← ContinuousLinearMap.comp_apply, hcomp, smul_apply]
  rw [hval]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_fourierMulCLM_le _ _ _) x

end BandDefect

end GaloisForLFunctions.HTGeometry
