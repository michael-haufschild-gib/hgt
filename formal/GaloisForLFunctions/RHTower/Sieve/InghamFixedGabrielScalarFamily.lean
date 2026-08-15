import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielDualPower

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Truncated center moment appearing in fixed Gabriel interpolation. -/
def inghamFixedGabrielCenterMoment (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, ‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
    (364 / 237 : ℝ)

/-- Actual scalar analytic family obtained by pairing the shifted field with its fixed center dual
datum. -/
def inghamFixedGabrielScalarFamily (f : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc (-T) T,
    f (z + t * I) *
      inghamFixedGabrielDualPower
        (inghamFixedGabrielDualSeed
          (f ((inghamFixedGabrielSigma : ℂ) + t * I))) z

/-- The scalar family represents the center moment exactly. -/
theorem inghamFixedGabrielScalarFamily_center (f : ℂ → ℂ) (T : ℝ) :
    inghamFixedGabrielScalarFamily f T (inghamFixedGabrielSigma : ℂ) =
      (inghamFixedGabrielCenterMoment f T : ℂ) := by
  rw [inghamFixedGabrielScalarFamily, inghamFixedGabrielCenterMoment]
  calc
    (∫ t in Icc (-T) T,
      f ((inghamFixedGabrielSigma : ℂ) + t * I) *
        inghamFixedGabrielDualPower
          (inghamFixedGabrielDualSeed
            (f ((inghamFixedGabrielSigma : ℂ) + t * I)))
          (inghamFixedGabrielSigma : ℂ)) =
        ∫ t in Icc (-T) T,
          (↑(‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
            (364 / 237 : ℝ)) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inghamFixedGabrielDualPower_center, mul_inghamFixedGabrielDualSeed]
    _ = (↑(∫ t in Icc (-T) T,
        ‖f ((inghamFixedGabrielSigma : ℂ) + t * I)‖ ^
          (364 / 237 : ℝ)) : ℂ) := integral_ofReal

/-- The truncated center moment is nonnegative when the interval has its natural orientation. -/
theorem inghamFixedGabrielCenterMoment_nonneg (f : ℂ → ℂ) (T : ℝ) :
    0 ≤ inghamFixedGabrielCenterMoment f T := by
  exact integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _

/-- Consequently the center norm of the scalar family is exactly the center moment. -/
theorem norm_inghamFixedGabrielScalarFamily_center
    (f : ℂ → ℂ) (T : ℝ) :
    ‖inghamFixedGabrielScalarFamily f T (inghamFixedGabrielSigma : ℂ)‖ =
      inghamFixedGabrielCenterMoment f T := by
  rw [inghamFixedGabrielScalarFamily_center, Complex.norm_real,
    Real.norm_of_nonneg (inghamFixedGabrielCenterMoment_nonneg f T)]

private theorem memLp_restrict_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : Continuous g) (a b : ℝ) (p : ENNReal) :
    MemLp g p (volume.restrict (Icc a b)) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hg.norm.continuousOn
  apply MemLp.of_bound hg.aestronglyMeasurable K
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hK (mem_image_of_mem (fun u => ‖g u‖) hx)

theorem norm_inghamFixedGabrielScalarFamily_left_le
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ} (hz : z.re = 1 / 2) :
    ‖inghamFixedGabrielScalarFamily f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (inghamFixedGabrielCenterMoment f T) ^ (1 / 4 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamFixedGabrielDualPower
      (inghamFixedGabrielDualSeed
        (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hzexp : 0 < (inghamFixedGabrielDualExponent z).re := by
    rw [inghamFixedGabrielDualExponent_re_left hz]
    norm_num
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamFixedGabrielDualPower_const z hzexp).comp
      (continuous_inghamFixedGabrielDualSeed.comp
        (hf.comp (by fun_prop)))
  have hFLp : MemLp F (ENNReal.ofReal (4 / 3 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (4 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := mu) hpq hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (4 : ℝ) ∂mu) =
      inghamFixedGabrielCenterMoment f T := by
    rw [inghamFixedGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamFixedGabrielDualPower_seed_left_pow_four _ _ hz
  rw [show (1 / (4 / 3 : ℝ)) = 3 / 4 by norm_num,
    show (1 / (4 : ℝ)) = 1 / 4 by norm_num, hGmoment] at hholder
  rw [inghamFixedGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamFixedGabrielDualPower
            (inghamFixedGabrielDualSeed
              (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamFixedGabrielDualPower
            (inghamFixedGabrielDualSeed
              (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (4 / 3 : ℝ) ∂mu) ^ (3 / 4 : ℝ) *
        (inghamFixedGabrielCenterMoment f T) ^ (1 / 4 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) * (inghamFixedGabrielCenterMoment f T) ^ (1 / 4 : ℝ) := rfl

theorem norm_inghamFixedGabrielScalarFamily_right_le
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ}
    (hz : z.re = inghamPowerSavingRightEdge) :
    ‖inghamFixedGabrielScalarFamily f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (inghamFixedGabrielCenterMoment f T) ^ (1 / 2 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamFixedGabrielDualPower
      (inghamFixedGabrielDualSeed
        (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hzexp : 0 < (inghamFixedGabrielDualExponent z).re := by
    rw [inghamFixedGabrielDualExponent_re_right hz]
    norm_num
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamFixedGabrielDualPower_const z hzexp).comp
      (continuous_inghamFixedGabrielDualSeed.comp
        (hf.comp (by fun_prop)))
  have hFLp : MemLp F (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := mu) Real.HolderConjugate.two_two hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (2 : ℝ) ∂mu) =
      inghamFixedGabrielCenterMoment f T := by
    rw [inghamFixedGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamFixedGabrielDualPower_seed_right_pow_two _ _ hz
  rw [show (1 / (2 : ℝ)) = 1 / 2 by norm_num, hGmoment] at hholder
  rw [inghamFixedGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamFixedGabrielDualPower
            (inghamFixedGabrielDualSeed
              (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamFixedGabrielDualPower
            (inghamFixedGabrielDualSeed
              (f ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        (inghamFixedGabrielCenterMoment f T) ^ (1 / 2 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) * (inghamFixedGabrielCenterMoment f T) ^ (1 / 2 : ℝ) := rfl


end

end RHTower.Sieve
