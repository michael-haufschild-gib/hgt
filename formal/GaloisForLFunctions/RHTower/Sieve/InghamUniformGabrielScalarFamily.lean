import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielDualPower

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Truncated center moment for the moving Gabriel strip. -/
def inghamUniformGabrielCenterMoment
    (sigma : ℝ) (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T,
    ‖f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)‖ ^
      inghamUniformGabrielInteriorPower sigma

/-- Scalar analytic family pairing the shifted field with its moving center dual datum. -/
def inghamUniformGabrielScalarFamily
    (sigma : ℝ) (f : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Icc (-T) T,
    f (z + t * I) *
      inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma
          (f ((inghamUniformGabrielCenter sigma : ℂ) + t * I))) z

/-- Scalar family represents the moving center moment exactly. -/
theorem inghamUniformGabrielScalarFamily_center
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (f : ℂ → ℂ) (T : ℝ) :
    inghamUniformGabrielScalarFamily sigma f T
        (inghamUniformGabrielCenter sigma : ℂ) =
      (inghamUniformGabrielCenterMoment sigma f T : ℂ) := by
  rw [inghamUniformGabrielScalarFamily,
    inghamUniformGabrielCenterMoment]
  calc
    (∫ t in Icc (-T) T,
      f ((inghamUniformGabrielCenter sigma : ℂ) + t * I) *
        inghamUniformGabrielDualPower sigma
          (inghamUniformGabrielDualSeed sigma
            (f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)))
          (inghamUniformGabrielCenter sigma : ℂ)) =
        ∫ t in Icc (-T) T,
          (↑(‖f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)‖ ^
            inghamUniformGabrielInteriorPower sigma) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inghamUniformGabrielDualPower_center hsigma0,
        mul_inghamUniformGabrielDualSeed hsigma0 hsigma1]
    _ = (↑(∫ t in Icc (-T) T,
        ‖f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)‖ ^
          inghamUniformGabrielInteriorPower sigma) : ℂ) := integral_ofReal

theorem inghamUniformGabrielCenterMoment_nonneg
    (sigma : ℝ) (f : ℂ → ℂ) (T : ℝ) :
    0 ≤ inghamUniformGabrielCenterMoment sigma f T := by
  exact integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _

theorem norm_inghamUniformGabrielScalarFamily_center
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (f : ℂ → ℂ) (T : ℝ) :
    ‖inghamUniformGabrielScalarFamily sigma f T
        (inghamUniformGabrielCenter sigma : ℂ)‖ =
      inghamUniformGabrielCenterMoment sigma f T := by
  rw [inghamUniformGabrielScalarFamily_center hsigma0 hsigma1,
    Complex.norm_real,
    Real.norm_of_nonneg (inghamUniformGabrielCenterMoment_nonneg sigma f T)]

theorem memLp_restrict_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : Continuous g) (a b : ℝ) (p : ENNReal) :
    MemLp g p (volume.restrict (Icc a b)) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hg.norm.continuousOn
  apply MemLp.of_bound hg.aestronglyMeasurable K
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hK (mem_image_of_mem (fun u => ‖g u‖) hx)

theorem norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T : ℝ) {z : ℂ}
    (hFcont : Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (hcenterCont : Continuous fun t : ℝ =>
      f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
    (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z
  have hFcont' : Continuous F := by
    simpa only [F] using hFcont
  have hzexp : 0 < (inghamUniformGabrielDualExponent sigma z).re := by
    apply inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1
    rw [hz]
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamUniformGabrielDualPower_const sigma z hzexp).comp
      ((continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp hcenterCont)
  have hFLp : MemLp F (ENNReal.ofReal (4 / 3 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont' (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (4 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := mu) hpq hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (4 : ℝ) ∂mu) =
      inghamUniformGabrielCenterMoment sigma f T := by
    rw [inghamUniformGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamUniformGabrielDualPower_seed_left_pow_four
      hsigma0 hsigma1 _ _ hz
  rw [show (1 / (4 / 3 : ℝ)) = 3 / 4 by norm_num,
    show (1 / (4 : ℝ)) = 1 / 4 by norm_num, hGmoment] at hholder
  rw [inghamUniformGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (4 / 3 : ℝ) ∂mu) ^ (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := rfl

theorem norm_inghamUniformGabrielScalarFamily_left_le
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ} (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := by
  apply norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
    hsigma0 hsigma1 T
  · exact hf.comp (by fun_prop)
  · exact hf.comp (by fun_prop)
  · exact hz

theorem norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T : ℝ) {z : ℂ}
    (hFcont : Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (hcenterCont : Continuous fun t : ℝ =>
      f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z
  have hFcont' : Continuous F := by
    simpa only [F] using hFcont
  have hzexp : 0 < (inghamUniformGabrielDualExponent sigma z).re := by
    apply inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1
    rw [hz]
    unfold inghamUniformGabrielRightEdge
    nlinarith
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamUniformGabrielDualPower_const sigma z hzexp).comp
      ((continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp hcenterCont)
  have hFLp : MemLp F (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont' (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := mu) Real.HolderConjugate.two_two hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (2 : ℝ) ∂mu) =
      inghamUniformGabrielCenterMoment sigma f T := by
    rw [inghamUniformGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamUniformGabrielDualPower_seed_right_pow_two
      hsigma0 hsigma1 _ _ hz
  rw [show (1 / (2 : ℝ)) = 1 / 2 by norm_num, hGmoment] at hholder
  rw [inghamUniformGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := rfl

theorem norm_inghamUniformGabrielScalarFamily_right_le
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ}
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := by
  apply norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
    hsigma0 hsigma1 T
  · exact hf.comp (by fun_prop)
  · exact hf.comp (by fun_prop)
  · exact hz

end

end RHTower.Sieve
