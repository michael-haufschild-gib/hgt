import GaloisForLFunctions.ArithmeticPositiveDuality.SymmetricRationalZeroRelocationBohrObstruction
import GaloisForLFunctions.RHTower.ZetaStripBohrFourierCoefficients
import GaloisForLFunctions.RHTower.ZetaStripBesicovitchAlmostPeriodicity

/-!
# Rational zero relocation is invisible to mean spectra

A continuous multiplier tending to one preserves every finite Cesàro square
mean. Its additive error has zero square mean and zero Fourier means. Applied
to the literal rational zero-relocation factor, this preserves zeta's mean
spectrum in the strip even though exact Bohr almost periodicity is destroyed
in the absolutely convergent half-plane.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- A vanishing nonnegative weight kills every bounded nonnegative Cesàro mean. -/
theorem tendsto_weightedMean_zero {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, 0 ≤ f t)
    (hg0 : ∀ t, 0 ≤ g t) (hlim : Tendsto g atTop (𝓝 0)) {C : ℝ}
    (hbound : ∀ᶠ T : ℝ in atTop, (∫ t in (0 : ℝ)..T, f t) / T ≤ C) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, f t * g t) / T) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K := |C| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith only [le_abs_self C]
  let δ := ε / (2 * K)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδK : δ * K = ε / 2 := by dsimp only [δ]; field_simp
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hlim.eventually_lt_const hδ)
  let L := max L₀ 0
  have hL0 : 0 ≤ L := le_max_right _ _
  have hsmall : ∀ t, L ≤ t → g t ≤ δ :=
    fun t ht => (hL₀ t ((le_max_left _ _).trans ht)).le
  let D := ∫ t in (0 : ℝ)..L, f t * g t
  have hD : Tendsto (fun T : ℝ => D / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop (max L 1), hbound,
    hD.eventually_lt_const (show 0 < ε / 2 by positivity)] with T hT hB hDT
  have hLT : L ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hT)
  have hpre : 0 ≤ ∫ t in (0 : ℝ)..L, f t :=
    intervalIntegral.integral_nonneg hL0 fun t _ => hf0 t
  have hsplitF := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 L) (hf.intervalIntegrable L T)
  have htailF : (∫ t in L..T, f t) ≤ ∫ t in (0 : ℝ)..T, f t := by
    linarith only [hpre, hsplitF]
  have htail : (∫ t in L..T, f t * g t) ≤ δ * ∫ t in (0 : ℝ)..T, f t := by
    calc
      _ ≤ ∫ t in L..T, δ * f t :=
        intervalIntegral.integral_mono_on hLT ((hf.mul hg).intervalIntegrable _ _)
          ((continuous_const.mul hf).intervalIntegrable _ _)
          (fun t ht => by
            change f t * g t ≤ δ * f t
            simpa only [mul_comm (f t) δ] using
              mul_le_mul_of_nonneg_left (hsmall t ht.1) (hf0 t))
      _ = δ * ∫ t in L..T, f t := intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htailF hδ.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hf.mul hg).intervalIntegrable 0 L) ((hf.mul hg).intervalIntegrable L T)
  have htotal : (∫ t in (0 : ℝ)..T, f t * g t) ≤ D + δ * ∫ t in (0 : ℝ)..T, f t := by
    change D + (∫ t in L..T, f t * g t) = ∫ t in (0 : ℝ)..T, f t * g t at hsplit
    linarith only [htail, hsplit]
  have hratio := div_le_div_of_nonneg_right htotal hT0.le
  rw [add_div, mul_div_assoc] at hratio
  have hpay := mul_le_mul_of_nonneg_left (hB.trans hCK) hδ.le
  have hnonneg : 0 ≤ (∫ t in (0 : ℝ)..T, f t * g t) / T :=
    div_nonneg (intervalIntegral.integral_nonneg hT0.le
      fun t _ => mul_nonneg (hf0 t) (hg0 t)) hT0.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith only [hratio, hpay, hDT, hδK]

/-- Multipliers tending to one create no Cesàro square-mass error. -/
theorem tendsto_multiplier_error_meanSquare {F m : ℝ → ℂ}
    (hF : Continuous F) (hm : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) {C : ℝ}
    (hbound : ∀ᶠ T : ℝ in atTop, (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T ≤ C) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t * m t - F t‖ ^ 2) / T)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun t => ‖m t - 1‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hlim.sub_const 1).norm.pow 2
  have h := tendsto_weightedMean_zero (hF.norm.pow 2) ((hm.sub continuous_const).norm.pow 2)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) hg hbound
  convert h using 1
  funext T
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change ‖F t * m t - F t‖ ^ 2 = ‖F t‖ ^ 2 * ‖m t - 1‖ ^ 2
  rw [show F t * m t - F t = F t * (m t - 1) by ring, norm_mul, mul_pow]

/-- The mean-square limit itself is unchanged by a multiplier tending to one. -/
theorem tendsto_multiplier_meanSquare {F m : ℝ → ℂ}
    (hF : Continuous F) (hm : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) {C : ℝ}
    (hmean : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t * m t‖ ^ 2) / T) atTop (𝓝 C) := by
  have hbound : ∀ᶠ T : ℝ in atTop, (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T ≤ C + 1 :=
    (hmean.eventually_lt_const (lt_add_one C)).mono fun _ h => h.le
  have hg : Tendsto (fun t => |‖m t‖ ^ 2 - 1|) atTop (𝓝 0) := by
    simpa only [norm_one, one_pow, sub_self, abs_zero] using
      ((hlim.norm.pow 2).sub_const 1).abs
  have ht := tendsto_weightedMean_zero (hF.norm.pow 2)
    (((hm.norm.pow 2).sub continuous_const).abs)
    (fun _ => sq_nonneg _) (fun _ => abs_nonneg _) hg hbound
  have hd : Tendsto (fun T : ℝ =>
      ((∫ t in (0 : ℝ)..T, ‖F t * m t‖ ^ 2) / T) -
        ((∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hT]
    apply div_le_div_of_nonneg_right _ hT.le
    have hGsq : Continuous (fun t : ℝ => ‖F t * m t‖ ^ 2) := (hF.mul hm).norm.pow 2
    have hFsq : Continuous (fun t : ℝ => ‖F t‖ ^ 2) := hF.norm.pow 2
    rw [← intervalIntegral.integral_sub (hGsq.intervalIntegrable 0 T)
      (hFsq.intervalIntegrable 0 T)]
    refine (intervalIntegral.abs_integral_le_integral_abs hT.le).trans_eq ?_
    apply intervalIntegral.integral_congr
    intro t _
    change |‖F t * m t‖ ^ 2 - ‖F t‖ ^ 2| = ‖F t‖ ^ 2 * |‖m t‖ ^ 2 - 1|
    rw [norm_mul, mul_pow, show ‖F t‖ ^ 2 * ‖m t‖ ^ 2 - ‖F t‖ ^ 2 =
      ‖F t‖ ^ 2 * (‖m t‖ ^ 2 - 1) by ring, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa only [sub_add_cancel, zero_add] using hd.add hmean

/-- Vanishing square mean forces vanishing average absolute mass. -/
theorem tendsto_average_norm_of_meanSquare_zero {F : ℝ → ℂ} (hF : Continuous F)
    (hmean : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t‖) / T) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hmean.eventually_lt_const (show 0 < ε ^ 2 by positivity)] with T hT hsmall
  have hbound : (∫ t in (0 : ℝ)..T, ‖F t‖) ≤
      T * (ε / 2) + (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / (2 * ε) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hT.le (hF.norm.intervalIntegrable _ _)
      ((continuous_const.add ((hF.norm.pow 2).div_const (2 * ε))).intervalIntegrable _ _)
      (fun t _ => RHTower.real_le_half_add_sq_div (x := ‖F t‖) hε)
    have hi₁ : IntervalIntegrable (fun _ : ℝ => ε / 2) volume 0 T :=
      continuous_const.intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun t : ℝ => ‖F t‖ ^ 2 / (2 * ε)) volume 0 T :=
      ((hF.norm.pow 2).div_const (2 * ε)).intervalIntegrable _ _
    change (∫ t in (0 : ℝ)..T, ‖F t‖) ≤ ∫ t in (0 : ℝ)..T, ε / 2 + ‖F t‖ ^ 2 / (2 * ε) at h
    rw [intervalIntegral.integral_add hi₁ hi₂,
      intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul, sub_zero] at h
    exact h
  have hd := div_le_div_of_nonneg_right hbound hT.le
  have he : (T * (ε / 2) + (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / (2 * ε)) / T =
      ε / 2 + ((∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T) / (2 * ε) := by
    field_simp
  rw [he] at hd
  have heps : ε ^ 2 / (2 * ε) = ε / 2 := by field_simp
  have hs := div_lt_div_of_pos_right hsmall (show 0 < 2 * ε by positivity)
  rw [heps] at hs
  have hnonneg : 0 ≤ (∫ t in (0 : ℝ)..T, ‖F t‖) / T :=
    div_nonneg (intervalIntegral.integral_nonneg hT.le fun t _ => norm_nonneg _) hT.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith only [hd, hs]

/-- Every Fourier average vanishes for a continuous function of zero square mean. -/
theorem tendsto_fourierMean_of_meanSquare_zero {F : ℝ → ℂ} (hF : Continuous F)
    (hmean : Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T) atTop (𝓝 0))
    (lam : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      F t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_average_norm_of_meanSquare_zero hF hmean)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT.le)
  refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro t _
  change ‖F t * Complex.exp ((lam : ℂ) * I * (t : ℂ))‖ = ‖F t‖
  rw [norm_mul, RHTower.norm_exp_real_mul_I_mul_real, mul_one]

/-- A multiplier tending to one preserves every existing Fourier mean. -/
theorem tendsto_multiplier_fourierMean {F m : ℝ → ℂ}
    (hF : Continuous F) (hm : Continuous m) (hlim : Tendsto m atTop (𝓝 1)) {C : ℝ}
    (hbound : ∀ᶠ T : ℝ in atTop, (∫ t in (0 : ℝ)..T, ‖F t‖ ^ 2) / T ≤ C)
    (lam : ℝ) {L : ℂ}
    (hmean : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      F t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      F t * m t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop (𝓝 L) := by
  have herror := tendsto_fourierMean_of_meanSquare_zero ((hF.mul hm).sub hF)
    (tendsto_multiplier_error_meanSquare hF hm hlim hbound) lam
  have hsum := herror.add hmean
  simp only [zero_add] at hsum
  apply hsum.congr'
  apply Eventually.of_forall
  intro T
  have hi₁ : IntervalIntegrable (fun t : ℝ =>
      (F t * m t - F t) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) volume 0 T :=
    ((((hF.mul hm).sub hF).mul (by fun_prop))).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t : ℝ =>
      F t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) volume 0 T :=
    (hF.mul (by fun_prop)).intervalIntegrable _ _
  change (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T,
      (F t * m t - F t) * Complex.exp ((lam : ℂ) * I * (t : ℂ))) +
    (T : ℂ)⁻¹ * (∫ t in (0 : ℝ)..T, F t * Complex.exp ((lam : ℂ) * I * (t : ℂ))) =
    (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, F t * m t * Complex.exp ((lam : ℂ) * I * (t : ℂ))
  rw [← mul_add, ← intervalIntegral.integral_add hi₁ hi₂]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- The literal zeta function multiplied by the monic symmetric relocation factor. -/
def relocatedZeta (ρ : ℂ) (γ₁ γ₂ : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * zeroRelocationFactor ρ γ₁ γ₂ s

theorem continuous_zeroRelocationFactor_vertical (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : σ ≠ 1 / 2) :
    Continuous (fun t : ℝ => zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (differentiableAt_zeroRelocationFactor ρ γ₁ γ₂ (by simpa using hσ)).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) (by fun_prop)

/-- Carlson's theorem and absolute convergence give bounded square means off the pole line. -/
theorem eventually_zeta_squareMean_bounded {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T ≤ C := by
  rcases lt_or_gt_of_ne hσ1 with hlt | hgt
  · exact ⟨_, ((RHTower.carlson_zeta_meanSquare hσ hlt).eventually_lt_const
      (lt_add_one (RHTower.zetaCoefficientTailMass 0 σ))).mono fun _ h => h.le⟩
  · obtain ⟨C, hC⟩ := GaloisForLFunctions.exists_bound_of_isBohrAlmostPeriodic
      (continuous_riemannZeta_vertical hgt) (isBohrAlmostPeriodic_riemannZeta_vertical hgt)
    refine ⟨C ^ 2, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hb := intervalIntegral.integral_mono_on (μ := volume) hT.le
      (((continuous_riemannZeta_vertical hgt).norm.pow 2).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun t _ => pow_le_pow_left₀ (norm_nonneg _) (hC t) 2)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hb
    exact (div_le_div_of_nonneg_right hb hT.le).trans_eq
      (mul_div_cancel_left₀ (C ^ 2) hT.ne')

/-- Relocating finitely many zeros changes no square-mean class above the critical line. -/
theorem relocatedZeta_error_meanSquare (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≠ 1) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
      ‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := eventually_zeta_squareMean_bounded hσ hσ1
  exact tendsto_multiplier_error_meanSquare (RHTower.continuous_riemannZeta_vertical_line hσ1)
    (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne')
    (tendsto_zeroRelocationFactor_vertical_atTop ρ γ₁ γ₂ σ) hC

/-- The relocated function has exactly the same Carlson square mean in the strip. -/
theorem relocatedZeta_meanSquare (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
      ‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T)
      atTop (𝓝 (RHTower.zetaCoefficientTailMass 0 σ)) :=
  tendsto_multiplier_meanSquare (RHTower.continuous_riemannZeta_vertical_line hσ1.ne)
    (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne')
    (tendsto_zeroRelocationFactor_vertical_atTop ρ γ₁ γ₂ σ)
    (RHTower.carlson_zeta_meanSquare hσ hσ1)

/-- Every Fourier mean of the relocation error vanishes, including in absolute convergence. -/
theorem relocatedZeta_error_fourierMean (ρ : ℂ) (γ₁ γ₂ lam : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≠ 1) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      (relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)) *
          Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop (𝓝 0) :=
  tendsto_fourierMean_of_meanSquare_zero
    (((RHTower.continuous_riemannZeta_vertical_line hσ1).mul
      (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne')).sub
        (RHTower.continuous_riemannZeta_vertical_line hσ1))
    (relocatedZeta_error_meanSquare ρ γ₁ γ₂ hσ hσ1) lam

/-- The exact Dirichlet frequencies and coefficients survive finite rational relocation. -/
theorem relocatedZeta_fourierMean_log (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) *
        Complex.exp ((Real.log (n : ℝ) : ℂ) * I * (t : ℂ)))
      atTop (𝓝 (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := eventually_zeta_squareMean_bounded hσ hσ1.ne
  exact tendsto_multiplier_fourierMean (RHTower.continuous_riemannZeta_vertical_line hσ1.ne)
    (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne')
    (tendsto_zeroRelocationFactor_vertical_atTop ρ γ₁ γ₂ σ) hC (Real.log n)
    (RHTower.tendsto_zeta_line_mul_char_average_log hσ hσ1 hn)

/-- Relocation creates no additional mean frequencies in the strip. -/
theorem relocatedZeta_fourierMean_off_spectrum (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) {lam : ℝ}
    (hlam : ∀ n : ℕ, 1 ≤ n → lam ≠ Real.log (n : ℝ)) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T,
      relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) *
        Complex.exp ((lam : ℂ) * I * (t : ℂ))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := eventually_zeta_squareMean_bounded hσ hσ1.ne
  exact tendsto_multiplier_fourierMean (RHTower.continuous_riemannZeta_vertical_line hσ1.ne)
    (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne')
    (tendsto_zeroRelocationFactor_vertical_atTop ρ γ₁ γ₂ σ) hC lam
    (RHTower.tendsto_zeta_line_mul_char_average_of_forall_ne hσ hσ1 hlam)

/-- Identical mean-square data coexist with failure of every exact Dirichlet-series realization. -/
theorem zeroRelocation_meanInvisible_but_not_dirichlet {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (γ₁ γ₂ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T,
      ‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I) -
        riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) / T) atTop (𝓝 0) ∧
    ¬ _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) ∧
    (∀ a : ℕ → ℂ, LSeriesSummable a (σ : ℂ) →
      ¬ ∀ t : ℝ, LSeries a ((σ : ℂ) + (t : ℂ) * I) =
        relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ) * I)) :=
  ⟨relocatedZeta_error_meanSquare ρ γ₁ γ₂ (by linarith only [hσ]) hσ.ne',
    (zeroRelocation_destroys_vertical_bohr_and_LSeries hρ γ₁ γ₂ hσ).2⟩


end GaloisForLFunctions.ArithmeticPositiveDuality
