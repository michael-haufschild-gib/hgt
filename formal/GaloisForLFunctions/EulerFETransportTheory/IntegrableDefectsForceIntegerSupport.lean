import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsVanishInTheUnitGap

/-!
# The origin tent forces integer support

The real boundary defect vanishes in the unit gap. Its integrable square-root majorant
therefore makes the origin Fejér defect tend to zero. Positivity of the sinc-squared
Fourier weight then forces every generalized integer norm onto the ordinary integer lattice.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The radial Fejér defect has an integrable majorant on the positive unit interval. -/
theorem norm_fejerDefectKernel_le_on_unit_interval {g : ℝ → ℂ} (hg : Integrable g)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (hs1 : s ≤ 1) :
    ‖fejerDefectKernel g ε s‖ ≤
      (3 / Real.pi * ∫ t, ‖g t‖) * s ^ (-(1 / 2 : ℝ)) := by
  let z : ℂ := (ε : ℂ) + (s : ℂ) * I
  let C : ℝ := 3 / (2 * Real.pi) * ∫ t, ‖g t‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hz : 0 < z.re := by simpa only [z, Complex.add_re, Complex.ofReal_re,
    Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero] using hε
  have hz0 : z ≠ 0 := fun he => by simp [he] at hz
  have hsn : s ≤ ‖z‖ := by
    have hb := Complex.abs_im_le_norm z
    simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add, abs_of_pos hs] using hb
  have hj : ‖defectLaplace g z‖ ≤ C * s ^ (-(1 / 2 : ℝ)) := by
    rw [← closedDefectLaplace_eq hz]
    exact (norm_closedDefectLaplace_le hg hz.le hz0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs hsn (by norm_num)) hC)
  have hw : 0 ≤ 2 * (1 - |s|) := by
    rw [abs_of_pos hs]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr hs1)
  have hw2 : 2 * (1 - |s|) ≤ 2 := by linarith only [abs_nonneg s]
  rw [fejerDefectKernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  calc 2 * (1 - |s|) * |(defectLaplace g z).re| ≤ 2 * ‖defectLaplace g z‖ :=
      mul_le_mul hw2 (Complex.abs_re_le_norm _) (abs_nonneg _) (by norm_num)
    _ ≤ 2 * (C * s ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hj (by norm_num)
    _ = _ := by dsimp only [C]; ring

/-- Unit-gap vanishing removes the entire origin Fejér defect in the radial limit. -/
theorem beurling_tendsto_integral_fejerDefectKernel
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, fejerDefectKernel g ε s) (𝓝[>] 0) (𝓝 0) := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hhalf : Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..1, fejerDefectKernel g ε s)
      (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..1, fejerDefectKernel g ε s)
        (𝓝[>] 0) (𝓝 (∫ _s in (0 : ℝ)..1, (0 : ℝ))) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun s : ℝ => (3 / Real.pi * ∫ t, ‖g t‖) * s ^ (-(1 / 2 : ℝ)))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (continuous_fejerDefectKernel hgm.aestronglyMeasurable hgb hε).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        apply Eventually.of_forall
        intro s hs
        rw [uIoc_of_le zero_le_one] at hs
        exact norm_fejerDefectKernel_le_on_unit_interval hgi hε hs.1 hs.2
      · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
      · apply Eventually.of_forall
        intro s hs
        rw [uIoc_of_le zero_le_one] at hs
        have hv : 2 * (1 - |s|) * (defectBoundary g s).re = 0 := by
          rcases lt_or_eq_of_le hs.2 with hlt | heq
          · rw [beurling_defectBoundary_re_eq_zero_on_unit_gap B hBsum hgm hgb hgi hθ hs.1 hlt,
              mul_zero]
          · simp [heq]
        have hl := ((Complex.continuous_re.tendsto _).comp
          (tendsto_defectLaplace_boundary hgi hs.1.ne')).const_mul (2 * (1 - |s|))
        simpa only [fejerDefectKernel, Function.comp_apply, hv] using hl
    simpa only [intervalIntegral.integral_zero] using ht
  have hfold {ε : ℝ} (hε : 0 < ε) :
      (∫ s in (-1 : ℝ)..1, fejerDefectKernel g ε s) =
        2 * ∫ s in (0 : ℝ)..1, fejerDefectKernel g ε s := by
    rw [intervalIntegral_neg_one_one_eq (continuous_fejerDefectKernel hgm.aestronglyMeasurable hgb hε),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [fejerDefectKernel, abs_neg,
      defectLaplace_re_neg_of_theta_defect hsupp hmom hgm hgb hθ hε]
    ring
  have ht := hhalf.const_mul 2
  rw [mul_zero] at ht
  exact ht.congr' (eventually_nhdsWithin_of_forall fun ε hε => (hfold hε).symm)

/-- The unit gap makes the Poisson side of the origin pairing vanish. -/
theorem tendsto_integral_fejerSeriesKernel_zero {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    Tendsto (fun ε : ℝ => ∫ u : ℝ, (∫ s in (-1 : ℝ)..1, fejerSeriesKernel ε s u) ∂ν)
      (𝓝[>] 0) (𝓝 0) := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  have ht : Tendsto (fun ε : ℝ =>
      (24 * Real.sqrt ε / Real.pi) * ∫ u : ℝ, 1 / u ^ 2 ∂ν) (𝓝[>] 0) (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Real.sqrt_zero, mul_zero, zero_div, zero_mul] using
      ((hs.const_mul 24).div_const Real.pi).mul_const (∫ u : ℝ, 1 / u ^ 2 ∂ν)
  refine squeeze_zero' (hev.mono fun ε hε => ?_) (hev.mono fun ε hε => ?_) ht
  · apply integral_nonneg
    intro u
    exact intervalIntegral.integral_nonneg (by norm_num) fun s hs =>
      fejerSeriesKernel_nonneg hε.1 (abs_le.mpr hs) u
  · have hi : Integrable (fun u : ℝ => ∫ s in (-1 : ℝ)..1, fejerSeriesKernel ε s u) ν := by
      refine (integrable_fejerSeriesKernel hsupp hmom hε.1 hε.2.le).integral_prod_right.congr
        (Eventually.of_forall fun u => ?_)
      change (∫ s in uIoc (-1 : ℝ) 1, fejerSeriesKernel ε s u) =
        ∫ s in (-1 : ℝ)..1, fejerSeriesKernel ε s u
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← integral_const_mul]
    apply integral_mono_ae hi (hmom.const_mul _)
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    exact intervalIntegral_fejerSeriesKernel_le hu hε.1 hε.2.le

/-- The Fourier weight of the origin tent has zero mass for every integrable Beurling defect. -/
theorem beurling_integral_sinc_sq_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂beurlingSystemIntegerMeasure B = 0 := by
  let ν := beurlingSystemIntegerMeasure B
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp
    (integrable_rpow_beurlingSystemIntegerMeasure B hBsum)
  have hD (ε : ℝ) :
      (∫ u : ℝ, (∫ s in (-1 : ℝ)..1, tentDualKernel 1 0 ε s u) ∂ν) =
        ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
          (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    rw [intervalIntegral_tentDualKernel zero_lt_one (zero_lt_one.trans_le hu)]
    simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight]
  have hdual := (tendsto_integral_tentDualKernel hsupp hmom (h := 1) zero_lt_one 0).const_mul 2
  simp only [one_mul, mul_zero, Real.cos_zero, tentFourierWeight] at hdual
  have hdual' := hdual.congr' (Eventually.of_forall fun ε => congrArg (fun r : ℝ => 2 * r) (hD ε))
  have hright := ((tendsto_integral_fejerSeriesKernel_zero hsupp hmom).sub
    (tendsto_integral_fejerPolarKernel_neg (β : ℂ))).sub
      (beurling_tendsto_integral_fejerDefectKernel B hBsum hgm hgb hgi hθ)
  simp only [sub_zero] at hright
  have hzero : Tendsto (fun ε : ℝ => 2 * ∫ u : ℝ,
      Real.exp (-2 * Real.pi * u * ε) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν)
      (𝓝[>] 0) (𝓝 0) := by
    apply hright.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact (fejer_pairing_identity_of_theta_defect hsupp hmom hgm hgb hθ hε.1 hε.2.le).symm
  have he := tendsto_nhds_unique hdual' hzero
  linarith only [he]

/-- Arbitrary integrable theta defects force natural-number norms, without a lattice premise. -/
theorem beurling_intNorm_nat_of_integrable_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ x : B.Integer, ∃ k : ℕ, B.intNorm x = k := by
  have hsum : Summable fun i : B.Integer =>
      (Real.sin (Real.pi * B.intNorm i) / (Real.pi * B.intNorm i)) ^ 2 := by
    refine (summable_norm_tentFourierCoefficient B.intNorm_pos (summable_beurling_inv_sq B hBsum)
      (h := 1) zero_lt_one).congr fun i => ?_
    simp only [tentFourierWeight, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (sq_nonneg _)
  have hz := beurling_integral_sinc_sq_eq_zero B hBsum hgm hgb hgi hθ
  rw [integral_beurlingSystemIntegerMeasure_eq_tsum] at hz
  intro x
  have ht := hsum.le_tsum x (fun _ _ => sq_nonneg _)
  rw [hz] at ht
  have hr := abs_sub_round_le_of_sinc_sq_le (B.one_le_intNorm x) ht
  simp only [mul_zero, Real.sqrt_zero, zero_mul] at hr
  have he : B.intNorm x = (round (B.intNorm x) : ℝ) :=
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hr (abs_nonneg _)))
  have hnonneg : (0 : ℤ) ≤ round (B.intNorm x) := by
    have hreal : (0 : ℝ) ≤ (round (B.intNorm x) : ℝ) := he ▸ (B.intNorm_pos x).le
    exact_mod_cast hreal
  refine ⟨(round (B.intNorm x)).toNat, ?_⟩
  have hm := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hnonneg)
  push_cast at hm
  exact he.trans hm.symm

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_integral_sinc_sq_eq_zero
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_intNorm_nat_of_integrable_theta_defect
