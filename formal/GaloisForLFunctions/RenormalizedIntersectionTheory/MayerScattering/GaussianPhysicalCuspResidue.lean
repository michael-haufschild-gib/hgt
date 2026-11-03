import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.UniformNormalizedCuspRemainder
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianPhysicalCoreSynthesis

/-!
# Complete Weil energy as a Gaussian physical cusp residue

The uniform linear cusp remainder makes the actual-minus-model square energy
integrable for Gaussian packets of the existing zero coordinates. Each spectral
strip gap is retained in the cross term. Absolutely summable finite-depth
counterterms then leave the reflected coefficient pairing as the mean energy.
Removing damping recovers the complete Weil form; subtraction supplies no sign.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open scoped lp ENNReal ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Gaussian damping of the existing CWS zero coordinates. -/
def gaussianCuspCoefficient (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (s : upperMayerResonances) : ℂ :=
  (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s)

private theorem cusp_gaussian_weight_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (B : ℝ) (N : ℕ) :
    Summable (fun s : upperMayerResonances =>
      ‖gaussianCuspCoefficient ε x s‖ * (1 + s.1.im) ^ N * Real.exp (B * s.1.im)) := by
  have hsum := (upperMayer_gaussian_growth_summable hε B N).mul_left ‖x‖
  refine Summable.of_nonneg_of_le (fun s => by have hy := s.2.1; positivity) (fun s => ?_) hsum
  have hcoef := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s)
  rw [gaussianCuspCoefficient, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hp : 0 ≤ (1 + s.1.im) ^ N := pow_nonneg (by linarith only [s.2.1]) _
  calc
    _ ≤ (Real.exp (-ε * s.1.im ^ 2) * ‖x‖) * (1 + s.1.im) ^ N * Real.exp (B * s.1.im) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le) hp) (Real.exp_pos _).le
    _ = _ := by ring

private theorem cusp_gaussian_coefficient_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Summable (fun s : upperMayerResonances => ‖gaussianCuspCoefficient ε x s‖) := by
  simpa only [pow_zero, zero_mul, Real.exp_zero, mul_one] using cusp_gaussian_weight_summable hε x 0 0

private theorem cusp_log_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ u : ℝ,
      ‖(Real.exp (u / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-u)) -
        Complex.exp ((2 * s.1 - 1 / 2) * (u : ℂ))‖ ≤
      (C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)) * Real.exp (-u / 2) := by
  obtain ⟨C, hC, hb⟩ := mayerCuspNormalizedCore_uniform_remainder_bound
  refine ⟨C, hC, fun s u => ?_⟩
  have hp : ((Real.exp (-u) : ℝ) : ℂ) ^ (1 - 2 * s.1) =
      Complex.exp ((-u : ℂ) * (1 - 2 * s.1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg]
  have he : (Real.exp (u / 2) : ℂ) *
      ((Real.exp (-u) : ℝ) : ℂ) ^ (1 - 2 * s.1) =
      Complex.exp ((2 * s.1 - 1 / 2) * (u : ℂ)) := by
    rw [hp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (u / 2) *
        ((C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left (hb s _ (Real.exp_pos _)) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm (Real.exp (u / 2)), ← Real.exp_add,
        show u / 2 + -u = -u / 2 by ring]

/-- Gaussian synthesis of the charge-normalized physical cores. -/
def gaussianNormalizedCuspCore (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (a : ℝ) : ℂ :=
  ∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s * mayerCuspNormalizedCore s a

/-- Physical logarithmic cusp packet with the critical square-energy weighting. -/
def gaussianCuspLogPacket (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) * gaussianNormalizedCuspCore ε x (Real.exp (-u))

/-- Physical square-energy up to logarithmic cusp depth `T`. -/
def gaussianCuspEnergy (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (T : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..T, ‖gaussianCuspLogPacket ε x u‖ ^ 2

/-- Integrated nonconstant mode of a pair of Gaussian coefficients. -/
def gaussianCuspPairCounterterm (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (T : ℝ)
    (p : upperMayerResonances × upperMayerResonances) : ℂ := by
  classical
  exact if mayerCuspPairExponent p.1 p.2 = 0 then 0 else
    gaussianCuspCoefficient ε x p.1 * conj (gaussianCuspCoefficient ε x p.2) *
      (Complex.exp (mayerCuspPairExponent p.1 p.2 * (T : ℂ)) - 1) /
        mayerCuspPairExponent p.1 p.2

/-- Nonconstant spectral pair modes integrated to depth `T`. -/
def gaussianCuspCounterterm (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (T : ℝ) : ℝ :=
  (∑' p : upperMayerResonances × upperMayerResonances, gaussianCuspPairCounterterm ε x T p).re

private theorem cusp_leading_power_bound (s : upperMayerResonances) {a : ℝ} (ha : 0 < a) :
    ‖(a : ℂ) ^ (1 - 2 * s.1)‖ ≤ max 1 a := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha,
    show (1 - 2 * s.1).re = 1 - 2 * s.1.re by simp]
  by_cases ha1 : 1 ≤ a
  · rw [max_eq_right ha1]
    calc
      _ ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1
        (by linarith only [s.2.2.1])
      _ = a := Real.rpow_one a
  · rw [max_eq_left (le_of_not_ge ha1)]
    exact Real.rpow_le_one ha.le (le_of_not_ge ha1) (by linarith only [s.2.2.2.1])

/-- Every positive physical coordinate admits an absolutely convergent
Gaussian sum of the charge-normalized actual cores. -/
theorem gaussianNormalizedCuspCore_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {a : ℝ} (ha : 0 < a) :
    Summable (fun s : upperMayerResonances =>
      gaussianCuspCoefficient ε x s * mayerCuspNormalizedCore s a) := by
  obtain ⟨C, hC, hb⟩ := mayerCuspNormalizedCore_uniform_remainder_bound
  have h0 := (cusp_gaussian_coefficient_summable hε x).mul_right (max 1 a)
  have h1 := (cusp_gaussian_weight_summable hε x Real.pi 4).mul_right (C * a)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_) (h0.add h1)
  have hc : ‖mayerCuspNormalizedCore s a‖ ≤ max 1 a +
      (C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)) * a := by
    calc
      _ = ‖(a : ℂ) ^ (1 - 2 * s.1) +
          (mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1))‖ := by congr 1; ring
      _ ≤ ‖(a : ℂ) ^ (1 - 2 * s.1)‖ +
          ‖mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (cusp_leading_power_bound s ha) (hb s a ha)
  rw [norm_mul]
  calc
    _ ≤ ‖gaussianCuspCoefficient ε x s‖ * (max 1 a +
        (C * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)) * a) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = _ := by ring

private def cuspLeadingMode (s : upperMayerResonances) (u : ℝ) : ℂ :=
  Complex.exp ((2 * s.1 - 1 / 2) * (u : ℂ))

private def cuspLogError (s : upperMayerResonances) (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-u)) - cuspLeadingMode s u

private theorem cusp_leading_mode_norm (s : upperMayerResonances) (u : ℝ) :
    ‖cuspLeadingMode s u‖ = Real.exp ((2 * s.1.re - 1 / 2) * u) := by
  rw [cuspLeadingMode, Complex.norm_exp]
  congr 1
  simp

private theorem cusp_leading_mode_bound (s : upperMayerResonances) (u : ℝ) :
    ‖cuspLeadingMode s u‖ ≤ Real.exp (|u| / 2) := by
  rw [cusp_leading_mode_norm]
  apply Real.exp_le_exp.mpr
  have he : |2 * s.1.re - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith only [s.2.2.1], by linarith only [s.2.2.2.1]⟩
  calc
    _ ≤ |(2 * s.1.re - 1 / 2) * u| := le_abs_self _
    _ = |2 * s.1.re - 1 / 2| * |u| := abs_mul _ _
    _ ≤ (1 / 2) * |u| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ = _ := by ring

private theorem cusp_leading_series_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) :
    Summable (fun s : upperMayerResonances => gaussianCuspCoefficient ε x s * cuspLeadingMode s u) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    ((cusp_gaussian_coefficient_summable hε x).mul_right (Real.exp (|u| / 2)))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (cusp_leading_mode_bound s u) (norm_nonneg _)

private theorem cusp_integrable_series {F : upperMayerResonances → ℝ → ℝ}
    (hi : ∀ s, IntegrableOn (F s) (Ioi 0))
    (hs : Summable (fun s => ∫ u in Ioi (0 : ℝ), ‖F s u‖)) :
    IntegrableOn (fun u => ∑' s, F s u) (Ioi 0) := by
  letI : Countable upperMayerResonances := upperMayerResonances_countable
  refine ⟨AEStronglyMeasurable.tsum fun s => (hi s).1, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun u => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun s => (hi s).1.enorm)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun s => integral_nonneg (fun u => norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

private def cuspDampedModelBound (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) : ℝ :=
  ∑' s : upperMayerResonances, ‖gaussianCuspCoefficient ε x s‖ *
    Real.exp (-(1 - 2 * s.1.re) * u)

/-- Each retained strip gap costs its reciprocal, controlled by Gaussian height summability. -/
private theorem cusp_damped_model_integrable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) : IntegrableOn (cuspDampedModelBound ε x) (Ioi 0) := by
  let F : upperMayerResonances → ℝ → ℝ := fun s u =>
    ‖gaussianCuspCoefficient ε x s‖ * Real.exp (-(1 - 2 * s.1.re) * u)
  have hg (s : upperMayerResonances) : 0 < 1 - 2 * s.1.re := by linarith only [s.2.2.2.1]
  have hi (s : upperMayerResonances) : IntegrableOn (F s) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hg s)) 0).const_mul _
  have he (s : upperMayerResonances) :
      (∫ u in Ioi (0 : ℝ), ‖F s u‖) =
        ‖gaussianCuspCoefficient ε x s‖ * (1 / (1 - 2 * s.1.re)) := by
    have hn (u : ℝ) : ‖F s u‖ = F s u := Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    simp_rw [hn]
    dsimp only [F]
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (hg s)) 0]
    simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg]
  have hr (s : upperMayerResonances) : 1 / (1 - 2 * s.1.re) ≤ 116 * (1 + s.1.im) := by
    have h := (upperMayerResonance_reciprocal_bound (reflectUpperResonance s)).2
    rw [reflectUpperResonance_coe, riemannMayerReflect_re, riemannMayerReflect_im,
      show 2 * (1 / 2 - s.1.re) = 1 - 2 * s.1.re by ring] at h
    linarith only [h]
  have hw : Summable (fun s : upperMayerResonances =>
      ‖gaussianCuspCoefficient ε x s‖ * (1 + s.1.im)) := by
    simpa only [pow_one, zero_mul, Real.exp_zero, mul_one] using
      cusp_gaussian_weight_summable hε x 0 1
  have hs : Summable (fun s => ∫ u in Ioi (0 : ℝ), ‖F s u‖) := by
    refine Summable.of_nonneg_of_le (fun s => integral_nonneg (fun u => norm_nonneg _))
      (fun s => ?_) (hw.mul_left 116)
    rw [he]
    exact (mul_le_mul_of_nonneg_left (hr s) (norm_nonneg _)).trans_eq (by ring)
  exact cusp_integrable_series hi hs

private def gaussianCuspModel (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) : ℂ :=
  ∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s * cuspLeadingMode s u

private theorem cusp_packet_sub_model {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) :
    gaussianCuspLogPacket ε x u - gaussianCuspModel ε x u =
      ∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s * cuspLogError s u := by
  have ha := (gaussianNormalizedCuspCore_summable hε x (Real.exp_pos (-u))).mul_left
    (Real.exp (u / 2) : ℂ)
  have hm := cusp_leading_series_summable hε x u
  rw [gaussianCuspLogPacket, gaussianNormalizedCuspCore, gaussianCuspModel, ← tsum_mul_left,
    ← ha.tsum_sub hm]
  apply tsum_congr
  intro s
  dsimp only [cuspLogError]
  ring

private theorem cusp_packet_error_bound {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℝ,
      ‖gaussianCuspLogPacket ε x u - gaussianCuspModel ε x u‖ ≤ D * Real.exp (-u / 2) := by
  obtain ⟨C, hC, hb⟩ := cusp_log_remainder_bound
  let W : upperMayerResonances → ℝ := fun s =>
    ‖gaussianCuspCoefficient ε x s‖ * (1 + s.1.im) ^ 4 * Real.exp (Real.pi * s.1.im)
  have hW : Summable W := cusp_gaussian_weight_summable hε x Real.pi 4
  have hW0 (s : upperMayerResonances) : 0 ≤ W s := by
    dsimp only [W]
    positivity
  refine ⟨C * ∑' s, W s, mul_nonneg hC (tsum_nonneg hW0), fun u => ?_⟩
  have hterm (s : upperMayerResonances) :
      ‖gaussianCuspCoefficient ε x s * cuspLogError s u‖ ≤
        (C * W s) * Real.exp (-u / 2) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb s u) (norm_nonneg _)).trans_eq (by dsimp only [W]; ring)
  have hmajor := (hW.mul_left C).mul_right (Real.exp (-u / 2))
  have hs : Summable (fun s : upperMayerResonances =>
      ‖gaussianCuspCoefficient ε x s * cuspLogError s u‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmajor
  rw [cusp_packet_sub_model hε]
  calc
    _ ≤ ∑' s : upperMayerResonances, ‖gaussianCuspCoefficient ε x s * cuspLogError s u‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' s : upperMayerResonances, (C * W s) * Real.exp (-u / 2) :=
      hs.tsum_le_tsum hterm hmajor
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]

private theorem cusp_model_damped_bound {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) :
    ‖gaussianCuspModel ε x u‖ * Real.exp (-u / 2) ≤ cuspDampedModelBound ε x u := by
  have hs := (cusp_leading_series_summable hε x u).norm
  calc
    _ ≤ (∑' s : upperMayerResonances,
        ‖gaussianCuspCoefficient ε x s * cuspLeadingMode s u‖) * Real.exp (-u / 2) :=
      mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hs) (Real.exp_pos _).le
    _ = ∑' s : upperMayerResonances,
        ‖gaussianCuspCoefficient ε x s * cuspLeadingMode s u‖ * Real.exp (-u / 2) :=
      tsum_mul_right.symm
    _ = _ := by
      apply tsum_congr
      intro s
      rw [norm_mul, cusp_leading_mode_norm, mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem measurable_gaussianCuspLogPacket (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Measurable (gaussianCuspLogPacket ε x) := by
  letI : Countable upperMayerResonances := upperMayerResonances_countable
  have hc (s : upperMayerResonances) : Measurable (mayerCuspNormalizedCore s) :=
    (mayerPeriodCore_measurable s.2.1).neg.div_const _
  have hm : Measurable (gaussianNormalizedCuspCore ε x) := by
    apply Measurable.tsum
    intro s
    exact (hc s).const_mul _
  unfold gaussianCuspLogPacket
  fun_prop

private theorem measurable_gaussianCuspModel (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Measurable (gaussianCuspModel ε x) := by
  letI : Countable upperMayerResonances := upperMayerResonances_countable
  apply Measurable.tsum
  intro s
  dsimp only [cuspLeadingMode]
  fun_prop

private theorem cusp_square_difference_bound (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := by
  have hdiff := abs_norm_sub_norm_le a b
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc
      _ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖a - b‖ * (‖a - b‖ + 2 * ‖b‖) :=
      mul_le_mul_of_nonneg_left (by linarith only [htri]) (norm_nonneg _)
    _ = _ := by ring

/-- The cross term uses the damped model sum; a uniform exponential model bound
would discard the individual gaps needed for integrability. -/
private theorem cusp_gaussian_energy_error_integrable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    IntegrableOn (fun u : ℝ => ‖gaussianCuspLogPacket ε x u‖ ^ 2 -
      ‖gaussianCuspModel ε x u‖ ^ 2) (Ioi 0) := by
  obtain ⟨D, hD, hb⟩ := cusp_packet_error_bound hε x
  have hm := (cusp_damped_model_integrable hε x).const_mul (2 * D)
  have he : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  apply (hm.add (he.const_mul (D ^ 2))).mono'
  · exact (((measurable_gaussianCuspLogPacket ε x).norm.pow_const 2).sub
      ((measurable_gaussianCuspModel ε x).norm.pow_const 2)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs]
    have hsquare : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
      rw [sq, ← Real.exp_add, show -u / 2 + -u / 2 = -u by ring]
    calc
      _ ≤ 2 * ‖gaussianCuspModel ε x u‖ *
          ‖gaussianCuspLogPacket ε x u - gaussianCuspModel ε x u‖ +
          ‖gaussianCuspLogPacket ε x u - gaussianCuspModel ε x u‖ ^ 2 :=
        cusp_square_difference_bound _ _
      _ ≤ 2 * ‖gaussianCuspModel ε x u‖ * (D * Real.exp (-u / 2)) +
          (D * Real.exp (-u / 2)) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (hb u) (by positivity))
          (pow_le_pow_left₀ (norm_nonneg _) (hb u) 2)
      _ = (2 * D) * (‖gaussianCuspModel ε x u‖ * Real.exp (-u / 2)) +
          D ^ 2 * Real.exp (-u) := by rw [mul_pow, hsquare]; ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (cusp_model_damped_bound hε x u) (by positivity)) le_rfl

#print axioms gaussianNormalizedCuspCore_summable

private def cuspPairMode (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (p : upperMayerResonances × upperMayerResonances) (u : ℝ) : ℂ :=
  gaussianCuspCoefficient ε x p.1 * conj (gaussianCuspCoefficient ε x p.2) *
    Complex.exp (mayerCuspPairExponent p.1 p.2 * (u : ℂ))

private def cuspPairMass (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (p : upperMayerResonances × upperMayerResonances) : ℝ :=
  ‖gaussianCuspCoefficient ε x p.1‖ * ‖gaussianCuspCoefficient ε x p.2‖

private theorem cusp_pair_mass_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) : Summable (cuspPairMass ε x) :=
  (cusp_gaussian_coefficient_summable hε x).mul_of_nonneg
    (cusp_gaussian_coefficient_summable hε x) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

private theorem cusp_pair_mode_bound (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (p : upperMayerResonances × upperMayerResonances) {u T : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    ‖cuspPairMode ε x p u‖ ≤ cuspPairMass ε x p * Real.exp T := by
  have hr : (mayerCuspPairExponent p.1 p.2).re ≤ 1 := by
    simp only [mayerCuspPairExponent, Complex.sub_re, Complex.add_re, Complex.one_re]
    norm_num
    linarith only [p.1.2.2.2.1, p.2.2.2.2.1]
  have he : (mayerCuspPairExponent p.1 p.2 * (u : ℂ)).re ≤ T := by
    have h := mul_le_mul_of_nonneg_right hr hu
    rw [one_mul] at h
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h.trans huT
  rw [cuspPairMode, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem cusp_model_square_series {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℝ) :
    ((‖gaussianCuspModel ε x u‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : upperMayerResonances × upperMayerResonances, cuspPairMode ε x p u := by
  have hs := (cusp_leading_series_summable hε x u).norm
  have hc : Summable (fun s : upperMayerResonances =>
      ‖conj (gaussianCuspCoefficient ε x s * cuspLeadingMode s u)‖) := by
    simpa only [Complex.norm_conj] using hs
  rw [Complex.sq_norm, ← Complex.mul_conj, gaussianCuspModel, Complex.conj_tsum,
    tsum_mul_tsum_of_summable_norm hs hc]
  apply tsum_congr
  intro p
  rw [map_mul, cuspLeadingMode, cuspLeadingMode, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have he : mayerCuspPairExponent p.1 p.2 * (u : ℂ) =
      (2 * p.1.1 - 1 / 2) * (u : ℂ) + conj (2 * p.2.1 - 1 / 2) * (u : ℂ) := by
    simp only [mayerCuspPairExponent, map_sub, map_mul, map_div₀, map_ofNat, map_one]
    ring
  rw [cuspPairMode, he, Complex.exp_add]
  ring

/-- Finite-depth integration is dominated before dividing by a pair exponent,
so no separation between spectral parameters is needed. -/
private theorem cusp_pair_integral_norm_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {T : ℝ} (hT : 0 ≤ T) :
    Summable (fun p : upperMayerResonances × upperMayerResonances =>
      ∫ u in Ioc (0 : ℝ) T, ‖cuspPairMode ε x p u‖) := by
  have hi (p : upperMayerResonances × upperMayerResonances) :
      IntegrableOn (cuspPairMode ε x p) (Ioc 0 T) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    have hc : Continuous (cuspPairMode ε x p) := by unfold cuspPairMode; fun_prop
    exact hc.intervalIntegrable _ _
  have hc (p : upperMayerResonances × upperMayerResonances) :
      IntegrableOn (fun _ : ℝ => cuspPairMass ε x p * Real.exp T) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp intervalIntegrable_const
  refine Summable.of_nonneg_of_le (fun p => integral_nonneg (fun u => norm_nonneg _))
    (fun p => ?_) (((cusp_pair_mass_summable hε x).mul_right (Real.exp T)).mul_left
      (volume.real (Ioc (0 : ℝ) T)))
  calc
    _ ≤ ∫ _u in Ioc (0 : ℝ) T, cuspPairMass ε x p * Real.exp T :=
      setIntegral_mono_on (hi p).norm (hc p) measurableSet_Ioc
        (fun u hu => cusp_pair_mode_bound ε x p hu.1.le hu.2)
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

private theorem cusp_pair_integral_interchange {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T,
      ∑' p : upperMayerResonances × upperMayerResonances, cuspPairMode ε x p u) =
      ∑' p : upperMayerResonances × upperMayerResonances, ∫ u in (0 : ℝ)..T, cuspPairMode ε x p u := by
  letI : Countable upperMayerResonances := upperMayerResonances_countable
  have hi (p : upperMayerResonances × upperMayerResonances) :
      IntegrableOn (cuspPairMode ε x p) (Ioc 0 T) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    have hc : Continuous (cuspPairMode ε x p) := by unfold cuspPairMode; fun_prop
    exact hc.intervalIntegrable _ _
  simpa only [intervalIntegral.integral_of_le hT] using
    (integral_tsum_of_summable_integral_norm hi (cusp_pair_integral_norm_summable hε x hT)).symm

private theorem cusp_model_intervalIntegrable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => ‖gaussianCuspModel ε x u‖ ^ 2) volume 0 T := by
  let K : ℝ := (∑' s : upperMayerResonances, ‖gaussianCuspCoefficient ε x s‖) * Real.exp (T / 2)
  have hK : 0 ≤ K := mul_nonneg (tsum_nonneg fun _ => norm_nonneg _) (Real.exp_pos _).le
  have hc : IntegrableOn (fun _ : ℝ => K ^ 2) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp intervalIntegrable_const
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  apply hc.mono' ((measurable_gaussianCuspModel ε x).norm.pow_const 2).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  calc
    _ ≤ ∑' s : upperMayerResonances, ‖gaussianCuspCoefficient ε x s * cuspLeadingMode s u‖ :=
      norm_tsum_le_tsum_norm (cusp_leading_series_summable hε x u).norm
    _ ≤ ∑' s : upperMayerResonances, ‖gaussianCuspCoefficient ε x s‖ * Real.exp (T / 2) := by
      apply Summable.tsum_le_tsum _ (cusp_leading_series_summable hε x u).norm
        ((cusp_gaussian_coefficient_summable hε x).mul_right _)
      intro s
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (cusp_leading_mode_bound s u).trans
      apply Real.exp_le_exp.mpr
      rw [abs_of_pos hu.1]
      exact div_le_div_of_nonneg_right hu.2 (by norm_num)
    _ = K := tsum_mul_right

private def cuspPairZeroMode (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (p : upperMayerResonances × upperMayerResonances) : ℂ := by
  classical
  exact if mayerCuspPairExponent p.1 p.2 = 0 then
    gaussianCuspCoefficient ε x p.1 * conj (gaussianCuspCoefficient ε x p.2) else 0

private theorem cusp_pair_zero_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) : Summable (cuspPairZeroMode ε x) := by
  classical
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    (cusp_pair_mass_summable hε x)
  unfold cuspPairZeroMode cuspPairMass
  split_ifs
  · rw [norm_mul, Complex.norm_conj]
  · rw [norm_zero]
    positivity

private theorem cusp_pair_zero_reflect_iff (s t : upperMayerResonances) :
    mayerCuspPairExponent s t = 0 ↔ t = reflectUpperResonance s := by
  constructor
  · intro h
    apply Subtype.ext
    change t.1 = 1 / 2 - conj s.1
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num [mayerCuspPairExponent, Complex.mul_re] at hr
    norm_num [mayerCuspPairExponent, Complex.mul_im] at hi
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.conj_re]
      norm_num
      linarith only [hr]
    · simp only [Complex.sub_im, Complex.conj_im]
      norm_num
      linarith only [hi]
  · rintro rfl
    change 2 * s.1 + 2 * conj (1 / 2 - conj s.1) - 1 = 0
    simp only [map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
    ring

private theorem cusp_zero_modes_sum {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    (∑' p : upperMayerResonances × upperMayerResonances, cuspPairZeroMode ε x p) =
      ∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s *
        conj (gaussianCuspCoefficient ε x (reflectUpperResonance s)) := by
  classical
  rw [(cusp_pair_zero_summable hε x).tsum_prod]
  apply tsum_congr
  intro s
  simp only [cuspPairZeroMode, cusp_pair_zero_reflect_iff]
  exact tsum_eq_single (reflectUpperResonance s) (fun t ht => if_neg ht) |>.trans (if_pos rfl)

private theorem cusp_pair_mode_integral (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ))
    (T : ℝ) (p : upperMayerResonances × upperMayerResonances) :
    (∫ u in (0 : ℝ)..T, cuspPairMode ε x p u) =
      (T : ℂ) * cuspPairZeroMode ε x p + gaussianCuspPairCounterterm ε x T p := by
  classical
  unfold cuspPairMode
  rw [intervalIntegral.integral_const_mul]
  by_cases h : mayerCuspPairExponent p.1 p.2 = 0
  · simp [h, cuspPairZeroMode, gaussianCuspPairCounterterm, mul_comm]
  · rw [integral_exp_mul_complex h]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, cuspPairZeroMode,
      gaussianCuspPairCounterterm, if_neg h, mul_zero, zero_add]
    ring

/-- The nonconstant pair counterterms are absolutely summable at every finite cusp depth. -/
theorem gaussianCuspCounterterm_summable {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {T : ℝ} (hT : 0 ≤ T) :
    Summable (gaussianCuspPairCounterterm ε x T) := by
  classical
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    (cusp_pair_integral_norm_summable hε x hT)
  by_cases h : mayerCuspPairExponent p.1 p.2 = 0
  · simp only [gaussianCuspPairCounterterm, if_pos h, norm_zero]
    exact integral_nonneg fun _ => norm_nonneg _
  · have he := cusp_pair_mode_integral ε x T p
    simp only [cuspPairZeroMode, if_neg h, mul_zero, zero_add] at he
    rw [← he, intervalIntegral.integral_of_le hT]
    exact norm_integral_le_integral_norm _

private theorem cusp_gaussian_model_integral {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T, ‖gaussianCuspModel ε x u‖ ^ 2) =
      T * (∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s *
        conj (gaussianCuspCoefficient ε x (reflectUpperResonance s))).re +
      gaussianCuspCounterterm ε x T := by
  have hzero := (cusp_pair_zero_summable hε x).mul_left (T : ℂ)
  have hct := gaussianCuspCounterterm_summable hε x hT
  have hc : ((∫ u in (0 : ℝ)..T, ‖gaussianCuspModel ε x u‖ ^ 2 : ℝ) : ℂ) =
      (T : ℂ) * (∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s *
        conj (gaussianCuspCoefficient ε x (reflectUpperResonance s))) +
      ∑' p : upperMayerResonances × upperMayerResonances, gaussianCuspPairCounterterm ε x T p := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [cusp_model_square_series hε]
    rw [cusp_pair_integral_interchange hε x hT]
    simp_rw [cusp_pair_mode_integral]
    rw [hzero.tsum_add hct, tsum_mul_left, cusp_zero_modes_sum hε]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, gaussianCuspCounterterm, gaussianCuspPairCounterterm] using hr

/-- The renormalized mean square-energy of the actual Gaussian cusp packet
is its damped PM reflection pairing. -/
theorem gaussianCuspEnergy_renormalized_mean {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    Tendsto (fun T : ℝ => (gaussianCuspEnergy ε x T - gaussianCuspCounterterm ε x T) / T)
      atTop (𝓝 (∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s *
        conj (gaussianCuspCoefficient ε x (reflectUpperResonance s))).re) := by
  let Q : ℝ := (∑' s : upperMayerResonances, gaussianCuspCoefficient ε x s *
    conj (gaussianCuspCoefficient ε x (reflectUpperResonance s))).re
  have hi := cusp_gaussian_energy_error_integrable hε x
  have ht := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hzero : Tendsto (fun T : ℝ =>
      (∫ u in (0 : ℝ)..T, ‖gaussianCuspLogPacket ε x u‖ ^ 2 - ‖gaussianCuspModel ε x u‖ ^ 2) / T)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, id_eq] using ht.mul tendsto_inv_atTop_zero
  have hlim : Tendsto (fun T : ℝ =>
      (∫ u in (0 : ℝ)..T, ‖gaussianCuspLogPacket ε x u‖ ^ 2 - ‖gaussianCuspModel ε x u‖ ^ 2) / T + Q)
      atTop (𝓝 Q) := by simpa only [zero_add] using hzero.add_const Q
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have he : IntervalIntegrable (fun u : ℝ =>
      ‖gaussianCuspLogPacket ε x u‖ ^ 2 - ‖gaussianCuspModel ε x u‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hm := cusp_model_intervalIntegrable hε x hT.le
  have hp : IntervalIntegrable (fun u : ℝ => ‖gaussianCuspLogPacket ε x u‖ ^ 2) volume 0 T := by
    simpa only [sub_add_cancel] using he.add hm
  rw [intervalIntegral.integral_sub hp hm, cusp_gaussian_model_integral hε x hT.le]
  change (_ - (T * Q + gaussianCuspCounterterm ε x T)) / T + Q = _
  dsimp only [gaussianCuspEnergy]
  field_simp [hT.ne']
  ring

/-- Twice the physical cusp residue equals the existing Gaussian-damped
complete Weil energy of the original real window test. -/
theorem gaussianWindowCuspEnergy_renormalized_mean {A : ℝ} {ε : ℝ} (hε : 0 < ε)
    (H : windowTests A) :
    Tendsto (fun T : ℝ =>
      2 * (gaussianCuspEnergy ε (windowZeroMap A H) T -
        gaussianCuspCounterterm ε (windowZeroMap A H) T) / T)
      atTop (𝓝 (gaussianWindowWeilEnergy ε H)) := by
  have hp : (∑' s : upperMayerResonances,
      gaussianCuspCoefficient ε (windowZeroMap A H) s *
        conj (gaussianCuspCoefficient ε (windowZeroMap A H) (reflectUpperResonance s))) =
      ∑' s : upperMayerResonances, (Real.exp (-2 * ε * s.1.im ^ 2) : ℂ) *
        zetaZeroConfig.Wsummand (cx H) (cx H) (2 * s.1) := by
    apply tsum_congr
    intro s
    exact gaussian_window_reflection_product ε H s
  have h := (gaussianCuspEnergy_renormalized_mean hε (windowZeroMap A H)).const_mul 2
  rw [hp] at h
  simpa only [gaussianWindowWeilEnergy, mul_div_assoc] using h

/-- Removing Gaussian damping after taking the renormalized physical cusp
mean recovers the complete Weil window form, with every zero multiplicity. -/
theorem tendsto_physicalCuspMean_weilQuad {A : ℝ} (H : windowTests A) :
    Tendsto (fun ε : ℝ => Filter.limUnder atTop (fun T : ℝ =>
      2 * (gaussianCuspEnergy ε (windowZeroMap A H) T -
        gaussianCuspCounterterm ε (windowZeroMap A H) T) / T))
      (𝓝[>] 0) (𝓝 (weilQuad H)) := by
  have hlim := (tendsto_gaussianWindowWeilEnergy H).mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ Ici 0 from fun ε h => (show (0 : ℝ) < ε from h).le))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (gaussianWindowCuspEnergy_renormalized_mean hε H).limUnder_eq.symm

#print axioms gaussianCuspCounterterm_summable
#print axioms gaussianCuspEnergy_renormalized_mean
#print axioms gaussianWindowCuspEnergy_renormalized_mean
#print axioms tendsto_physicalCuspMean_weilQuad

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
