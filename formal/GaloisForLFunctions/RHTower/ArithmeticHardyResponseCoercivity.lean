import GaloisForLFunctions.RHTower.ArithmeticCriticalResponseDerivative
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# Hardy phase coercivity of the actual arithmetic response

The literal EDQ critical response is the conjugate derivative of
`Z(s)=zeta(s)/(s*(s+1))`. Its actual Hardy rotation has real component
`-beta*hardyZ` and imaginary component the negative corrected Hardy derivative.
The normalization correction has positive real part, so `beta` tends to positive
infinity. The exact norm identity controls both components and classifies all
sufficiently high response zeros as simultaneous zeta and derivative zeros.

Both off-line zero disks retain the full quadratic target correction in these
coordinates. No simplicity theorem, signed arithmetic separation, or RH is asserted.
-/

set_option autoImplicit false
noncomputable section
open Complex Real Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The denominator of the fixed normalized zeta function on the critical line. -/
def hardyResponseDenominator (t : ℝ) : ℂ :=
  criticalResponsePoint t * (criticalResponsePoint t + 1)

/-- Logarithmic derivative of the fixed normalization denominator. -/
def hardyResponseNormalizationRate (t : ℝ) : ℂ :=
  1 / criticalResponsePoint t + 1 / (criticalResponsePoint t + 1)

/-- The actual Hardy phase rate including the normalization correction. -/
def hardyResponseCoercivity (t : ℝ) : ℝ :=
  gammaHardyPhaseRate t + (hardyResponseNormalizationRate t).re

/-- The Hardy derivative with the exact imaginary normalization correction. -/
def hardyResponseSlope (t : ℝ) : ℝ :=
  deriv hardyZ t + (hardyResponseNormalizationRate t).im * hardyZ t

/-- The arithmetic critical point is the Hardy critical-line point. -/
theorem criticalResponsePoint_eq_linePt (t : ℝ) : criticalResponsePoint t = linePt t := by
  norm_num [criticalResponsePoint, linePt]

/-- The normalization denominator never vanishes at a real height. -/
theorem hardyResponseDenominator_ne_zero (t : ℝ) : hardyResponseDenominator t ≠ 0 := by
  have hc : criticalResponsePoint t ∈ minimumStrip := by
    norm_num [criticalResponsePoint, minimumStrip]
  have hd := unitPhaseStrip_denominators hc
  exact mul_ne_zero hd.1 hd.2.2

/-- The real normalization correction is strictly positive at every height. -/
theorem hardyResponseNormalizationRate_re_pos (t : ℝ) :
    0 < (hardyResponseNormalizationRate t).re := by
  have h₀ : (0:ℝ) < Complex.normSq (criticalResponsePoint t) := by
    norm_num [Complex.normSq_apply, criticalResponsePoint]
    nlinarith [sq_nonneg t]
  have h₁ : (0:ℝ) < Complex.normSq (criticalResponsePoint t + 1) := by
    norm_num [Complex.normSq_apply, criticalResponsePoint]
    nlinarith [sq_nonneg t]
  simp only [hardyResponseNormalizationRate, one_div, Complex.add_re, Complex.inv_re]
  have hc : (criticalResponsePoint t).re = 1/2 := by simp [criticalResponsePoint]
  rw [hc, Complex.one_re]
  positivity

/-- The actual normalization preserves the Gamma phase rate's divergence to positive infinity. -/
theorem hardyResponseCoercivity_tendsto_atTop :
    Tendsto hardyResponseCoercivity atTop atTop := by
  apply tendsto_atTop_mono (f := gammaHardyPhaseRate) _ gammaHardyPhaseRate_tendsto_atTop
  intro t
  exact le_add_of_nonneg_right (le_of_lt (hardyResponseNormalizationRate_re_pos t))

/-- The actual Hardy response is coercive at all sufficiently large positive heights. -/
theorem eventually_hardyResponseCoercivity_pos :
    ∀ᶠ t : ℝ in atTop, 0 < hardyResponseCoercivity t := by
  filter_upwards [eventually_gammaHardyPhaseRate_pos] with t ht
  exact add_pos ht (hardyResponseNormalizationRate_re_pos t)

/-- Exact derivative of normalized zeta with the normalization rate retained. -/
theorem hardyResponseDenominator_mul_derivative (t : ℝ) :
    hardyResponseDenominator t * deriv normalizedMinimumZeta (criticalResponsePoint t) =
      deriv riemannZeta (criticalResponsePoint t) -
        hardyResponseNormalizationRate t * riemannZeta (criticalResponsePoint t) := by
  let c := criticalResponsePoint t
  have hc : c ∈ minimumStrip := by norm_num [c, criticalResponsePoint, minimumStrip]
  have hd := unitPhaseStrip_denominators hc
  have hq := ((unitPhaseZeta_analytic c hc).differentiableAt.hasDerivAt).fun_div
    ((hasDerivAt_id c).mul ((hasDerivAt_id c).add_const (1:ℂ)))
    (mul_ne_zero hd.1 hd.2.2)
  change HasDerivAt normalizedMinimumZeta _ c at hq
  rw [hq.deriv]
  change c*(c+1)*((deriv riemannZeta c*(c*(c+1))-
    riemannZeta c*(1*(c+1)+c*1))/(c*(c+1))^(2 : ℕ)) =
      deriv riemannZeta c-(1/c+1/(c+1))*riemannZeta c
  field_simp [hd.1, hd.2.2]

/-- Hardy rotation resolves the actual normalized derivative into two real components. -/
theorem hardy_rotated_normalized_derivative (t : ℝ) :
    Complex.exp (I * (gammaHardyTheta t : ℂ)) * hardyResponseDenominator t *
        deriv normalizedMinimumZeta (criticalResponsePoint t) =
      -((hardyResponseCoercivity t * hardyZ t : ℝ) : ℂ) -
        I * (hardyResponseSlope t : ℂ) := by
  have hD := exp_theta_mul_deriv_riemannZeta_line t
  rw [deriv_riemannZeta_line, ←criticalResponsePoint_eq_linePt] at hD
  have hZ := exp_theta_mul_riemannZeta_line_eq_hardyZ t
  rw [←criticalResponsePoint_eq_linePt] at hZ
  have hrot : Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      deriv riemannZeta (criticalResponsePoint t) =
        -(gammaHardyPhaseRate t : ℂ)*(hardyZ t : ℂ)-I*((deriv hardyZ t : ℝ) : ℂ) := by
    have h := congrArg (fun z : ℂ => z * (-I)) hD
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) h
  rw [mul_assoc, hardyResponseDenominator_mul_derivative, mul_sub, hrot]
  rw [show Complex.exp (I * (gammaHardyTheta t : ℂ)) *
      (hardyResponseNormalizationRate t * riemannZeta (criticalResponsePoint t)) =
        hardyResponseNormalizationRate t * (hardyZ t : ℂ) by
          rw [mul_left_comm, hZ]]
  apply Complex.ext <;> simp [hardyResponseCoercivity, hardyResponseSlope] <;> ring

/-- The Hardy rotation has unit norm at every real height. -/
theorem norm_hardy_response_rotation (t : ℝ) :
    ‖Complex.exp (I * (gammaHardyTheta t : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

/-- The actual arithmetic response has an exact positive two-component norm decomposition. -/
theorem hardy_response_norm_sq (t : ℝ) :
    ‖hardyResponseDenominator t‖^(2 : ℕ) *
        ‖criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t)‖^(2 : ℕ) =
      (hardyResponseCoercivity t * hardyZ t)^(2 : ℕ) + (hardyResponseSlope t)^(2 : ℕ) := by
  rw [criticalFullLogResponse_add_target_eq_derivative, norm_star]
  have h := congrArg (fun z : ℂ => ‖z‖^(2 : ℕ)) (hardy_rotated_normalized_derivative t)
  rw [norm_mul, norm_mul, norm_hardy_response_rotation, one_mul, mul_pow] at h
  rw [h, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- Both real Hardy components obey the actual critical response norm, with no zero premise. -/
theorem hardy_response_component_bounds (t : ℝ) :
    |hardyResponseCoercivity t * hardyZ t| ≤ ‖hardyResponseDenominator t‖ *
        ‖criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t)‖ ∧
    |hardyResponseSlope t| ≤ ‖hardyResponseDenominator t‖ *
        ‖criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t)‖ := by
  have h := hardy_response_norm_sq t
  have hn := mul_nonneg (norm_nonneg (hardyResponseDenominator t))
    (norm_nonneg (criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t)))
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [sq_nonneg (hardyResponseCoercivity t * hardyZ t), sq_nonneg (hardyResponseSlope t)]

/-- Every fixed Hardy-amplitude coefficient is eventually dominated by the actual response norm. -/
theorem eventually_hardy_amplitude_bound (B : ℝ) :
    ∀ᶠ t : ℝ in atTop, B * |hardyZ t| ≤ ‖hardyResponseDenominator t‖ *
      ‖criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t)‖ := by
  filter_upwards [hardyResponseCoercivity_tendsto_atTop.eventually (eventually_ge_atTop B),
    eventually_hardyResponseCoercivity_pos] with t hB ht
  calc
    B * |hardyZ t| ≤ hardyResponseCoercivity t * |hardyZ t| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    _ = |hardyResponseCoercivity t * hardyZ t| := by
      rw [abs_mul, abs_of_pos ht]
    _ ≤ _ := (hardy_response_component_bounds t).1

/-- Under the actual positive coefficient, response vanishing forces both Hardy jets to vanish. -/
theorem hardy_response_eq_zero_iff (t : ℝ) (ht : 0 < hardyResponseCoercivity t) :
    criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t) = 0 ↔
      hardyZ t = 0 ∧ deriv hardyZ t = 0 := by
  have h := hardy_response_norm_sq t
  constructor
  · intro hz
    rw [hz, norm_zero, zero_pow (by decide), mul_zero] at h
    have hv : hardyResponseCoercivity t * hardyZ t = 0 := by
      nlinarith [sq_nonneg (hardyResponseSlope t)]
    have hH : hardyZ t = 0 := (mul_eq_zero.mp hv).resolve_left (ne_of_gt ht)
    have hJ : hardyResponseSlope t = 0 := by nlinarith
    exact ⟨hH, by simpa [hardyResponseSlope, hH] using hJ⟩
  · rintro ⟨hH, hD⟩
    norm_num [hardyResponseSlope, hH, hD] at h
    exact h.resolve_left (hardyResponseDenominator_ne_zero t)

/-- At every sufficiently large height, response zeros are exactly simultaneous zeta and derivative zeros. -/
theorem eventually_hardy_response_eq_zero_iff_zeta_jet :
    ∀ᶠ t : ℝ in atTop,
      (criticalFullLogResponse t + reflectionZeroTarget (criticalResponsePoint t) = 0 ↔
        riemannZeta (criticalResponsePoint t) = 0 ∧
          deriv riemannZeta (criticalResponsePoint t) = 0) := by
  filter_upwards [eventually_hardyResponseCoercivity_pos] with t ht
  rw [hardy_response_eq_zero_iff t ht, criticalResponsePoint_eq_linePt]
  constructor
  · rintro ⟨hH, hD⟩
    have hz := (riemannZeta_line_eq_zero_iff_hardyZ t).mpr hH
    exact ⟨hz, (deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero hz).mpr hD⟩
  · rintro ⟨hz, hD⟩
    exact ⟨(riemannZeta_line_eq_zero_iff_hardyZ t).mp hz,
      (deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero hz).mp hD⟩

/-- The full even target correction in the actual Hardy phase frame. -/
def hardyReflectionCorrection (s : ℂ) : ℂ :=
  Complex.exp (I * (gammaHardyTheta s.im : ℂ)) * hardyResponseDenominator s.im *
    star (reflectionTargetQuadraticCorrection s)

/-- Exact joint Hardy value and slope identity for the full off-line source. -/
theorem hardy_rotated_reflection_source {s : ℂ} (hs : s ∈ minimumStrip) :
    Complex.exp (I * (gammaHardyTheta s.im : ℂ)) * hardyResponseDenominator s.im *
        star (reflectionDiskSource s) =
      -((hardyResponseCoercivity s.im * hardyZ s.im : ℝ) : ℂ) -
        I * (hardyResponseSlope s.im : ℂ) -
        (((s.re-1/2)^(2 : ℕ) : ℝ) : ℂ) * hardyReflectionCorrection s := by
  have h := congrArg (star : ℂ → ℂ) (reflectionDiskSource_eq_derivative_correction hs)
  have hstar : star ((((s.re-1/2)^(2 : ℕ) : ℝ) : ℂ)) = (((s.re-1/2)^(2 : ℕ) : ℝ) : ℂ) := by simp
  simp only [star_sub, star_star, star_mul, hstar] at h
  rw [h, mul_sub, hardy_rotated_normalized_derivative]
  unfold hardyReflectionCorrection
  congr 1
  ring

/-- The complete reflected source norm is the joint corrected Hardy value/slope square. -/
theorem hardy_reflection_source_norm_sq {s : ℂ} (hs : s ∈ minimumStrip) :
    ‖hardyResponseDenominator s.im‖^(2 : ℕ) * ‖reflectionDiskSource s‖^(2 : ℕ) =
      (hardyResponseCoercivity s.im * hardyZ s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).re)^(2 : ℕ) +
      (hardyResponseSlope s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).im)^(2 : ℕ) := by
  have h := congrArg (fun z : ℂ => ‖z‖^(2 : ℕ)) (hardy_rotated_reflection_source hs)
  rw [norm_mul, norm_mul, norm_hardy_response_rotation, one_mul, norm_star, mul_pow] at h
  rw [h, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]
  ring

/-- Every actual off-line zero satisfies the full joint Hardy value/slope disk. -/
theorem hardy_joint_constraint_at_offline_zero {s : ℂ} (hs : s ∈ minimumStrip)
    (hd : s.re ≠ 1/2) (hz : riemannZeta s = 0) :
    (hardyResponseCoercivity s.im * hardyZ s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).re)^(2 : ℕ) +
      (hardyResponseSlope s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).im)^(2 : ℕ) ≤
        (‖hardyResponseDenominator s.im‖ * ((s.re-1/2)^(2 : ℕ)/12))^(2 : ℕ) := by
  rw [←hardy_reflection_source_norm_sq hs, mul_pow]
  have h := norm_criticalFullLogResponse_zero_constraint hs.1 hs.2 hd hz
  change ‖reflectionDiskSource s‖ ≤ _ at h
  gcongr

/-- The height-saving disk constrains the same pair, with every correction retained. -/
theorem hardy_joint_height_constraint_at_offline_zero {s : ℂ} (hs : s ∈ minimumStrip)
    (hd : s.re ≠ 1/2) (ht : s.im ≠ 0) (hz : riemannZeta s = 0) :
    (hardyResponseCoercivity s.im * hardyZ s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).re)^(2 : ℕ) +
      (hardyResponseSlope s.im +
        (s.re-1/2)^(2 : ℕ) * (hardyReflectionCorrection s).im)^(2 : ℕ) ≤
        (‖hardyResponseDenominator s.im‖ * ((s.re-1/2)^(2 : ℕ) *
          reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|)))^(2 : ℕ) := by
  rw [←hardy_reflection_source_norm_sq hs, mul_pow]
  have h := norm_criticalFullLogResponse_zero_constraint_height hs.1 hs.2 hd ht hz
  change ‖reflectionDiskSource s‖ ≤ _ at h
  gcongr

end RHTower.DeletionMixedRefinement

