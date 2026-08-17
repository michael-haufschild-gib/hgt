import GaloisForLFunctions.HTGeometry.BesselK1SectorialPoincare
import GaloisForLFunctions.HTGeometry.ShellCarrierTruncationBound

/-!
# The mass carrier against its order-`m` deep-time partial sum

The exact carrier identity splits the carrier into its deep-time profile times the distortion, plus
the carrier weight of the Schläfli remainder.  The distortion is now controlled uniformly over a
shell of frequencies, and the Schläfli remainder is controlled by the modulus of the shell root, so
the carrier itself agrees with an explicit polynomial in the reciprocal spectral parameter to any
prescribed order.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ShellRemainder

theorem norm_shellPoincareRemainder_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ‖shellPoincareRemainder a z (m + 1)‖
      ≤ Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
        * (rayRemConst (m + 1) / (2 * (a * ‖z‖)) ^ (m + 1)) := by
  have hre : (0 : ℝ) < ((a : ℂ) * z).re := by
    have h : ((a : ℂ) * z).re = a * z.re := by simp [Complex.mul_re]
    rw [h]
    positivity
  have hnorm : ‖(a : ℂ) * z‖ = a * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hreval : ((a : ℂ) * z).re = a * z.re := by simp [Complex.mul_re]
  have hmain := norm_besselK1C_sub_poincare_le_norm m hre
  rw [hnorm, hreval] at hmain
  refine le_trans (le_of_eq ?_) hmain
  congr 1
  rw [shellPoincareRemainder, shellPoincareSum]
  ring

end ShellRemainder

section CarrierPartialSum

/-- **The mass carrier against its order-`m` deep-time partial sum**, with a constant free of the
shell frequency. -/
theorem norm_massBesselCarrier_sub_partialSum_le {a x r c : ℝ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hxr : x ^ 2 * r ^ 2 ≤ 1 / 2) (hxc : x ^ 2 * r ≤ c)
    (hdef : a * shellDefectRate x * r ≤ 1 / 2) (m n : ℕ) {t : ℂ} (htre : 0 < t.re)
    (htim : 0 < t.im) (hsmall : Real.sqrt 2 * x ^ 2 < t.re * ‖t‖) (hw : ‖t⁻¹‖ ≤ r) :
    ‖_root_.HTGeometry.massBesselCarrier a t x
        - _root_.HTGeometry.massBesselLeading a t
          * (truncBelow m (carrierProductPoly a x (n + 1) m)).eval t⁻¹‖
      ≤ ‖_root_.HTGeometry.massBesselLeading a t‖
          * (carrierTruncConst a c (n + 1) m * max 1 (x ^ 2) ^ m * ‖t⁻¹‖ ^ m)
        + 2 * a * ‖t‖ / ‖_root_.HTGeometry.massBesselRoot t x‖
          * (Real.exp (-(a * (_root_.HTGeometry.massBesselRoot t x).re))
            * ((2 * (a * ‖_root_.HTGeometry.massBesselRoot t x‖)) ^ ((1 : ℝ) / 2))⁻¹
            * (rayRemConst (n + 1)
              / (2 * (a * ‖_root_.HTGeometry.massBesselRoot t x‖)) ^ (n + 1))) := by
  set z : ℂ := _root_.HTGeometry.massBesselRoot t x with hzdef
  have hzre : 0 < z.re := _root_.HTGeometry.massBesselRoot_re_pos htre htim x
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hzne
  have hid := massBesselCarrier_eq_distortion (a := a) (t := t) ha htre x hzre (n + 1)
  have hsplit : _root_.HTGeometry.massBesselCarrier a t x
      - _root_.HTGeometry.massBesselLeading a t
        * (truncBelow m (carrierProductPoly a x (n + 1) m)).eval t⁻¹
      = _root_.HTGeometry.massBesselLeading a t
          * (carrierDistortion a t z (n + 1)
            - (truncBelow m (carrierProductPoly a x (n + 1) m)).eval t⁻¹)
        + 2 * (a : ℂ) * t * shellPoincareRemainder a z (n + 1) / z := by
    rw [hid]
    ring
  have hdist : ‖carrierDistortion a t z (n + 1)
      - (truncBelow m (carrierProductPoly a x (n + 1) m)).eval t⁻¹‖
      ≤ carrierTruncConst a c (n + 1) m * max 1 (x ^ 2) ^ m * ‖t⁻¹‖ ^ m := by
    rw [hzdef, carrierDistortion_eq_shellCarrierProfile a htre htim x hsmall (n + 1)]
    exact norm_shellCarrierProfile_sub_trunc_le ha.le hr0 hr1 hxr hxc hdef (n + 1) m hw
  have hrem : ‖2 * (a : ℂ) * t * shellPoincareRemainder a z (n + 1) / z‖
      ≤ 2 * a * ‖t‖ / ‖z‖
        * (Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
          * (rayRemConst (n + 1) / (2 * (a * ‖z‖)) ^ (n + 1))) := by
    have hb := norm_shellPoincareRemainder_le ha hzre n
    have hnum : ‖2 * (a : ℂ) * t * shellPoincareRemainder a z (n + 1)‖
        = 2 * a * ‖t‖ * ‖shellPoincareRemainder a z (n + 1)‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
        show ‖(2 : ℂ)‖ = 2 by simp]
    rw [norm_div, hnum, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hznorm]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ hrem)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hdist (norm_nonneg _)

end CarrierPartialSum

end

end GaloisForLFunctions.HTGeometry
