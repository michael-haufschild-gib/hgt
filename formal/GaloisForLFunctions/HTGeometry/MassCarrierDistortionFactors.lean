import GaloisForLFunctions.HTGeometry.PrincipalRootMultiplicative

/-!
# The carrier distortion in shell factors

Once the shell root is factored through the spectral parameter, the distortion of the carrier against
its deep-time profile is a product of four elementary factors of the shell quantity `1 + x²/t²`: its
inverse root, the inverse root of that root, the exponential of the root defect, and the Poincaré
polynomial at the shell argument.  Each of these has its own expansion in the reciprocal spectral
parameter.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section DistortionFactors

variable {a : ℝ} {t : ℂ}

/-- The shell quantity of a frequency at a spectral parameter. -/
def shellQuantity (t : ℂ) (x : ℝ) : ℂ := 1 + (x : ℂ) ^ 2 / t ^ 2

theorem norm_shellQuantity_sub_one (t : ℂ) (x : ℝ) :
    ‖shellQuantity t x - 1‖ = x ^ 2 / ‖t‖ ^ 2 := by
  rw [shellQuantity, add_sub_cancel_left, norm_shellQuot]

theorem re_shellQuantity_pos {t : ℂ} {x : ℝ} (h : x ^ 2 < ‖t‖ ^ 2) :
    0 < (shellQuantity t x).re := by
  have hu : ‖shellQuantity t x - 1‖ = x ^ 2 / ‖t‖ ^ 2 := norm_shellQuantity_sub_one t x
  have htn : (0 : ℝ) < ‖t‖ ^ 2 := by nlinarith [sq_nonneg x, h]
  have hlt : ‖shellQuantity t x - 1‖ < 1 := by
    rw [hu, div_lt_one htn]
    exact h
  have hb : |(shellQuantity t x - 1).re| ≤ ‖shellQuantity t x - 1‖ :=
    Complex.abs_re_le_norm _
  have hbb := abs_le.mp hb
  have hsub : (shellQuantity t x - 1).re = (shellQuantity t x).re - 1 := by simp
  rw [hsub] at hbb
  linarith [hbb.1, hlt]

/-- **The distortion in shell factors.** -/
theorem carrierDistortion_eq_shellFactors (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ)
    (hsmall : Real.sqrt 2 * x ^ 2 < t.re * ‖t‖) (n : ℕ) :
    carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n
      = ((Real.sqrt 2 : ℝ) : ℂ)
        * (_root_.HTGeometry.csqrt (shellQuantity t x))⁻¹
        * (_root_.HTGeometry.csqrt (_root_.HTGeometry.csqrt (shellQuantity t x)))⁻¹
        * Complex.exp (-((a : ℂ) * (t * (_root_.HTGeometry.csqrt (shellQuantity t x) - 1))))
        * ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ)
            * (((a : ℂ) * (t * _root_.HTGeometry.csqrt (shellQuantity t x)))⁻¹) ^ k := by
  have htne : t ≠ 0 := by
    intro h
    rw [h] at htre
    simp at htre
  have htnorm : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr htne
  have hrele : t.re ≤ ‖t‖ := Complex.re_le_norm t
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hxsq : x ^ 2 < ‖t‖ ^ 2 := by nlinarith [sq_nonneg x, hsmall, hrele, htnorm]
  have hxlt : x ^ 2 < t.re * ‖t‖ := by nlinarith [sq_nonneg x, hsmall, hs2]
  have hre1 : 0 < (shellQuantity t x).re := re_shellQuantity_pos hxsq
  set s : ℂ := _root_.HTGeometry.csqrt (shellQuantity t x) with hsdef
  have hsre : 0 < s.re := by
    rw [hsdef, _root_.HTGeometry.csqrt_re]
    exact _root_.HTGeometry.csqrtRe_pos hre1
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hsre
    simp at hsre
  have hzeq : _root_.HTGeometry.massBesselRoot t x = t * s := by
    rw [hsdef, shellQuantity]
    exact massBesselRoot_eq_mul_csqrt htre htim x hxlt
  have hzre : 0 < (t * s).re := by
    rw [← hzeq]
    exact _root_.HTGeometry.massBesselRoot_re_pos htre htim x
  have hclose : Real.sqrt 2 * ‖s - 1‖ < 1 := by
    have h1 : ‖s - 1‖ ≤ ‖shellQuantity t x - 1‖ := by
      rw [hsdef]
      exact _root_.HTGeometry.norm_csqrt_sub_one_le hre1
    have h2 : ‖shellQuantity t x - 1‖ = x ^ 2 / ‖t‖ ^ 2 := norm_shellQuantity_sub_one t x
    have h3 : Real.sqrt 2 * (x ^ 2 / ‖t‖ ^ 2) < 1 := by
      rw [mul_div_assoc'] at *
      rw [div_lt_one (by positivity)]
      nlinarith [hsmall, hrele, htnorm]
    have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc Real.sqrt 2 * ‖s - 1‖ ≤ Real.sqrt 2 * (x ^ 2 / ‖t‖ ^ 2) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 hs2nn
      _ < 1 := h3
  have hcsmul : _root_.HTGeometry.csqrt (t * s)
      = _root_.HTGeometry.csqrt t * _root_.HTGeometry.csqrt s :=
    csqrt_mul_of_near_one htre hsre hzre hclose
  have hcst : _root_.HTGeometry.csqrt t ≠ 0 := _root_.HTGeometry.csqrt_ne_zero htre
  have hcss : _root_.HTGeometry.csqrt s ≠ 0 := _root_.HTGeometry.csqrt_ne_zero hsre
  rw [carrierDistortion, shellPoincareSum, hzeq, hcsmul]
  have hdiv1 : t / (t * s) = s⁻¹ := by
    field_simp
  have hdiv2 : _root_.HTGeometry.csqrt t / (_root_.HTGeometry.csqrt t * _root_.HTGeometry.csqrt s)
      = (_root_.HTGeometry.csqrt s)⁻¹ := by
    field_simp
  have hsub : t * s - t = t * (s - 1) := by ring
  rw [hdiv1, hdiv2, hsub]

end DistortionFactors

end

end GaloisForLFunctions.HTGeometry
