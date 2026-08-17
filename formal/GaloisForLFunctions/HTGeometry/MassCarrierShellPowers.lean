import GaloisForLFunctions.HTGeometry.ShellPrincipalPowers
import GaloisForLFunctions.HTGeometry.ShellRootDefectExpansion

/-!
# The carrier distortion in the reciprocal spectral parameter

Rewriting every principal root as a principal power turns the distortion into a product of powers of
the shell quantity `1 + x²w²` at the reciprocal spectral parameter `w`, an exponential of the root
defect at that parameter, and a polynomial in `w`.  Every factor now has an expansion in `w`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section DistortionPowers

variable {a : ℝ} {t : ℂ}

theorem shellQuantity_eq_inv (ht : t ≠ 0) (x : ℝ) :
    shellQuantity t x = 1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2 := by
  rw [shellQuantity]
  field_simp

/-- **The distortion as powers of the shell quantity at the reciprocal parameter.** -/
theorem carrierDistortion_eq_shellPowers (htre : 0 < t.re) (htim : 0 < t.im) (x : ℝ)
    (hsmall : Real.sqrt 2 * x ^ 2 < t.re * ‖t‖) (n : ℕ) :
    carrierDistortion a t (_root_.HTGeometry.massBesselRoot t x) n
      = ((Real.sqrt 2 : ℝ) : ℂ)
        * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-1 / 2 : ℝ)) : ℂ)
        * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-1 / 4 : ℝ)) : ℂ)
        * Complex.exp (-((a : ℂ) * shellDefect x t⁻¹))
        * ∑ k ∈ Finset.range n, ((besselK1Coeff k : ℝ) : ℂ) * ((a : ℂ)⁻¹) ^ k * (t⁻¹) ^ k
            * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ) := by
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
  have hre1 : 0 < (shellQuantity t x).re := re_shellQuantity_pos hxsq
  have hQ : shellQuantity t x = 1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2 := shellQuantity_eq_inv htne x
  have hdefect : t * (_root_.HTGeometry.csqrt (shellQuantity t x) - 1) = shellDefect x t⁻¹ := by
    rw [shellDefect, _root_.HTGeometry.csqrt_eq_cpow_half hre1, hQ,
      show (((1 : ℝ) / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
    field_simp
  have hpow : ∀ k : ℕ,
      (((a : ℂ) * (t * _root_.HTGeometry.csqrt (shellQuantity t x)))⁻¹) ^ k
        = ((a : ℂ)⁻¹) ^ k * (t⁻¹) ^ k
          * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-(k : ℝ) / 2 : ℝ)) : ℂ) := by
    intro k
    rw [mul_inv, mul_inv, mul_pow, mul_pow, inv_csqrt_pow_eq_cpow hre1 k, hQ]
    ring
  rw [carrierDistortion_eq_shellFactors htre htim x hsmall n, inv_csqrt_eq_cpow hre1,
    inv_csqrt_csqrt_eq_cpow hre1, hdefect]
  rw [hQ]
  refine congrArg (fun S : ℂ => ((Real.sqrt 2 : ℝ) : ℂ)
      * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-1 / 2 : ℝ)) : ℂ)
      * (1 + (x : ℂ) ^ 2 * (t⁻¹) ^ 2) ^ (((-1 / 4 : ℝ)) : ℂ)
      * Complex.exp (-((a : ℂ) * shellDefect x t⁻¹)) * S) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hQ, hpow k, hQ]
  ring

end DistortionPowers

end

end GaloisForLFunctions.HTGeometry
