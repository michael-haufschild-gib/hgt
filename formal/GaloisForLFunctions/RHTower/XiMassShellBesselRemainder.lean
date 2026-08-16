import GaloisForLFunctions.RHTower.XiMassShellAmplitudeRatio

/-!
# The Schläfli remainder is relatively small

Against its own leading term the Schläfli remainder is smaller by one full power of the argument:

`‖K₁(aZ) − e^{-aZ}(1/√2)√(π/(aZ))‖ ≤ (2/(e·a·Re Z))·√(2‖Z‖/Re Z) · ‖e^{-aZ}(1/√2)√(π/(aZ))‖`.

Both sides carry the same exponential factor `e^{-a Re Z}` and the same square-root amplitude, so
the comparison is a pure constant computation; the gain is the factor `1/(a Re Z)`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem norm_besselLeadingFactor {a : ℝ} (ha : 0 < a) {Z : ℂ} (hZ : 0 < Z.re) :
    ‖Complex.exp (-((a : ℂ) * Z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * Z))‖
      = Real.exp (-(a * Z.re)) * (Real.sqrt 2)⁻¹ * Real.sqrt (Real.pi / (a * ‖Z‖)) := by
  have haZ : (0 : ℝ) < ((a : ℂ) * Z).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos ha hZ
  have hre : ((a : ℂ) * Z).re = a * Z.re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hdivre : 0 < ((Real.pi : ℂ) / ((a : ℂ) * Z)).re :=
    HTGeometry.re_ofReal_div_pos haZ Real.pi_pos
  have hZne : Z ≠ 0 := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hnormdiv : ‖(Real.pi : ℂ) / ((a : ℂ) * Z)‖ = Real.pi / (a * ‖Z‖) := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos ha]
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    HTGeometry.norm_csqrt hdivre, hnormdiv]
  have hneg : (-((a : ℂ) * Z)).re = -(a * Z.re) := by
    rw [Complex.neg_re, hre]
  rw [hneg]
  congr 1
  congr 1
  rw [abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt 2)⁻¹)]

/-- **The Schläfli remainder against its own leading term.** -/
theorem norm_besselRemainder_le_relative {a : ℝ} (ha : 0 < a) {Z : ℂ} (hZ : 0 < Z.re) :
    ‖HTGeometry.besselK1C ((a : ℂ) * Z)
        - Complex.exp (-((a : ℂ) * Z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * Z))‖
      ≤ (2 / (Real.exp 1 * (a * Z.re)) * Real.sqrt (2 * ‖Z‖ / Z.re))
        * (Real.exp (-(a * Z.re)) * (Real.sqrt 2)⁻¹ * Real.sqrt (Real.pi / (a * ‖Z‖))) := by
  have haZ : (0 : ℝ) < ((a : ℂ) * Z).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos ha hZ
  have hre : ((a : ℂ) * Z).re = a * Z.re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hZne : Z ≠ 0 := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hnormZ : 0 < ‖Z‖ := by simpa using hZne
  have hbase := HTGeometry.norm_besselK1C_sub_leading_csqrt_le haZ
  rw [hre] at hbase
  refine le_trans hbase (le_of_eq ?_)
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hprod : Real.sqrt (2 * ‖Z‖ / Z.re) * Real.sqrt (Real.pi / (a * ‖Z‖))
      = Real.sqrt (2 * Real.pi / (a * Z.re)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc Real.exp (-(a * Z.re))
        * (Real.sqrt 2 / (Real.exp 1 * (a * Z.re)) * Real.sqrt (2 * Real.pi / (a * Z.re)))
      = (2 / (Real.exp 1 * (a * Z.re)))
        * (Real.exp (-(a * Z.re)) * (Real.sqrt 2)⁻¹
          * Real.sqrt (2 * Real.pi / (a * Z.re))) * ((Real.sqrt 2)⁻¹ * Real.sqrt 2) := by
        field_simp
        exact Real.sq_sqrt (by norm_num)
    _ = (2 / (Real.exp 1 * (a * Z.re)) * Real.sqrt (2 * ‖Z‖ / Z.re))
        * (Real.exp (-(a * Z.re)) * (Real.sqrt 2)⁻¹ * Real.sqrt (Real.pi / (a * ‖Z‖))) := by
        rw [← hprod]
        field_simp

end

end RHTower
