import GaloisForLFunctions.RHTower.ScrewTailPrimitive
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewRegularKernel

/-!
# The even-shift filtered screw source
-/

namespace RHTower

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

/-- **Equation `(20)`.**  The regular part of the normalized screw current derivative is exactly
Suzuki's regular screw kernel. -/
theorem two_cosh_sub_screwTailKernel {t : ℝ} (ht : 0 < t) :
    2 * Real.cosh (t / 2) - screwTailKernel t
      = GaloisForLFunctions.RHTower.screwRegularKernel t := by
  rw [GaloisForLFunctions.RHTower.screwRegularKernel_eq_tailForm ht, screwTailKernel,
    Real.cosh_eq]
  ring

/-- The regular density of the even-shift filtered kernel, equation `(23)`. -/
def shiftedScrewDensity (h : ℝ) : ℝ :=
  Real.exp (h / 2) - Real.exp (-(3 * h / 2)) - Real.exp (-(5 * h / 2))

/-- **Equations `(22)`–`(23)`.**  One even shift turns the regular screw kernel into a
three-exponential density. -/
theorem one_sub_exp_mul_screwRegularKernel {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-(2 * t))) * GaloisForLFunctions.RHTower.screwRegularKernel t
      = shiftedScrewDensity t := by
  have hpos : 0 < 1 - Real.exp (-(2 * t)) :=
    GaloisForLFunctions.RHTower.one_sub_exp_neg_two_mul_pos ht
  have hmul : Real.exp (-(2 * t)) * Real.exp (t / 2) = Real.exp (-(3 * t / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have key : (1 - Real.exp (-(2 * t))) *
      (Real.exp (t / 2) - Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t))))
      = (1 - Real.exp (-(2 * t))) * Real.exp (t / 2) - Real.exp (-(5 * t / 2)) := by
    field_simp
  rw [GaloisForLFunctions.RHTower.screwRegularKernel, key, shiftedScrewDensity, ← hmul]
  ring

/-- **Equation `(27)`.**  The filtered regular density has finite contact value `-1`. -/
theorem shiftedScrewDensity_zero : shiftedScrewDensity 0 = -1 := by
  simp [shiftedScrewDensity]

/-! ## The Laplace transform of the filtered regular density -/

theorem integral_Ioi_exp_neg_mul_shiftedScrewDensity {w : ℂ} (hw : 1 / 2 < w.re) :
    ∫ h in Ioi (0 : ℝ), Complex.exp (-(w * (h : ℂ))) * ((shiftedScrewDensity h : ℝ) : ℂ)
      = 1 / (w - 1 / 2) - 1 / (w + 3 / 2) - 1 / (w + 5 / 2) := by
  have hre1 : ((1 / 2 : ℂ) - w).re < 0 := by
    simp only [Complex.sub_re, Complex.div_re]
    norm_num
    linarith
  have hre2 : ((-(3 / 2) : ℂ) - w).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.div_re]
    norm_num
    linarith
  have hre3 : ((-(5 / 2) : ℂ) - w).re < 0 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.div_re]
    norm_num
    linarith
  have hpoint : ∀ h : ℝ, Complex.exp (-(w * (h : ℂ))) * ((shiftedScrewDensity h : ℝ) : ℂ)
      = Complex.exp (((1 / 2 : ℂ) - w) * (h : ℂ))
        - Complex.exp (((-(3 / 2) : ℂ) - w) * (h : ℂ))
        - Complex.exp (((-(5 / 2) : ℂ) - w) * (h : ℂ)) := by
    intro h
    rw [shiftedScrewDensity]
    push_cast
    rw [show ((1 / 2 : ℂ) - w) * (h : ℂ) = -(w * (h : ℂ)) + (h : ℂ) / 2 by ring,
      show ((-(3 / 2) : ℂ) - w) * (h : ℂ) = -(w * (h : ℂ)) + (-(3 * (h : ℂ) / 2)) by ring,
      show ((-(5 / 2) : ℂ) - w) * (h : ℂ) = -(w * (h : ℂ)) + (-(5 * (h : ℂ) / 2)) by ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h _ => hpoint h)]
  rw [integral_sub, integral_sub]
  · rw [integral_exp_mul_complex_Ioi hre1 0, integral_exp_mul_complex_Ioi hre2 0,
      integral_exp_mul_complex_Ioi hre3 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have h1 : (1 / 2 : ℂ) - w ≠ 0 := by
      intro hc
      have : ((1 / 2 : ℂ) - w).re = 0 := by rw [hc]; simp
      linarith [hre1, this]
    have h2 : (-(3 / 2) : ℂ) - w ≠ 0 := by
      intro hc
      have : ((-(3 / 2) : ℂ) - w).re = 0 := by rw [hc]; simp
      linarith [hre2, this]
    have h3 : (-(5 / 2) : ℂ) - w ≠ 0 := by
      intro hc
      have : ((-(5 / 2) : ℂ) - w).re = 0 := by rw [hc]; simp
      linarith [hre3, this]
    rw [show ((1 / 2 : ℂ) - w) = -(w - 1 / 2) by ring,
      show ((-(3 / 2) : ℂ) - w) = -(w + 3 / 2) by ring,
      show ((-(5 / 2) : ℂ) - w) = -(w + 5 / 2) by ring]
    simp only [div_neg, neg_neg, neg_div]
  · exact integrableOn_exp_mul_complex_Ioi hre1 0
  · exact integrableOn_exp_mul_complex_Ioi hre2 0
  · exact (integrableOn_exp_mul_complex_Ioi hre1 0).sub
      (integrableOn_exp_mul_complex_Ioi hre2 0)
  · exact integrableOn_exp_mul_complex_Ioi hre3 0

/-- **Equation `(24)`.**  In the completed coordinate `s = 1/2 + w` the Laplace transform is the
rational archimedean shift defect. -/
theorem shiftedScrewLaplace_reindex (w : ℂ) :
    1 / (w - 1 / 2) - 1 / (w + 3 / 2) - 1 / (w + 5 / 2)
      = -(1 / ((1 / 2 + w) + 2) + 1 / ((1 / 2 + w) + 1) - 1 / ((1 / 2 + w) - 1)) := by
  have e1 : (1 / 2 + w) + 2 = w + 5 / 2 := by ring
  have e2 : (1 / 2 + w) + 1 = w + 3 / 2 := by ring
  have e3 : (1 / 2 + w) - 1 = w - 1 / 2 := by ring
  rw [e1, e2, e3]
  ring

end

end RHTower
