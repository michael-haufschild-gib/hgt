import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# One integration by parts against an oscillation

Against the oscillation `e^{iηL}` a `C¹` amplitude loses a full power of the frequency:

`‖∫_a^A g(η) e^{iηL} dη‖ ≤ (‖g(A)‖ + ‖g(a)‖ + ∫_a^A ‖g'‖) / L`.

The primitive `e^{iηL}/(iL)` has modulus `1/L`, so both the boundary terms and the transferred
derivative carry the same factor.  This is the estimate that makes every non-constant part of a
smooth cutoff subcritical in the half-log scattering expansion.
-/

open Complex intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The oscillation primitive at frequency `L`. -/
def oscPrimitive (L η : ℝ) : ℂ := Complex.exp ((η * L : ℝ) * I) / ((L : ℂ) * I)

theorem norm_oscPrimitive {L : ℝ} (hL : 0 < L) (η : ℝ) : ‖oscPrimitive L η‖ = 1 / L := by
  rw [oscPrimitive, norm_div, Complex.norm_exp, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  simp

theorem hasDerivAt_oscPrimitive {L : ℝ} (hL : 0 < L) (η : ℝ) :
    HasDerivAt (oscPrimitive L) (Complex.exp ((η * L : ℝ) * I)) η := by
  have hLI : ((L : ℂ) * I) ≠ 0 := by
    have hLne : ((L : ℂ)) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hL
    simp [hLne, Complex.I_ne_zero]
  have h1 : HasDerivAt (fun x : ℝ => ((x * L : ℝ) : ℂ) * I) ((L : ℂ) * I) η := by
    have hbase : HasDerivAt (fun x : ℝ => ((x * L : ℝ) : ℂ)) ((L : ℂ)) η := by
      have hreal : HasDerivAt (fun x : ℝ => x * L) L η := by
        simpa using (hasDerivAt_id' η).mul_const L
      exact hreal.ofReal_comp
    have := hbase.mul_const I
    exact this
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (((x * L : ℝ) : ℂ) * I))
      (Complex.exp (((η * L : ℝ) : ℂ) * I) * ((L : ℂ) * I)) η := h1.cexp
  have hdiv := hexp.div_const ((L : ℂ) * I)
  have hval : Complex.exp (((η * L : ℝ) : ℂ) * I) * ((L : ℂ) * I) / ((L : ℂ) * I)
      = Complex.exp (((η * L : ℝ) : ℂ) * I) := by
    rw [mul_div_assoc, div_self hLI, mul_one]
  have hfun : oscPrimitive L = fun x : ℝ => Complex.exp (((x * L : ℝ) : ℂ) * I) / ((L : ℂ) * I) :=
    rfl
  rw [hfun, ← hval]
  exact hdiv

/-- **The oscillatory integration by parts bound.** -/
theorem norm_integral_oscillatory_le {g g' : ℝ → ℂ} {a A L : ℝ} (hL : 0 < L) (hab : a ≤ A)
    (hderiv : ∀ x ∈ Set.uIcc a A, HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' volume a A) :
    ‖∫ η in a..A, g η * Complex.exp ((η * L : ℝ) * I)‖
      ≤ (‖g A‖ + ‖g a‖ + ∫ η in a..A, ‖g' η‖) / L := by
  have hderiv_v : ∀ x ∈ Set.uIcc a A,
      HasDerivAt (oscPrimitive L) (Complex.exp ((x * L : ℝ) * I)) x :=
    fun x _ => hasDerivAt_oscPrimitive hL x
  have hint_v : IntervalIntegrable (fun x : ℝ => Complex.exp ((x * L : ℝ) * I)) volume a A := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hparts := integral_mul_deriv_eq_deriv_mul hderiv hderiv_v hg' hint_v
  rw [hparts]
  have hnormg' : ‖∫ η in a..A, g' η * oscPrimitive L η‖ ≤ (∫ η in a..A, ‖g' η‖) / L := by
    have hbound : ‖∫ η in a..A, g' η * oscPrimitive L η‖
        ≤ ∫ η in a..A, ‖g' η‖ * (1 / L) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ (hg'.norm.mul_const (1 / L))
      filter_upwards with η _
      rw [norm_mul, norm_oscPrimitive hL]
    rw [intervalIntegral.integral_mul_const] at hbound
    calc ‖∫ η in a..A, g' η * oscPrimitive L η‖
        ≤ (∫ η in a..A, ‖g' η‖) * (1 / L) := hbound
      _ = (∫ η in a..A, ‖g' η‖) / L := by ring
  have hA : ‖g A * oscPrimitive L A‖ = ‖g A‖ / L := by
    rw [norm_mul, norm_oscPrimitive hL]
    ring
  have ha : ‖g a * oscPrimitive L a‖ = ‖g a‖ / L := by
    rw [norm_mul, norm_oscPrimitive hL]
    ring
  calc ‖g A * oscPrimitive L A - g a * oscPrimitive L a
        - ∫ η in a..A, g' η * oscPrimitive L η‖
      ≤ ‖g A * oscPrimitive L A - g a * oscPrimitive L a‖
        + ‖∫ η in a..A, g' η * oscPrimitive L η‖ := norm_sub_le _ _
    _ ≤ (‖g A‖ / L + ‖g a‖ / L) + (∫ η in a..A, ‖g' η‖) / L := by
        have htri := norm_sub_le (g A * oscPrimitive L A) (g a * oscPrimitive L a)
        rw [hA, ha] at htri
        linarith [htri, hnormg']
    _ = (‖g A‖ + ‖g a‖ + ∫ η in a..A, ‖g' η‖) / L := by ring

end

end GaloisForLFunctions.HTGeometry
