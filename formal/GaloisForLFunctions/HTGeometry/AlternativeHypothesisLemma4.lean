import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A closed exceptional Fourier value from Alternative Hypothesis Lemma 4

Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, arXiv:2508.10857v1,
Lemma 4, uses a parity-dependent compactly supported test function `g_n`.
This module closes its `n = 1`, `t = 1/2` exceptional Fourier value directly.
The source's displayed quotient has a removable singularity at this point, so
the theorem states the integral itself rather than treating `0 / 0` as a value.
It does not claim the paper's full parameterized lemma.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace GaloisForLFunctions.HTGeometry

/-- The `n = 1` interior branch of the source test function `g_n`. -/
def alternativeHypothesisLemma4GOne (x : ℝ) : ℝ :=
  Real.cos (Real.pi * x / 2) ^ (2 : ℕ)

/-- The source Fourier convention `e(-t x)` at the literal point `t = 1 / 2`,
restricted to the support interval of `g₁`. -/
def alternativeHypothesisLemma4GOneFourierHalf : ℂ :=
  ∫ x in (-1 : ℝ)..1,
    (alternativeHypothesisLemma4GOne x : ℂ) *
      Complex.exp (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I)

private theorem alternativeHypothesisLemma4_int_cos_pi :
    (∫ x in (-1 : ℝ)..1, Real.cos (Real.pi * x)) = 0 := by
  rw [show (fun x : ℝ => Real.cos (Real.pi * x)) = fun x => Real.cos (x * Real.pi) by
    funext x
    ring_nf]
  rw [intervalIntegral.integral_comp_mul_right (fun x : ℝ => Real.cos x) Real.pi_ne_zero]
  rw [smul_eq_mul, integral_cos]
  rw [show (-1 : ℝ) * Real.pi = -Real.pi by ring_nf,
    show (1 : ℝ) * Real.pi = Real.pi by ring_nf,
    Real.sin_neg, Real.sin_pi]
  norm_num

private theorem alternativeHypothesisLemma4_int_sin_pi :
    (∫ x in (-1 : ℝ)..1, Real.sin (Real.pi * x)) = 0 := by
  rw [show (fun x : ℝ => Real.sin (Real.pi * x)) = fun x => Real.sin (x * Real.pi) by
    funext x
    ring_nf]
  rw [intervalIntegral.integral_comp_mul_right (fun x : ℝ => Real.sin x) Real.pi_ne_zero]
  rw [smul_eq_mul, integral_sin]
  rw [show (-1 : ℝ) * Real.pi = -Real.pi by ring_nf,
    show (1 : ℝ) * Real.pi = Real.pi by ring_nf,
    Real.cos_neg, Real.cos_pi]
  norm_num

private theorem alternativeHypothesisLemma4_int_cos_sq_pi :
    (∫ x in (-1 : ℝ)..1, Real.cos (Real.pi * x) ^ (2 : ℕ)) = 1 := by
  rw [show (fun x : ℝ => Real.cos (Real.pi * x) ^ (2 : ℕ)) =
      fun x => Real.cos (x * Real.pi) ^ (2 : ℕ) by
    funext x
    ring_nf]
  rw [intervalIntegral.integral_comp_mul_right (fun x : ℝ => Real.cos x ^ (2 : ℕ)) Real.pi_ne_zero]
  rw [smul_eq_mul, integral_cos_sq]
  rw [show (-1 : ℝ) * Real.pi = -Real.pi by ring_nf,
    show (1 : ℝ) * Real.pi = Real.pi by ring_nf,
    Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  field_simp
  ring_nf

private theorem alternativeHypothesisLemma4_int_sin_mul_cos_pi :
    (∫ x in (-1 : ℝ)..1, Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) = 0 := by
  rw [show (fun x : ℝ => Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) =
      fun x => Real.sin (x * Real.pi) * Real.cos (x * Real.pi) by
    funext x
    ring_nf]
  rw [intervalIntegral.integral_comp_mul_right
    (fun x : ℝ => Real.sin x * Real.cos x) Real.pi_ne_zero]
  rw [smul_eq_mul, integral_sin_mul_cos₁]
  rw [show (-1 : ℝ) * Real.pi = -Real.pi by ring_nf,
    show (1 : ℝ) * Real.pi = Real.pi by ring_nf,
    Real.sin_neg, Real.sin_pi]
  norm_num

private theorem alternativeHypothesisLemma4_gOne_rewrite (x : ℝ) :
    alternativeHypothesisLemma4GOne x = (1 + Real.cos (Real.pi * x)) / 2 := by
  rw [alternativeHypothesisLemma4GOne]
  have h := Real.cos_two_mul (Real.pi * x / 2)
  rw [show 2 * (Real.pi * x / 2) = Real.pi * x by ring_nf] at h
  linarith

private theorem alternativeHypothesisLemma4_half_phase (x : ℝ) :
    Complex.exp (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I) =
      (Real.cos (Real.pi * x) : ℂ) - Complex.I * (Real.sin (Real.pi * x) : ℂ) := by
  rw [Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring_nf

private theorem alternativeHypothesisLemma4_int_cos_pi_complex :
    (∫ x in (-1 : ℝ)..1, (Real.cos (Real.pi * x) : ℂ)) = 0 := by
  rw [intervalIntegral.integral_ofReal, alternativeHypothesisLemma4_int_cos_pi]
  norm_num

private theorem alternativeHypothesisLemma4_int_sin_pi_complex :
    (∫ x in (-1 : ℝ)..1, (Real.sin (Real.pi * x) : ℂ)) = 0 := by
  rw [intervalIntegral.integral_ofReal, alternativeHypothesisLemma4_int_sin_pi]
  norm_num

private theorem alternativeHypothesisLemma4_int_cos_sq_pi_complex :
    (∫ x in (-1 : ℝ)..1, ((Real.cos (Real.pi * x) ^ (2 : ℕ) : ℝ) : ℂ)) = 1 := by
  rw [intervalIntegral.integral_ofReal, alternativeHypothesisLemma4_int_cos_sq_pi]
  norm_num

private theorem alternativeHypothesisLemma4_int_sin_mul_cos_pi_complex :
    (∫ x in (-1 : ℝ)..1,
      ((Real.sin (Real.pi * x) * Real.cos (Real.pi * x) : ℝ) : ℂ)) = 0 := by
  rw [intervalIntegral.integral_ofReal, alternativeHypothesisLemma4_int_sin_mul_cos_pi]
  norm_num

/-- The fully discharged `n = 1`, `t = 1/2` exceptional value in Lemma 4. -/
theorem alternativeHypothesisLemma4_n1_halfIntegerFourier :
    alternativeHypothesisLemma4GOneFourierHalf = 1 / 2 := by
  unfold alternativeHypothesisLemma4GOneFourierHalf
  have hpoint : ∀ x : ℝ,
      (alternativeHypothesisLemma4GOne x : ℂ) *
          Complex.exp (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I) =
        (1 / 2 : ℂ) *
          ((Real.cos (Real.pi * x) : ℂ) + ((Real.cos (Real.pi * x) ^ (2 : ℕ) : ℝ) : ℂ) -
            Complex.I * ((Real.sin (Real.pi * x) : ℂ) +
              ((Real.sin (Real.pi * x) * Real.cos (Real.pi * x) : ℝ) : ℂ))) := by
    intro x
    rw [alternativeHypothesisLemma4_gOne_rewrite, alternativeHypothesisLemma4_half_phase]
    push_cast
    ring_nf
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x)]
  have hcos : Continuous fun x : ℝ => (Real.cos (Real.pi * x) : ℂ) := by fun_prop
  have hcosSq : Continuous fun x : ℝ => ((Real.cos (Real.pi * x) ^ (2 : ℕ) : ℝ) : ℂ) := by fun_prop
  have hsin : Continuous fun x : ℝ => (Real.sin (Real.pi * x) : ℂ) := by fun_prop
  have hsinCos : Continuous fun x : ℝ =>
      ((Real.sin (Real.pi * x) * Real.cos (Real.pi * x) : ℝ) : ℂ) := by fun_prop
  have hcosInt : IntervalIntegrable (fun x : ℝ => (Real.cos (Real.pi * x) : ℂ)) volume (-1) 1 :=
    hcos.intervalIntegrable _ _
  have hcosSqInt : IntervalIntegrable
      (fun x : ℝ => ((Real.cos (Real.pi * x) ^ (2 : ℕ) : ℝ) : ℂ)) volume (-1) 1 :=
    hcosSq.intervalIntegrable _ _
  have hsinInt : IntervalIntegrable (fun x : ℝ => (Real.sin (Real.pi * x) : ℂ)) volume (-1) 1 :=
    hsin.intervalIntegrable _ _
  have hsinCosInt : IntervalIntegrable
      (fun x : ℝ => ((Real.sin (Real.pi * x) * Real.cos (Real.pi * x) : ℝ) : ℂ)) volume (-1) 1 :=
    hsinCos.intervalIntegrable _ _
  have hleft := hcosInt.add hcosSqInt
  have hright : IntervalIntegrable
      (fun x : ℝ => Complex.I * ((Real.sin (Real.pi * x) : ℂ) +
        ((Real.sin (Real.pi * x) * Real.cos (Real.pi * x) : ℝ) : ℂ))) volume (-1) 1 :=
    (continuous_const.mul (hsin.add hsinCos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub hleft hright]
  rw [intervalIntegral.integral_add hcosInt hcosSqInt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hsinInt hsinCosInt]
  rw [alternativeHypothesisLemma4_int_cos_pi_complex,
    alternativeHypothesisLemma4_int_cos_sq_pi_complex,
    alternativeHypothesisLemma4_int_sin_pi_complex,
    alternativeHypothesisLemma4_int_sin_mul_cos_pi_complex]
  norm_num

end GaloisForLFunctions.HTGeometry
