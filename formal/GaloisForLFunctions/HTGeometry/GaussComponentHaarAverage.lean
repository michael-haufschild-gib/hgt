import Mathlib

/-!
# The exact two-variable Haar average of a prime-power scale

The critical weak-Schatten residue of a Gauss-component quasi-inner defect reduces, after the
Connes–Consani source decomposition and the iterated moving-amplitude lemma, to an exact average
of the `m`-th power of the scale `s_p(x) = p^(1-x)` against its inverse over the unit circle
`ℝ/ℤ`.  Haar invariance and Fubini turn the two-variable diagonal average into the *product* of two
one-dimensional moment integrals, and each is an elementary exponential integral.  The result is the
closed constant

`(∫₀¹ s_p^m)(∫₀¹ s_p^{-m}) = (p^m − 1)² / (p^m · m² · (log p)²)`,

the exact arithmetic factor sitting inside the final residue `Tr_ω(|H|^{2m}) =
2 (p−1)^{2m} (p^m−1)² / (p^{2m} m² log p)`.  This file formalises that constant unconditionally; the
surrounding trace-class stability and Dixmier-trace evaluation are the operator-analytic layer.
-/

open intervalIntegral MeasureTheory
open scoped Real

namespace GaloisForLFunctions

/-- The elementary affine-exponential integral `∫₀¹ exp(c(1-x)) dx = (exp c − 1)/c`, `c ≠ 0`,
obtained from the antiderivative `-(1/c) exp(c(1-x))`. -/
theorem integral_exp_affine (c : ℝ) (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.exp (c * (1 - x)) = (Real.exp c - 1) / c := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => -c⁻¹ * Real.exp (c * (1 - x)))
      (Real.exp (c * (1 - x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => c * (1 - x)) (-c) x := by
      have := ((hasDerivAt_id x).const_sub (1:ℝ)).const_mul c
      simpa using this
    have h3 := (h1.exp).const_mul (-c⁻¹)
    convert h3 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    ((Continuous.intervalIntegrable (by fun_prop) 0 1))]
  simp only [mul_sub, mul_one, sub_self, mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **Exact two-variable Haar average** (Gauss-component residue constant).  For a prime-power
scale `s_p(x) = p^(1-x)`, the product of the `m`-th and `(-m)`-th moment integrals over the unit
circle equals the exact arithmetic constant appearing in the critical weak-Schatten residue:
`(∫₀¹ s_p^m)(∫₀¹ s_p^{-m}) = (p^m − 1)² / (p^m · m² · (log p)²)`. -/
theorem gauss_haar_average (p : ℝ) (hp : 1 < p) (m : ℕ) (hm : 1 ≤ m) :
    (∫ x in (0:ℝ)..1, p ^ ((1 - x) * (m : ℝ)))
      * (∫ x in (0:ℝ)..1, p ^ (-((1 - x) * (m : ℝ))))
      = (p ^ m - 1) ^ 2 / (p ^ m * (m : ℝ) ^ 2 * (Real.log p) ^ 2) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hLpos : 0 < Real.log p := Real.log_pos hp
  have hLne : Real.log p ≠ 0 := ne_of_gt hLpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hcne : (m : ℝ) * Real.log p ≠ 0 := mul_ne_zero hmne hLne
  have hrw1 : (fun x : ℝ => p ^ ((1 - x) * (m : ℝ)))
      = fun x => Real.exp (((m : ℝ) * Real.log p) * (1 - x)) := by
    funext x; rw [Real.rpow_def_of_pos hp0]; congr 1; ring
  have hrw2 : (fun x : ℝ => p ^ (-((1 - x) * (m : ℝ))))
      = fun x => Real.exp ((-((m : ℝ) * Real.log p)) * (1 - x)) := by
    funext x; rw [Real.rpow_def_of_pos hp0]; congr 1; ring
  rw [hrw1, hrw2, integral_exp_affine _ hcne, integral_exp_affine _ (neg_ne_zero.mpr hcne)]
  have hEc : Real.exp ((m : ℝ) * Real.log p) = p ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have hEnc : Real.exp (-((m : ℝ) * Real.log p)) = (p ^ m)⁻¹ := by rw [Real.exp_neg, hEc]
  have hpmne : (p ^ m : ℝ) ≠ 0 := ne_of_gt (pow_pos hp0 m)
  rw [hEc, hEnc]
  field_simp
  ring

end GaloisForLFunctions
