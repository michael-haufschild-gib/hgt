import GaloisForLFunctions.HTGeometry.MomentNormalBlockRecurrence

/-!
# Source divided differences through normal moment blocks

Applying the moment functional to a polynomial divided difference produces
the source's second-kind value. Extended normal-block orthogonality kills
the extra term in the polynomial product rule, even across a gap of more
than one degree. At the initial block its only survivor is the first
nonzero source coupling.
-/

open Polynomial
namespace HTGeometry
noncomputable section

/-- Polynomial divided difference `(p(X)-p(x))/(X-x)`. -/
def momentDividedDifference (p : ℝ[X]) (x : ℝ) : ℝ[X] := p /ₘ (X - C x)

theorem mul_momentDividedDifference (p : ℝ[X]) (x : ℝ) :
    (X - C x) * momentDividedDifference p x = p - C (p.eval x) := by
  have h := modByMonic_add_div p (X - C x)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  change (X - C x) * (p /ₘ (X - C x)) = _
  linear_combination h

@[simp] theorem momentDividedDifference_one (x : ℝ) :
    momentDividedDifference 1 x = 0 := by
  have h := mul_momentDividedDifference 1 x
  simp only [eval_one, map_one, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (X_sub_C_ne_zero x)

/-- Exact product rule, with no division by a scalar spectral value. -/
theorem momentDividedDifference_mul (p q : ℝ[X]) (x : ℝ) :
    momentDividedDifference (p * q) x =
      C (p.eval x) * momentDividedDifference q x + q * momentDividedDifference p x := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero x)
  rw [mul_momentDividedDifference, eval_mul, C_mul]
  have hp := mul_momentDividedDifference p x
  have hq := mul_momentDividedDifference q x
  linear_combination -C (p.eval x) * hq - q * hp

theorem momentDividedDifference_sub_C_mul (p q : ℝ[X]) (b x : ℝ) :
    momentDividedDifference (p - C b * q) x =
      momentDividedDifference p x - C b * momentDividedDifference q x := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero x)
  rw [mul_momentDividedDifference, eval_sub, eval_mul, eval_C, C_sub, C_mul]
  have hp := mul_momentDividedDifference p x
  have hq := mul_momentDividedDifference q x
  linear_combination -hp + C b * hq

/-- Source second-kind value attached to an arbitrary polynomial. -/
def momentDividedValue (s : ℕ → ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  momentFunctional s (momentDividedDifference p x)

theorem momentDividedValue_sub_C_mul (s : ℕ → ℝ) (p q : ℝ[X]) (b x : ℝ) :
    momentDividedValue s (p - C b * q) x =
      momentDividedValue s p x - b * momentDividedValue s q x := by
  simp only [momentDividedValue, momentDividedDifference_sub_C_mul]
  rw [show momentDividedDifference p x - C b * momentDividedDifference q x =
      momentDividedDifference p x + (-b) • momentDividedDifference q x by
    rw [smul_eq_C_mul, C_neg]; ring,
    momentFunctional_add, momentFunctional_smul]
  ring

/-- Across a noninitial normal block, the source second-kind transform
intertwines multiplication by every polynomial of degree at most the gap. -/
theorem MomentNormalBlock.divided_value_mul {s : ℕ → ℝ} {n d : ℕ}
    (h : MomentNormalBlock s n d) (hn : 0 < n) {A : ℝ[X]}
    (hA : A.natDegree ≤ d) (x : ℝ) :
    momentDividedValue s (A * monicMomentAdmissionPolynomial s n) x =
      A.eval x * momentDividedValue s (monicMomentAdmissionPolynomial s n) x := by
  have hz : momentFunctional s
      (monicMomentAdmissionPolynomial s n * momentDividedDifference A x) = 0 := by
    have hh := momentFunctional_X_pow_mul_mul_eq_zero (i := 0) h.vanishing
      (q := momentDividedDifference A x) (by
        intro j hj
        have hj' := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
        rw [momentDividedDifference, natDegree_divByMonic A (monic_X_sub_C x),
          natDegree_X_sub_C] at hj'
        have := h.length_pos
        omega)
    simpa only [pow_zero, one_mul] using hh
  simp only [momentDividedValue, momentDividedDifference_mul]
  rw [momentFunctional_add, ← smul_eq_C_mul, momentFunctional_smul, hz, add_zero]

/-- The initial gap contributes precisely its first surviving coupling. -/
theorem MomentNormalBlock.divided_value_first {s : ℕ → ℝ} {d : ℕ}
    (h : MomentNormalBlock s 0 d) (x : ℝ) :
    momentDividedValue s (monicMomentAdmissionPolynomial s d) x =
      momentBlockCoupling s 0 d := by
  have hm := monicMomentAdmissionPolynomial_monic s d
  have hdeg : (momentDividedDifference (monicMomentAdmissionPolynomial s d) x).natDegree =
      d - 1 := by
    rw [momentDividedDifference, natDegree_divByMonic _ (monic_X_sub_C x),
      monicMomentAdmissionPolynomial_natDegree, natDegree_X_sub_C]
  have hl : (momentDividedDifference (monicMomentAdmissionPolynomial s d) x).leadingCoeff = 1 := by
    rw [momentDividedDifference, leadingCoeff_divByMonic_of_monic (monic_X_sub_C x)]
    · exact hm.leadingCoeff
    · rw [degree_X_sub_C, degree_eq_natDegree hm.ne_zero,
        monicMomentAdmissionPolynomial_natDegree]
      exact_mod_cast (show 1 ≤ d from h.length_pos)
  have hP : monicMomentAdmissionPolynomial s 0 = 1 := by
    simp [monicMomentAdmissionPolynomial_eq, Polynomial.ofFn_eq_sum_monomial]
  have hh := momentFunctional_X_pow_mul_mul_first (i := 0) h.vanishing
    (q := momentDividedDifference (monicMomentAdmissionPolynomial s d) x)
    (by simp only [hdeg, zero_add])
  rw [hl, one_mul] at hh
  simpa only [momentDividedValue, momentBlockCoupling, hP, pow_zero, one_mul] using hh

end
end HTGeometry
