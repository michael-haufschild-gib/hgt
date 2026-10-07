import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorLogMoments
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Invertible polynomial axis data for the actual Poisson integral

The logarithmic moment polynomials form a triangular basis: every diagonal
coefficient is the nonzero beta factor. The resulting linear equivalence is
exactly the axis map of the convergent polynomial-weight Poisson integral.
Thus every finite logarithmic order is realized, with no simple-pole restriction.
-/

noncomputable section

open MeasureTheory Set Complex Polynomial
open scoped BigOperators

namespace RHTower.WeilHigherDenominator

/-- The axis polynomial produced by the `n`th logarithmic boundary weight. -/
def polarAxisPolynomial (ρ : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial (n - j) ((n.choose j : ℂ) * polarLogMoment ρ j)

theorem polarAxisPolynomial_natDegree_le (ρ : ℂ) (n : ℕ) :
    (polarAxisPolynomial ρ n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)

theorem polarAxisPolynomial_coeff_top (ρ : ℂ) (n : ℕ) :
    (polarAxisPolynomial ρ n).coeff n = polarLogMoment ρ 0 := by
  classical
  rw [polarAxisPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj₀
    rw [Polynomial.coeff_monomial]
    have hne : n - j ≠ n := by have := Finset.mem_range.mp hj; omega
    simp [hne]
  · simp

/-- No highest logarithmic order is lost in passing from boundary to axis. -/
theorem polarAxisPolynomial_degree {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (n : ℕ) : (polarAxisPolynomial ρ n).degree = n := by
  apply le_antisymm (Polynomial.degree_le_of_natDegree_le (polarAxisPolynomial_natDegree_le ρ n))
  apply Polynomial.le_degree_of_ne_zero
  rw [polarAxisPolynomial_coeff_top, polarLogMoment_zero hρ₀ hρ₁]
  exact polarAxisFactor_ne_zero hρ₀ hρ₁

private def polarAxisSequence {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    Polynomial.Sequence ℂ where
  elems' := polarAxisPolynomial ρ
  degree_eq' := polarAxisPolynomial_degree hρ₀ hρ₁

private theorem polarAxisSequence_unit {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (n : ℕ) : IsUnit ((polarAxisSequence hρ₀ hρ₁) n).leadingCoeff := by
  exact isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
    ((polarAxisSequence hρ₀ hρ₁).ne_zero n))

/-- The exact axis operator, including its inverse at every polynomial degree. -/
def polarAxisEquiv {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    ℂ[X] ≃ₗ[ℂ] ℂ[X] :=
  (Polynomial.basisMonomials ℂ).equiv
    ((polarAxisSequence hρ₀ hρ₁).basis (polarAxisSequence_unit hρ₀ hρ₁)) (Equiv.refl ℕ)

theorem polarAxisEquiv_monomial {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (n : ℕ) (c : ℂ) :
    polarAxisEquiv hρ₀ hρ₁ (Polynomial.monomial n c) = c • polarAxisPolynomial ρ n := by
  have h : polarAxisEquiv hρ₀ hρ₁ (Polynomial.monomial n 1) = polarAxisPolynomial ρ n := by
    simpa only [polarAxisEquiv, Polynomial.coe_basisMonomials, Polynomial.Sequence.basis_eq_self,
      Equiv.refl_apply, polarAxisSequence] using
      (Module.Basis.equiv_apply (Polynomial.basisMonomials ℂ) n
        ((polarAxisSequence hρ₀ hρ₁).basis (polarAxisSequence_unit hρ₀ hρ₁)) (Equiv.refl ℕ))
  have hm : Polynomial.monomial n c = c • Polynomial.monomial n (1 : ℂ) := by
    simp only [Polynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, h]

/-- The binomial moment polynomial is the actual translated-weight integral. -/
theorem polarAxisPolynomial_eval_integral {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (n : ℕ) (x : ℂ) :
    (polarAxisPolynomial ρ n).eval x =
      ∫ t : ℝ, (x + (Real.log |t| : ℂ)) ^ n * polarKernel ρ I t := by
  have hp (t : ℝ) : (x + (Real.log |t| : ℂ)) ^ n * polarKernel ρ I t =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * x ^ (n - j)) * logPolarKernel ρ I j t := by
    rw [add_comm x _, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [logPolarKernel]
    ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_logPolarKernel hρ₀ hρ₁ (by simp) j).const_mul _)]
  simp only [polarAxisPolynomial, eval_finsetSum, eval_monomial, integral_const_mul,
    polarLogMoment]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive real dilation of the actual polynomial-weight integral. -/
theorem integral_polynomial_polarKernel_dilate (ρ z : ℂ) (P : ℂ[X])
    {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ ((a : ℂ) * z) t) =
      (a : ℂ) ^ (-ρ) * ∫ t : ℝ,
        P.eval ((Real.log a : ℂ) + (Real.log |t| : ℂ)) * polarKernel ρ z t := by
  let f (t : ℝ) : ℂ := P.eval (Real.log |t| : ℂ) * polarKernel ρ ((a : ℂ) * z) t
  let g (t : ℝ) : ℂ := P.eval ((Real.log a : ℂ) + (Real.log |t| : ℂ)) * polarKernel ρ z t
  have hsub := Measure.integral_comp_mul_left f a
  have hi : (∫ t : ℝ, f (a * t)) = ((a : ℂ) ^ (-ρ) / (a : ℂ)) * ∫ t : ℝ, g t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have hne : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t ht
    dsimp [f, g]
    rw [abs_mul, abs_of_pos ha, Real.log_mul ha.ne' (abs_pos.mpr ht).ne', ofReal_add,
      polarKernel_dilate ρ z ha]
    ring
  rw [hi] at hsub
  simp only [abs_of_pos (inv_pos.mpr ha), Complex.real_smul, ofReal_inv] at hsub
  have ha₀ : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  change (∫ t : ℝ, f t) = (a : ℂ) ^ (-ρ) * ∫ t : ℝ, g t
  calc
    _ = (a : ℂ) * ((a : ℂ)⁻¹ * ∫ t : ℝ, f t) := by
      rw [← mul_assoc, mul_inv_cancel₀ ha₀, one_mul]
    _ = _ := by rw [← hsub]; field_simp

/-- The linear equivalence is precisely the axis map of the constructed integral. -/
theorem polynomialPolarMode_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (P : ℂ[X]) {y : ℝ} (hy : 0 < y) :
    polynomialPolarMode ρ P ((y : ℂ) * I) =
      (y : ℂ) ^ (1 / 2 - ρ) * (polarAxisEquiv hρ₀ hρ₁ P).eval (Real.log y : ℂ) := by
  have hi : ∀ P : ℂ[X],
      (∫ t : ℝ, P.eval ((Real.log y : ℂ) + (Real.log |t| : ℂ)) * polarKernel ρ I t) =
        (polarAxisEquiv hρ₀ hρ₁ P).eval (Real.log y : ℂ) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        simp only [eval_add, add_mul, map_add]
        rw [integral_add, hP, hQ]
        · convert integrable_polynomial_polarKernel (z := I) hρ₀ hρ₁ (by simp)
              (P.comp (X + C (Real.log y : ℂ))) using 1
          funext t
          rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
            add_comm (Real.log |t| : ℂ)]
        · convert integrable_polynomial_polarKernel (z := I) hρ₀ hρ₁ (by simp)
              (Q.comp (X + C (Real.log y : ℂ))) using 1
          funext t
          rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
            add_comm (Real.log |t| : ℂ)]
    | monomial n c =>
        simp only [eval_monomial, mul_assoc, integral_const_mul, polarAxisEquiv_monomial,
          eval_smul, smul_eq_mul, polarAxisPolynomial_eval_integral hρ₀ hρ₁]
  have hy₀ : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hs : (Real.sqrt y : ℂ) = (y : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hy.le]
    norm_num
  simp only [polynomialPolarMode, mul_im, ofReal_re, ofReal_im, I_im, I_re,
    mul_one, mul_zero, add_zero, integral_polynomial_polarKernel_dilate ρ I P hy, hi]
  rw [hs, sub_eq_add_neg, cpow_add _ _ hy₀]
  ring

/-- Every polynomial axis defect has an actual convergent polynomial-weight realization. -/
theorem exists_polynomialPolarMode_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (Q : ℂ[X]) : ∃ P : ℂ[X], ∀ y : ℝ, 0 < y →
      polynomialPolarMode ρ P ((y : ℂ) * I) =
        (y : ℂ) ^ (1 / 2 - ρ) * Q.eval (Real.log y : ℂ) := by
  refine ⟨(polarAxisEquiv hρ₀ hρ₁).symm Q, fun y hy => ?_⟩
  rw [polynomialPolarMode_axis hρ₀ hρ₁ _ hy, LinearEquiv.apply_symm_apply]

end RHTower.WeilHigherDenominator
