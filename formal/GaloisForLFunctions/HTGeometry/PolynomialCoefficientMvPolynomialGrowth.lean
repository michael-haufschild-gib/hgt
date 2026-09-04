import GaloisForLFunctions.HTGeometry.StrelitzLeadingCoefficientIsolation
import GaloisForLFunctions.HTGeometry.MvPolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# Growth bounds for multivariate polynomials with polynomial coefficients

Evaluation first specializes each one-variable polynomial coefficient and then evaluates the
remaining multivariate polynomial.  The resulting norm is bounded by one coefficient-norm sum,
one uniform coefficient degree, and the total degree in the remaining variables.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sum of coefficient-norm sums over the finite multivariate support. -/
def polynomialMvCoeffNormSum {m : ℕ}
    (Q : MvPolynomial (Fin m) (Polynomial ℂ)) : ℝ :=
  ∑ e ∈ Q.support, coeffNormSum (Q.coeff e)

/-- Largest one-variable degree among the polynomial coefficients. -/
def polynomialMvCoeffDegree {m : ℕ}
    (Q : MvPolynomial (Fin m) (Polynomial ℂ)) : ℕ :=
  Q.support.sup fun e => (Q.coeff e).natDegree

/-- Every supported coefficient has degree at most the uniform coefficient degree. -/
theorem polynomialMvCoeffDegree_le {m : ℕ}
    (Q : MvPolynomial (Fin m) (Polynomial ℂ)) {e : Fin m →₀ ℕ}
    (he : e ∈ Q.support) :
    (Q.coeff e).natDegree ≤ polynomialMvCoeffDegree Q := by
  classical
  exact Finset.le_sup (f := fun d => (Q.coeff d).natDegree) he

/-- Every supported exponent is bounded by the multivariate total degree. -/
theorem polynomialMv_exponent_le_totalDegree {m : ℕ}
    (Q : MvPolynomial (Fin m) (Polynomial ℂ)) {e : Fin m →₀ ℕ}
    (he : e ∈ Q.support) (i : Fin m) : e i ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (MvPolynomial.le_totalDegree he)
  by_cases hi : i ∈ e.support
  · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

/-- **Uniform nested evaluation bound.** Polynomial growth in the coefficient variable and all
remaining variables is explicit and depends only on finite data attached to `Q`. -/
theorem norm_eval₂_le_polynomialMvCoeffNormSum
    {m : ℕ} (Q : MvPolynomial (Fin m) (Polynomial ℂ))
    (z : ℂ) (x : Fin m → ℂ) :
    ‖MvPolynomial.eval₂ (Polynomial.evalRingHom z) x Q‖ ≤
      polynomialMvCoeffNormSum Q * (1 + ‖z‖) ^ polynomialMvCoeffDegree Q *
        ∏ i : Fin m, (1 + ‖x i‖) ^ Q.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  refine le_trans (norm_sum_le _ _) ?_
  rw [polynomialMvCoeffNormSum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro e he
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hcoeff : ‖(Q.coeff e).eval z‖ ≤
      coeffNormSum (Q.coeff e) * (1 + ‖z‖) ^ polynomialMvCoeffDegree Q := by
    refine (norm_eval_le_coeffNormSum (Q.coeff e) z).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hz1 (polynomialMvCoeffDegree_le Q he))
      (coeffNormSum_nonneg _)
  have hprod : ‖e.prod (fun i k => x i ^ k)‖ = ∏ i : Fin m, ‖x i‖ ^ e i := by
    rw [Finsupp.prod_fintype _ _ (by intro i; simp), norm_prod]
    exact Finset.prod_congr rfl fun i _ => norm_pow _ _
  have hvars : ∏ i : Fin m, ‖x i‖ ^ e i ≤
      ∏ i : Fin m, (1 + ‖x i‖) ^ Q.totalDegree := by
    refine Finset.prod_le_prod (fun i _ => by positivity) ?_
    intro i hi
    calc
      ‖x i‖ ^ e i ≤ (1 + ‖x i‖) ^ e i :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg (x i)]) _
      _ ≤ (1 + ‖x i‖) ^ Q.totalDegree :=
        pow_le_pow_right₀ (by linarith [norm_nonneg (x i)])
          (polynomialMv_exponent_le_totalDegree Q he i)
  rw [norm_mul]
  change ‖(Q.coeff e).eval z‖ * ‖e.prod (fun i k => x i ^ k)‖ ≤ _
  rw [hprod]
  calc
    ‖(Polynomial.evalRingHom z) (Q.coeff e)‖ * ∏ i : Fin m, ‖x i‖ ^ e i ≤
        (coeffNormSum (Q.coeff e) * (1 + ‖z‖) ^ polynomialMvCoeffDegree Q) *
          ∏ i : Fin m, (1 + ‖x i‖) ^ Q.totalDegree := by
      exact mul_le_mul hcoeff hvars
        (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (coeffNormSum_nonneg _) (pow_nonneg (by linarith [norm_nonneg z]) _))
    _ = coeffNormSum (Q.coeff e) * (1 + ‖z‖) ^ polynomialMvCoeffDegree Q *
          ∏ i : Fin m, (1 + ‖x i‖) ^ Q.totalDegree := rfl

end

end GaloisForLFunctions.HTGeometry
