import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHausdorffSource
import GaloisForLFunctions.HTGeometry.FiniteMomentNullPolynomialRoots

/-!
# Polynomial actions of collision Hankel matrices

A coefficient vector is the existing finite Hankel null polynomial.
Matrix action and quadratic energy are completely determined by evaluating
that polynomial at the two surviving collision nodes.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

private theorem coefficient_polynomial_eval (d : ℕ) (v : Fin d → ℝ) (x : ℝ) :
    (_root_.HTGeometry.finiteHankelNullPolynomial v).eval x =
      ∑ j : Fin d, v j * x ^ (j : ℕ) := by
  rw [_root_.HTGeometry.finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

/-- Every Hankel matrix-vector coordinate is a two-node evaluation of the coefficient polynomial. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_mulVec_polynomial (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (v : Fin d → ℝ) (i : Fin d) :
    (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).mulVec v i =
      ((4 / 9 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
        (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9) +
      ((1 / 36 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
        (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36) := by
  change (∑ j : Fin d, egbFixedChargeAGibbsCollisionExcess n
    ((i : ℕ) + (j : ℕ) + o + 1) β E * v j) = _
  have he (j : Fin d) : egbFixedChargeAGibbsCollisionExcess n
      ((i : ℕ) + (j : ℕ) + o + 1) β E =
      ((4 / 9 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (j : ℕ) +
      ((1 / 36 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (j : ℕ) := by
    rw [egbFixedChargeAGibbsCollisionExcess_two_rate n ((i : ℕ) + (j : ℕ) + o) β E]
    have hn : (i : ℕ) + (j : ℕ) + o + 1 = ((i : ℕ) + o + 1) + (j : ℕ) := by omega
    rw [hn, pow_add (4 / 9 : ℝ) ((i : ℕ) + o + 1) (j : ℕ),
      pow_add (1 / 36 : ℝ) ((i : ℕ) + o + 1) (j : ℕ)]
    ring
  calc
    _ = ∑ j : Fin d,
        (((4 / 9 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) * (4 / 9 : ℝ) ^ (j : ℕ) +
          ((1 / 36 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) * (1 / 36 : ℝ) ^ (j : ℕ)) * v j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [he j]
    _ = ((4 / 9 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
          (∑ j : Fin d, v j * (4 / 9 : ℝ) ^ (j : ℕ)) +
        ((1 / 36 : ℝ) ^ ((i : ℕ) + o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
          (∑ j : Fin d, v j * (1 / 36 : ℝ) ^ (j : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [← coefficient_polynomial_eval d v (4 / 9), ← coefficient_polynomial_eval d v (1 / 36)]

/-- The quadratic Hankel energy is exactly the sum of the two weighted squared polynomial evaluations. -/
theorem egbFixedChargeAGibbsCollisionHankelMatrix_quadratic_polynomial (n o d : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (v : Fin d → ℝ) :
    dotProduct v ((egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).mulVec v) =
      ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9)) ^ (2 : ℕ) +
      ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
        ((_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36)) ^ (2 : ℕ) := by
  change (∑ i : Fin d, v i * (egbFixedChargeAGibbsCollisionHankelMatrix n o d β E).mulVec v i) = _
  simp_rw [egbFixedChargeAGibbsCollisionHankelMatrix_mulVec_polynomial]
  have hr (i : Fin d) : (4 / 9 : ℝ) ^ ((i : ℕ) + o + 1) =
      (4 / 9 : ℝ) ^ (o + 1) * (4 / 9 : ℝ) ^ (i : ℕ) := by
    rw [show (i : ℕ) + o + 1 = (o + 1) + (i : ℕ) by omega, pow_add]
  have hs (i : Fin d) : (1 / 36 : ℝ) ^ ((i : ℕ) + o + 1) =
      (1 / 36 : ℝ) ^ (o + 1) * (1 / 36 : ℝ) ^ (i : ℕ) := by
    rw [show (i : ℕ) + o + 1 = (o + 1) + (i : ℕ) by omega, pow_add]
  calc
    _ = (((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
          (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (4 / 9)) *
          (∑ i : Fin d, v i * (4 / 9 : ℝ) ^ (i : ℕ)) +
        (((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
          (_root_.HTGeometry.finiteHankelNullPolynomial v).eval (1 / 36)) *
          (∑ i : Fin d, v i * (1 / 36 : ℝ) ^ (i : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hr i, hs i]
      ring
    _ = _ := by
      rw [← coefficient_polynomial_eval d v (4 / 9), ← coefficient_polynomial_eval d v (1 / 36)]
      ring

end
end GaloisForLFunctions.HTGeometry
