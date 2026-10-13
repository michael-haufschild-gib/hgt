import GaloisForLFunctions.HTGeometry.FiniteNodePolynomialIdeal
import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftJointTransportGeometry

/-! Exact finite polynomial observables and covariance null vectors modulo the support polynomial. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem finiteWeilCanonicalJointQuadraticTilt_polynomial_ae_eq_iff_dvd
    (r k : ℕ) (a b d : ℝ) (p q : Polynomial ℝ) :
    (∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E),
      p.eval (z 0) = q.eval (z 0)) ↔
        Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣ p - q := by
  rw [finiteWeilCanonicalJointQuadraticTilt_ae_iff]
  exact finite_node_polynomial_eval_eq_iff_dvd
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) p q

theorem finiteWeilCanonicalJointQuadraticTilt_polynomial_ae_eq_iff_remainder
    (r k : ℕ) (a b d : ℝ) (p q : Polynomial ℝ) :
    (∀ᵐ z ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E),
      p.eval (z 0) = q.eval (z 0)) ↔
        p %ₘ Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) =
          q %ₘ Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_ae_iff]
  exact finite_node_polynomial_eval_eq_iff_remainder
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) p q

theorem finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_dvd
    (r k : ℕ) (a b d : ℝ) (p : Polynomial ℝ) :
    variance (fun z : E => p.eval (z 0))
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) = 0 ↔
        Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣
          p - Polynomial.C (p.eval (finiteWeilCanonicalFluctuationPoint r k 0 0)) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values]
  simpa only [Polynomial.eval_C] using finite_node_polynomial_eval_eq_iff_dvd
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) p
    (Polynomial.C (p.eval (finiteWeilCanonicalFluctuationPoint r k 0 0)))

theorem finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_unique_factor
    (r k : ℕ) (a b d : ℝ) (p : Polynomial ℝ) :
    variance (fun z : E => p.eval (z 0))
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) = 0 ↔
        ∃! q : Polynomial ℝ, p = Polynomial.C (p.eval (finiteWeilCanonicalFluctuationPoint r k 0 0)) +
          Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) * q := by
  rw [finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values]
  exact finite_node_polynomial_constant_iff_unique_factor
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
    (finiteWeilCanonicalFluctuationPoint_fst_injective r k) 0 p

theorem finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_mulVec_zero_iff_dvd
    (r k : ℕ) (a b d : ℝ) (n : ℕ) (c : Fin n → ℝ) :
    (powerCovarianceMatrix (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (fun z => z 0) n).mulVec c = 0 ↔
        Lagrange.nodal Finset.univ (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) ∣
          (∑ j : Fin n, Polynomial.monomial ((j : ℕ) + 1) (c j)) -
            Polynomial.C (∑ j : Fin n, c j *
              (finiteWeilCanonicalFluctuationPoint r k 0 0) ^ ((j : ℕ) + 1)) := by
  rw [finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_mulVec_eq_zero_iff_values]
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C] using
    finite_node_polynomial_eval_eq_iff_dvd
      (fun i => finiteWeilCanonicalFluctuationPoint r k i 0)
      (finiteWeilCanonicalFluctuationPoint_fst_injective r k)
      (∑ j : Fin n, Polynomial.monomial ((j : ℕ) + 1) (c j))
      (Polynomial.C (∑ j : Fin n, c j *
        (finiteWeilCanonicalFluctuationPoint r k 0 0) ^ ((j : ℕ) + 1)))

end RHTower
