import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltRealization
import GaloisForLFunctions.RHTower.WeilLogShiftPowerCovarianceEntropy
import GaloisForLFunctions.HTGeometry.AtomicPowerCovarianceDeterminant

/-! # Polynomial attainment of the uniform covariance benchmark -/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem finiteWeilCanonicalJointProbabilityLaw_uniform_polynomial_tilt (r k : ℕ) :
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
      (fun z => (finiteWeilCanonicalLogDensityPolynomial r k
        (Law.uniform (Fin (r + 1)))).eval (z 0)) =
      ((Law.uniform (Fin (r + 1))).atomicProbability
        (finiteWeilCanonicalFluctuationPoint r k) : Measure E) :=
  finiteWeilCanonicalLogDensityPolynomial_tilt_eq_atomic_of_pos r k _
    (fun i => by rw [Law.uniform_apply]; positivity)

theorem finiteWeilCanonicalJointProbabilityLaw_uniform_polynomial_covariance_det
    (r k : ℕ) :
    (powerCovarianceMatrix
      ((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
        (fun z => (finiteWeilCanonicalLogDensityPolynomial r k
          (Law.uniform (Fin (r + 1)))).eval (z 0)))
      (fun z : E => z 0) r).det = finiteWeilPowerCovarianceUniformBenchmark r := by
  rw [finiteWeilCanonicalJointProbabilityLaw_uniform_polynomial_tilt,
    atomicProbability_powerCovarianceMatrix_det, Matrix.det_vandermonde]
  simp_rw [← Finset.prod_pow, finiteWeilCanonicalFluctuationPoint_fst_sub_sq, Law.uniform_apply]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    finiteWeilPowerCovarianceUniformBenchmark]

/-- Every finite base admits a degree-at-most-r polynomial tilt attaining uniform maximal volume. -/
theorem finiteWeilCanonicalJointProbabilityLaw_exists_polynomial_uniform_maximum
    (r k : ℕ) :
    ∃ p : Polynomial ℝ, p.degree < (r + 1 : ℕ) ∧
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => p.eval (z 0)) =
        ((Law.uniform (Fin (r + 1))).atomicProbability
          (finiteWeilCanonicalFluctuationPoint r k) : Measure E) ∧
      (powerCovarianceMatrix
        ((finiteWeilCanonicalJointProbabilityLaw r k : Measure E).tilted
          (fun z => p.eval (z 0))) (fun z : E => z 0) r).det =
        finiteWeilPowerCovarianceUniformBenchmark r :=
  ⟨finiteWeilCanonicalLogDensityPolynomial r k (Law.uniform (Fin (r + 1))),
    finiteWeilCanonicalLogDensityPolynomial_degree_lt r k _,
    finiteWeilCanonicalJointProbabilityLaw_uniform_polynomial_tilt r k,
    finiteWeilCanonicalJointProbabilityLaw_uniform_polynomial_covariance_det r k⟩

end RHTower
