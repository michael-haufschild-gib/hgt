import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialTiltMoments
import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel

/-! Polynomial covariance and variance converge to those of the diagonal Gaussian restriction. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_covariance
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (p q : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun r => covariance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (fun z : E => MvPolynomial.eval (fun i => z i) q)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (covariance (fun x : ℝ => MvPolynomial.eval (fun _ => x) p)
        (fun x : ℝ => MvPolynomial.eval (fun _ => x) q)
        (gaussianReal 0 (finiteWeilQuadraticTiltVariance
          ⟨a + 2 * b + d.val, d.property⟩)))) := by
  rw [covariance_eq_sub (gaussianZero_memLp_two_binaryPolynomial_diagonal _ p)
    (gaussianZero_memLp_two_binaryPolynomial_diagonal _ q)]
  have hlim := (tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_moment t a b d (p * q)).sub
    ((tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_moment t a b d p).mul
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_moment t a b d q))
  simp only [MvPolynomial.eval_mul] at hlim
  exact hlim.congr fun r => (covariance_eq_sub
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val _)
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val _)).symm

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (variance (fun x : ℝ => MvPolynomial.eval (fun _ => x) p)
        (gaussianReal 0 (finiteWeilQuadraticTiltVariance
          ⟨a + 2 * b + d.val, d.property⟩)))) := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_covariance t a b d p p
  rw [covariance_self (gaussianZero_memLp_two_binaryPolynomial_diagonal _ p).aemeasurable] at hlim
  exact hlim.congr fun r => covariance_self
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val _).aemeasurable

end RHTower
