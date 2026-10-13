import GaloisForLFunctions.HTGeometry.BinaryPolynomialGaussianMoments
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltMoments

/-! Every polynomial observable of the actual tilted Weil law has its diagonal Gaussian moment limit. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun r => ∫ z : E, MvPolynomial.eval (fun i => z i) p
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (∫ x : ℝ, MvPolynomial.eval (fun _ => x) p
        ∂(gaussianReal 0 (finiteWeilQuadraticTiltVariance
          ⟨a + 2 * b + d.val, d.property⟩)))) := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      have hlim := (tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment
        t a b d (e 0) (e 1)).const_mul c
      simpa only [binaryPolynomial_eval_monomial, ← pow_add, integral_const_mul] using hlim
  | add p q hp hq =>
      have hlim := hp.add hq
      rw [← integral_add (gaussianZero_integrable_binaryPolynomial_diagonal _ p)
        (gaussianZero_integrable_binaryPolynomial_diagonal _ q)] at hlim
      simpa only [MvPolynomial.eval_add] using hlim.congr (fun r =>
        (integral_add (finiteWeilCanonicalJointQuadraticTilt_integrable r
          (2 * (r + 1) ^ 2 + t r) a b d.val _)
          (finiteWeilCanonicalJointQuadraticTilt_integrable r
            (2 * (r + 1) ^ 2 + t r) a b d.val _)).symm)

end RHTower
