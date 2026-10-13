import GaloisForLFunctions.RHTower.WeilLogShiftPolynomialCovarianceLimit
import GaloisForLFunctions.HTGeometry.GaussianContinuousVarianceRigidity

/-! The limiting polynomial variance kernel is exactly constant diagonal restriction, independent of subcritical tilt. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) ↔
        ∀ x : ℝ, MvPolynomial.eval (fun _ => x) p = MvPolynomial.eval (fun _ => 0) p := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance t a b d p
  have hv : finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩ ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < 1 / (4 - 2 * (a + 2 * b + d.val))
    exact one_div_pos.mpr (by linarith only [d.property])
  have hc : Continuous (fun x : ℝ => MvPolynomial.eval (fun _ : Fin 2 => x) p) :=
    p.continuous_eval.comp (by fun_prop)
  have hk := gaussianReal_variance_eq_zero_iff_constant 0 _ hv hc
    (gaussianZero_memLp_two_binaryPolynomial_diagonal _ p)
  constructor
  · intro hzero
    exact hk.mp (tendsto_nhds_unique hlim hzero)
  · intro hconst
    simpa only [hk.mpr hconst] using hlim

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff_probe
    (t u : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) (p : MvPolynomial (Fin 2) ℝ) :
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) ↔
    Tendsto (fun r => variance (fun z : E => MvPolynomial.eval (fun i => z i) p)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + u r) A B D.val : Measure E))
      atTop (𝓝 0) := by
  rw [tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff,
    tendsto_finiteWeilCanonicalJointQuadraticTilt_polynomial_variance_zero_iff]

end RHTower
