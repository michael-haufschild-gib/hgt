import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLaw

/-! Every finite tilted observable is integrable, and quadratic responses are exact partition ratios. -/

open MeasureTheory ProbabilityTheory

namespace RHTower

theorem finiteWeilJointQuadratic_add (a b d A B D : ℝ) :
    finiteWeilJointQuadratic a b d + finiteWeilJointQuadratic A B D =
      finiteWeilJointQuadratic (a + A) (b + B) (d + D) := by
  funext z
  change finiteWeilJointQuadratic a b d z + finiteWeilJointQuadratic A B D z = _
  unfold finiteWeilJointQuadratic
  ring

theorem finiteWeilCanonicalJointQuadraticTilt_integrable (r k : ℕ) (a b d : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    Integrable f (finiteWeilCanonicalJointQuadraticTilt r k a b d :
      Measure (EuclideanSpace ℝ (Fin 2))) := by
  simp only [finiteWeilCanonicalJointQuadraticTilt, ProbabilityMeasure.coe_mk]
  apply (integrable_tilted_iff
    (μ := (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))))
    (f := finiteWeilJointQuadratic a b d)
    (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d) f).mpr
  exact finiteWeilCanonicalObservableLaw_integrable r k (finiteWeilCanonicalFluctuationPoint r k)
    (fun z => Real.exp (finiteWeilJointQuadratic a b d z) • f z)

theorem finiteWeilCanonicalJointQuadraticTilt_response_eq (r k : ℕ) (a b d A B D : ℝ) :
    (∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure _)) =
      (∫ z, Real.exp (finiteWeilJointQuadratic (a + A) (b + B) (d + D) z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure _)) /
      ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) := by
  change (∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
    ∂((finiteWeilCanonicalJointProbabilityLaw r k : Measure _).tilted
      (finiteWeilJointQuadratic a b d))) = _
  rw [integral_exp_tilted, finiteWeilJointQuadratic_add]

end RHTower
