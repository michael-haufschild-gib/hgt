import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltResponseLimit

/-! The remaining radial exponential margin uniformly controls every squared mixed moment. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilQuadraticTiltGaussian_mixed_pow_integrable (s : {s : ℝ // s < 2}) (p q : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) => z 0 ^ p * z 1 ^ q)
      (finiteWeilQuadraticTiltGaussian s : Measure _) := by
  simp only [finiteWeilQuadraticTiltGaussian, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
  apply (integrable_map_measure (f := finiteWeilDiagonalPoint)
    (g := fun z : EuclideanSpace ℝ (Fin 2) => z 0 ^ p * z 1 ^ q) (by fun_prop)
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable).mpr
  change Integrable (fun x : ℝ => x ^ p * x ^ q) (gaussianReal 0 (finiteWeilQuadraticTiltVariance s))
  simpa only [← pow_add] using gaussianZero_integrable_nat_pow (finiteWeilQuadraticTiltVariance s) (p + q)

theorem finiteWeilQuadraticTiltGaussian_mixed_pow_integral (s : {s : ℝ // s < 2}) (p q : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin 2), z 0 ^ p * z 1 ^ q
      ∂(finiteWeilQuadraticTiltGaussian s : Measure _)) =
      ∫ x : ℝ, x ^ (p + q) ∂(gaussianReal 0 (finiteWeilQuadraticTiltVariance s)) := by
  change (∫ z : EuclideanSpace ℝ (Fin 2), z 0 ^ p * z 1 ^ q
    ∂Measure.map finiteWeilDiagonalPoint (gaussianReal 0 (finiteWeilQuadraticTiltVariance s))) = _
  rw [integral_map (f := fun z : EuclideanSpace ℝ (Fin 2) => z 0 ^ p * z 1 ^ q)
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable (by fun_prop)]
  change (∫ x : ℝ, x ^ p * x ^ q ∂(gaussianReal 0 (finiteWeilQuadraticTiltVariance s))) = _
  simp only [← pow_add]

theorem finiteWeilQuadraticTiltGaussian_mixed_square_integrable
    (s : {s : ℝ // s < 2}) (p q : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) => (z 0 ^ p * z 1 ^ q) ^ 2)
      (finiteWeilQuadraticTiltGaussian s : Measure _) := by
  simpa only [mul_pow, ← pow_mul] using
    finiteWeilQuadraticTiltGaussian_mixed_pow_integrable s (p * 2) (q * 2)

theorem bddAbove_finiteWeilCanonicalJointQuadraticTilt_mixed_square
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (p q : ℕ) :
    BddAbove (range (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), (z 0 ^ p * z 1 ^ q) ^ 2
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))) := by
  let η := (2 - (a + 2 * b + d.val)) / 4
  let K := ((p + q).factorial : ℝ) / η ^ (p + q)
  have hη : 0 < η := by dsimp [η]; linarith only [d.property]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmargin : (a + η) + 2 * (b + 0) + (d.val + η) < 2 := by
    dsimp [η]
    linarith only [d.property]
  obtain ⟨C, hC⟩ := (bddAbove_finiteWeilCanonicalJointQuadraticTilt_response_iff
    t a b d η 0 η).mpr hmargin
  refine ⟨K * C, ?_⟩
  rintro _ ⟨r, rfl⟩
  have hquad (z : EuclideanSpace ℝ (Fin 2)) :
      finiteWeilJointQuadratic η 0 η z = η * (z 0 ^ 2 + z 1 ^ 2) := by
    unfold finiteWeilJointQuadratic
    ring
  calc
    _ ≤ ∫ z, K * Real.exp (finiteWeilJointQuadratic η 0 η z)
        ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _) := by
      apply integral_mono_ae
        (finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)
        (finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [hquad]
        exact mixed_monomial_sq_le_quadratic_exponential p q (z 0) (z 1) hη
    _ = K * ∫ z, Real.exp (finiteWeilJointQuadratic η 0 η z)
        ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _) :=
      integral_const_mul _ _
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hC ⟨r, rfl⟩) hK

end RHTower
