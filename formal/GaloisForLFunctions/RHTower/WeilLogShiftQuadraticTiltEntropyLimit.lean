import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEntropy
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltInformationGeometry
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltMoments

/-! Actual tilted Weil laws have an explicit relative-entropy limit and an exact diagonal rigidity law. -/

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (A B D : ℝ) :
    Tendsto (fun r => ∫ z, finiteWeilJointQuadratic A B D z
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val :
        Measure (EuclideanSpace ℝ (Fin 2)))) atTop
      (𝓝 ((A + 2 * B + D) / (4 - 2 * (a + 2 * b + d.val)))) := by
  have h00 := tendsto_finiteWeilCanonicalJointQuadraticTilt_second_moment t a b d 0 0
  have h01 := tendsto_finiteWeilCanonicalJointQuadraticTilt_second_moment t a b d 0 1
  have h11 := tendsto_finiteWeilCanonicalJointQuadraticTilt_second_moment t a b d 1 1
  have h := ((h00.const_mul A).add (h01.const_mul (2 * B))).add (h11.const_mul D)
  have hval : A * (1 / (4 - 2 * (a + 2 * b + d.val))) +
      (2 * B) * (1 / (4 - 2 * (a + 2 * b + d.val))) +
      D * (1 / (4 - 2 * (a + 2 * b + d.val))) =
      (A + 2 * B + D) / (4 - 2 * (a + 2 * b + d.val)) := by ring
  rw [hval] at h
  refine h.congr fun r => ?_
  have hInt := finiteWeilCanonicalJointQuadraticTilt_integrable r
    (2 * (r + 1) ^ 2 + t r) a b d.val
  have hq : finiteWeilJointQuadratic A B D =
      fun z : EuclideanSpace ℝ (Fin 2) =>
        A * (z 0 * z 0) + (2 * B) * (z 0 * z 1) + D * (z 1 * z 1) := by
    funext z
    unfold finiteWeilJointQuadratic
    ring
  rw [hq, integral_add (hInt _) (hInt _), integral_add (hInt _) (hInt _)]
  simp only [integral_const_mul]

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r => (klDiv
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val :
        Measure (EuclideanSpace ℝ (Fin 2)))).toReal) atTop
      (𝓝 (finiteWeilQuadraticTiltEntropy ⟨a + 2 * b + d.val, d.property⟩
        ⟨A + 2 * B + D.val, D.property⟩)) := by
  have hq := tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_moment t a b d a b d.val
  have hQ := tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_moment t a b d A B D.val
  have hz := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b d).log
    (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).ne'
  have hZ := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t A B D).log
    (finiteWeilQuadraticTilt_normalizer_pos ⟨A + 2 * B + D.val, D.property⟩).ne'
  have h := ((hq.sub hQ).sub hz).add hZ
  have hval : (a + 2 * b + d.val) / (4 - 2 * (a + 2 * b + d.val)) -
      (A + 2 * B + D.val) / (4 - 2 * (a + 2 * b + d.val)) =
      ((a + 2 * b + d.val) - (A + 2 * B + D.val)) /
        (4 - 2 * (a + 2 * b + d.val)) := by ring
  rw [hval, finiteWeilQuadraticTiltEntropy_partition_form
    ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩] at h
  refine h.congr fun r => ?_
  rw [finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal,
    integral_sub (finiteWeilCanonicalJointQuadraticTilt_integrable _ _ _ _ _ _)
      (finiteWeilCanonicalJointQuadraticTilt_integrable _ _ _ _ _ _)]

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r => klDiv
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure (EuclideanSpace ℝ (Fin 2))))
        atTop (𝓝 (ENNReal.ofReal (finiteWeilQuadraticTiltEntropy
          ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩))) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal t a b d A B D)
  exact h.congr fun r => ENNReal.ofReal_toReal
    (finiteWeilCanonicalJointQuadraticTilt_klDiv_ne_top _ _ _ _ _ _ _ _)

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv_zero_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r => klDiv
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure (EuclideanSpace ℝ (Fin 2)))
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure (EuclideanSpace ℝ (Fin 2))))
        atTop (𝓝 0) ↔ a + 2 * b + d.val = A + 2 * B + D.val := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv t a b d A B D
  constructor
  · intro h
    have he := ENNReal.ofReal_eq_zero.mp (tendsto_nhds_unique hlim h)
    exact (finiteWeilQuadraticTiltEntropy_eq_zero_iff _ _).mp
      (le_antisymm he (finiteWeilQuadraticTiltEntropy_nonneg _ _))
  · intro h
    have he := (finiteWeilQuadraticTiltEntropy_eq_zero_iff
      ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩).mpr h
    simpa only [he, ENNReal.ofReal_zero] using hlim

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_symmetric_klDiv
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) :
    Tendsto (fun r =>
      (klDiv (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure (EuclideanSpace ℝ (Fin 2)))).toReal +
      (klDiv (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) A B D.val : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure (EuclideanSpace ℝ (Fin 2)))).toReal)
      atTop (𝓝 (((a + 2 * b + d.val) - (A + 2 * B + D.val)) ^ 2 /
        (2 * (2 - (a + 2 * b + d.val)) * (2 - (A + 2 * B + D.val))))) := by
  simpa only [finiteWeilQuadraticTiltEntropy_swap_add] using
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal t a b d A B D).add
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_klDiv_toReal t A B D a b d)

end RHTower
