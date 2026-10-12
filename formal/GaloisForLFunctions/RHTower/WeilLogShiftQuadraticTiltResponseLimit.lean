import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltResponse
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticCriticality
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltDensity

/-! A quadratic tilt leaves exactly the exponential region determined by its remaining diagonal margin. -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace RHTower

theorem finiteWeil_quadratic_partition_ratio {s S : ℝ} (hS : S < 2) :
    Real.sqrt (2 / (2 - S)) / Real.sqrt (2 / (2 - s)) =
      Real.sqrt ((2 - s) / (2 - S)) := by
  rw [← Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 / (2 - S))]
  congr 1
  field_simp

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_response_subcritical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (A B : ℝ)
    (D : {D : ℝ // (a + A) + 2 * (b + B) + (d.val + D) < 2}) :
    Tendsto (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic A B D.val z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 (Real.sqrt ((2 - (a + 2 * b + d.val)) /
          (2 - ((a + A) + 2 * (b + B) + (d.val + D.val)))))) := by
  have h := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical
    t (a + A) (b + B) ⟨d.val + D.val, D.property⟩).div
      (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b d)
      (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).ne'
  rw [finiteWeil_quadratic_partition_ratio D.property] at h
  exact h.congr fun r =>
    (finiteWeilCanonicalJointQuadraticTilt_response_eq r (2 * (r + 1) ^ 2 + t r)
      a b d.val A B D.val).symm

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_response_critical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (A B : ℝ)
    (D : {D : ℝ // 2 ≤ (a + A) + 2 * (b + B) + (d.val + D)}) :
    Tendsto (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic A B D.val z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop atTop := by
  have hZ := finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩
  have h := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_critical
    t (a + A) (b + B) ⟨d.val + D.val, D.property⟩).atTop_mul_pos
      (inv_pos.mpr hZ)
      ((tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b d).inv₀ hZ.ne')
  simpa only [finiteWeilCanonicalJointQuadraticTilt_response_eq, div_eq_mul_inv] using h

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_response_extended
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (A B D : ℝ) :
    Tendsto (fun r => ∫⁻ z, ENNReal.ofReal (Real.exp (finiteWeilJointQuadratic A B D z))
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))
        atTop (𝓝 (if (a + A) + 2 * (b + B) + (d.val + D) < 2 then
          ENNReal.ofReal (Real.sqrt ((2 - (a + 2 * b + d.val)) /
            (2 - ((a + A) + 2 * (b + B) + (d.val + D))))) else ⊤)) := by
  have h : Tendsto (fun r => ENNReal.ofReal (∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _)))
        atTop (𝓝 (if (a + A) + 2 * (b + B) + (d.val + D) < 2 then
          ENNReal.ofReal (Real.sqrt ((2 - (a + 2 * b + d.val)) /
            (2 - ((a + A) + 2 * (b + B) + (d.val + D))))) else ⊤)) := by
    by_cases hD : (a + A) + 2 * (b + B) + (d.val + D) < 2
    · rw [if_pos hD]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_finiteWeilCanonicalJointQuadraticTilt_response_subcritical t a b d A B ⟨D, hD⟩)
    · rw [if_neg hD]
      exact ENNReal.tendsto_ofReal_atTop.comp
        (tendsto_finiteWeilCanonicalJointQuadraticTilt_response_critical t a b d A B
          ⟨D, le_of_not_gt hD⟩)
  exact h.congr fun r => ofReal_integral_eq_lintegral_ofReal
    (finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)

theorem bddAbove_finiteWeilCanonicalJointQuadraticTilt_response_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (A B D : ℝ) :
    BddAbove (range (fun r => ∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))) ↔
        (a + A) + 2 * (b + B) + (d.val + D) < 2 := by
  constructor
  · intro h
    by_contra hD
    exact (not_bddAbove_of_tendsto_atTop
      (tendsto_finiteWeilCanonicalJointQuadraticTilt_response_critical t a b d A B
        ⟨D, le_of_not_gt hD⟩)) h
  · intro hD
    exact (tendsto_finiteWeilCanonicalJointQuadraticTilt_response_subcritical t a b d A B
      ⟨D, hD⟩).isBoundedUnder_le.bddAbove_range

theorem bddAbove_finiteWeilCanonicalJointQuadraticTilt_radial_response_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (c : ℝ) :
    BddAbove (range (fun r => ∫ z : EuclideanSpace ℝ (Fin 2), Real.exp (c * ‖z‖ ^ 2)
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure _))) ↔
        c < (2 - (a + 2 * b + d.val)) / 2 := by
  have h := bddAbove_finiteWeilCanonicalJointQuadraticTilt_response_iff t a b d c 0 c
  simp only [finiteWeilJointQuadratic_radial] at h
  exact h.trans (by constructor <;> intro hc <;> linarith)

end RHTower
