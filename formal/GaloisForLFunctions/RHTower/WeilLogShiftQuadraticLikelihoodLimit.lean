import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticLikelihood
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltResponseLimit

/-! The exact finite branch and sharp critical boundary of quadratic likelihood moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

def finiteWeilQuadraticLikelihoodFiniteLimit (s S : {s : ℝ // s < 2}) (θ : ℝ) : ℝ :=
  Real.exp (θ * (Real.log (Real.sqrt (2 / (2 - S.val))) -
    Real.log (Real.sqrt (2 / (2 - s.val))))) *
      Real.sqrt ((2 - s.val) / (2 - (s.val + θ * (s.val - S.val))))

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_factor
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) (θ : ℝ) :
    Tendsto (fun r => Real.exp (θ *
      (Real.log (∫ z, Real.exp (finiteWeilJointQuadratic A B D.val z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) : Measure E)) -
      Real.log (∫ z, Real.exp (finiteWeilJointQuadratic a b d.val z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) : Measure E)))))
      atTop (𝓝 (Real.exp (θ *
        (Real.log (Real.sqrt (2 / (2 - (A + 2 * B + D.val)))) -
        Real.log (Real.sqrt (2 / (2 - (a + 2 * b + d.val)))))))) := by
  have hP := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b d).log
    (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).ne'
  have hQ := (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t A B D).log
    (finiteWeilQuadraticTilt_normalizer_pos ⟨A + 2 * B + D.val, D.property⟩).ne'
  exact (Real.continuous_exp.tendsto _).comp ((hQ.sub hP).const_mul θ)

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_subcritical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2})
    (θ : {θ : ℝ // (a + 2 * b + d.val) +
      θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) < 2}) :
    Tendsto (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ.val) atTop
      (𝓝 (finiteWeilQuadraticLikelihoodFiniteLimit
        ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ θ.val)) := by
  have he : (a + θ.val * (a - A)) + 2 * (b + θ.val * (b - B)) +
      (d.val + θ.val * (d.val - D.val)) = (a + 2 * b + d.val) +
        θ.val * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) := by ring
  have hδ : (a + θ.val * (a - A)) + 2 * (b + θ.val * (b - B)) +
      (d.val + θ.val * (d.val - D.val)) < 2 := by
    rw [he]
    exact θ.property
  have hr := tendsto_finiteWeilCanonicalJointQuadraticTilt_response_subcritical t a b d
    (θ.val * (a - A)) (θ.val * (b - B)) ⟨θ.val * (d.val - D.val), hδ⟩
  rw [he] at hr
  have h := (tendsto_finiteWeilCanonicalQuadraticLikelihood_factor t a b d A B D θ.val).mul hr
  simpa only [finiteWeilQuadraticLikelihoodFiniteLimit] using h.congr (fun r =>
    (finiteWeilCanonicalQuadraticLikelihoodMoment_eq_response
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ.val).symm)

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_critical
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2})
    (θ : {θ : ℝ // 2 ≤ (a + 2 * b + d.val) +
      θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val))}) :
    Tendsto (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ.val) atTop atTop := by
  have he : (a + θ.val * (a - A)) + 2 * (b + θ.val * (b - B)) +
      (d.val + θ.val * (d.val - D.val)) = (a + 2 * b + d.val) +
        θ.val * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) := by ring
  have hδ : 2 ≤ (a + θ.val * (a - A)) + 2 * (b + θ.val * (b - B)) +
      (d.val + θ.val * (d.val - D.val)) := by
    rw [he]
    exact θ.property
  have hr := tendsto_finiteWeilCanonicalJointQuadraticTilt_response_critical t a b d
    (θ.val * (a - A)) (θ.val * (b - B)) ⟨θ.val * (d.val - D.val), hδ⟩
  have h := (tendsto_finiteWeilCanonicalQuadraticLikelihood_factor t a b d A B D θ.val).pos_mul_atTop
    (Real.exp_pos _) hr
  exact h.congr fun r => (finiteWeilCanonicalQuadraticLikelihoodMoment_eq_response
    r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ.val).symm

theorem tendsto_finiteWeilCanonicalQuadraticLikelihood_extended
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) (θ : ℝ) :
    Tendsto (fun r => ENNReal.ofReal (finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ)) atTop
      (𝓝 (if (a + 2 * b + d.val) + θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) < 2
        then ENNReal.ofReal (finiteWeilQuadraticLikelihoodFiniteLimit
          ⟨a + 2 * b + d.val, d.property⟩ ⟨A + 2 * B + D.val, D.property⟩ θ) else ⊤)) := by
  by_cases hθ : (a + 2 * b + d.val) +
      θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) < 2
  · rw [if_pos hθ]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_finiteWeilCanonicalQuadraticLikelihood_subcritical t a b d A B D ⟨θ, hθ⟩)
  · rw [if_neg hθ]
    exact ENNReal.tendsto_ofReal_atTop.comp
      (tendsto_finiteWeilCanonicalQuadraticLikelihood_critical t a b d A B D ⟨θ, le_of_not_gt hθ⟩)

theorem bddAbove_finiteWeilCanonicalQuadraticLikelihood_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (A B : ℝ) (D : {D : ℝ // A + 2 * B + D < 2}) (θ : ℝ) :
    BddAbove (range (fun r => finiteWeilCanonicalQuadraticLikelihoodMoment
      r (2 * (r + 1) ^ 2 + t r) a b d.val A B D.val θ)) ↔
      (a + 2 * b + d.val) + θ * ((a + 2 * b + d.val) - (A + 2 * B + D.val)) < 2 := by
  constructor
  · intro h
    by_contra hθ
    exact (not_bddAbove_of_tendsto_atTop
      (tendsto_finiteWeilCanonicalQuadraticLikelihood_critical t a b d A B D
        ⟨θ, le_of_not_gt hθ⟩)) h
  · intro hθ
    exact (tendsto_finiteWeilCanonicalQuadraticLikelihood_subcritical
      t a b d A B D ⟨θ, hθ⟩).isBoundedUnder_le.bddAbove_range

end RHTower
