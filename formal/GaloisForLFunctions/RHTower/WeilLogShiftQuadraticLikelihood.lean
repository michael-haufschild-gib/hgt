import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEntropy

/-! Exact exponential moments of actual finite quadratic log-likelihood ratios. -/

noncomputable section
open MeasureTheory ProbabilityTheory
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

def finiteWeilCanonicalQuadraticLikelihoodMoment (r k : ℕ)
    (a b d A B D θ : ℝ) : ℝ :=
  ∫ z, Real.exp (θ * llr
    (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
    (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) z)
      ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)

theorem finiteWeilJointQuadratic_scaled_sub (a b d A B D θ : ℝ) (z : E) :
    finiteWeilJointQuadratic (θ * (a - A)) (θ * (b - B)) (θ * (d - D)) z =
      θ * (finiteWeilJointQuadratic a b d z - finiteWeilJointQuadratic A B D z) := by
  unfold finiteWeilJointQuadratic
  ring

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_eq_response
    (r k : ℕ) (a b d A B D θ : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D θ =
      Real.exp (θ * (Real.log (∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) -
        Real.log (∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)))) *
      ∫ z, Real.exp (finiteWeilJointQuadratic (θ * (a - A)) (θ * (b - B)) (θ * (d - D)) z)
        ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) := by
  unfold finiteWeilCanonicalQuadraticLikelihoodMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [finiteWeilCanonicalJointQuadraticTilt_llr r k a b d A B D] with z hz
  rw [hz, finiteWeilJointQuadratic_scaled_sub, ← Real.exp_add]
  congr 1
  ring

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_eq_partition
    (r k : ℕ) (a b d A B D θ : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D θ =
      Real.exp (θ * Real.log (∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)) -
        (θ + 1) * Real.log (∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E))) *
      ∫ z, Real.exp (finiteWeilJointQuadratic
        (a + θ * (a - A)) (b + θ * (b - B)) (d + θ * (d - D)) z)
          ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E) := by
  let ZP := ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
    ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)
  let ZQ := ∫ z, Real.exp (finiteWeilJointQuadratic A B D z)
    ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure E)
  have hZ : 0 < ZP := finiteWeilCanonicalJointQuadratic_partition_pos r k a b d
  have hsplit : θ * Real.log ZQ - (θ + 1) * Real.log ZP =
      θ * (Real.log ZQ - Real.log ZP) - Real.log ZP := by ring
  rw [finiteWeilCanonicalQuadraticLikelihoodMoment_eq_response,
    finiteWeilCanonicalJointQuadraticTilt_response_eq]
  rw [hsplit, Real.exp_sub, Real.exp_log hZ]
  ring

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_pos
    (r k : ℕ) (a b d A B D θ : ℝ) :
    0 < finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D θ := by
  apply integral_exp_pos
  exact finiteWeilCanonicalJointQuadraticTilt_integrable r k a b d _

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_zero
    (r k : ℕ) (a b d A B D : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D 0 = 1 := by
  simp [finiteWeilCanonicalQuadraticLikelihoodMoment]

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_neg_one
    (r k : ℕ) (a b d A B D : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D (-1) = 1 := by
  unfold finiteWeilCanonicalQuadraticLikelihoodMoment
  simp only [neg_one_mul]
  rw [integral_congr_ae (exp_neg_llr
    (finiteWeilCanonicalJointQuadraticTilt_absolutelyContinuous r k a b d A B D)),
    Measure.integral_toReal_rnDeriv
      (finiteWeilCanonicalJointQuadraticTilt_absolutelyContinuous r k A B D a b d)]
  simp

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_half_eq_overlap
    (r k : ℕ) (a b d A B D : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D (-1 / 2) =
      ∫ z, Real.sqrt (((finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E).rnDeriv
        (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) z).toReal)
          ∂(finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E) := by
  unfold finiteWeilCanonicalQuadraticLikelihoodMoment
  apply integral_congr_ae
  filter_upwards [exp_neg_llr
    (finiteWeilCanonicalJointQuadraticTilt_absolutelyContinuous r k a b d A B D)] with z hz
  have h : (-1 / 2 : ℝ) * llr
      (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
      (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) z =
      (-llr (finiteWeilCanonicalJointQuadraticTilt r k a b d : Measure E)
        (finiteWeilCanonicalJointQuadraticTilt r k A B D : Measure E) z) / 2 := by ring
  rw [h, Real.exp_half, hz]

theorem finiteWeilCanonicalQuadraticLikelihoodMoment_swap
    (r k : ℕ) (a b d A B D θ : ℝ) :
    finiteWeilCanonicalQuadraticLikelihoodMoment r k a b d A B D θ =
      finiteWeilCanonicalQuadraticLikelihoodMoment r k A B D a b d (-1 - θ) := by
  rw [finiteWeilCanonicalQuadraticLikelihoodMoment_eq_partition,
    finiteWeilCanonicalQuadraticLikelihoodMoment_eq_partition]
  have ha : A + (-1 - θ) * (A - a) = a + θ * (a - A) := by ring
  have hb : B + (-1 - θ) * (B - b) = b + θ * (b - B) := by ring
  have hd : D + (-1 - θ) * (D - d) = d + θ * (d - D) := by ring
  rw [ha, hb, hd]
  congr 1
  congr 1
  ring

end RHTower
