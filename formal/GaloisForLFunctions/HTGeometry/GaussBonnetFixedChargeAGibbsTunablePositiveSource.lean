import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableLimits

/-! # The exact positive measure surviving each tunable Gibbs attenuation -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- The observed slow mass provides a positive scalar for exact source normalization. -/
def egbFixedChargeAGibbsTunableSourceMass (n k m : ℕ) (t : ℝ) : NNReal :=
  egbFixedChargeAGibbsCollisionSlowSourceMass n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t)

/-- The ratio parameter supplies a nonnegative fast-atom mass, including the pure slow endpoint. -/
def egbFixedChargeAGibbsTunableRatioMass (t : ℝ) : NNReal := ⟨t ^ 2, sq_nonneg t⟩

/-- A literal positive two-atom source independent of attenuation and grid. -/
def egbFixedChargeAGibbsTunableNormalizedSource (t : ℝ) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource 1 egbFixedChargeAGibbsCollisionSlowNode +
    hausdorffAtomSource (egbFixedChargeAGibbsTunableRatioMass t) egbFixedChargeAGibbsCollisionFastNode

instance (t : ℝ) : IsFiniteMeasure (egbFixedChargeAGibbsTunableNormalizedSource t) := by
  unfold egbFixedChargeAGibbsTunableNormalizedSource
  infer_instance

/-- Every actual observed collision source is exactly a positive scalar times the same normalized source. -/
theorem egbFixedChargeAGibbsTunable_source_factorization (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableSourceMass n k m t • egbFixedChargeAGibbsTunableNormalizedSource t := by
  have hf : egbFixedChargeAGibbsCollisionFastSourceMass n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableSourceMass n k m t * egbFixedChargeAGibbsTunableRatioMass t := by
    apply Subtype.ext
    exact egbFixedChargeAGibbsTunable_source_mass_ratio n k m t
  simp only [egbFixedChargeAGibbsCollisionHausdorffSource, egbFixedChargeAGibbsTunableNormalizedSource,
    hausdorffAtomSource, smul_add, smul_smul, mul_one, hf, egbFixedChargeAGibbsTunableSourceMass]

/-- Positive rescaling recovers the literal normalized source at every finite stage. -/
theorem egbFixedChargeAGibbsTunable_rescaled_source_eq (n k m : ℕ) (t : ℝ) :
    (egbFixedChargeAGibbsTunableSourceMass n k m t)⁻¹ •
      egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableNormalizedSource t := by
  have hm : egbFixedChargeAGibbsTunableSourceMass n k m t ≠ 0 := by
    intro h
    have hp := egbFixedChargeAGibbsTunable_slow_mass_pos n k m t
    change 0 < (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) at hp
    rw [h] at hp
    norm_num at hp
  rw [egbFixedChargeAGibbsTunable_source_factorization, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- The normalized positive survivor has an exact two-rate moment sequence. -/
theorem egbFixedChargeAGibbsTunable_normalized_source_moment (t : ℝ) (l : ℕ) :
    hausdorffMoment (egbFixedChargeAGibbsTunableNormalizedSource t) l =
      (4 / 9 : ℝ) ^ l + t ^ 2 * (1 / 36 : ℝ) ^ l := by
  unfold egbFixedChargeAGibbsTunableNormalizedSource
  have ha := integrable_hausdorffDifferenceIntegrand
    (hausdorffAtomSource 1 egbFixedChargeAGibbsCollisionSlowNode) 0 l
  have hb := integrable_hausdorffDifferenceIntegrand
    (hausdorffAtomSource (egbFixedChargeAGibbsTunableRatioMass t) egbFixedChargeAGibbsCollisionFastNode) 0 l
  change (∫ y, (y : ℝ) ^ l ∂(hausdorffAtomSource 1 egbFixedChargeAGibbsCollisionSlowNode +
    hausdorffAtomSource (egbFixedChargeAGibbsTunableRatioMass t) egbFixedChargeAGibbsCollisionFastNode)) = _
  rw [integral_add_measure (by simpa using ha) (by simpa using hb)]
  change hausdorffMoment (hausdorffAtomSource 1 egbFixedChargeAGibbsCollisionSlowNode) l +
    hausdorffMoment (hausdorffAtomSource (egbFixedChargeAGibbsTunableRatioMass t) egbFixedChargeAGibbsCollisionFastNode) l = _
  rw [hausdorffMoment_atom, hausdorffMoment_atom]
  change (1 : ℝ) * (4 / 9 : ℝ) ^ l + t ^ 2 * (1 / 36 : ℝ) ^ l = _
  ring

/-- The positive source recovered by normalization never vanishes, even at the zero-Fisher endpoint. -/
theorem egbFixedChargeAGibbsTunable_normalized_source_ne_zero (t : ℝ) :
    egbFixedChargeAGibbsTunableNormalizedSource t ≠ 0 := by
  intro h
  have hm := egbFixedChargeAGibbsTunable_normalized_source_moment t 0
  simp [h, hausdorffMoment] at hm
  nlinarith [sq_nonneg t]

/-- The normalized survivor has exactly the Fisher value retained by the actual Gibbs attenuation path. -/
theorem egbFixedChargeAGibbsTunable_normalized_source_fisher (t : ℝ) :
    _root_.HTGeometry.pureStateQuantumFisherValue
      (hausdorffMoment (egbFixedChargeAGibbsTunableNormalizedSource t) 0)
      (hausdorffMoment (egbFixedChargeAGibbsTunableNormalizedSource t) 1)
      (hausdorffMoment (egbFixedChargeAGibbsTunableNormalizedSource t) 2) =
      egbFixedChargeAGibbsTunableFisherCurve t := by
  rw [egbFixedChargeAGibbsTunable_normalized_source_moment,
    egbFixedChargeAGibbsTunable_normalized_source_moment,
    egbFixedChargeAGibbsTunable_normalized_source_moment]
  unfold _root_.HTGeometry.pureStateQuantumFisherValue _root_.HTGeometry.projectiveQuantumTangentValue
    egbFixedChargeAGibbsTunableFisherCurve
  have hd : 1 + t ^ 2 ≠ 0 := (show 0 < 1 + t ^ 2 by positivity).ne'
  norm_num only [pow_zero, pow_one, mul_one]
  field_simp [hd]
  <;> ring

end
end GaloisForLFunctions.HTGeometry
