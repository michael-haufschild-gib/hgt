import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeSpectralEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeSource

/-! # Literal positive sources on the erased, slow, and fast collision nodes -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- Add the erased endpoint atom to the existing surviving source cone. -/
def egbFixedChargeAGibbsFullConeSource (R A B : NNReal) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource R egbFixedChargeAGibbsCollisionZeroNode + egbFixedChargeAGibbsConeSource A B

instance (R A B : NNReal) : IsFiniteMeasure (egbFixedChargeAGibbsFullConeSource R A B) := by
  unfold egbFixedChargeAGibbsFullConeSource
  infer_instance

/-- The three prescribed masses give the complete moment sequence, including time zero. -/
theorem egbFixedChargeAGibbsFullConeSource_moment (R A B : NNReal) (m : ℕ) :
    hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) m =
      (R : ℝ) * (0 : ℝ) ^ m + (A : ℝ) * (4 / 9 : ℝ) ^ m + (B : ℝ) * (1 / 36 : ℝ) ^ m := by
  have hR := integrable_hausdorffDifferenceIntegrand
    (hausdorffAtomSource R egbFixedChargeAGibbsCollisionZeroNode) 0 m
  have hAB := integrable_hausdorffDifferenceIntegrand (egbFixedChargeAGibbsConeSource A B) 0 m
  change (∫ z, (z : ℝ) ^ m ∂(hausdorffAtomSource R egbFixedChargeAGibbsCollisionZeroNode +
    egbFixedChargeAGibbsConeSource A B)) = _
  rw [integral_add_measure (by simpa using hR) (by simpa using hAB)]
  change hausdorffMoment (hausdorffAtomSource R egbFixedChargeAGibbsCollisionZeroNode) m +
    hausdorffMoment (egbFixedChargeAGibbsConeSource A B) m = _
  rw [hausdorffMoment_atom, egbFixedChargeAGibbsConeSource_moment]
  change (R : ℝ) * (0 : ℝ) ^ m + _ = _
  ring

/-- Scaling all masses is literally scaling the positive measure. -/
theorem egbFixedChargeAGibbsFullConeSource_scale (c R A B : NNReal) :
    egbFixedChargeAGibbsFullConeSource (c * R) (c * A) (c * B) =
      c • egbFixedChargeAGibbsFullConeSource R A B := by
  simp only [egbFixedChargeAGibbsFullConeSource, egbFixedChargeAGibbsConeSource_scale,
    hausdorffAtomSource, smul_add, smul_smul]

/-- Actual full-support Gibbs states realize every three-atom source up to a common positive scale. -/
theorem egbFixedChargeAGibbsFullCone_source_factorization (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeScale n k R A B • egbFixedChargeAGibbsFullConeSource R A B := by
  rw [egbFixedChargeAGibbsFullCollisionHausdorffSource, egbFixedChargeAGibbsFullCone_erased_mass,
    egbFixedChargeAGibbsFullCone_slow_mass, egbFixedChargeAGibbsFullCone_fast_mass,
    ← egbFixedChargeAGibbsFullConeSource_scale]
  exact add_assoc _ _ _

/-- Exact positive normalization recovers all three masses, including boundary faces and the origin. -/
theorem egbFixedChargeAGibbsFullCone_rescaled_source_eq (n k : ℕ) (R A B : NNReal) :
    (egbFixedChargeAGibbsFullConeScale n k R A B)⁻¹ •
      egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
        egbFixedChargeAGibbsFullConeSource R A B := by
  have hc : egbFixedChargeAGibbsFullConeScale n k R A B ≠ 0 := by
    intro h
    have hp := egbFixedChargeAGibbsFullConeScale_pos n k R A B
    rw [h] at hp
    norm_num at hp
  rw [egbFixedChargeAGibbsFullCone_source_factorization, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Every nonnegative three-mass ray has an actual full-support Gibbs realization on every grid. -/
theorem egbFixedChargeAGibbsFullCone_source_realizable (n : ℕ) (R A B : NNReal) :
    ∃ E : Fin (2 ^ (n + 3)) → ℝ, ∃ c : NNReal,
      0 < (c : ℝ) ∧ egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 E =
        c • egbFixedChargeAGibbsFullConeSource R A B ∧
          ∀ i, 0 < _root_.HTGeometry.finiteGibbsStateWeight 1 E i := by
  exact ⟨egbFixedChargeAGibbsFullConeEnergy n 0 R A B, egbFixedChargeAGibbsFullConeScale n 0 R A B,
    egbFixedChargeAGibbsFullConeScale_pos n 0 R A B, egbFixedChargeAGibbsFullCone_source_factorization n 0 R A B,
    egbFixedChargeAGibbsFullCone_probability_pos n 0 R A B⟩

/-- Removing the same known positive scale recovers every full-history moment from actual collisions. -/
theorem egbFixedChargeAGibbsFullCone_rescaled_collision (n k m : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) /
      (egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) =
        hausdorffMoment (egbFixedChargeAGibbsFullConeSource R A B) m := by
  rw [egbFixedChargeAGibbsFullCone_collision, egbFixedChargeAGibbsFullConeSource_moment]
  change _ / egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 = _
  have h := (egbFixedChargeAGibbsFullConeAmplitude_pos n k R A B).ne'
  field_simp [h]
  <;> ring

end
end GaloisForLFunctions.HTGeometry
