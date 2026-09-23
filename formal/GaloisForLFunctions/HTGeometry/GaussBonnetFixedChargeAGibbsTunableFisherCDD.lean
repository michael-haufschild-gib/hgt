import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableSourceIdentification
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionCDDPhase

/-! # Scattering-phase recovery from two thermal Fisher observations
The CDD construction is the corpus's mathematical source-to-phase realization;
it is not an extra physical claim about the black-hole paper. -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The recovered source generates a phase with exactly the reconstructed relative shell mass. -/
theorem egbFixedChargeAGibbsTunable_normalized_CDD_phase (t θ : ℝ) :
    hausdorffCDDPhase (egbFixedChargeAGibbsTunableNormalizedSource t) θ =
      cddPhaseKernel (4 / 9) θ + t ^ (2 : ℕ) * cddPhaseKernel (1 / 36) θ := by
  rw [egbFixedChargeAGibbsTunableNormalizedSource, hausdorffCDDPhase_add,
    hausdorffCDDPhase_atom, hausdorffCDDPhase_atom]
  change (1 : ℝ) * cddPhaseKernel (4 / 9) θ + t ^ (2 : ℕ) * cddPhaseKernel (1 / 36) θ = _
  ring

/-- Normalizing the actual Gibbs phase by its positive slow source mass recovers the literal survivor phase. -/
theorem egbFixedChargeAGibbsTunable_CDD_phase_normalization (n k m : ℕ) (t θ : ℝ) :
    egbFixedChargeAGibbsCollisionCDDPhase n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) θ /
      (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) =
        hausdorffCDDPhase (egbFixedChargeAGibbsTunableNormalizedSource t) θ := by
  rw [egbFixedChargeAGibbsCollisionCDDPhase_formula]
  change ((egbFixedChargeAGibbsCollisionSlowSourceMass n m 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) * cddPhaseKernel (4 / 9) θ +
    (egbFixedChargeAGibbsCollisionFastSourceMass n m 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) * cddPhaseKernel (1 / 36) θ) / _ = _
  rw [egbFixedChargeAGibbsTunable_source_mass_ratio, egbFixedChargeAGibbsTunable_normalized_CDD_phase]
  have hx := egbFixedChargeAGibbsTunable_slow_mass_pos n k m t
  change 0 < (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) at hx
  change ((egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) * _ +
    ((egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) * t ^ (2 : ℕ)) * _) / _ = _
  generalize (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) = x at hx ⊢
  field_simp
  <;> ring

/-- Two actual Fisher observations reconstruct the normalized CDD phase at every real rapidity. -/
theorem egbFixedChargeAGibbsTunable_CDD_phase_decode (n k m : ℕ) (t θ : ℝ) :
    hausdorffCDDPhase (egbFixedChargeAGibbsTunableNormalizedSource t) θ =
      cddPhaseKernel (4 / 9) θ +
        egbFixedChargeAGibbsFisherRatioDecoder
          (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t))
          (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t)) *
        cddPhaseKernel (1 / 36) θ := by
  rw [egbFixedChargeAGibbsTunable_fisher_ratio_decode, egbFixedChargeAGibbsTunable_normalized_CDD_phase]

/-- One additional unnormalized mass fixes the actual phase amplitude left invisible by the Fisher pair. -/
theorem egbFixedChargeAGibbsTunable_CDD_phase_full_decode (n k m : ℕ) (t θ : ℝ) :
    egbFixedChargeAGibbsCollisionCDDPhase n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) θ =
      (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) *
        (cddPhaseKernel (4 / 9) θ +
          egbFixedChargeAGibbsFisherRatioDecoder
            (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t))
            (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t)) *
          cddPhaseKernel (1 / 36) θ) := by
  have h := egbFixedChargeAGibbsTunable_CDD_phase_normalization n k m t θ
  rw [egbFixedChargeAGibbsTunable_CDD_phase_decode n k m t θ] at h
  have hx := egbFixedChargeAGibbsTunable_slow_mass_pos n k m t
  change 0 < (egbFixedChargeAGibbsTunableSourceMass n k m t : ℝ) at hx
  calc
    _ = _ := (div_eq_iff hx.ne').1 h
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry
