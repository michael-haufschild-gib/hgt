import GaloisForLFunctions.HilbertMetric.CCRFiniteBlockObstruction
import GaloisForLFunctions.HilbertMetric.CCRScaleCalibration

/-!
# Closed finite matrix-mechanics consequences of the CCR interface

The abstract CCR obstruction, invariant-block replacement, variance law, and scale calibration are
specialized to one mode on a two-level compression. Every theorem is a closed proposition.
-/

namespace GaloisForLFunctions.HilbertMetric

open Set

/-- One-mode two-level full CCR is impossible, while the invariant block CCR is realized. -/
theorem oneMode_twoLevel_fullCCR_obstructed_blockCCR_realized :
    (¬ ∃ T : Fin 1 →
        Matrix (Fin 2 ⊕ (Fin 1 × Fin 2)) (Fin 2 ⊕ (Fin 1 × Fin 2)) ℝ,
        IsFullCCRMatrixTuple T) ∧
      ∃ T : Fin 1 →
        Matrix (Fin 2 ⊕ (Fin 1 × Fin 2)) (Fin 2 ⊕ (Fin 1 × Fin 2)) ℝ,
        IsInvariantFullCompression T ∧
          IsCommutingFullTuple T ∧
            IsCommutingCCRCompression (fullCCRCompressionBlock T) ∧
              IsBlockCCRMatrixTuple T :=
  isFullCCRMatrixTuple_empty_and_isBlockCCRMatrixTuple_inhabited
    (I := Fin 1) (n := Fin 2)

/-- In one mode, scalar-compression number variance exactly equals mean energy. -/
theorem oneMode_twoLevel_numberVariance_eq_meanEnergy :
    ccrNumberVariance
        (fun _ : Fin 1 => (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (unitModeLeakage (I := Fin 1) (n := Fin 2)) =
      ccrMeanEnergy
        (fun _ : Fin 1 => (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ccrNumberVariance_scalar_eq_ccrMeanEnergy (c := fun _ : Fin 1 => 1)

/-- Closed one-mode two-level scale-sandwich law. -/
theorem oneMode_twoLevel_scaleSandwich :
    ConvexOn ℝ univ
        (logarithmicReparametrization (fun t => (Fintype.card (Fin 2) : ℝ) * t)) ∧
      ConcaveOn ℝ (Ioi 0)
        (dimensionPowerReparametrization (Fintype.card (Fin 1) : ℝ)
          (fun t => (Fintype.card (Fin 2) : ℝ) * t)) :=
  ccr_scaleSandwich_sqrtScalar (I := Fin 1) (n := Fin 2)

/-- A fully calibrated one-mode two-level invariant block tuple exists. -/
theorem oneMode_twoLevel_calibrated_fullCCRTuple_exists :
    ∃ (T : ℝ → Fin 1 →
        Matrix (Fin 2 ⊕ (Fin 1 × Fin 2)) (Fin 2 ⊕ (Fin 1 × Fin 2)) ℝ)
        (F F₁ F₂ : ℝ → ℝ),
      (∀ t, 0 < t → IsInvariantFullCompression (T t)) ∧
      (∀ t, 0 < t → IsCommutingCCRCompression (fullCCRCompressionBlock (T t))) ∧
      (∀ t, 0 < t → IsBlockCCRMatrixTuple (T t)) ∧
      (∀ t, 0 < t → HasDerivAt F (F₁ t) t) ∧
      (∀ t, 0 < t → HasDerivAt F₁ (F₂ t) t) ∧
      (∀ t, 0 < t →
        logarithmicScaleMean F₁ t = ccrMeanEnergy (fullCCRCompressionBlock (T t))) ∧
      (∀ t, 0 < t → logarithmicScaleVariance F₁ F₂ t =
        ccrNumberVariance (fullCCRCompressionBlock (T t))
          (fullCCRLeakageBlock (T t))) :=
  exists_calibrated_fullCCRTuple (I := Fin 1) (n := Fin 2)

end GaloisForLFunctions.HilbertMetric
