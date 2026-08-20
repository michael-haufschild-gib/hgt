import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import GaloisForLFunctions.HTGeometry.DerivationLowerJetJacobianWitness
import GaloisForLFunctions.HTGeometry.HeisenbergHorizonRepresentation
import GaloisForLFunctions.RHTower.L2FourierUncertainty
import GaloisForLFunctions.RHTower.BandUncertainty
import GaloisForLFunctions.HilbertMetric.CCRFiniteBlockObstruction
import GaloisForLFunctions.HilbertMetric.CCRScaleCalibration

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev FreeNatShiftField := FreeCoordinateRationalField ℂ ℕ

def freeNatShiftDerivation : Derivation ℂ FreeNatShiftField FreeNatShiftField :=
  extendFreeCoordinatePolynomialDerivation natShiftDerivation

@[simp]
theorem freeNatShiftDerivation_freeCoordinate (k : ℕ) :
    freeNatShiftDerivation (freeCoordinate ℂ ℕ k) = freeCoordinate ℂ ℕ (k + 1) := by
  rw [freeNatShiftDerivation, freeCoordinate,
    extendFreeCoordinatePolynomialDerivation_algebraMap, natShiftDerivation_X]

theorem freeCoordinate_canonical_commutation (i : ℕ) :
    ⁅derivationEndomorphism (freeCoordinateDerivation ℂ ℕ i),
        Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ i)⁆ =
      LinearMap.id := by
  rw [derivationEndomorphism_commutator_multiplication,
    freeCoordinateDerivation_freeCoordinate_self]
  ext f
  simp

theorem freeNatShift_heisenberg_commutator (k : ℕ) :
    ⁅derivationEndomorphism freeNatShiftDerivation,
        Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ k)⁆ =
      Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ (k + 1)) := by
  rw [derivationEndomorphism_commutator_multiplication,
    freeNatShiftDerivation_freeCoordinate]

theorem freeNatShiftDerivation_iterate_freeCoordinate (n k : ℕ) :
    ((freeNatShiftDerivation : FreeNatShiftField → FreeNatShiftField)^[n])
        (freeCoordinate ℂ ℕ k) = freeCoordinate ℂ ℕ (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        freeNatShiftDerivation_freeCoordinate]
      congr 2
      omega

theorem freeNatShift_heisenbergJetOperator (n : ℕ) :
    heisenbergJetOperator freeNatShiftDerivation (freeCoordinate ℂ ℕ 0) n =
      Algebra.lmul ℂ FreeNatShiftField (freeCoordinate ℂ ℕ n) := by
  rw [heisenbergJetOperator_eq_multiplication,
    freeNatShiftDerivation_iterate_freeCoordinate]
  simp

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set FourierTransform
open scoped FourierTransform

theorem no_nonzero_integrable_bicompact_fourier_pair :
    ¬ ∃ (f : ℝ → ℂ) (a b : ℝ),
      Integrable f ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → f x = 0) ∧
        (∀ᵐ w ∂volume,
          w ∉ Icc (-b) b → FourierTransform.fourier f w = 0) ∧
        ¬ f =ᵐ[volume] 0 := by
  rintro ⟨f, a, b, hf, hs, hF, hne⟩
  exact hne (integrable_fourier_uncertainty hf hs hF)

theorem no_nonzero_l2_bicompact_fourier_pair :
    ¬ ∃ (f : Lp ℂ 2 (volume : Measure ℝ)) (a b : ℝ),
      f ≠ 0 ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0) ∧
        (∀ᵐ w ∂volume, w ∉ Icc (-b) b →
          (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) := by
  rintro ⟨f, a, b, hne, hs, hF⟩
  exact hne (l2_fourier_uncertainty f hs hF)

theorem no_nonzero_bounded_l2_with_fourier_spectral_gap :
    ¬ ∃ (f : Lp ℂ 2 (volume : Measure ℝ)) (a c d : ℝ),
      f ≠ 0 ∧ c < d ∧
        (∀ᵐ x ∂volume, x ∉ Icc (-a) a → (f : ℝ → ℂ) x = 0) ∧
        (∀ᵐ w ∂volume, w ∈ Ioo c d →
          (((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = 0)) := by
  rintro ⟨f, a, c, d, hne, hcd, hs, hF⟩
  exact hne (l2_eq_zero_of_bounded_support_fourier_vanishes_on_Ioo f hs hcd hF)

theorem no_band_interior_signal_with_zero_spectral_tail :
    ¬ ∃ (c : ℝ) (Φ : ℝ → ℝ) (x : ℝ),
      0 < c ∧ Continuous Φ ∧ x ∈ Ioo (-1 : ℝ) 1 ∧ Φ x ≠ 0 ∧
        (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
          ‖𝓕 (bandTrunc Φ) ξ‖ ^ 2) = 0 := by
  rintro ⟨c, Φ, x, hc, hΦ, hx, hne, htail⟩
  exact hne (eqOn_zero_of_spectral_tail_eq_zero hc hΦ htail x hx)

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.HilbertMetric

open Set

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

theorem oneMode_twoLevel_numberVariance_eq_meanEnergy :
    ccrNumberVariance
        (fun _ : Fin 1 => (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (unitModeLeakage (I := Fin 1) (n := Fin 2)) =
      ccrMeanEnergy
        (fun _ : Fin 1 => (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ccrNumberVariance_scalar_eq_ccrMeanEnergy (c := fun _ : Fin 1 => 1)

theorem oneMode_twoLevel_scaleSandwich :
    ConvexOn ℝ univ
        (logarithmicReparametrization (fun t => (Fintype.card (Fin 2) : ℝ) * t)) ∧
      ConcaveOn ℝ (Ioi 0)
        (dimensionPowerReparametrization (Fintype.card (Fin 1) : ℝ)
          (fun t => (Fintype.card (Fin 2) : ℝ) * t)) :=
  ccr_scaleSandwich_sqrtScalar (I := Fin 1) (n := Fin 2)

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
