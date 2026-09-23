import GaloisForLFunctions.HTGeometry.CoulombDeSitterZeroModeObservabilityUniversalityLaw
import GaloisForLFunctions.HTGeometry.GammaSameSignProductBoundary
import GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Thermal/de Sitter oriented-Gamma tomography universality

At every Coulomb partial wave, the integral-weight thermal response is differentially algebraic
and the corresponding de Sitter angular-zero carrier has unit intensity while remaining
hypertranscendental.  Multiplying the two cancels the reflected Gamma factor and reconstructs a
positive-charge Gamma square times an elementary exponential.  The reconstructed product is
therefore hypertranscendental.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The thermal response cancels the negative-slope Gamma factor in the de Sitter zero-mode
carrier and reconstructs an oriented Gamma square. -/
theorem thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare
    (ell : ℕ) (lambda : ℂ) :
    thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
        deSitterTypeIStaticBogoliubovGammaCarrierMero
          (coulombDeSitterZeroModeBranchMass ell) 0 =
      gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ (2 : ℕ) *
        physicalExponentialMero lambda := by
  rw [deSitterZeroModeGammaCarrier_eq_coulombPhase,
    thermalCFTFrequencyResponseMero, gammaReflectionProductMero,
    coulombPhaseMero]
  have hn : gammaNegativeShiftMero (((ell + 1 : ℕ) : ℂ)) ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero _)
      (inv_ne_zero (gammaShiftMero_ne_zero _))
  field_simp [hn]

/-- Integral Coulomb weights lie on the differentially algebraic side of the thermal-response
boundary. -/
theorem differentialAlgebraicOver_thermalCFTResponse_coulombWeight
    (ell : ℕ) (lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda) := by
  apply (differentialAlgebraicOver_thermalCFTFrequencyResponseMero_iff_integerWeight
    (((ell + 1 : ℕ) : ℂ)) lambda).2
  refine ⟨-(2 * (ell : ℤ) + 1), ?_⟩
  push_cast
  ring

/-- The unit-intensity de Sitter zero-mode carrier retains the Coulomb phase's oriented
hypertranscendence. -/
theorem hypertranscendentalOver_deSitterZeroModeGammaCarrier (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (deSitterTypeIStaticBogoliubovGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0) := by
  rw [deSitterZeroModeGammaCarrier_eq_coulombPhase]
  exact hypertranscendentalOver_coulombPhaseMero ell

/-- The reconstructed oriented Gamma square remains hypertranscendental even though its thermal
factor is differentially algebraic. -/
theorem hypertranscendentalOver_thermalCFTResponse_mul_deSitterZeroModeCarrier
    (ell : ℕ) (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
        deSitterTypeIStaticBogoliubovGammaCarrierMero
          (coulombDeSitterZeroModeBranchMass ell) 0) := by
  rw [thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare]
  have hgamma : HypertranscendentalOver (RatFunc ℂ)
      (gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ (2 : ℕ)) := by
    have h := hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
      (fun _ : Fin 1 => (((ell + 1 : ℕ) : ℂ)))
      (fun _ : Fin 1 => (2 : ℤ)) (by intro i; norm_num)
    simpa [gammaFintypeOrbitProductMero] using! h
  exact
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero lambda)
      (physicalExponentialMero_ne_zero lambda)).2 hgamma

/-- **Thermal/de Sitter oriented-Gamma tomography universality.**  A differentially algebraic
thermal magnitude channel and a unit-intensity de Sitter phase carrier reconstruct an
orientation-sensitive hypertranscendental Gamma square. -/
theorem thermalDeSitter_orientedGammaTomographyUniversality
    (ell : ℕ) (lambda : ℂ) :
    thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
          deSitterTypeIStaticBogoliubovGammaCarrierMero
            (coulombDeSitterZeroModeBranchMass ell) 0 =
        gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ (2 : ℕ) *
          physicalExponentialMero lambda ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda) ∧
      deSitterTypeIStaticBogoliubovIntensityMero
          (coulombDeSitterZeroModeBranchMass ell) 0 = 1 ∧
      HypertranscendentalOver (RatFunc ℂ)
        (deSitterTypeIStaticBogoliubovGammaCarrierMero
          (coulombDeSitterZeroModeBranchMass ell) 0) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
          deSitterTypeIStaticBogoliubovGammaCarrierMero
            (coulombDeSitterZeroModeBranchMass ell) 0) :=
  ⟨thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare ell lambda,
    differentialAlgebraicOver_thermalCFTResponse_coulombWeight ell lambda,
    (coulombDeSitter_zeroModeObservabilityUniversality ell).2.2.2.2.2,
    hypertranscendentalOver_deSitterZeroModeGammaCarrier ell,
    hypertranscendentalOver_thermalCFTResponse_mul_deSitterZeroModeCarrier ell lambda⟩

end

end GaloisForLFunctions
