import GaloisForLFunctions.HTGeometry.ThermalDeSitterOrientedGammaTomographyUniversalityLaw
import GaloisForLFunctions.RHTower.ZetaHorizonGammaIntensitySeparation
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Thermal/de Sitter--zeta quarter cross-center Gamma separation

Thermal/de Sitter tomography reconstructs a positive Gamma square at every integral Coulomb
center. Centered-zeta phase--intensity tomography reconstructs a positive Gamma fourth power at
the quarter center. Their quotient carries signed charges on two distinct integer-translation
orbits, so it remains hypertranscendental under every thermal exponential gauge and admits no
differentially algebraic multiplicative calibration.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

private theorem complex_quarter_sub_nat_ne_integer (n : ℕ) (k : ℤ) :
    (1 / 4 : ℂ) - (n : ℂ) ≠ (k : ℂ) := by
  intro h
  have hfour := congrArg (fun z : ℂ => 4 * z) h
  have hreal := congrArg Complex.re hfour
  norm_num [mul_sub] at hreal
  have hz : (1 : ℤ) = 4 * ((n : ℤ) + k) := by
    exact_mod_cast (show (1 : ℝ) = 4 * ((n : ℝ) + (k : ℝ)) by linarith)
  omega

/-- The integral Coulomb center and zeta's quarter center support a signed Gamma ratio that is
hypertranscendental over the rational coordinate field. -/
theorem hypertranscendentalOver_thermalDeSitterZetaQuarter_crossCenterGammaRatio
    (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ 2 /
        gammaShiftMero (1 / 4) ^ 4) := by
  let shifts : Fin 2 → ℂ := ![(((ell + 1 : ℕ) : ℂ)), (1 / 4 : ℂ)]
  let charges : Fin 2 → ℤ := ![2, -4]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges 0
    · simp [charges]
    · intro i hi k
      fin_cases i
      · exact (hi rfl).elim
      · simpa [shifts] using complex_quarter_sub_nat_ne_integer (ell + 1) k
  simpa [gammaOrbitProductMero, shifts, charges, div_eq_mul_inv] using hproduct

/-- Quotient of the thermal/de Sitter positive-amplitude reconstruction by the centered-zeta
positive-amplitude reconstruction. -/
def thermalDeSitterCenteredZetaPositiveCrossRatioMero
    (ell : ℕ) (lambda : ℂ) : meroField Set.univ :=
  (thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
      deSitterTypeIStaticBogoliubovGammaCarrierMero
        (coulombDeSitterZeroModeBranchMass ell) 0) /
    (centeredZetaGammaIntensityCoreMero ^ 2 /
      centeredZetaGammaPhaseObservationMero)

theorem hypertranscendentalOver_thermalDeSitterCenteredZetaPositiveCrossRatioMero
    (ell : ℕ) (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (thermalDeSitterCenteredZetaPositiveCrossRatioMero ell lambda) := by
  rw [thermalDeSitterCenteredZetaPositiveCrossRatioMero,
    thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth]
  have hgamma :=
    hypertranscendentalOver_thermalDeSitterZetaQuarter_crossCenterGammaRatio ell
  have hgauged : HypertranscendentalOver (RatFunc ℂ)
      ((gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ 2 /
          gammaShiftMero (1 / 4) ^ 4) * physicalExponentialMero lambda) :=
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero lambda)
      (physicalExponentialMero_ne_zero lambda)).2 hgamma
  convert hgauged using 1
  ring

/-- No differentially algebraic multiplicative gauge converts the thermal/de Sitter
reconstruction into the centered-zeta quarter reconstruction. -/
theorem thermalDeSitterReconstruction_ne_da_mul_centeredZetaPositiveReconstruction
    (ell : ℕ) (lambda : ℂ) (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
        deSitterTypeIStaticBogoliubovGammaCarrierMero
          (coulombDeSitterZeroModeBranchMass ell) 0 ≠
      g * (centeredZetaGammaIntensityCoreMero ^ 2 /
        centeredZetaGammaPhaseObservationMero) := by
  intro heq
  apply hypertranscendentalOver_thermalDeSitterCenteredZetaPositiveCrossRatioMero ell lambda
  rw [thermalDeSitterCenteredZetaPositiveCrossRatioMero, heq]
  have hden : centeredZetaGammaIntensityCoreMero ^ 2 /
      centeredZetaGammaPhaseObservationMero ≠ 0 := by
    rw [centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth]
    exact pow_ne_zero 4 (gammaShiftMero_ne_zero (1 / 4))
  simpa [hden] using hg

/-- **Thermal/de Sitter--zeta quarter cross-center Gamma-separation universality law.** The two
tomography channels reconstruct positive Gamma amplitudes on permanently separated translation
orbits; their quotient is hypertranscendental and no DA calibration identifies them. -/
theorem thermalDeSitter_centeredZetaQuarter_crossCenterGammaSeparationUniversality
    (ell : ℕ) (lambda : ℂ) :
    thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
          deSitterTypeIStaticBogoliubovGammaCarrierMero
            (coulombDeSitterZeroModeBranchMass ell) 0 =
        gammaShiftMero (((ell + 1 : ℕ) : ℂ)) ^ 2 *
          physicalExponentialMero lambda ∧
      centeredZetaGammaIntensityCoreMero ^ 2 /
          centeredZetaGammaPhaseObservationMero =
        gammaShiftMero (1 / 4) ^ 4 ∧
      HypertranscendentalOver (RatFunc ℂ)
        (thermalDeSitterCenteredZetaPositiveCrossRatioMero ell lambda) ∧
      ∀ g : meroField Set.univ,
        DifferentialAlgebraicOver (RatFunc ℂ) g →
          thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
              deSitterTypeIStaticBogoliubovGammaCarrierMero
                (coulombDeSitterZeroModeBranchMass ell) 0 ≠
            g * (centeredZetaGammaIntensityCoreMero ^ 2 /
              centeredZetaGammaPhaseObservationMero) := by
  exact ⟨thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare ell lambda,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth,
    hypertranscendentalOver_thermalDeSitterCenteredZetaPositiveCrossRatioMero ell lambda,
    fun g hg =>
      thermalDeSitterReconstruction_ne_da_mul_centeredZetaPositiveReconstruction
        ell lambda g hg⟩

end

end RHTower
