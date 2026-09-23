import GaloisForLFunctions.HTGeometry.ScaledBetaDirichletJacobiQEDSpinGaugeUniversalityLaw
import GaloisForLFunctions.RHTower.ThermalDeSitterZetaQuarterCrossCenterGammaSeparationUniversalityLaw
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Thermal/beta-QED/zeta three-Gamma-orbit superselection

Thermal/de Sitter reconstruction has an integral Gamma charge, the common scaled-beta/
Dirichlet/Jacobi-MANOVA/QED spin class has surviving integral and half-orbit charges, and
centered-zeta reconstruction has a quarter-orbit charge.  Their three pairwise quotients are
hypertranscendental, so the reconstructions occupy three distinct nonzero
differential-algebraic multiplicative gauge classes.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- A hypertranscendental quotient obstructs a nonzero DA multiplicative gauge. -/
theorem not_differentialAlgebraicGaugeEquivalent_of_div_hypertranscendental
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x y : E} (hy : y ≠ 0)
    (hxy : HypertranscendentalOver F (x / y)) :
    ¬ GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := F) x y := by
  rintro ⟨g, _hg0, hg, hxyEq⟩
  apply hxy
  rw [hxyEq, mul_div_cancel_right₀ g hy]
  exact hg

/-- Thermal/de Sitter positive-amplitude reconstruction. -/
def thermalDeSitterPositiveReconstructionMero
    (ell : ℕ) (lambda : ℂ) : meroField Set.univ :=
  thermalCFTFrequencyResponseMero (((ell + 1 : ℕ) : ℂ)) lambda *
    deSitterTypeIStaticBogoliubovGammaCarrierMero
      (coulombDeSitterZeroModeBranchMass ell) 0

/-- Centered-zeta positive quarter-amplitude reconstruction. -/
def centeredZetaPositiveReconstructionMero : meroField Set.univ :=
  centeredZetaGammaIntensityCoreMero ^ (2 : ℕ) /
    centeredZetaGammaPhaseObservationMero

/-- Quotient of thermal/de Sitter reconstruction by the QED spin-statistics carrier. -/
def thermalDeSitterQEDSpinCrossRatioMero
    (ell : ℕ) (lambda : ℂ) : meroField Set.univ :=
  thermalDeSitterPositiveReconstructionMero ell lambda /
    constantMagneticQEDSpinStatisticsRatioMero

/-- Rational recurrence and exponential gauge in the thermal/QED cross ratio. -/
def thermalDeSitterQEDSpinCrossGaugeMero
    (ell : ℕ) (lambda : ℂ) : meroField Set.univ :=
  algebraMap (RatFunc ℂ) (meroField Set.univ)
      (gammaOrbitNatFactor 1 ell) ^ (2 : ℕ) *
    physicalExponentialMero lambda

theorem thermalDeSitterQEDSpinCrossGaugeMero_ne_zero
    (ell : ℕ) (lambda : ℂ) :
    thermalDeSitterQEDSpinCrossGaugeMero ell lambda ≠ 0 := by
  rw [thermalDeSitterQEDSpinCrossGaugeMero]
  exact mul_ne_zero
    (pow_ne_zero 2 ((map_ne_zero_iff _
      (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).2
        (gammaOrbitNatFactor_ne_zero 1 ell)))
    (physicalExponentialMero_ne_zero lambda)

theorem differentialAlgebraicOver_thermalDeSitterQEDSpinCrossGaugeMero
    (ell : ℕ) (lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (thermalDeSitterQEDSpinCrossGaugeMero ell lambda) := by
  rw [thermalDeSitterQEDSpinCrossGaugeMero]
  exact HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_pow
      (HTGeometry.differentialAlgebraicOver_algebraMap _) 2)
    (differentialAlgebraicOver_physicalExponentialMero lambda)

/-- Recurrence cancels one integral Gamma charge and leaves the same-sign QED product. -/
theorem thermalDeSitterQEDSpinCrossRatioMero_eq_gauge_mul_combinedQED
    (ell : ℕ) (lambda : ℂ) :
    thermalDeSitterQEDSpinCrossRatioMero ell lambda =
      thermalDeSitterQEDSpinCrossGaugeMero ell lambda *
        constantMagneticQEDCombinedGammaCarrierMero := by
  have hshift := gammaShiftMero_add_nat (1 : ℂ) ell
  have hcenter : (1 : ℂ) + (ell : ℂ) = ((ell + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hcenter] at hshift
  have hmap :
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaOrbitNatFactor 1 ell) =
        algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor 1 ell) := rfl
  rw [hmap] at hshift
  rw [thermalDeSitterQEDSpinCrossRatioMero,
    thermalDeSitterPositiveReconstructionMero,
    thermalCFTResponse_mul_deSitterZeroModeCarrier_eq_orientedGammaSquare,
    constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticQEDCombinedGammaCarrierMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero,
    thermalDeSitterQEDSpinCrossGaugeMero,
    hshift]
  field_simp [gammaShiftMero_ne_zero]

/-- The thermal/QED class quotient is hypertranscendental. -/
theorem hypertranscendentalOver_thermalDeSitterQEDSpinCrossRatioMero
    (ell : ℕ) (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (thermalDeSitterQEDSpinCrossRatioMero ell lambda) := by
  rw [thermalDeSitterQEDSpinCrossRatioMero_eq_gauge_mul_combinedQED, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_thermalDeSitterQEDSpinCrossGaugeMero ell lambda)
    (thermalDeSitterQEDSpinCrossGaugeMero_ne_zero ell lambda)).2
      hypertranscendentalOver_constantMagneticQEDCombinedGammaCarrierMero

/-- Quotient of the QED/beta class by zeta's quarter reconstruction. -/
def QEDSpinCenteredZetaPositiveCrossRatioMero : meroField Set.univ :=
  constantMagneticQEDSpinStatisticsRatioMero /
    centeredZetaPositiveReconstructionMero

private theorem complex_half_sub_one_ne_integer (k : ℤ) :
    (1 / 2 : ℂ) - 1 ≠ (k : ℂ) := by
  intro h
  have htwo := congrArg (fun z : ℂ => 2 * z) h
  norm_num at htwo
  have hz : (-1 : ℤ) = 2 * k := by exact_mod_cast htwo
  omega

private theorem complex_quarter_sub_one_ne_integer (k : ℤ) :
    (1 / 4 : ℂ) - 1 ≠ (k : ℂ) := by
  intro h
  have hfour := congrArg (fun z : ℂ => 4 * z) h
  norm_num at hfour
  have hz : (-3 : ℤ) = 4 * k := by exact_mod_cast hfour
  omega

/-- Half- and quarter-orbit charges all survive in the QED/zeta quotient. -/
theorem hypertranscendentalOver_QEDSpinCenteredZetaPositiveCrossRatioMero :
    HypertranscendentalOver (RatFunc ℂ)
      QEDSpinCenteredZetaPositiveCrossRatioMero := by
  let shifts : Fin 3 → ℂ := ![1, (1 / 2 : ℂ), (1 / 4 : ℂ)]
  let charges : Fin 3 → ℤ := ![1, -1, -4]
  have hproduct : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero shifts charges) := by
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges 0
    · simp [charges]
    · intro i hi k
      fin_cases i
      · exact (hi rfl).elim
      · simpa [shifts] using complex_half_sub_one_ne_integer k
      · simpa [shifts] using complex_quarter_sub_one_ne_integer k
  rw [QEDSpinCenteredZetaPositiveCrossRatioMero,
    centeredZetaPositiveReconstructionMero,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth,
    constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero]
  convert hproduct using 1
  simp [gammaOrbitProductMero, shifts, charges, div_eq_mul_inv,
    Fin.prod_univ_three, gammaShiftMero_ne_zero]
  rfl

theorem constantMagneticQEDSpinStatisticsRatioMero_ne_zero :
    constantMagneticQEDSpinStatisticsRatioMero ≠ 0 := by
  rw [constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero]
  exact div_ne_zero (gammaShiftMero_ne_zero 1) (gammaShiftMero_ne_zero (1 / 2))

theorem centeredZetaPositiveReconstructionMero_ne_zero :
    centeredZetaPositiveReconstructionMero ≠ 0 := by
  rw [centeredZetaPositiveReconstructionMero,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth]
  exact pow_ne_zero 4 (gammaShiftMero_ne_zero (1 / 4))

/-- **Three-Gamma-orbit superselection law.** Integral thermal/de Sitter reconstruction, the
half-orbit beta/QED class, and quarter-orbit zeta reconstruction are pairwise DA-incomparable. -/
theorem thermalBetaQEDZeta_threeGammaOrbitSuperselectionUniversality
    (ell : ℕ) (lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (thermalDeSitterQEDSpinCrossRatioMero ell lambda) ∧
      HypertranscendentalOver (RatFunc ℂ)
        QEDSpinCenteredZetaPositiveCrossRatioMero ∧
      HypertranscendentalOver (RatFunc ℂ)
        (thermalDeSitterPositiveReconstructionMero ell lambda /
          centeredZetaPositiveReconstructionMero) ∧
      HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
        constantMagneticQEDSpinStatisticsRatioMero (scaledEulerBetaMero 1 1) ∧
      scaledEulerBetaMero 1 1 = (symmetricDirichletNormalizerMero 2)⁻¹ ∧
      jacobiMANOVAPartitionNormalizerMero 1 1 1 /
          gaussianBetaEnsemblePartitionNormalizerMero 1 =
        (symmetricDirichletNormalizerMero 2)⁻¹ ∧
      ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
        (thermalDeSitterPositiveReconstructionMero ell lambda)
        constantMagneticQEDSpinStatisticsRatioMero ∧
      ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
        constantMagneticQEDSpinStatisticsRatioMero
        centeredZetaPositiveReconstructionMero ∧
      ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
        (thermalDeSitterPositiveReconstructionMero ell lambda)
        centeredZetaPositiveReconstructionMero := by
  have hTZ : HypertranscendentalOver (RatFunc ℂ)
      (thermalDeSitterPositiveReconstructionMero ell lambda /
        centeredZetaPositiveReconstructionMero) := by
    simpa [thermalDeSitterPositiveReconstructionMero,
      centeredZetaPositiveReconstructionMero,
      thermalDeSitterCenteredZetaPositiveCrossRatioMero] using
        hypertranscendentalOver_thermalDeSitterCenteredZetaPositiveCrossRatioMero
          ell lambda
  refine ⟨hypertranscendentalOver_thermalDeSitterQEDSpinCrossRatioMero ell lambda,
    hypertranscendentalOver_QEDSpinCenteredZetaPositiveCrossRatioMero,
    hTZ, ?_, scaledEulerBetaMero_one_one_eq_inv_symmetricDirichlet,
    jacobiMANOVA_one_one_one_div_gaussian_eq_inv_symmetricDirichlet, ?_, ?_, ?_⟩
  · exact ⟨scaledBetaQEDSpinGaugeMero,
      scaledBetaQEDSpinGaugeMero_ne_zero,
      differentialAlgebraicOver_scaledBetaQEDSpinGaugeMero,
      constantMagneticQEDSpinStatisticsRatioMero_eq_gauge_mul_scaledEulerBeta⟩
  · exact not_differentialAlgebraicGaugeEquivalent_of_div_hypertranscendental
      constantMagneticQEDSpinStatisticsRatioMero_ne_zero
      (hypertranscendentalOver_thermalDeSitterQEDSpinCrossRatioMero ell lambda)
  · exact not_differentialAlgebraicGaugeEquivalent_of_div_hypertranscendental
      centeredZetaPositiveReconstructionMero_ne_zero
      hypertranscendentalOver_QEDSpinCenteredZetaPositiveCrossRatioMero
  · exact not_differentialAlgebraicGaugeEquivalent_of_div_hypertranscendental
      centeredZetaPositiveReconstructionMero_ne_zero hTZ

end

end RHTower
