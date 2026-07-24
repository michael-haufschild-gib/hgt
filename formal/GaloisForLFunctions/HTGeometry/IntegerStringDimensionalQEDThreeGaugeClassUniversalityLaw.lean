import GaloisForLFunctions.HTGeometry.DimensionalQEDGammaGaugePartitionUniversalityLaw
import GaloisForLFunctions.HTGeometry.GammaIntegerOrbitOpenClosedSpinUniversalityLaw

/-!
# Integer-string/dimensional-QED three-gauge-class universality

At an integer channel parameter, the generalized-spin, reduced open-string, and reduced
closed-string Gamma carriers are nonzero and differentially algebraic. Hence they occupy one
nonzero differential-algebraic multiplicative gauge class. The dimensional-QED partition and the
scale-one Gamma theorem expose two further hypertranscendental classes: bubble/triangle/scalar-QED
and spinor-QED. This module proves that these are exactly three distinct classes.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

namespace HTGeometry

/-- Any two nonzero differentially algebraic elements lie in the same nonzero DA gauge class. -/
theorem differentialAlgebraicGaugeEquivalent_of_nonzero_of_differentialAlgebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : E} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : DifferentialAlgebraicOver F x)
    (hy : DifferentialAlgebraicOver F y) :
    DifferentialAlgebraicGaugeEquivalent (F := F) x y := by
  exact ⟨x / y, div_ne_zero hx0 hy0, differentialAlgebraicOver_div hx hy,
    (div_mul_cancel₀ x hy0).symm⟩

/-- A DA element and an HT element cannot lie in the same nonzero DA gauge class. -/
theorem not_differentialAlgebraicGaugeEquivalent_of_differentialAlgebraic_of_hypertranscendental
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : E} (hx : DifferentialAlgebraicOver F x)
    (hy : HypertranscendentalOver F y) :
    ¬ DifferentialAlgebraicGaugeEquivalent (F := F) x y := by
  rintro ⟨g, hg0, hg, hxy⟩
  apply hy
  have hDA : DifferentialAlgebraicOver F (g⁻¹ * x) :=
    differentialAlgebraicOver_mul (differentialAlgebraicOver_inv hg) hx
  rw [hxy] at hDA
  simpa [hg0, mul_assoc] using hDA

end HTGeometry

local instance integerStringDimensionalQEDDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance integerStringDimensionalQEDDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance integerStringDimensionalQEDRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance integerStringDimensionalQEDRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance integerStringDimensionalQEDDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance integerStringDimensionalQEDCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Exact three-class certificate for the seven integer-string and dimensional-QED carriers.
The displayed equivalences generate each class; the three representative separations make the
classes pairwise distinct. -/
structure IntegerStringDimensionalQEDThreeGaugeClassCertificate (a N : ℂ) : Prop where
  integerStringCollapse :
    DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ∧
      DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a N)
  integerStringNonzero :
    generalizedSpinTowerChannelMero N ≠ 0 ∧
      reducedVenezianoAmplitudeMero a N ≠ 0 ∧
      reducedVirasoroShapiroAmplitudeMero a N ≠ 0
  spinOpen :
    HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      (generalizedSpinTowerChannelMero N) (reducedVenezianoAmplitudeMero a N)
  spinClosed :
    HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      (generalizedSpinTowerChannelMero N)
      (reducedVirasoroShapiroAmplitudeMero a N)
  dimensionalQED : DimensionalQEDGammaGaugePartitionCertificate
  scalarQEDHypertranscendental :
    HypertranscendentalOver (RatFunc ℂ) constantMagneticScalarQEDGammaCarrierMero
  spinorQEDHypertranscendental :
    HypertranscendentalOver (RatFunc ℂ) constantMagneticSpinorQEDGammaCarrierMero
  stringScalarSeparated :
    ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      (generalizedSpinTowerChannelMero N) constantMagneticScalarQEDGammaCarrierMero
  stringSpinorSeparated :
    ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      (generalizedSpinTowerChannelMero N) constantMagneticSpinorQEDGammaCarrierMero

/-- **Integer-string/dimensional-QED three-gauge-class law.** At every integer channel,
generalized-spin/open/closed carriers form one nonzero DA gauge class; bubble/triangle/scalar-QED
form a second HT class; spinor-QED forms a third HT class. -/
theorem integerStringDimensionalQED_threeGaugeClassUniversality
    (a N : ℂ) (hN : ∃ k : ℤ, N = (k : ℂ)) :
    IntegerStringDimensionalQEDThreeGaugeClassCertificate a N := by
  have hcollapse :=
    (gammaIntegerOrbit_openClosedSpin_simultaneousCollapse a N).1 hN
  have hnegative (b : ℂ) : gammaNegativeShiftMero b ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - b)))
  have hspin0 : generalizedSpinTowerChannelMero N ≠ 0 := by
    rw [generalizedSpinTowerChannelMero]
    exact div_ne_zero
      (mul_ne_zero (hnegative 1) (gammaShiftMero_ne_zero (1 + N)))
      (mul_ne_zero (gammaShiftMero_ne_zero 1) (hnegative (1 + N)))
  have hopen0 : reducedVenezianoAmplitudeMero a N ≠ 0 := by
    rw [reducedVenezianoAmplitudeMero]
    exact div_ne_zero (gammaShiftMero_ne_zero a) (gammaShiftMero_ne_zero (a + N))
  have hclosed0 : reducedVirasoroShapiroAmplitudeMero a N ≠ 0 := by
    rw [reducedVirasoroShapiroAmplitudeMero]
    exact div_ne_zero
      (mul_ne_zero (gammaShiftMero_ne_zero a) (hnegative (1 - a - N)))
      (mul_ne_zero (hnegative (1 - a)) (gammaShiftMero_ne_zero (a + N)))
  have hscalarHT :
      HypertranscendentalOver (RatFunc ℂ) constantMagneticScalarQEDGammaCarrierMero := by
    simpa [constantMagneticScalarQEDGammaCarrierMero] using
      (hypertranscendentalOver_gammaNatScaleMero
        (n := 1) (show 0 < 1 by norm_num) (1 / 2))
  have hspinorHT :
      HypertranscendentalOver (RatFunc ℂ) constantMagneticSpinorQEDGammaCarrierMero := by
    simpa [constantMagneticSpinorQEDGammaCarrierMero] using
      (hypertranscendentalOver_gammaNatScaleMero
        (n := 1) (show 0 < 1 by norm_num) 1)
  refine ⟨hcollapse, ⟨hspin0, hopen0, hclosed0⟩, ?_, ?_,
    dimensionalQEDGamma_gaugePartitionUniversality,
    hscalarHT, hspinorHT, ?_, ?_⟩
  · exact
      HTGeometry.differentialAlgebraicGaugeEquivalent_of_nonzero_of_differentialAlgebraic
        hspin0 hopen0 hcollapse.1 hcollapse.2.1
  · exact
      HTGeometry.differentialAlgebraicGaugeEquivalent_of_nonzero_of_differentialAlgebraic
        hspin0 hclosed0 hcollapse.1 hcollapse.2.2
  · exact
      HTGeometry.not_differentialAlgebraicGaugeEquivalent_of_differentialAlgebraic_of_hypertranscendental
        hcollapse.1 hscalarHT
  · exact
      HTGeometry.not_differentialAlgebraicGaugeEquivalent_of_differentialAlgebraic_of_hypertranscendental
        hcollapse.1 hspinorHT

end

end GaloisForLFunctions
