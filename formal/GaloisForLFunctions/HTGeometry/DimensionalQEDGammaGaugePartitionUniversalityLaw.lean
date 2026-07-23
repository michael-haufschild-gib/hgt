import GaloisForLFunctions.HTGeometry.ConstantFieldQEDGammaClock
import GaloisForLFunctions.HTGeometry.DimensionalRegularizationGammaBoundary

/-!
# Dimensional/QED Gamma gauge-partition universality

The exact orbit normal forms for the dimensionally regulated bubble and triangle meet the
constant-field QED determinant carriers at the literal half-shift Gamma clock.  This module first
extracts the universal nonzero differential-algebraic multiplicative-gauge equivalence relation.
It then proves that the scalar-QED, bubble, and triangle carriers occupy one gauge class, whereas
the spinor-QED carrier occupies a distinct class.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

namespace HTGeometry

/-- Two nonzero observables are in the same differential-algebraic multiplicative gauge class
when one is a nonzero DA multiple of the other. -/
def DifferentialAlgebraicGaugeEquivalent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x y : E) : Prop :=
  ∃ g : E, g ≠ 0 ∧ DifferentialAlgebraicOver F g ∧ x = g * y

/-- Nonzero DA-gauge equivalence is reflexive. -/
theorem differentialAlgebraicGaugeEquivalent_refl
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) :
    DifferentialAlgebraicGaugeEquivalent (F := F) x x := by
  refine ⟨1, one_ne_zero, ?_, by simp⟩
  simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) (1 : F)

/-- Nonzero DA-gauge equivalence is symmetric. -/
theorem differentialAlgebraicGaugeEquivalent_symm
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y : E}
    (h : DifferentialAlgebraicGaugeEquivalent (F := F) x y) :
    DifferentialAlgebraicGaugeEquivalent (F := F) y x := by
  obtain ⟨g, hg0, hg, hxy⟩ := h
  refine ⟨g⁻¹, inv_ne_zero hg0, differentialAlgebraicOver_inv hg, ?_⟩
  rw [hxy]
  simp [hg0]

/-- Nonzero DA-gauge equivalence is transitive. -/
theorem differentialAlgebraicGaugeEquivalent_trans
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {x y z : E}
    (hxy : DifferentialAlgebraicGaugeEquivalent (F := F) x y)
    (hyz : DifferentialAlgebraicGaugeEquivalent (F := F) y z) :
    DifferentialAlgebraicGaugeEquivalent (F := F) x z := by
  obtain ⟨g, hg0, hg, rfl⟩ := hxy
  obtain ⟨h, hh0, hh, rfl⟩ := hyz
  exact ⟨g * h, mul_ne_zero hg0 hh0, differentialAlgebraicOver_mul hg hh, by ring⟩

end HTGeometry

local instance dimensionalQEDGaugePartitionDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance dimensionalQEDGaugePartitionDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance dimensionalQEDGaugePartitionRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance dimensionalQEDGaugePartitionRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance dimensionalQEDGaugePartitionDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance dimensionalQEDGaugePartitionCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Exact four-carrier gauge partition exposed by the shared half-shift Gamma orbit. -/
structure DimensionalQEDGammaGaugePartitionCertificate : Prop where
  bubbleScalar : HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
    masslessBubbleGammaMero constantMagneticScalarQEDGammaCarrierMero
  triangleScalar : HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
    masslessTriangleGammaMero constantMagneticScalarQEDGammaCarrierMero
  spinorScalar : ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
    constantMagneticSpinorQEDGammaCarrierMero constantMagneticScalarQEDGammaCarrierMero
  spinorBubble : ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
    constantMagneticSpinorQEDGammaCarrierMero masslessBubbleGammaMero
  spinorTriangle : ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
    constantMagneticSpinorQEDGammaCarrierMero masslessTriangleGammaMero

/-- **Dimensional/QED Gamma gauge-partition law.**  Bubble, triangle, and scalar-QED carriers
occupy one nonzero DA-gauge class, while spinor-QED is separated from all three. -/
theorem dimensionalQEDGamma_gaugePartitionUniversality :
    DimensionalQEDGammaGaugePartitionCertificate := by
  have hv0 : reducedVenezianoAmplitudeMero (-1 / 2) 1 ≠ 0 := by
    rw [reducedVenezianoAmplitudeMero]
    exact div_ne_zero (gammaShiftMero_ne_zero (-1 / 2))
      (gammaShiftMero_ne_zero ((-1 / 2) + 1))
  have hvDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (reducedVenezianoAmplitudeMero (-1 / 2) 1) :=
    (differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
      (-1 / 2) 1).2 ⟨1, by norm_num⟩
  have hbubble : HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      masslessBubbleGammaMero constantMagneticScalarQEDGammaCarrierMero := by
    refine ⟨masslessBubbleGammaGaugeMero *
        reducedVenezianoAmplitudeMero (-1 / 2) 1,
      mul_ne_zero masslessBubbleGammaGaugeMero_ne_zero hv0,
      HTGeometry.differentialAlgebraicOver_mul
        differentialAlgebraicOver_masslessBubbleGammaGaugeMero hvDA, ?_⟩
    rw [masslessBubbleGammaMero_normalForm,
      constantMagneticScalarQEDGammaCarrierMero,
      reducedVenezianoAmplitudeMero]
    norm_num
    rw [mul_assoc, div_mul_cancel₀ _ (gammaShiftMero_ne_zero (1 / 2))]
  have htriangle : HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      masslessTriangleGammaMero constantMagneticScalarQEDGammaCarrierMero := by
    exact ⟨masslessTriangleGammaGaugeMero,
      masslessTriangleGammaGaugeMero_ne_zero,
      differentialAlgebraicOver_masslessTriangleGammaGaugeMero,
      by rw [masslessTriangleGammaMero_normalForm,
        constantMagneticScalarQEDGammaCarrierMero]⟩
  have hspinorScalar : ¬ HTGeometry.DifferentialAlgebraicGaugeEquivalent (F := RatFunc ℂ)
      constantMagneticSpinorQEDGammaCarrierMero
        constantMagneticScalarQEDGammaCarrierMero := by
    rintro ⟨g, _, hg, heq⟩
    exact constantMagneticSpinorQEDGammaCarrierMero_ne_da_mul_scalar g hg heq
  refine ⟨hbubble, htriangle, hspinorScalar, ?_, ?_⟩
  · intro hspinorBubble
    exact hspinorScalar
      (HTGeometry.differentialAlgebraicGaugeEquivalent_trans hspinorBubble hbubble)
  · intro hspinorTriangle
    exact hspinorScalar
      (HTGeometry.differentialAlgebraicGaugeEquivalent_trans hspinorTriangle htriangle)

end

end GaloisForLFunctions
