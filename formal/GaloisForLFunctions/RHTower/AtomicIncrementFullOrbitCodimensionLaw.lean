import GaloisForLFunctions.RHTower.XiAtomicIncrementCorrection
import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid

/-!
# Atomic increments force the full completed-Xi translation orbit

`AtomicIncrementPrimitive` proves the abstract finite-rank amplification theorem: algebraically
independent translates of one affine increment force algebraic independence of every primitive
translation jet.  `XiAtomicIncrementCorrection` identifies the exposed von Mangoldt source with
the affine `+2` increment of the completed-Xi logarithmic derivative and applies that theorem over
both Nagoshi's small-growth field and the rational-coordinate field.

This file closes the remaining finite-superposition clause.  On every finite packet of distinct
complex shifts, arbitrary constant-coefficient differential-operator rows represent exactly their
localized polynomial row matroid.  Consequently every nonlinear differential-algebraic dependence
among the outputs is already forced by an ordinary differential-linear dependence among the rows.
-/

open Complex Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] xiAtomicUpperEndDomain
attribute [local instance] xiAtomicUpperEndComplexAlgebra
attribute [local instance] xiAtomicUpperEndDifferential
attribute [local instance] xiAtomicUpperEndCharZero
attribute [local instance] xiAtomicRationalBaseDifferential
attribute [local instance] xiAtomicRationalBaseDifferentialAlgebra

local instance atomicCapstoneComplexDifferential : Differential ℂ where
  deriv := 0

local instance atomicCapstoneComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c => by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

/-- **Completed-Xi atomic-increment capstone.**  The filtered von Mangoldt family is the exact
affine increment family of the completed logarithmic derivative, and the resulting primitive jet
family is algebraically independent over both Nagoshi's small-growth field and the genuine
rational-coordinate field.  The two differential-independence statements are the orbit form of
the same conclusion. -/
theorem xiAtomicIncrement_fullOrbitCodimension_complete :
    (∀ hk : ℂ × ℕ,
      differentialJet hk.2
          (upperEndTranslationMeroEquiv (I * hk.1)
            filteredVonMangoldtUpperEndCarrier) =
        xiLogDerivRotatedFullComplexShiftJets
            (GaloisForLFunctions.MatroidGluing.complexJetEvenShift hk) -
          xiLogDerivRotatedFullComplexShiftJets hk -
          algebraMap SmallGrowthMeromorphicField upperEndMeroField
            (xiShiftTwoRationalCorrectionSmallGrowthJet hk)) ∧
    AlgebraicIndependent SmallGrowthMeromorphicField
      xiLogDerivRotatedFullComplexShiftJets ∧
    AlgebraicIndependent upperEndRationalCoordinateField
      xiLogDerivRotatedFullComplexShiftJets ∧
    DifferentialIndependent SmallGrowthMeromorphicField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiLogDerivRotatedUpperEndCarrier) ∧
    DifferentialIndependent upperEndRationalCoordinateField
      (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
        xiLogDerivRotatedUpperEndCarrier) := by
  exact ⟨filteredVonMangoldt_fullComplexShiftJets_eq_xi_affineIncrement,
    xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent_over_smallGrowth,
    xiLogDerivRotated_fullComplexShiftJets_algebraicIndependent,
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent_over_smallGrowth,
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent⟩

/-- **Complete finite-superposition differential matroid.**  For any finite packet of distinct
complex shifts of the completed-Xi logarithmic derivative and any finite family of
constant-coefficient differential-operator rows, the represented nonlinear differential matroid
is exactly the localized polynomial row matroid. -/
theorem xiLogDerivRotated_finiteOperatorRows_differentialMatroid
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (shift : κ → ℂ) (hshift : Function.Injective shift)
    (L : ι → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L
          ((fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
            xiLogDerivRotatedUpperEndCarrier) ∘ shift)) =
      differentialOperatorRowMatroid L := by
  let x : κ → upperEndMeroField :=
    (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
      xiLogDerivRotatedUpperEndCarrier) ∘ shift
  have hxR : DifferentialIndependent upperEndRationalCoordinateField x :=
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent.comp shift hshift
  have hxC : DifferentialIndependent ℂ x :=
    DifferentialIndependent.restrictScalars (F := ℂ) hxR
  simpa only [x, Function.comp_apply] using
    (differentialFamilyMatroid_differentialOperatorRows_eq
      upperEndMero_deriv_complexConstant L x hxC)

/-- **Numerical codimension law.**  Differential transcendence rank of every selected output
packet is the dimension, over `Frac(ℂ[∂])`, of the span of its localized operator rows. -/
theorem xiLogDerivRotated_finiteOperatorRows_eRk_eq_finrank_span
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (shift : κ → ℂ) (hshift : Function.Injective shift)
    (L : ι → κ → Polynomial ℂ) (Iout : Finset ι) :
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L
          ((fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
            xiLogDerivRotatedUpperEndCarrier) ∘ shift))).eRk (Iout : Set ι) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (Iout : Set ι))) : ℕ∞) := by
  let x : κ → upperEndMeroField :=
    (fun h : ℂ => upperEndTranslationMeroEquiv (I * h)
      xiLogDerivRotatedUpperEndCarrier) ∘ shift
  have hxR : DifferentialIndependent upperEndRationalCoordinateField x :=
    xiLogDerivRotated_fullComplexShiftOrbit_differentialIndependent.comp shift hshift
  have hxC : DifferentialIndependent ℂ x :=
    DifferentialIndependent.restrictScalars (F := ℂ) hxR
  simpa only [x, Function.comp_apply] using
    (differentialOperatorRows_eRk_eq_finrank_span
      upperEndMero_deriv_complexConstant L x hxC Iout)

end
end RHTower
