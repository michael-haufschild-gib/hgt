import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicOrbitInvariance

/-!
# Complete finite Herglotz gauge slices
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter Set Topology MeasureTheory
open scoped Differential

noncomputable section

local instance gaugeSliceDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gaugeSliceComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gaugeSliceCharZero :
    CharZero upperEndMeroField :=
  charZero_of_injective_ringHom
    upperEndComplexToMero.injective

local instance gaugeSliceDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gaugeSliceCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _
    upperEndRationalCoordinateField_derivationClosed

local instance gaugeSliceCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField
      upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- **Complete finite rational-gauge slice law.**  Any two
coefficient vectors over one positive H0 background determine
translated carriers with the same embedded differential field,
represented differential matroid, differential-independence status,
and pointed generator class modulo `ℂ(z)`.  The second carrier has
exact Pick index equal to its sign-cube distance from the positive
chamber. -/
theorem finiteAtomicHerglotzGaugeSlice_complete
    {d : ℕ} (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu)
    (a : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, nu {a j} = 0)
    (c₀ c₁ : Fin d → ℝ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (chamberHerglotzTranslateFamily
            nu hH0 a c₁)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range
          (chamberHerglotzTranslateFamily
            nu hH0 a c₀)) ∧
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily nu hH0 a c₁) =
        differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily nu hH0 a c₀) ∧
      (DifferentialIndependent upperEndRationalCoordinateField
           (chamberHerglotzTranslateFamily
             nu hH0 a c₁) ↔
         DifferentialIndependent upperEndRationalCoordinateField
           (chamberHerglotzTranslateFamily
             nu hH0 a c₀)) ∧
      (∀ h : ℂ,
        upperEndRationalGaugeClass
            (chamberHerglotzTranslateFamily
              nu hH0 a c₁ h) =
          upperEndRationalGaugeClass
            (chamberHerglotzTranslateFamily
              nu hH0 a c₀ h)) ∧
      ∀ᶠ y : ℝ in 𝓝[≠] 0,
        (∀ W : Submodule ℂ (Fin d → ℂ),
            (∀ x ∈ W, x ≠ 0 →
              (star x ⬝ᵥ
                (chamberPickKernel nu a c₁ y).mulVec x).re <
                  0) →
            Module.finrank ℂ W ≤
              hammingDist
                (signPattern c₁) (positiveChamber d)) ∧
          Module.finrank ℂ (negSupported c₁) =
            hammingDist
              (signPattern c₁) (positiveChamber d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      (chamberHerglotzTranslateFamily_differentialAdjoin_eq
        nu hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialAdjoin_eq
          nu hH0 a c₀).symm
  · exact
      (chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
        nu hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
          nu hH0 a c₀).symm
  · exact
      (chamberHerglotzTranslateFamily_differentialIndependent_iff
        nu hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialIndependent_iff
          nu hH0 a c₀).symm
  · intro h
    exact
      (chamberHerglotzTranslateFamily_rationalGaugeClass_eq
        nu hH0 a c₁ h).trans
        (chamberHerglotzTranslateFamily_rationalGaugeClass_eq
          nu hH0 a c₀ h).symm
  · exact chamberLaw_herglotzMeasure
      nu hH0 a c₁ ha hatom

end

end GaloisForLFunctions.HTGeometry
