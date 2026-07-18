import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.EllipticGammaExternalDefectOstrowski
import GaloisForLFunctions.HTGeometry.MeromorphicRationalCoordinateDifferentialAdjoin

/-!
# Irrational elliptic-gamma defects over the natural rational base

The genuine elliptic-gamma external defects were already proved differentially independent over
the paired elliptic compositum.  That coefficient field and `ℂ(z)` are incomparable.  The general
differential-algebraic base-change law closes the comparison: restrict first to the constants and
then adjoin the DA coordinate `z`, whose differential adjunction is exactly the embedded rational
function field.

The result is the nonlinear defect matroid over the natural coefficient field used in algebraic
differential equations, not merely over an auxiliary elliptic field.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaRationalBaseDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaRationalBaseComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaRationalBaseComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance ellipticGammaRationalBaseComplexDifferential : Differential ℂ where
  deriv := 0

local instance ellipticGammaRationalBaseMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

private theorem meroField_deriv_algebraMap_complex_rationalBase (c : ℂ) :
    (algebraMap ℂ (meroField Set.univ) c)′ = 0 := by
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap]
  have hconst : analyticSubringDeriv isOpen_univ
      (constToAnalytic Set.univ c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    change (deriv (fun _ : ℂ ↦ c) : Germ (𝒱 Set.univ) ℂ) = 0
    simp
  rw [hconst, map_zero]

local instance ellipticGammaRationalBaseComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField Set.univ) :=
  ⟨fun c ↦ by
    rw [meroField_deriv_algebraMap_complex_rationalBase]
    rfl⟩

local instance ellipticGammaRationalBaseCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _
    meromorphicRationalCoordinateField_derivationClosed

local instance ellipticGammaRationalBaseCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-- **Actual elliptic-gamma defect matroid over `ℂ(z)`.**  External defects in pairwise distinct
nonzero rank-three period cosets are differentially algebraically independent over the genuine
embedded rational-coordinate field. -/
theorem ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
    {kappa : Type*} [DecidableEq kappa]
    (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) := by
  let x := ellipticGammaExternalDefectFamily h sigma tau hsigma htau
  have hElliptic : DifferentialIndependent
      (meromorphicEllipticCompositum sigma tau) x :=
    ellipticGammaExternalDefectFamily_differentialIndependent
      h sigma tau hsigma htau hindependent hnonres hsep
  have hConstants : DifferentialIndependent ℂ x :=
    HTGeometry.DifferentialIndependent.restrictScalarsTower hElliptic
  have hCoordinate :=
    hConstants.extendScalarsDifferentialAdjoinSingleton
      differentialAlgebraicOver_meromorphicRationalCoordinate
  rw [differentialAdjoin_meromorphicRationalCoordinate_eq] at hCoordinate
  exact hCoordinate

/-- The represented nonlinear differential matroid of every separated external-defect family is
the free matroid over `ℂ(z)`. -/
theorem ellipticGammaExternalDefectFamily_differentialMatroid_eq_freeOn_rationalBase
    {kappa : Type*} [DecidableEq kappa]
    (h : kappa → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) =
      Matroid.freeOn Set.univ :=
  differentialFamilyMatroid_eq_freeOn_of_differentialIndependent
    (ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
      h sigma tau hsigma htau hindependent hnonres hsep)

/-- Every nonresonant external difference of the genuine elliptic-gamma logarithmic derivative is
hypertranscendental over `ℂ(z)`. -/
theorem hypertranscendentalOver_ellipticGammaExternalLogDerivDefectMero
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ThetaTranslationNonresonant tau sigma h) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  simpa [ellipticGammaExternalDefectFamily] using
    ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase
      (fun _ : Unit ↦ h) sigma tau hsigma htau hindependent
      (fun _ ↦ hnonres) (by simp)

end

end GaloisForLFunctions
