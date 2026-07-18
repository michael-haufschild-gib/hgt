import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.DifferentialAutomorphismDefectEscape
import GaloisForLFunctions.HTGeometry.EllipticGammaExternalDefectOstrowski
import GaloisForLFunctions.HTGeometry.MeromorphicRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

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
  meromorphicEllipticCompositumComplexAlgebraMero

local instance ellipticGammaRationalBaseComplexDifferential : Differential ℂ where
  deriv := 0

local instance ellipticGammaRationalBaseMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaRationalBaseMeroCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

private theorem meroField_deriv_algebraMap_complex_rationalBase (c : ℂ) :
    (algebraMap ℂ (meroField Set.univ) c)′ = 0 := by
  change
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty]
  have hconst : analyticSubringDeriv isOpen_univ
      (constToAnalytic Set.univ c) = 0 := by
    apply Subtype.ext
    rw [analyticSubringDeriv_coe]
    let f : ℂ → ℂ := fun _ ↦ c
    calc
      Germ.coeRingHom (Filter.principal Set.univ) (deriv f) =
          Germ.coeRingHom (Filter.principal Set.univ) (0 : ℂ → ℂ) := by
        congr 1
        funext z
        simp [f]
      _ = 0 := (Germ.coeRingHom (Filter.principal Set.univ)).map_zero
  rw [hconst, map_zero]

local instance ellipticGammaRationalBaseComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField Set.univ) :=
  ⟨fun c ↦ by
    rw [meroField_deriv_algebraMap_complex_rationalBase]
    change (0 : meroField Set.univ) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

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

/-- Additive translation of global meromorphic functions, bundled as a differential
automorphism over the complex constants. -/
noncomputable def addTranslationMeroDifferentialAlgEquiv (q : ℂ) :
    HTGeometry.DifferentialAlgEquiv ℂ (meroField Set.univ) where
  toAlgEquiv := addTranslationMeroAlgEquiv q
  map_deriv' x := by
    simpa using addTranslationMeroEquiv_deriv q x

/-- The enlarged rank-three period lattice is countable, so it always admits an external shift. -/
theorem exists_thetaTranslationNonresonant (tau sigma : ℂ) :
    ∃ h : ℂ, ThetaTranslationNonresonant tau sigma h := by
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  let lattice : Set ℂ := Set.range fun p : ℤ × (ℤ × ℤ) ↦
    (p.1 : ℂ) + (p.2.1 : ℂ) * tau + (p.2.2 : ℂ) * sigma
  have hcountable : lattice.Countable := Set.countable_range _
  have hproper : lattice ≠ Set.univ := by
    intro hall
    apply Set.not_countable_univ (α := ℂ)
    rw [← hall]
    exact hcountable
  obtain ⟨h, hh⟩ := (Set.ne_univ_iff_exists_notMem lattice).mp hproper
  refine ⟨h, ?_⟩
  rintro ⟨a, b, n, hab⟩
  apply hh
  refine ⟨(a, (b, n)), ?_⟩
  simpa [lattice] using hab.symm

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
    HTGeometry.DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
      hConstants
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

/-- The actual elliptic-gamma logarithmic derivative is hypertranscendental over `ℂ(z)` when
`1`, `sigma`, and `tau` are rationally independent.  An external translated defect supplies the
infinite differential source; translation cannot create it from a DA primitive. -/
theorem hypertranscendentalOver_ellipticGammaLogDerivMero_rationalBase
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (ellipticGammaLogDerivMero sigma tau hsigma htau) := by
  obtain ⟨h, hnonres⟩ := exists_thetaTranslationNonresonant tau sigma
  have hdefectRational :=
    hypertranscendentalOver_ellipticGammaExternalLogDerivDefectMero
      h sigma tau hsigma htau hindependent hnonres
  have hdefectConstants : HypertranscendentalOver ℂ
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) := by
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hdefectRational
    rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
    exact HTGeometry.DifferentialIndependent.restrictScalarsTower hdefectRational
  have hlogConstants : HypertranscendentalOver ℂ
      (ellipticGammaLogDerivMero sigma tau hsigma htau) := by
    apply (addTranslationMeroDifferentialAlgEquiv h).hypertranscendentalOver_of_sub_self
    simpa [addTranslationMeroDifferentialAlgEquiv,
      ellipticGammaExternalLogDerivDefectMero] using hdefectConstants
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at hlogConstants
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hbaseChanged :=
    HTGeometry.DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
      hlogConstants
      differentialAlgebraicOver_meromorphicRationalCoordinate
  rw [differentialAdjoin_meromorphicRationalCoordinate_eq] at hbaseChanged
  exact hbaseChanged

/-- **Natural-base elliptic-gamma hypertranscendence.**  For rationally independent rank-three
periods, the genuine meromorphic elliptic-gamma product is hypertranscendental over the embedded
rational function field `ℂ(z)`. -/
theorem hypertranscendentalOver_ellipticGammaMero_rationalBase
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (ellipticGammaMero sigma tau hsigma htau) := by
  rw [← hypertranscendentalOver_deriv_div_self_iff]
  simpa [ellipticGammaLogDerivMero] using
    hypertranscendentalOver_ellipticGammaLogDerivMero_rationalBase
      sigma tau hsigma htau hindependent

end

end GaloisForLFunctions
