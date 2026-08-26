import GaloisForLFunctions.HTGeometry.TripticMixedConstraintNormalForm
import GaloisForLFunctions.HTGeometry.EllipticCompositumMatroidTransport
import GaloisForLFunctions.HTGeometry.EllipticGammaTranslateOrbitSeparated
import GaloisForLFunctions.HTGeometry.EllipticGammaQuotientPeriodCosetMatroid
import GaloisForLFunctions.HTGeometry.LaurentMonomialDifferentialMatroid

/-!
# Atomic defects force the full differential translation-orbit matroid

This file closes every formal clause of the atomic-defect/full-orbit card at the explicit
prime-log period pair.  A finite generic recentering turns pairwise separated shifts into a
base-pointed packet; translation back removes the artificial base point.  Coordinatewise
logarithmic differentiation then transfers the result from the genuine elliptic-gamma logarithmic
derivative to the actual elliptic-gamma product.  Finally, the Laurent-monomial matroid theorem
identifies arbitrary finite products with the ordinary complex row matroid of their integral
divisors.

The same closed package retains the arbitrary-shift pointed collision matroids of additive defects
and multiplicative quotients, the complete localized `ℂ(δ)` operator-row matroid and rank law,
and the full triptic mixed-constraint normal form.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Matrix

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-- The actual elliptic-gamma products translated by an indexed shift family. -/
def ellipticGammaRawTranslateFamily {ι : Type*} (h : ι → ℂ) (a b : ℂ)
    (ha : 0 < a.im) (hb : 0 < b.im) : ι → meroField Set.univ :=
  fun i ↦ addTranslationMeroEquiv (h i) (ellipticGammaMero a b ha hb)

/-- The coordinatewise logarithmic derivatives of actual elliptic-gamma translates are the
translated order-one elliptic-gamma source. -/
theorem ellipticGammaRawTranslateFamily_logDeriv {ι : Type*} (h : ι → ℂ) (a b : ℂ)
    (ha : 0 < a.im) (hb : 0 < b.im) :
    (fun i ↦ Differential.logDeriv (ellipticGammaRawTranslateFamily h a b ha hb i)) =
      ellipticGammaTranslateFamily h a b ha hb := by
  funext i
  exact logDeriv_addTranslationMeroEquiv_ellipticGammaMero (h i) a b ha hb

/-- **Base-point-free indexed orbit theorem.**  Pairwise separation modulo the rank-three period
group suffices; no chosen shift must itself avoid the zero period class. -/
theorem differentialIndependent_ellipticGammaTranslateFamily_pairwiseSeparated
    {a b : ℂ} {ι : Type*} [Fintype ι]
    (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (h : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) :
    DifferentialIndependent ℂ (ellipticGammaTranslateFamily h a b ha hb) := by
  classical
  obtain ⟨w, hw⟩ := exists_thetaGenericShift b a (Finset.image h Finset.univ)
  have hnonres : ∀ i, ThetaTranslationNonresonant b a (w + h i) := by
    intro i
    exact hw (h i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hsep' : ∀ i j, i ≠ j →
      ThetaTranslationNonresonant b a ((w + h j) - (w + h i)) := by
    intro i j hij
    convert hsep i j hij using 1 <;> ring
  have hshift := differentialIndependent_ellipticGammaTranslateFamily
    ha hb hperiods (fun i ↦ w + h i) hnonres hsep'
  have hback :=
    (addTranslationMeroDifferentialAlgEquiv w).symm.differentialIndependent_map hshift
  have hfamily :
      (fun i ↦ (addTranslationMeroAlgEquiv (-w))
        (addTranslationMeroEquiv (w + h i)
          (ellipticGammaLogDerivMero a b ha hb))) =
        ellipticGammaTranslateFamily h a b ha hb := by
    funext i
    change addTranslationMeroEquiv (-w)
        (addTranslationMeroEquiv (w + h i)
          (ellipticGammaLogDerivMero a b ha hb)) = _
    rw [addTranslationMeroEquiv_add]
    congr 2
    ring
  have hfamily' :
      (fun i ↦ (addTranslationMeroAlgEquiv (-w))
        (ellipticGammaTranslateFamily (fun i ↦ w + h i) a b ha hb i)) =
        ellipticGammaTranslateFamily h a b ha hb := by
    simpa only [ellipticGammaTranslateFamily] using hfamily
  simpa only [DifferentialAlgEquiv.symm, addTranslationMeroDifferentialAlgEquiv,
    addTranslationMeroAlgEquiv_symm_apply, hfamily'] using hback

/-- The base-point-free logarithmic-derivative orbit remains independent over the genuine rational
coordinate field `ℂ(z)`. -/
theorem differentialIndependent_ellipticGammaTranslateFamily_pairwiseSeparated_rationalBase
    {a b : ℂ} {ι : Type*} [Fintype ι]
    (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (h : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (ellipticGammaTranslateFamily h a b ha hb) :=
  (differentialIndependent_meromorphicRationalCoordinateField_iff
    (ellipticGammaTranslateFamily h a b ha hb)).mpr
      (differentialIndependent_ellipticGammaTranslateFamily_pairwiseSeparated
        ha hb hperiods h hsep)

/-- **Actual elliptic-gamma orbit theorem.**  Distinct rank-three period classes give a
differentially independent family of genuine translated elliptic-gamma products over `ℂ(z)`. -/
theorem differentialIndependent_ellipticGammaRawTranslateFamily_pairwiseSeparated_rationalBase
    {a b : ℂ} {ι : Type} [Fintype ι]
    (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (h : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (ellipticGammaRawTranslateFamily h a b ha hb) := by
  apply (differentialIndependent_deriv_div_self_iff
    (ellipticGammaRawTranslateFamily h a b ha hb)).mpr
  have hlog :
      (fun i ↦ (ellipticGammaRawTranslateFamily h a b ha hb i)′ /
        ellipticGammaRawTranslateFamily h a b ha hb i) =
        ellipticGammaTranslateFamily h a b ha hb := by
    simpa only [Differential.logDeriv] using
      ellipticGammaRawTranslateFamily_logDeriv h a b ha hb
  rw [hlog]
  exact differentialIndependent_ellipticGammaTranslateFamily_pairwiseSeparated_rationalBase
    ha hb hperiods h hsep

/-- Adjoining the rational meromorphic coordinate changes no represented differential matroid,
for any indexed family of global meromorphic functions. -/
theorem differentialFamilyMatroid_meromorphicRationalCoordinateField_eq_complex
    {ι : Type*} (x : ι → meroField Set.univ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField) x =
      differentialFamilyMatroid (F := ℂ) x := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      differentialFamilyMatroid_indep_iff]
    exact differentialIndependent_meromorphicRationalCoordinateField_iff
      (fun i : I ↦ x i)

/-- **Exact actual-product matroid.**  For any finite family of integral translate divisors, the
complete nonlinear differential matroid of the corresponding genuine elliptic-gamma products over
`ℂ(z)` is exactly the ordinary complex row matroid of those divisors. -/
theorem ellipticGammaRawTranslateProducts_differentialMatroid
    {a b : ℂ} {ι ρ : Type} [Fintype ι] [Fintype ρ]
    [DecidableEq ι] [DecidableEq ρ]
    (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (h : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i))
    (A : Matrix ρ ι ℤ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (integerLaurentMonomialFamily A
          (ellipticGammaRawTranslateFamily h a b ha hb)) =
      linearFamilyMatroid (integerCastMatrix ℂ A) := by
  rw [differentialFamilyMatroid_meromorphicRationalCoordinateField_eq_complex]
  exact differentialFamilyMatroid_integerLaurentMonomialFamily_eq_linearFamilyMatroid
    A (ellipticGammaRawTranslateFamily h a b ha hb)
      ((differentialIndependent_meromorphicRationalCoordinateField_iff
        (ellipticGammaRawTranslateFamily h a b ha hb)).mp
          (differentialIndependent_ellipticGammaRawTranslateFamily_pairwiseSeparated_rationalBase
            ha hb hperiods h hsep))

/-- Numerical `ℂ`-rank formula for every finite packet of genuine elliptic-gamma translate
products. -/
theorem ellipticGammaRawTranslateProducts_differentialRank
    {a b : ℂ} {ι ρ : Type} [Fintype ι] [Fintype ρ]
    [DecidableEq ι] [DecidableEq ρ]
    (ha : 0 < a.im) (hb : 0 < b.im)
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b))
    (h : ι → ℂ)
    (hsep : ∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i))
    (A : Matrix ρ ι ℤ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (integerLaurentMonomialFamily A
          (ellipticGammaRawTranslateFamily h a b ha hb))).eRk (↑I : Set ρ) =
      (Module.finrank ℂ
        (Submodule.span ℂ (integerCastMatrix ℂ A '' (↑I : Set ρ))) : ℕ∞) := by
  rw [ellipticGammaRawTranslateProducts_differentialMatroid ha hb hperiods h hsep A]
  exact linearFamilyMatroid_eRk_finset (integerCastMatrix ℂ A) I

/-- Closed fixed-period package containing the atomic parent, bridge-edge orbit upgrade, actual
elliptic-gamma translates and products, complete differential group-algebra rows, and triptic
mixed-constraint classification. -/
structure AtomicDefectFullOrbitDifferentialMatroidPackage (a b : ℂ) : Prop where
  upperHalfPlaneA : 0 < a.im
  upperHalfPlaneB : 0 < b.im
  periodIndependent : LinearIndependent ℚ (ellipticGammaSourcePeriods a b)
  atomicDefectMatroid : ∀ {κ : Type} (h : κ → ℂ),
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalDefectFamily h a b upperHalfPlaneA upperHalfPlaneB) =
      affinePointedCollisionMatroid (ellipticGammaPeriodClass a b ∘ h) 0
  atomicQuotientMatroid : ∀ {κ : Type} (h : κ → ℂ),
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h a b upperHalfPlaneA upperHalfPlaneB) =
      affinePointedCollisionMatroid (ellipticGammaPeriodClass a b ∘ h) 0
  logarithmicOrbit : ∀ {ι : Type} (_ : Fintype ι) (h : ι → ℂ),
    (∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) →
    DifferentialIndependent meromorphicRationalCoordinateField
      (ellipticGammaTranslateFamily h a b upperHalfPlaneA upperHalfPlaneB)
  actualGammaOrbit : ∀ {ι : Type} (_ : Fintype ι) (h : ι → ℂ),
    (∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) →
    DifferentialIndependent meromorphicRationalCoordinateField
      (ellipticGammaRawTranslateFamily h a b upperHalfPlaneA upperHalfPlaneB)
  actualGammaProductMatroid : ∀ {ι ρ : Type}
    (_ : Fintype ι) (_ : Fintype ρ) (_ : DecidableEq ι) (_ : DecidableEq ρ)
    (h : ι → ℂ),
    (∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) →
    ∀ A : Matrix ρ ι ℤ,
      differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
          (integerLaurentMonomialFamily A
            (ellipticGammaRawTranslateFamily h a b upperHalfPlaneA upperHalfPlaneB)) =
        linearFamilyMatroid (integerCastMatrix ℂ A)
  actualGammaProductRank : ∀ {ι ρ : Type}
    (_ : Fintype ι) (_ : Fintype ρ) (_ : DecidableEq ι) (_ : DecidableEq ρ)
    (h : ι → ℂ),
    (∀ i j, i ≠ j → ThetaTranslationNonresonant b a (h j - h i)) →
    ∀ (A : Matrix ρ ι ℤ) (I : Finset ρ),
      (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
          (integerLaurentMonomialFamily A
            (ellipticGammaRawTranslateFamily h a b
              upperHalfPlaneA upperHalfPlaneB))).eRk (↑I : Set ρ) =
        (Module.finrank ℂ
          (Submodule.span ℂ (integerCastMatrix ℂ A '' (↑I : Set ρ))) : ℕ∞)
  mixedConstraintNormalForm : TripticMixedConstraintNormalFormPackage a b

/-- **Unconditional atomic-defect/full-orbit differential matroid.**  Explicit prime-log periods
discharge upper-half-plane and arithmetic genericity internally; every remaining quantifier is
part of the theorem's conclusion. -/
theorem atomicDefectFullOrbitDifferentialMatroid_unconditional :
    AtomicDefectFullOrbitDifferentialMatroidPackage
      (reflectionPairPeriods true) (reflectionPairPeriods false) := by
  let a := reflectionPairPeriods true
  let b := reflectionPairPeriods false
  have ha : 0 < a.im := reflectionPairPeriods_im_pos true
  have hb : 0 < b.im := reflectionPairPeriods_im_pos false
  have hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods a b) :=
    linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent
      reflectionPairPeriods reflectionPairPeriods_integrallyIndependent
        (by decide : true ≠ false)
  change AtomicDefectFullOrbitDifferentialMatroidPackage a b
  refine {
    upperHalfPlaneA := ha
    upperHalfPlaneB := hb
    periodIndependent := hperiods
    atomicDefectMatroid := ?_
    atomicQuotientMatroid := ?_
    logarithmicOrbit := ?_
    actualGammaOrbit := ?_
    actualGammaProductMatroid := ?_
    actualGammaProductRank := ?_
    mixedConstraintNormalForm := tripticMixedConstraintNormalForm_unconditional }
  · intro κ h
    exact ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase
      h a b ha hb hperiods
  · intro κ h
    exact ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase
      h a b ha hb hperiods
  · intro ι hι h hsep
    letI := hι
    exact differentialIndependent_ellipticGammaTranslateFamily_pairwiseSeparated_rationalBase
      ha hb hperiods h hsep
  · intro ι hι h hsep
    letI := hι
    exact differentialIndependent_ellipticGammaRawTranslateFamily_pairwiseSeparated_rationalBase
      ha hb hperiods h hsep
  · intro ι ρ hι hρ hdι hdρ h hsep A
    letI := hι
    letI := hρ
    letI := hdι
    letI := hdρ
    exact ellipticGammaRawTranslateProducts_differentialMatroid
      ha hb hperiods h hsep A
  · intro ι ρ hι hρ hdι hdρ h hsep A I
    letI := hι
    letI := hρ
    letI := hdι
    letI := hdρ
    exact ellipticGammaRawTranslateProducts_differentialRank
      ha hb hperiods h hsep A I

end

end GaloisForLFunctions.HTGeometry
