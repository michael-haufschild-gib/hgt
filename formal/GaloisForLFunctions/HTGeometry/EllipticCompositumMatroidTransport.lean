import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.MeromorphicRationalCoordinateDifferentialAdjoin

/-!
# Transporting the elliptic-gamma matroids from the elliptic base to `ℂ(z)`

The paired elliptic compositum is a differentially algebraic coefficient extension of the
constants, so it changes no differential matroid at all: adjoining differentially algebraic
coefficients preserves and reflects differential independence.  The embedded rational coordinate
field is a differentially algebraic extension of the constants for the same reason.  Consequently
every differential matroid over the natural elliptic base is *equal* to the one over `ℂ(z)`, and the
exact period-coset partition matroids and rank laws of the elliptic-gamma packets hold verbatim over
the rational base.

* `differentialAdjoin_self_of_derivationClosed`;
* **`differentialIndependent_meromorphicEllipticCompositum_iff`** — differential independence over
  the paired elliptic compositum is differential independence over the constants;
* **`differentialFamilyMatroid_rationalBase_eq_ellipticCompositum`** — hence the represented
  matroid is the same over `ℂ(z)` and over the elliptic base;
* **`ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase`**,
  **`ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase`**,
  **`ellipticGammaExternalQuotientFamily_eRk_eq_nonzeroPeriodClass_encard_rationalBase`** — the
  card's pointed partition matroids and rank law over the rational base.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaStructuralGeneratorRestrictedDifferential
  ellipticGammaStructuralGeneratorDifferentialAlgebra ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-- A derivation-closed intermediate field is its own differential adjunction. -/
theorem differentialAdjoin_self_of_derivationClosed {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (B : IntermediateField F K) (hB : DerivationClosed B) :
    differentialAdjoin F (B : Set K) = B :=
  le_antisymm (differentialAdjoin_le F (le_refl (B : Set K)) hB)
    (subset_differentialAdjoin F (B : Set K))

/-- **The paired elliptic compositum changes no differential independence.**  Every one of its
elements is differentially algebraic over the constants, and adjoining differentially algebraic
coefficients preserves and reflects differential independence. -/
theorem differentialIndependent_meromorphicEllipticCompositum_iff {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) {ι : Type*}
    (x : ι → meroField (Set.univ : Set ℂ)) :
    DifferentialIndependent (meromorphicEllipticCompositum σ τ) x ↔
      DifferentialIndependent ℂ x := by
  have hG : ∀ g ∈ (meromorphicEllipticCompositum σ τ : Set (meroField (Set.univ : Set ℂ))),
      DifferentialAlgebraicOver ℂ g :=
    fun g hg => differentialAlgebraicOver_complex_of_mem_meromorphicEllipticCompositum hσ hτ hg
  have h := differentialIndependent_differentialAdjoin_iff (F := ℂ)
    (G := (meromorphicEllipticCompositum σ τ : Set (meroField (Set.univ : Set ℂ)))) hG (x := x)
  rwa [differentialAdjoin_self_of_derivationClosed _
    (meromorphicEllipticCompositum_derivationClosed σ τ)] at h

/-- The embedded rational coordinate field likewise changes no differential independence. -/
theorem differentialIndependent_meromorphicRationalCoordinateField_iff {ι : Type*}
    (x : ι → meroField (Set.univ : Set ℂ)) :
    DifferentialIndependent meromorphicRationalCoordinateField x ↔
      DifferentialIndependent ℂ x := by
  have hG : ∀ g ∈ ({meromorphicRationalCoordinate} : Set (meroField (Set.univ : Set ℂ))),
      DifferentialAlgebraicOver ℂ g := by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact differentialAlgebraicOver_meromorphicRationalCoordinate
  have h := differentialIndependent_differentialAdjoin_iff (F := ℂ)
    (G := ({meromorphicRationalCoordinate} : Set (meroField (Set.univ : Set ℂ)))) hG (x := x)
  rwa [differentialAdjoin_meromorphicRationalCoordinate_eq] at h

/-- **The represented matroid is the same over `ℂ(z)` and over the paired elliptic compositum.** -/
theorem differentialFamilyMatroid_rationalBase_eq_ellipticCompositum {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) {ι : Type}
    (x : ι → meroField (Set.univ : Set ℂ)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField) x =
      differentialFamilyMatroid (F := meromorphicEllipticCompositum σ τ) x := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid, differentialMatroid_ground]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff, differentialFamilyMatroid_indep_iff,
      differentialIndependent_meromorphicRationalCoordinateField_iff,
      differentialIndependent_meromorphicEllipticCompositum_iff hσ hτ]

/-! ## The elliptic-gamma matroids over the rational base -/

/-- **Rational-base additive period-coset partition matroid.** -/
theorem ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase
    {κ : Type} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalDefectFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid (ellipticGammaPeriodClass sigma tau ∘ h) 0 := by
  rw [differentialFamilyMatroid_rationalBase_eq_ellipticCompositum hsigma htau]
  exact ellipticGammaExternalDefectFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent

/-- **Rational-base multiplicative period-coset partition matroid.** -/
theorem ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase
    {κ : Type} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      affinePointedCollisionMatroid (ellipticGammaPeriodClass sigma tau ∘ h) 0 := by
  rw [differentialFamilyMatroid_rationalBase_eq_ellipticCompositum hsigma htau]
  exact ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid
    h sigma tau hsigma htau hindependent

/-- **Rational-base exact rank law.**  The extended differential rank of an elliptic-gamma quotient
packet over `ℂ(z)` is the number of distinct nonzero period classes it meets. -/
theorem ellipticGammaExternalQuotientFamily_eRk_eq_nonzeroPeriodClass_encard_rationalBase
    {κ : Type} (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) (I : Set κ) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
      (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau)).eRk I =
      (((ellipticGammaPeriodClass sigma tau ∘ h) '' I) ∩ {q | q ≠ 0}).encard := by
  rw [ellipticGammaExternalQuotientFamily_differentialMatroid_eq_periodCosetPartitionMatroid_rationalBase
    h sigma tau hsigma htau hindependent, affinePointedCollisionMatroid_eRk]

end

end GaloisForLFunctions.HTGeometry
