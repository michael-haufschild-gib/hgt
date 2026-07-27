import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid

/-!
# Universal raw-face and rank-three-minor laws

Every deletion face is itself a genuine multiple elliptic-gamma system on its surviving
parameters.  Consequently, a rank-three minor inside that surviving family forces
hypertranscendence of both the raw face product and its logarithmic derivative, regardless of
rational relations involving any other surviving parameter.

On the fully nonresonant locus, the raw translated face functions have the same complete
differential matroid as their logarithmic derivatives.  In particular, all nonboundary raw face
coordinates are jointly differentially independent and have the same exact two-survivor
differential-algebraicity boundary.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The raw multiple elliptic-gamma function on the face obtained by deleting `J`. -/
def multipleEllipticGammaFaceMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) :
    meroField (Set.univ : Set ℂ) :=
  multipleEllipticGammaMero
    (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i)

/-- **Facewise rank-three-minor law.**  If the periods surviving a deletion face contain one
rank-three minor, both the genuine raw face function and its logarithmic derivative are
hypertranscendental over `ℂ(z)`.  No restriction is imposed on the other surviving periods. -/
theorem multipleEllipticGammaFace_rankThreeMinor_hypertranscendence
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    (hminor : MultipleEllipticGammaHasRankThreeMinor
      (multipleEllipticGammaFaceParameters τ J)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaFaceMero τ hτ J) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  exact ⟨
    hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor
      (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i) hminor,
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
      (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i) hminor⟩

/-- A faithful label for a raw or logarithmic-derivative coordinate on any face retaining at
least two periods. -/
structure MultipleEllipticGammaNonboundaryLabel (τ : ι → ℂ) where
  face : Finset ι
  face_nonboundary : 2 ≤ (faceᶜ).card
  shift : ℂ
  shift_mem : shift ∈ faceShiftLattice τ face

/-- The family of translated raw multiple elliptic-gamma face functions. -/
def multipleEllipticGammaRawFaceFamily
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    MultipleEllipticGammaNonboundaryLabel τ → meroField (Set.univ : Set ℂ) :=
  fun a => addTranslationMeroEquiv a.shift
    (multipleEllipticGammaFaceMero τ hτ a.face)

/-- The correspondingly labelled family of translated logarithmic derivatives. -/
def multipleEllipticGammaLogFaceFamily
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    MultipleEllipticGammaNonboundaryLabel τ → meroField (Set.univ : Set ℂ) :=
  fun a => addTranslationMeroEquiv a.shift
    (multipleEllipticGammaLogDerivFaceMero τ hτ a.face)

/-- Translation commutes with the algebraic logarithmic derivative of every raw face function. -/
theorem multipleEllipticGammaRawFace_logDeriv
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (a : MultipleEllipticGammaNonboundaryLabel τ) :
    (multipleEllipticGammaRawFaceFamily τ hτ a)′ /
        multipleEllipticGammaRawFaceFamily τ hτ a =
      multipleEllipticGammaLogFaceFamily τ hτ a := by
  simp only [multipleEllipticGammaRawFaceFamily,
    multipleEllipticGammaLogFaceFamily, multipleEllipticGammaFaceMero,
    multipleEllipticGammaLogDerivFaceMero, multipleEllipticGammaLogDerivMero,
    Differential.logDeriv]
  rw [← addTranslationMeroEquiv_deriv, ← map_div₀]

/-- Integral period independence makes the face-and-shift label of every nonboundary logarithmic
coordinate faithful. -/
theorem multipleEllipticGammaLogFaceFamily_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) :
    Function.Injective (multipleEllipticGammaLogFaceFamily τ hτ) := by
  intro a b hab
  by_cases hface : a.face = b.face
  · have hshift : a.shift = b.shift := by
      apply faceShiftLattice_translate_injective τ hτ hQ a.face a.face_nonboundary
        a.shift_mem
      · simpa [hface] using b.shift_mem
      · simpa only [multipleEllipticGammaLogFaceFamily, hface] using hab
    cases a
    cases b
    simp_all
  · exact False.elim
      (multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ
        a.face b.face hface a.face_nonboundary b.face_nonboundary
        a.shift_mem b.shift_mem hab)

/-- The complete translated raw face hierarchy is differentially independent over the constants
whenever all periods and the unit period are integrally independent. -/
theorem multipleEllipticGammaRawFaceFamily_differentialIndependent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) :
    DifferentialIndependent ℂ
      (multipleEllipticGammaRawFaceFamily τ hτ) := by
  rw [differentialIndependent_deriv_div_self_iff]
  have hlog : DifferentialIndependent ℂ
      (multipleEllipticGammaLogFaceFamily τ hτ) := by
    apply multipleEllipticGammaSelectedFaces_differentialIndependent
      τ hτ hQ hι
    · intro a
      exact Set.mem_iUnion₂.mpr ⟨a.face, a.face_nonboundary,
        ⟨a.shift, a.shift_mem, rfl⟩⟩
    · exact multipleEllipticGammaLogFaceFamily_injective τ hτ hQ
  simpa only [multipleEllipticGammaRawFace_logDeriv] using hlog

/-- The same complete raw-face independence over the natural rational coordinate field `ℂ(z)`. -/
theorem multipleEllipticGammaRawFaceFamily_differentialIndependent_rationalBase
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (multipleEllipticGammaRawFaceFamily τ hτ) := by
  rw [differentialIndependent_deriv_div_self_iff]
  have hlog : DifferentialIndependent meromorphicRationalCoordinateField
      (multipleEllipticGammaLogFaceFamily τ hτ) := by
    apply multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase
      τ hτ hQ hι
    · intro a
      exact Set.mem_iUnion₂.mpr ⟨a.face, a.face_nonboundary,
        ⟨a.shift, a.shift_mem, rfl⟩⟩
    · exact multipleEllipticGammaLogFaceFamily_injective τ hτ hQ
  simpa only [multipleEllipticGammaRawFace_logDeriv] using hlog

/-- Coordinatewise logarithmic differentiation preserves the entire differential matroid of the
raw translated hierarchy, without an arithmetic hypothesis. -/
theorem multipleEllipticGammaRawFaceFamily_differentialMatroid_eq_logFaceFamily
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (multipleEllipticGammaRawFaceFamily τ hτ) =
      differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (multipleEllipticGammaLogFaceFamily τ hτ) := by
  rw [differentialFamilyMatroid_deriv_div_self_eq]
  congr 1
  funext a
  exact multipleEllipticGammaRawFace_logDeriv τ hτ a

/-- **Raw-face phase boundary.** A translated raw face function is differentially algebraic over
`ℂ(z)` exactly when fewer than two periods survive. -/
theorem multipleEllipticGammaRawFacePacket_differentialAlgebraic_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) (g : ℂ) (hg : g ∈ faceShiftLattice τ J) :
    DifferentialAlgebraicOver meromorphicRationalCoordinateField
        (addTranslationMeroEquiv g (multipleEllipticGammaFaceMero τ hτ J)) ↔
      (Jᶜ).card < 2 := by
  rw [← differentialAlgebraicOver_deriv_div_self_iff]
  have hlog :
      (addTranslationMeroEquiv g (multipleEllipticGammaFaceMero τ hτ J))′ /
          addTranslationMeroEquiv g (multipleEllipticGammaFaceMero τ hτ J) =
        addTranslationMeroEquiv g
          (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
    simp only [multipleEllipticGammaFaceMero, multipleEllipticGammaLogDerivFaceMero,
      multipleEllipticGammaLogDerivMero, Differential.logDeriv]
    rw [← addTranslationMeroEquiv_deriv, ← map_div₀]
  rw [hlog]
  exact multipleEllipticGammaFacePacket_differentialAlgebraic_iff
    τ hτ hQ hι J ⟨g, hg, rfl⟩

end

end GaloisForLFunctions
