import GaloisForLFunctions.HTGeometry.FaceTranslateInjective
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacketDisjointness
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaStructuralSpanDecomposition

/-!
# The deep packet is faithfully coordinatized by face and shift

Face-packet disjointness separates distinct faces retaining at least two periods, and faithful
shift labelling separates distinct external lattice shifts on one such face.  Together the pair
`(face, shift)` is a faithful coordinate on the union of all deep packets.

Any finite family of pairwise distinct such pairs therefore selects a differentially independent
packet, so the differential matroid of every finite constant-coefficient differential-operator
family built on it is the localized operator-row matroid over `Frac(ℂ[∂])`.  Combined with the
structural span decomposition, this is the exact hierarchy-to-operator-row identification for
multiple elliptic gamma functions of every order.
-/

open Filter Set Topology Function Complex
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

/-! ## Faithfulness of the pair coordinate -/

/-- **The pair `(face, shift)` is a faithful coordinate on the deep packet union.** -/
theorem multipleEllipticGammaDeepCoordinate_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {J K : Finset ι} (hJ : 2 ≤ (Jᶜ).card) (hK : 2 ≤ (Kᶜ).card)
    {g h : ℂ} (hg : g ∈ faceShiftLattice τ J) (hh : h ∈ faceShiftLattice τ K)
    (heq : addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ K)) :
    J = K ∧ g = h := by
  by_cases hJK : J = K
  · subst hJK
    exact ⟨rfl, faceShiftLattice_translate_injective τ hτ hQ J hJ hg hh heq⟩
  · exact absurd heq
      (multipleEllipticGammaFace_translate_ne_of_ne τ hτ hQ J K hJK hJ hK hg hh)

/-- The coordinate attached to a selection of deep faces and external shifts. -/
def multipleEllipticGammaDeepCoordinate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {κ : Type} (face : κ → Finset ι) (shift : κ → ℂ) (k : κ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (shift k) (multipleEllipticGammaLogDerivFaceMero τ hτ (face k))

theorem multipleEllipticGammaDeepCoordinate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {κ : Type} (face : κ → Finset ι) (shift : κ → ℂ)
    (hdeep : ∀ k, 2 ≤ (((face k))ᶜ).card)
    (hshift : ∀ k, shift k ∈ faceShiftLattice τ (face k)) (k : κ) :
    multipleEllipticGammaDeepCoordinate τ hτ face shift k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card} :=
  Set.mem_iUnion₂.mpr ⟨face k, hdeep k, ⟨shift k, hshift k, rfl⟩⟩

theorem multipleEllipticGammaDeepCoordinate_family_injective
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {κ : Type} (face : κ → Finset ι) (shift : κ → ℂ)
    (hdeep : ∀ k, 2 ≤ (((face k))ᶜ).card)
    (hshift : ∀ k, shift k ∈ faceShiftLattice τ (face k))
    (hpair : ∀ k l : κ, face k = face l → shift k = shift l → k = l) :
    Function.Injective (multipleEllipticGammaDeepCoordinate τ hτ face shift) := by
  intro k l hkl
  obtain ⟨hface, hshifteq⟩ :=
    multipleEllipticGammaDeepCoordinate_injective τ hτ hQ (hdeep k) (hdeep l)
      (hshift k) (hshift l) hkl
  exact hpair k l hface hshifteq

/-! ## The operator-row matroid on a faithful deep selection -/

/-- **Hierarchy-to-operator-row identification.**  For a faithful finite selection of deep face
coordinates and any finite family of constant-coefficient differential-operator rows, the nonlinear
differential matroid of the outputs equals the localized operator-row matroid. -/
theorem multipleEllipticGammaDeepSelection_differentialMatroid
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (face : κ → Finset ι) (shift : κ → ℂ)
    (hdeep : ∀ k, 2 ≤ (((face k))ᶜ).card)
    (hshift : ∀ k, shift k ∈ faceShiftLattice τ (face k))
    (hpair : ∀ k l : κ, face k = face l → shift k = shift l → k = l)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L
          (multipleEllipticGammaDeepCoordinate τ hτ face shift)) =
      differentialOperatorRowMatroid L :=
  multipleEllipticGammaCompleteDifferentialMatroid τ hτ hQ hι _
    (multipleEllipticGammaDeepCoordinate_mem τ hτ face shift hdeep hshift)
    (multipleEllipticGammaDeepCoordinate_family_injective τ hτ hQ face shift hdeep hshift hpair) L

/-- Numerical form of the identification. -/
theorem multipleEllipticGammaDeepSelection_differentialRank
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (face : κ → Finset ι) (shift : κ → ℂ)
    (hdeep : ∀ k, 2 ≤ (((face k))ᶜ).card)
    (hshift : ∀ k, shift k ∈ faceShiftLattice τ (face k))
    (hpair : ∀ k l : κ, face k = face l → shift k = shift l → k = l)
    (L : ρ → κ → Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L
          (multipleEllipticGammaDeepCoordinate τ hτ face shift))).eRk (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) :=
  multipleEllipticGammaCompleteDifferentialRank τ hτ hQ hι _
    (multipleEllipticGammaDeepCoordinate_mem τ hτ face shift hdeep hshift)
    (multipleEllipticGammaDeepCoordinate_family_injective τ hτ hQ face shift hdeep hshift hpair)
    L I

end

end GaloisForLFunctions
