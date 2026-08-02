import GaloisForLFunctions.HTGeometry.MultipleGammaMultiplicativeAnnihilator
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaDeepPacketFaithfulness
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDepthValue

/-!
# The order-four structural differential matroid

An order-four multiple elliptic gamma is carried by five periods.  Its faces split into four
filtration layers — the top primitive, five order-three faces, ten order-two faces and ten bottom
order-one faces — and every one of them retains at least two periods.

The layered face-independence engine makes all four layers jointly differentially independent at
once, so no hypergraph elimination order is needed: the depth induction against the differentially
algebraic boundary replaces the graph-star argument that stops working past order three.  The exact
annihilator, the transverse depth, and the multiplicative classification then follow at order four
from their all-order forms.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

/-! ## The four face layers -/

/-- Faces of the order-four hierarchy that still retain two periods: the deletions of at most
three of the five parameters. -/
def orderFourDeepFaces : Set (Finset (Fin 5)) := {J | J.card ≤ 3}

theorem orderFourDeepFaces_subset :
    orderFourDeepFaces ⊆ {J : Finset (Fin 5) | 2 ≤ (Jᶜ).card} := by
  intro J hJ
  have htotal := Finset.card_add_card_compl J
  simp only [Fintype.card_fin] at htotal
  simp only [orderFourDeepFaces, Set.mem_setOf_eq] at hJ ⊢
  omega

/-- The four filtration layers, by number of deleted parameters. -/
theorem orderFourFaceLayer_cards :
    (Finset.univ.filter fun J : Finset (Fin 5) => J.card = 0).card = 1 ∧
      (Finset.univ.filter fun J : Finset (Fin 5) => J.card = 1).card = 5 ∧
      (Finset.univ.filter fun J : Finset (Fin 5) => J.card = 2).card = 10 ∧
      (Finset.univ.filter fun J : Finset (Fin 5) => J.card = 3).card = 10 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem orderFourDeepFacePacketUnion_subset (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    facePacketUnion τ hτ orderFourDeepFaces ⊆
      facePacketUnion τ hτ {J : Finset (Fin 5) | 2 ≤ (Jᶜ).card} :=
  Set.biUnion_mono orderFourDeepFaces_subset fun _ _ => subset_rfl

/-! ## Joint independence of all four layers -/

/-- **Order-four joint atomicity across every filtration layer.**  The external orbits of the top
primitive, the five order-three faces, the ten order-two faces and the ten bottom faces are
jointly differentially independent over the constants. -/
theorem orderFourFaceOrbits_diffIndepOn
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    DiffIndepOn ℂ (facePacketUnion τ hτ orderFourDeepFaces) :=
  (multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ (by simp)).subset
    (orderFourDeepFacePacketUnion_subset τ hτ)

/-- The same joint atomicity over the natural rational coordinate field `ℂ(z)`. -/
theorem orderFourFaceOrbits_diffIndepOn_rationalBase
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    DiffIndepOn meromorphicRationalCoordinateField
      (facePacketUnion τ hτ orderFourDeepFaces) :=
  multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase τ hτ hQ (by simp)
    (Subtype.val) (fun k => orderFourDeepFacePacketUnion_subset τ hτ k.2)
    Subtype.val_injective

/-! ## The order-four structural matroid and annihilator -/

/-- **Order-four operator matroid.**  For any faithful finite selection of face coordinates from
the four layers, the nonlinear differential matroid of every constant-coefficient
differential-operator family is the localized operator-row matroid. -/
theorem orderFourStructural_differentialMatroid
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (face : κ → Finset (Fin 5)) (shift : κ → ℂ)
    (hdeep : ∀ k, 2 ≤ (((face k))ᶜ).card)
    (hshift : ∀ k, shift k ∈ faceShiftLattice τ (face k))
    (hpair : ∀ k l : κ, face k = face l → shift k = shift l → k = l)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L
          (multipleEllipticGammaDeepCoordinate τ hτ face shift)) =
      differentialOperatorRowMatroid L :=
  multipleEllipticGammaDeepSelection_differentialMatroid τ hτ hQ (by simp)
    face shift hdeep hshift hpair L

/-- **Order-four exact annihilator.**  A constant-coefficient difference operator sends the
order-four source into the differentially algebraic locus exactly when every monomial uses at least
four distinct directions. -/
theorem orderFour_differentialAlgebraicOver_xApply_iff
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (P : MvPolynomial (Fin 5) ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (xApply τ P (multipleEllipticGammaLogDerivMero τ hτ)) ↔
      P ∈ veroneseIdeal ℂ (Fin 5) 4 :=
  differentialAlgebraicOver_xApply_iff_mem_veroneseIdeal τ hτ hQ 4 (by simp) P

/-- **Order-four transverse depth.** -/
theorem orderFour_transverseDADepth
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    multipleEllipticGammaTransverseDADepth τ hτ = 4 :=
  multipleEllipticGammaTransverseDADepth_eq_order τ hτ hQ 4 (by omega) (by simp)

/-- **Order-four multiplicative classification.**  A finite integer product of translated
order-four multiple elliptic gamma functions is differentially algebraic exactly when its exponent
operator lies in the squarefree degree-four ideal. -/
theorem orderFour_differentialAlgebraicOver_translateGammaProduct_iff
    (τ : Fin 5 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (c : ((Fin 5) →₀ ℕ) →₀ ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (translateGammaProduct τ hτ c) ↔
      translateProductOperator c ∈ veroneseIdeal ℂ (Fin 5) 4 :=
  differentialAlgebraicOver_translateGammaProduct_iff_mem_veroneseIdeal τ hτ hQ 4 (by simp) c

end

end GaloisForLFunctions
