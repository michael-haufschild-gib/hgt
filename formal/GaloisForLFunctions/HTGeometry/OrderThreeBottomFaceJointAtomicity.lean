import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid

/-!
# Joint atomicity of the six order-three bottom faces

Let `τ : Fin 4 → ℂ` be an order-three period family whose periods admit no integral relation with
`1`.  The bottom faces of the hierarchy are the two-element deletions `J = {i, j}`; there are six
of them, and the coordinate of the face `{i, j}` is the order-one elliptic-gamma logarithmic
derivative attached to the complementary parameter pair.  Its external orbit consists of the
translates by `a τ i + b τ j`.

The six external orbits are jointly differentially independent over `ℂ` and over `ℂ(z)`: distinct
orbit coordinates carry no nonlinear differential relation, even though all six descend from the
same order-three primitive.  Passing back through logarithmic derivatives, the corresponding
translated order-one elliptic gamma functions are jointly differentially independent as well.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-! ## The six bottom faces -/

/-- The bottom faces of the order-three hierarchy: the two-element deletions. -/
def orderThreeBottomFaces : Set (Finset (Fin 4)) := {J | J.card = 2}

/-- There are exactly six bottom faces. -/
theorem orderThreeBottomFaces_card_six :
    (Finset.univ.filter fun J : Finset (Fin 4) => J.card = 2).card = 6 := by decide

/-- Each bottom face retains exactly two periods, so it is a proper face of the hierarchy. -/
theorem orderThreeBottomFaces_subset_properFaces :
    orderThreeBottomFaces ⊆ {J : Finset (Fin 4) | 2 ≤ (Jᶜ).card} := by
  intro J hJ
  have htotal := Finset.card_add_card_compl J
  simp only [Fintype.card_fin] at htotal
  simp only [orderThreeBottomFaces, Set.mem_setOf_eq] at hJ ⊢
  omega

theorem orderThreeBottomFacePacketUnion_subset (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    facePacketUnion τ hτ orderThreeBottomFaces ⊆
      facePacketUnion τ hτ {J : Finset (Fin 4) | 2 ≤ (Jᶜ).card} :=
  Set.biUnion_mono orderThreeBottomFaces_subset_properFaces fun _ _ => subset_rfl

/-! ## Joint independence of the six bottom-face orbits -/

/-- **Order-three bottom-face joint atomicity.**  The union of the six external orbits of the
bottom faces is differentially independent over the constants. -/
theorem orderThreeBottomFaceOrbits_diffIndepOn
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    DiffIndepOn ℂ (facePacketUnion τ hτ orderThreeBottomFaces) :=
  (multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ (by simp)).subset
    (orderThreeBottomFacePacketUnion_subset τ hτ)

/-- The same joint atomicity over the natural rational coordinate field `ℂ(z)`. -/
theorem orderThreeBottomFaceOrbits_diffIndepOn_rationalBase
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ) :
    DiffIndepOn meromorphicRationalCoordinateField
      (facePacketUnion τ hτ orderThreeBottomFaces) :=
  multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase τ hτ hQ (by simp)
    (Subtype.val) (fun k => orderThreeBottomFacePacketUnion_subset τ hτ k.2)
    Subtype.val_injective

/-! ## The explicit orbit coordinates -/

/-- The orbit coordinate `T_i^a T_j^b A_{ij}`: the bottom-face coordinate of `{i, j}` translated by
`a τ i + b τ j`. -/
def orderThreeBottomFaceOrbitCoordinate
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (i j : Fin 4) (a b : ℤ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv ((a : ℂ) * τ i + (b : ℂ) * τ j)
    (multipleEllipticGammaLogDerivFaceMero τ hτ {i, j})

theorem zero_mem_faceShiftLattice {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (J : Finset ι) : (0 : ℂ) ∈ faceShiftLattice τ J :=
  ⟨0, fun _ _ => rfl, by simp⟩

theorem orderThreeBottomFaceShift_mem_faceShiftLattice
    (τ : Fin 4 → ℂ) (i j : Fin 4) (a b : ℤ) :
    (a : ℂ) * τ i + (b : ℂ) * τ j ∈ faceShiftLattice τ {i, j} := by
  have hj : j ∈ ({i, j} : Finset (Fin 4)) := by simp
  have hi : i ∈ ({i, j} : Finset (Fin 4)) := by simp
  have hb := faceShiftLattice_add_zsmul τ {i, j} hj (zero_mem_faceShiftLattice τ {i, j}) b
  have ha := faceShiftLattice_add_zsmul τ {i, j} hi (by simpa using hb) a
  simpa using ha

theorem orderThreeBottomFaceOrbitCoordinate_mem
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) {i j : Fin 4} (hij : i ≠ j) (a b : ℤ) :
    orderThreeBottomFaceOrbitCoordinate τ hτ i j a b ∈
      facePacketUnion τ hτ orderThreeBottomFaces := by
  refine Set.mem_iUnion₂.mpr ⟨{i, j}, ?_, ?_⟩
  · simpa [orderThreeBottomFaces] using Finset.card_pair hij
  · exact ⟨(a : ℂ) * τ i + (b : ℂ) * τ j,
      orderThreeBottomFaceShift_mem_faceShiftLattice τ i j a b, rfl⟩

/-- **Exact finite-family atomicity.**  Any family of pairwise distinct bottom-face orbit
coordinates is differentially independent over `ℂ(z)`; its differential transcendence degree is
therefore the number of its members. -/
theorem orderThreeBottomFaceOrbitCoordinates_differentialIndependent_rationalBase
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {κ : Type} (p q : κ → Fin 4) (a b : κ → ℤ) (hpq : ∀ k, p k ≠ q k)
    (hinj : Function.Injective
      fun k => orderThreeBottomFaceOrbitCoordinate τ hτ (p k) (q k) (a k) (b k)) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (fun k => orderThreeBottomFaceOrbitCoordinate τ hτ (p k) (q k) (a k) (b k)) :=
  multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase τ hτ hQ (by simp) _
    (fun k => orderThreeBottomFacePacketUnion_subset τ hτ
      (orderThreeBottomFaceOrbitCoordinate_mem τ hτ (hpq k) (a k) (b k)))
    hinj

/-! ## The multiplicative family -/

/-- The translated order-one elliptic gamma function attached to the bottom face `{i, j}`. -/
def orderThreeBottomFaceGamma
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (i j : Fin 4) (a b : ℤ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv ((a : ℂ) * τ i + (b : ℂ) * τ j)
    (multipleEllipticGammaMero (multipleEllipticGammaFaceParameters τ {i, j})
      (fun k => hτ k.1))

/-- The orbit coordinate is the logarithmic derivative of the translated gamma function. -/
theorem logDeriv_orderThreeBottomFaceGamma
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (i j : Fin 4) (a b : ℤ) :
    (orderThreeBottomFaceGamma τ hτ i j a b)′ / orderThreeBottomFaceGamma τ hτ i j a b =
      orderThreeBottomFaceOrbitCoordinate τ hτ i j a b := by
  set g : ℂ := (a : ℂ) * τ i + (b : ℂ) * τ j with hg
  set G : meroField (Set.univ : Set ℂ) :=
    multipleEllipticGammaMero (multipleEllipticGammaFaceParameters τ {i, j})
      (fun k => hτ k.1) with hG
  have hderiv : (addTranslationMeroEquiv g G)′ = addTranslationMeroEquiv g (G′) :=
    (addTranslationMeroEquiv_deriv g G).symm
  rw [orderThreeBottomFaceGamma, orderThreeBottomFaceOrbitCoordinate,
    multipleEllipticGammaLogDerivFaceMero, multipleEllipticGammaLogDerivMero,
    Differential.logDeriv, ← hG, hderiv, ← map_div₀]

/-- **Multiplicative joint atomicity.**  The translated order-one elliptic gamma functions of the
six bottom faces are jointly differentially independent over `ℂ(z)` whenever their logarithmic
derivatives are distinct. -/
theorem orderThreeBottomFaceGammas_differentialIndependent_rationalBase
    (τ : Fin 4 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {κ : Type} (p q : κ → Fin 4) (a b : κ → ℤ) (hpq : ∀ k, p k ≠ q k)
    (hinj : Function.Injective
      fun k => orderThreeBottomFaceOrbitCoordinate τ hτ (p k) (q k) (a k) (b k)) :
    DifferentialIndependent meromorphicRationalCoordinateField
      (fun k => orderThreeBottomFaceGamma τ hτ (p k) (q k) (a k) (b k)) := by
  rw [differentialIndependent_deriv_div_self_iff]
  have hlog : (fun k => (orderThreeBottomFaceGamma τ hτ (p k) (q k) (a k) (b k))′ /
        orderThreeBottomFaceGamma τ hτ (p k) (q k) (a k) (b k)) =
      fun k => orderThreeBottomFaceOrbitCoordinate τ hτ (p k) (q k) (a k) (b k) := by
    funext k
    exact logDeriv_orderThreeBottomFaceGamma τ hτ (p k) (q k) (a k) (b k)
  rw [hlog]
  exact orderThreeBottomFaceOrbitCoordinates_differentialIndependent_rationalBase
    τ hτ hQ p q a b hpq hinj

end

end GaloisForLFunctions
