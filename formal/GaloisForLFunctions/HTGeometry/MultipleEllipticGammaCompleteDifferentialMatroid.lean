import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaAllFaceIndependence
import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid

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

/-- Every injectively selected finite family of translated non-boundary face coordinates in the
complete multiple elliptic-gamma hierarchy is differentially independent. -/
theorem multipleEllipticGammaSelectedFaces_differentialIndependent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ : Type} (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x) :
    DifferentialIndependent ℂ x := by
  have hall := multipleEllipticGammaProperFacePackets_diffIndepOn τ hτ hQ hι
  unfold DiffIndepOn at hall
  exact hall.comp
    (fun k => ⟨x k, hxmem k⟩)
    (fun a b hab => hxinj (congrArg Subtype.val hab))

/-- The same complete selected-face independence over the natural rational coordinate field
`ℂ(z)`. -/
theorem multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ : Type} (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x) :
    DifferentialIndependent meromorphicRationalCoordinateField x := by
  have hC := multipleEllipticGammaSelectedFaces_differentialIndependent
    τ hτ hQ hι x hxmem hxinj
  have hCoordinate :=
    HTGeometry.DifferentialIndependent.extendScalarsDifferentialAdjoinSingleton
      hC differentialAlgebraicOver_meromorphicRationalCoordinate
  rw [differentialAdjoin_meromorphicRationalCoordinate_eq] at hCoordinate
  exact hCoordinate

/-- **Exact two-survivor phase boundary.**  A translated face coordinate is differentially
algebraic over `ℂ(z)` exactly when its face retains fewer than two periods. -/
theorem multipleEllipticGammaFacePacket_differentialAlgebraic_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    DifferentialAlgebraicOver meromorphicRationalCoordinateField y ↔
      (Jᶜ).card < 2 := by
  constructor
  · intro hda
    by_contra hnot
    have htwo : 2 ≤ (Jᶜ).card := by omega
    have hxmem : ∀ _ : Unit, y ∈
        facePacketUnion τ hτ {L : Finset ι | 2 ≤ (Lᶜ).card} := by
      intro _
      exact Set.mem_iUnion₂.mpr ⟨J, htwo, hy⟩
    have hsingle :=
      multipleEllipticGammaSelectedFaces_differentialIndependent_rationalBase
        τ hτ hQ hι (fun _ : Unit => y) hxmem (by intro a b _; exact Subsingleton.elim a b)
    have hht : HypertranscendentalOver meromorphicRationalCoordinateField y := by
      rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
      simpa using hsingle
    exact hht hda
  · intro hlt
    rw [differentialAlgebraicOver_meromorphicRationalCoordinateField_iff]
    exact differentialAlgebraicOver_facePacket_of_compl_lt_two
      τ hτ hQ hι J hlt hy

/-- **Complete differential-matroid law for the multiple elliptic-gamma hierarchy.**

For any finite selection of distinct translated non-boundary face coordinates and every finite
family of constant-coefficient differential-operator rows, the nonlinear differential matroid of
the resulting functions is exactly the ordinary row matroid over the fraction field of `ℂ[∂]`. -/
theorem multipleEllipticGammaCompleteDifferentialMatroid
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ]
    [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ) (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L := by
  exact differentialFamilyMatroid_differentialOperatorRows_eq
    meroField_deriv_algebraMap_complex_rationalBase L x
    (multipleEllipticGammaSelectedFaces_differentialIndependent
      τ hτ hQ hι x hxmem hxinj)

/-- Natural-base form of the complete law.  The nonlinear matroid over `ℂ(z)` remains the
constant-coefficient operator-row matroid over `Frac(ℂ[∂])`. -/
theorem multipleEllipticGammaCompleteDifferentialMatroid_rationalBase
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ]
    [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L := by
  rw [differentialFamilyMatroid]
  rw [differentialMatroid_meromorphicRationalCoordinateField_eq]
  exact multipleEllipticGammaCompleteDifferentialMatroid
    τ hτ hQ hι x hxmem hxinj L

/-- Numerical form of the complete law: differential transcendence rank equals localized
constant-coefficient differential-operator row rank for every finite output packet. -/
theorem multipleEllipticGammaCompleteDifferentialRank
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ]
    [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L x)).eRk (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) := by
  exact differentialOperatorRows_eRk_eq_finrank_span
    meroField_deriv_algebraMap_complex_rationalBase L x
    (multipleEllipticGammaSelectedFaces_differentialIndependent
      τ hτ hQ hι x hxmem hxinj) I

/-- Natural-base numerical rank law over `ℂ(z)`. -/
theorem multipleEllipticGammaCompleteDifferentialRank_rationalBase
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {κ ρ : Type} [Fintype κ] [Fintype ρ]
    [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L x)).eRk (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) := by
  rw [differentialFamilyMatroid]
  rw [differentialMatroid_meromorphicRationalCoordinateField_eq]
  exact multipleEllipticGammaCompleteDifferentialRank
    τ hτ hQ hι x hxmem hxinj L I

end

end GaloisForLFunctions
