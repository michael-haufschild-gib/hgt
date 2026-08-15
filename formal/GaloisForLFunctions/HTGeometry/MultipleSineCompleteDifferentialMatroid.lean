import GaloisForLFunctions.HTGeometry.MultipleSineMonomialCoefficients
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCompleteDifferentialMatroid

/-!
# The complete differential matroid of the multiple-sine hierarchy

Every injectively selected finite family of translated proper-face coordinates of the multiple sine
is differentially independent, so for every finite family of constant-coefficient
differential-operator rows the nonlinear differential matroid of the outputs is exactly the ordinary
row matroid over the fraction field of `ℂ[∂]`, and the differential transcendence rank of any finite
output packet is the localized row rank.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

noncomputable local instance mscdmDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Complete differential-matroid law for the multiple-sine hierarchy.**  For any finite selection
of distinct translated proper-face coordinates and every finite family of constant-coefficient
differential-operator rows, the nonlinear differential matroid of the resulting functions is exactly
the ordinary row matroid over the fraction field of `ℂ[∂]`. -/
theorem multipleSineCompleteDifferentialMatroid {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω
      {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := ℂ) (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L :=
  differentialFamilyMatroid_differentialOperatorRows_eq
    meroField_deriv_algebraMap_complex_rationalBase L x
    (multipleSineSelectedFaces_differentialIndependent hrad hind hω x hxmem hxinj)

set_option synthInstance.maxHeartbeats 1000000 in
/-- Natural-base form: the nonlinear matroid over `ℂ(z)` is the same operator-row matroid. -/
theorem multipleSineCompleteDifferentialMatroid_rationalBase {μ : ℂ} {rad : ι → ℝ}
    (hrad : ∀ k, 0 < rad k) (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω
      {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L := by
  rw [differentialFamilyMatroid, differentialMatroid_meromorphicRationalCoordinateField_eq]
  exact multipleSineCompleteDifferentialMatroid hrad hind hω x hxmem hxinj L

set_option synthInstance.maxHeartbeats 1000000 in
/-- Numerical form: the differential transcendence rank of a finite output packet equals the
localized constant-coefficient differential-operator row rank. -/
theorem multipleSineCompleteDifferentialRank {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {κ ρ : Type} [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (x : κ → meroField (Set.univ : Set ℂ))
    (hxmem : ∀ k, x k ∈ sineFacePacketUnion (fun k => μ * (rad k : ℂ)) hω
      {J : Finset ι | 2 ≤ (Jᶜ).card})
    (hxinj : Function.Injective x)
    (L : ρ → κ → Polynomial ℂ) (I : Finset ρ) :
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply L x)).eRk (↑I : Set ρ) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) :=
  differentialOperatorRows_eRk_eq_finrank_span
    meroField_deriv_algebraMap_complex_rationalBase L x
    (multipleSineSelectedFaces_differentialIndependent hrad hind hω x hxmem hxinj) I

end

end GaloisForLFunctions.HTGeometry
