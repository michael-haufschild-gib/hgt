import GaloisForLFunctions.HTGeometry.DifferentialOperatorMatroid
import GaloisForLFunctions.HTGeometry.EllipticCompositumMatroidTransport
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Constant-coefficient operator matroids over the meromorphic rational base

The coordinate field `ℂ(z)` is a differential-algebraic extension of the constants, so it changes
no meromorphic differential matroid.  Consequently every exact constant-coefficient operator-row
law proved over `ℂ` transfers verbatim to `ℂ(z)`, including complete matroid and numerical rank.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance meromorphicOperatorDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meromorphicOperatorComplexAlgebra :
    Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance meromorphicOperatorMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meromorphicOperatorMeroCharZero :
    CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective

local instance meromorphicOperatorComplexDifferential : Differential ℂ where
  deriv := 0

local instance meromorphicOperatorComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ⟨fun c => by
    rw [meroField_deriv_algebraMap_complex_rationalBase]
    change (0 : meroField Set.univ) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance meromorphicOperatorCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _ meromorphicRationalCoordinateField_derivationClosed

local instance meromorphicOperatorCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField (Set.univ : Set ℂ)) :=
  ⟨fun x => derivationClosedDifferential_apply meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-- **Complete meromorphic operator-row matroid over `ℂ(z)`.**  A finite differentially
independent meromorphic source packet remains exact under arbitrary constant-coefficient
differential-operator rows: the represented nonlinear differential matroid is precisely the
localized polynomial row matroid. -/
theorem differentialFamilyMatroid_differentialOperatorRows_rationalBase_eq
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ι → κ → Polynomial ℂ)
    (x : κ → meroField (Set.univ : Set ℂ))
    (hx : DifferentialIndependent meromorphicRationalCoordinateField x) :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L := by
  have hxC : DifferentialIndependent ℂ x :=
    (differentialIndependent_meromorphicRationalCoordinateField_iff x).1 hx
  rw [differentialFamilyMatroid, differentialMatroid_meromorphicRationalCoordinateField_eq]
  exact differentialFamilyMatroid_differentialOperatorRows_eq
    meroField_deriv_algebraMap_complex_rationalBase L x hxC

/-- **Numerical meromorphic operator-row rank over `ℂ(z)`.**  On every finite output packet,
differential transcendence rank is exactly the `ℂ(δ)`-dimension of the localized operator-row
span. -/
theorem differentialOperatorRows_eRk_rationalBase_eq_finrank_span
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ι → κ → Polynomial ℂ)
    (x : κ → meroField (Set.univ : Set ℂ))
    (hx : DifferentialIndependent meromorphicRationalCoordinateField x)
    (I : Finset ι) :
    (differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (differentialOperatorRowApply L x)).eRk (↑I : Set ι) =
      (Module.finrank (FractionRing (Polynomial ℂ))
        (Submodule.span (FractionRing (Polynomial ℂ))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ι))) : ℕ∞) := by
  rw [differentialFamilyMatroid, differentialMatroid_meromorphicRationalCoordinateField_eq]
  exact differentialOperatorRows_eRk_eq_finrank_span
    meroField_deriv_algebraMap_complex_rationalBase L x
    ((differentialIndependent_meromorphicRationalCoordinateField_iff x).1 hx) I

end

end GaloisForLFunctions.HTGeometry
