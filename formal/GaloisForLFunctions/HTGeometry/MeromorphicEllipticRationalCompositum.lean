import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositum
import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.GammaShiftEigenrelation

/-!
# The rationally augmented paired elliptic compositum

The paired elliptic carrier used in the elliptic-gamma Ostrowski argument must contain the
rational coordinate field, not only the two periodic meromorphic fields.  This module constructs
that base inside the genuine global meromorphic field.

The rational coordinate image is viewed as the bottom intermediate field over `RatFunc ℂ`, then
restricted to `ℂ`.  This presentation makes its derivation closure immediate from the existing
compatibility of the rational and meromorphic coordinate derivations.  Adjoining it to the paired
elliptic compositum gives a field which is closed under differentiation and invariant in both
directions under unit translation.  The ambient translation therefore restricts to a genuine
differential algebra automorphism of the augmented carrier.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicEllipticRationalCompositumDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicEllipticRationalCompositumComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicEllipticRationalCompositumComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance meromorphicEllipticRationalCompositumDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meromorphicEllipticRationalCompositumRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance meromorphicEllipticRationalCompositumRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance meromorphicEllipticRationalCompositumDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

/-- Constant rational functions and the chosen embedded complex constants have the same image in
the global meromorphic field. -/
theorem meromorphicRatFunc_algebraMap_complex (c : ℂ) :
    algebraMap (RatFunc ℂ) (meroField Set.univ)
        (algebraMap ℂ (RatFunc ℂ) c) =
      algebraMap ℂ (meroField Set.univ) c := by
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (RatFunc.C c) =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c)
  rw [show RatFunc.C c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) by rfl,
    ratfuncToMero_algebraMap_polynomial]
  change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (polyToAnalytic Set.univ (Polynomial.C c)) =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (constToAnalytic Set.univ c)
  congr 1
  apply Subtype.ext
  change Germ.ofFun (l := Filter.principal Set.univ)
      (fun z : ℂ => (Polynomial.C c).eval z) =
    Germ.ofFun (l := Filter.principal Set.univ) (fun _ : ℂ => c)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by simp

local instance meromorphicEllipticRationalCompositumScalarTower :
    IsScalarTower ℂ (RatFunc ℂ) (meroField Set.univ) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (meromorphicRatFunc_algebraMap_complex c).symm

/-- Additive translation as an algebra equivalence over the embedded complex constants. -/
noncomputable def addTranslationMeroAlgEquiv (q : ℂ) :
    meroField (Set.univ : Set ℂ) ≃ₐ[ℂ] meroField (Set.univ : Set ℂ) :=
  { addTranslationMeroEquiv q with
    commutes' := addTranslationMeroEquiv_algebraMap_complex q }

/-- The genuine image of `ℂ(X)` in the global meromorphic field, regarded as an intermediate
field over `ℂ`. -/
def meromorphicRationalCoordinateField :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  (⊥ : IntermediateField (RatFunc ℂ) (meroField Set.univ)).restrictScalars ℂ

theorem mem_meromorphicRationalCoordinateField_iff
    (x : meroField (Set.univ : Set ℂ)) :
    x ∈ meromorphicRationalCoordinateField ↔
      ∃ r : RatFunc ℂ,
        algebraMap (RatFunc ℂ) (meroField Set.univ) r = x := by
  rw [meromorphicRationalCoordinateField,
    IntermediateField.mem_restrictScalars, IntermediateField.mem_bot]
  rfl

/-- The rational coordinate image is closed under the genuine meromorphic derivation. -/
theorem meromorphicRationalCoordinateField_derivationClosed :
    DerivationClosed meromorphicRationalCoordinateField := by
  intro x hx
  obtain ⟨r, rfl⟩ :=
    (mem_meromorphicRationalCoordinateField_iff x).mp hx
  rw [deriv_algebraMap]
  exact (mem_meromorphicRationalCoordinateField_iff _).mpr ⟨r′, rfl⟩

/-- Unit translation preserves the rational coordinate image. -/
theorem addTranslationMeroAlgEquiv_one_mem_rationalCoordinateField
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicRationalCoordinateField) :
    addTranslationMeroAlgEquiv 1 x ∈ meromorphicRationalCoordinateField := by
  obtain ⟨r, rfl⟩ :=
    (mem_meromorphicRationalCoordinateField_iff x).mp hx
  apply (mem_meromorphicRationalCoordinateField_iff _).mpr
  refine ⟨ratShift r, ?_⟩
  exact (addTranslationMeroEquiv_ratfuncToMero r).symm

/-- Inverse unit translation also preserves the rational coordinate image. -/
theorem addTranslationMeroAlgEquiv_one_symm_mem_rationalCoordinateField
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicRationalCoordinateField) :
    (addTranslationMeroAlgEquiv 1).symm x ∈
      meromorphicRationalCoordinateField := by
  obtain ⟨r, rfl⟩ :=
    (mem_meromorphicRationalCoordinateField_iff x).mp hx
  apply (mem_meromorphicRationalCoordinateField_iff _).mpr
  refine ⟨ratShiftInv r, ?_⟩
  apply (addTranslationMeroAlgEquiv 1).injective
  rw [(addTranslationMeroAlgEquiv 1).apply_symm_apply]
  change addTranslationMeroEquiv 1
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (ratShiftInv r)) =
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ r
  rw [addTranslationMeroEquiv_ratfuncToMero, ratShift_ratShiftInv]

/-- Every element of the paired elliptic compositum is fixed by unit translation. -/
theorem addTranslationMeroAlgEquiv_one_fixed_of_mem_ellipticCompositum
    (σ τ : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticCompositum σ τ) :
    addTranslationMeroAlgEquiv 1 x = x := by
  change addTranslationMeroEquiv 1 x = x
  rw [meromorphicEllipticCompositum, IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction ℂ
    (s := ((ellipticMeroField σ : Set (meroField Set.univ)) ∪
      (ellipticMeroField τ : Set (meroField Set.univ))))
    (p := fun y _ => addTranslationMeroEquiv 1 y = y)
  · rintro y (hy | hy)
    · exact ((mem_ellipticMeroField_iff σ y).mp hy).1
    · exact ((mem_ellipticMeroField_iff τ y).mp hy).1
  · exact addTranslationMeroEquiv_algebraMap_complex 1
  · intro a b ha hb hfa hfb
    rw [map_add, hfa, hfb]
  · intro a ha hfa
    rw [map_inv₀, hfa]
  · intro a b ha hb hfa hfb
    rw [map_mul, hfa, hfb]
  exact hx

/-! ## The augmented carrier -/

/-- The compositum of the two elliptic coefficient fields and the genuine rational coordinate
field. -/
def meromorphicEllipticRationalCompositum (σ τ : ℂ) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  meromorphicEllipticCompositum σ τ ⊔ meromorphicRationalCoordinateField

theorem meromorphicEllipticCompositum_le_rationalCompositum (σ τ : ℂ) :
    meromorphicEllipticCompositum σ τ ≤
      meromorphicEllipticRationalCompositum σ τ :=
  le_sup_left

theorem meromorphicRationalCoordinateField_le_ellipticRationalCompositum
    (σ τ : ℂ) :
    meromorphicRationalCoordinateField ≤
      meromorphicEllipticRationalCompositum σ τ :=
  le_sup_right

/-- The rationally augmented paired elliptic carrier is closed under differentiation. -/
theorem meromorphicEllipticRationalCompositum_derivationClosed (σ τ : ℂ) :
    DerivationClosed (meromorphicEllipticRationalCompositum σ τ) :=
  derivationClosed_sup
    (meromorphicEllipticCompositum_derivationClosed σ τ)
    meromorphicRationalCoordinateField_derivationClosed

/-- Forward unit translation preserves the complete augmented carrier. -/
theorem addTranslationMeroAlgEquiv_one_mem_ellipticRationalCompositum
    (σ τ : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticRationalCompositum σ τ) :
    addTranslationMeroAlgEquiv 1 x ∈
      meromorphicEllipticRationalCompositum σ τ := by
  rw [meromorphicEllipticRationalCompositum,
    IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction ℂ
    (s := ((meromorphicEllipticCompositum σ τ : Set (meroField Set.univ)) ∪
      (meromorphicRationalCoordinateField : Set (meroField Set.univ))))
    (p := fun y _ => addTranslationMeroAlgEquiv 1 y ∈
      meromorphicEllipticRationalCompositum σ τ)
  · rintro y (hy | hy)
    · rw [addTranslationMeroAlgEquiv_one_fixed_of_mem_ellipticCompositum σ τ hy]
      exact meromorphicEllipticCompositum_le_rationalCompositum σ τ hy
    · exact meromorphicRationalCoordinateField_le_ellipticRationalCompositum σ τ
        (addTranslationMeroAlgEquiv_one_mem_rationalCoordinateField hy)
  · intro c
    exact (meromorphicEllipticRationalCompositum σ τ).algebraMap_mem c
  · intro a b ha hb hfa hfb
    rw [map_add]
    exact (meromorphicEllipticRationalCompositum σ τ).add_mem hfa hfb
  · intro a ha hfa
    rw [map_inv₀]
    exact (meromorphicEllipticRationalCompositum σ τ).inv_mem hfa
  · intro a b ha hb hfa hfb
    rw [map_mul]
    exact (meromorphicEllipticRationalCompositum σ τ).mul_mem hfa hfb
  exact hx

/-- Inverse unit translation preserves the complete augmented carrier. -/
theorem addTranslationMeroAlgEquiv_one_symm_mem_ellipticRationalCompositum
    (σ τ : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticRationalCompositum σ τ) :
    (addTranslationMeroAlgEquiv 1).symm x ∈
      meromorphicEllipticRationalCompositum σ τ := by
  rw [meromorphicEllipticRationalCompositum,
    IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction ℂ
    (s := ((meromorphicEllipticCompositum σ τ : Set (meroField Set.univ)) ∪
      (meromorphicRationalCoordinateField : Set (meroField Set.univ))))
    (p := fun y _ => (addTranslationMeroAlgEquiv 1).symm y ∈
      meromorphicEllipticRationalCompositum σ τ)
  · rintro y (hy | hy)
    · have hfixed :=
        addTranslationMeroAlgEquiv_one_fixed_of_mem_ellipticCompositum σ τ hy
      have hinv : (addTranslationMeroAlgEquiv 1).symm y = y := by
        have := congrArg (addTranslationMeroAlgEquiv 1).symm hfixed
        simpa using this.symm
      rw [hinv]
      exact meromorphicEllipticCompositum_le_rationalCompositum σ τ hy
    · exact meromorphicRationalCoordinateField_le_ellipticRationalCompositum σ τ
        (addTranslationMeroAlgEquiv_one_symm_mem_rationalCoordinateField hy)
  · intro c
    rw [(addTranslationMeroAlgEquiv 1).symm.commutes]
    exact (meromorphicEllipticRationalCompositum σ τ).algebraMap_mem c
  · intro a b ha hb hfa hfb
    rw [map_add]
    exact (meromorphicEllipticRationalCompositum σ τ).add_mem hfa hfb
  · intro a ha hfa
    rw [map_inv₀]
    exact (meromorphicEllipticRationalCompositum σ τ).inv_mem hfa
  · intro a b ha hb hfa hfb
    rw [map_mul]
    exact (meromorphicEllipticRationalCompositum σ τ).mul_mem hfa hfb
  exact hx

/-- Unit translation restricted to the augmented paired elliptic carrier. -/
noncomputable def meromorphicEllipticRationalCompositumUnitTranslationAlgHom
    (σ τ : ℂ) :
    meromorphicEllipticRationalCompositum σ τ →ₐ[ℂ]
      meromorphicEllipticRationalCompositum σ τ :=
  (((addTranslationMeroAlgEquiv 1).toAlgHom.comp
      (meromorphicEllipticRationalCompositum σ τ).val).codRestrict
    (meromorphicEllipticRationalCompositum σ τ).toSubalgebra
    (fun x => addTranslationMeroAlgEquiv_one_mem_ellipticRationalCompositum
      σ τ x.2))

theorem meromorphicEllipticRationalCompositumUnitTranslationAlgHom_bijective
    (σ τ : ℂ) :
    Function.Bijective
      (meromorphicEllipticRationalCompositumUnitTranslationAlgHom σ τ) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (addTranslationMeroAlgEquiv 1).injective
    exact congrArg
      (fun z : meromorphicEllipticRationalCompositum σ τ =>
        (z : meroField Set.univ)) hxy
  · intro x
    let y : meromorphicEllipticRationalCompositum σ τ :=
      ⟨(addTranslationMeroAlgEquiv 1).symm x,
        addTranslationMeroAlgEquiv_one_symm_mem_ellipticRationalCompositum
          σ τ x.2⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (addTranslationMeroAlgEquiv 1).apply_symm_apply x

/-- The unit shift is a genuine algebra automorphism of the rationally augmented paired elliptic
carrier. -/
noncomputable def meromorphicEllipticRationalCompositumUnitTranslationAlgEquiv
    (σ τ : ℂ) :
    meromorphicEllipticRationalCompositum σ τ ≃ₐ[ℂ]
      meromorphicEllipticRationalCompositum σ τ :=
  AlgEquiv.ofBijective
    (meromorphicEllipticRationalCompositumUnitTranslationAlgHom σ τ)
    (meromorphicEllipticRationalCompositumUnitTranslationAlgHom_bijective σ τ)

/-- The restricted unit shift commutes with the restricted meromorphic derivation. -/
theorem meromorphicEllipticRationalCompositumUnitTranslation_deriv
    (σ τ : ℂ) (x : meromorphicEllipticRationalCompositum σ τ) :
    letI : Differential (meromorphicEllipticRationalCompositum σ τ) :=
      derivationClosedDifferential _
        (meromorphicEllipticRationalCompositum_derivationClosed σ τ)
    meromorphicEllipticRationalCompositumUnitTranslationAlgEquiv σ τ x′ =
      (meromorphicEllipticRationalCompositumUnitTranslationAlgEquiv σ τ x)′ := by
  dsimp only [meromorphicEllipticRationalCompositumUnitTranslationAlgEquiv]
  apply Subtype.ext
  change addTranslationMeroEquiv 1 ((x : meroField Set.univ)′) =
    (addTranslationMeroEquiv 1 (x : meroField Set.univ))′
  exact addTranslationMeroEquiv_deriv 1 x

end

end GaloisForLFunctions
