import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositum
import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect

/-!
# The rationally augmented paired elliptic compositum

The paired elliptic carrier used in the elliptic-gamma Ostrowski argument must contain the
rational coordinate field, not only the two periodic meromorphic fields.  This module constructs
that base inside the genuine global meromorphic field.

The rational coordinate image is viewed as the bottom intermediate field over `RatFunc ℂ`, then
restricted to `ℂ`.  This presentation makes its derivation closure immediate from the existing
compatibility of the rational and meromorphic coordinate derivations.  Adjoining it to the paired
elliptic compositum gives a field which is closed under differentiation and invariant in both
directions under every additive translation.  Each ambient translation therefore restricts to a
genuine differential algebra automorphism of the augmented carrier.
-/

open Filter Topology Set Function
open scoped Differential nonZeroDivisors

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

/-! ## Arbitrary rational-coordinate translations -/

/-- Polynomial substitution by `X + q`, valued in the rational function field. -/
def ratFuncAddTranslationCompHom (q : ℂ) : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.eval₂RingHom Polynomial.C
      (Polynomial.X + Polynomial.C q))

theorem ratFuncAddTranslationCompHom_apply (q : ℂ) (p : Polynomial ℂ) :
    ratFuncAddTranslationCompHom q p =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (p.comp (Polynomial.X + Polynomial.C q)) :=
  rfl

theorem polynomial_comp_X_add_C_ne_zero
    (q : ℂ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (Polynomial.X + Polynomial.C q) ≠ 0 := by
  intro hzero
  exact hp ((Polynomial.comp_eq_zero_iff.mp hzero).resolve_right
    (fun hconstant => by simpa using hconstant.2))

theorem ratFuncAddTranslationCompHom_mem_nonZeroDivisors (q : ℂ) :
    (Polynomial ℂ)⁰ ≤
      (RatFunc ℂ)⁰.comap (ratFuncAddTranslationCompHom q) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [ratFuncAddTranslationCompHom_apply]
  intro hzero
  exact polynomial_comp_X_add_C_ne_zero q hp
    (RatFunc.algebraMap_injective ℂ (by rw [hzero, map_zero]))

/-- The arbitrary translation endomorphism `r(X) ↦ r(X+q)` of `ℂ(X)`. -/
def ratFuncAddTranslation (q : ℂ) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom (ratFuncAddTranslationCompHom q)
    (ratFuncAddTranslationCompHom_mem_nonZeroDivisors q)

theorem ratFuncAddTranslation_algebraMap
    (q : ℂ) (p : Polynomial ℂ) :
    ratFuncAddTranslation q
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (p.comp (Polynomial.X + Polynomial.C q)) := by
  have h := RatFunc.liftRingHom_apply_div
    (ratFuncAddTranslationCompHom q)
    (ratFuncAddTranslationCompHom_mem_nonZeroDivisors q) p 1
  simpa only [map_one, div_one] using h

/-- Global meromorphic translation intertwines arbitrary rational-coordinate translation. -/
theorem addTranslationMeroEquiv_ratfuncToMero_addTranslation
    (q : ℂ) (r : RatFunc ℂ) :
    addTranslationMeroEquiv q
        (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ r) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (ratFuncAddTranslation q r) := by
  let rho := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
  have hhom :
      (addTranslationMeroEquiv q).toRingHom.comp rho =
        rho.comp (ratFuncAddTranslation q) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply,
      ratfuncToMero_algebraMap_polynomial,
      ratFuncAddTranslation_algebraMap,
      ratfuncToMero_algebraMap_polynomial]
    simp only [polyToMero, RingHom.comp_apply]
    change addTranslationMeroEquiv q
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ p)) = _
    rw [addTranslationMeroEquiv_algebraMap,
      addTranslationAnalyticEquiv_polyToAnalytic]
  exact RingHom.congr_fun hhom r

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

/-- Every additive translation preserves the rational coordinate image. -/
theorem addTranslationMeroAlgEquiv_mem_rationalCoordinateField
    (q : ℂ)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicRationalCoordinateField) :
    addTranslationMeroAlgEquiv q x ∈ meromorphicRationalCoordinateField := by
  obtain ⟨r, rfl⟩ :=
    (mem_meromorphicRationalCoordinateField_iff x).mp hx
  apply (mem_meromorphicRationalCoordinateField_iff _).mpr
  refine ⟨ratFuncAddTranslation q r, ?_⟩
  exact (addTranslationMeroEquiv_ratfuncToMero_addTranslation q r).symm

/-- Zero translation is the identity on the global meromorphic field. -/
theorem addTranslationMeroAlgEquiv_zero_apply
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroAlgEquiv 0 x = x := by
  change addTranslationMeroEquiv 0 x = x
  apply (addTranslationMeroEquiv 0).injective
  simpa using addTranslationMeroEquiv_add 0 0 x

/-- The inverse of translation by `q` is translation by `-q`. -/
theorem addTranslationMeroAlgEquiv_symm_apply
    (q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    (addTranslationMeroAlgEquiv q).symm x =
      addTranslationMeroAlgEquiv (-q) x := by
  symm
  apply (addTranslationMeroAlgEquiv q).injective
  rw [(addTranslationMeroAlgEquiv q).apply_symm_apply]
  change addTranslationMeroEquiv q (addTranslationMeroEquiv (-q) x) = x
  rw [addTranslationMeroEquiv_add, add_neg_cancel]
  exact addTranslationMeroAlgEquiv_zero_apply x

/-- Inverse additive translation preserves the rational coordinate image. -/
theorem addTranslationMeroAlgEquiv_symm_mem_rationalCoordinateField
    (q : ℂ)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicRationalCoordinateField) :
    (addTranslationMeroAlgEquiv q).symm x ∈
      meromorphicRationalCoordinateField := by
  rw [addTranslationMeroAlgEquiv_symm_apply]
  exact addTranslationMeroAlgEquiv_mem_rationalCoordinateField (-q) hx

/-- Translation by `q` preserves every translation-fixed meromorphic field. -/
theorem addTranslationMeroAlgEquiv_mem_translationFixedField
    (p q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicTranslationFixedField p) :
    addTranslationMeroAlgEquiv q x ∈ meromorphicTranslationFixedField p := by
  change addTranslationMeroEquiv p x = x at hx
  change addTranslationMeroEquiv p (addTranslationMeroEquiv q x) =
    addTranslationMeroEquiv q x
  calc
    addTranslationMeroEquiv p (addTranslationMeroEquiv q x) =
        addTranslationMeroEquiv (p + q) x :=
      addTranslationMeroEquiv_add p q x
    _ = addTranslationMeroEquiv (q + p) x := by rw [add_comm]
    _ = addTranslationMeroEquiv q (addTranslationMeroEquiv p x) :=
      (addTranslationMeroEquiv_add q p x).symm
    _ = addTranslationMeroEquiv q x := congrArg (addTranslationMeroEquiv q) hx

/-- Every additive translation preserves a concrete elliptic meromorphic field. -/
theorem addTranslationMeroAlgEquiv_mem_ellipticMeroField
    (p q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ ellipticMeroField p) :
    addTranslationMeroAlgEquiv q x ∈ ellipticMeroField p := by
  rw [mem_ellipticMeroField_iff] at hx ⊢
  exact ⟨
    addTranslationMeroAlgEquiv_mem_translationFixedField 1 q hx.1,
    addTranslationMeroAlgEquiv_mem_translationFixedField p q hx.2⟩

/-- Every additive translation preserves the paired elliptic compositum. -/
theorem addTranslationMeroAlgEquiv_mem_ellipticCompositum
    (σ τ q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticCompositum σ τ) :
    addTranslationMeroAlgEquiv q x ∈ meromorphicEllipticCompositum σ τ := by
  rw [meromorphicEllipticCompositum, IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction ℂ
    (s := ((ellipticMeroField σ : Set (meroField Set.univ)) ∪
      (ellipticMeroField τ : Set (meroField Set.univ))))
    (p := fun y _ => addTranslationMeroAlgEquiv q y ∈
      meromorphicEllipticCompositum σ τ)
  · rintro y (hy | hy)
    · exact (show ellipticMeroField σ ≤
          meromorphicEllipticCompositum σ τ by
            rw [meromorphicEllipticCompositum]
            exact le_sup_left)
        (addTranslationMeroAlgEquiv_mem_ellipticMeroField σ q hy)
    · exact (show ellipticMeroField τ ≤
          meromorphicEllipticCompositum σ τ by
            rw [meromorphicEllipticCompositum]
            exact le_sup_right)
        (addTranslationMeroAlgEquiv_mem_ellipticMeroField τ q hy)
  · intro c
    exact (meromorphicEllipticCompositum σ τ).algebraMap_mem c
  · intro a b ha hb hfa hfb
    rw [map_add]
    exact (meromorphicEllipticCompositum σ τ).add_mem hfa hfb
  · intro a ha hfa
    rw [map_inv₀]
    exact (meromorphicEllipticCompositum σ τ).inv_mem hfa
  · intro a b ha hb hfa hfb
    rw [map_mul]
    exact (meromorphicEllipticCompositum σ τ).mul_mem hfa hfb
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

/-- Every additive translation preserves the complete augmented carrier. -/
theorem addTranslationMeroAlgEquiv_mem_ellipticRationalCompositum
    (σ τ q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticRationalCompositum σ τ) :
    addTranslationMeroAlgEquiv q x ∈
      meromorphicEllipticRationalCompositum σ τ := by
  rw [meromorphicEllipticRationalCompositum,
    IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction ℂ
    (s := ((meromorphicEllipticCompositum σ τ : Set (meroField Set.univ)) ∪
      (meromorphicRationalCoordinateField : Set (meroField Set.univ))))
    (p := fun y _ => addTranslationMeroAlgEquiv q y ∈
      meromorphicEllipticRationalCompositum σ τ)
  · rintro y (hy | hy)
    · exact meromorphicEllipticCompositum_le_rationalCompositum σ τ
        (addTranslationMeroAlgEquiv_mem_ellipticCompositum σ τ q hy)
    · exact meromorphicRationalCoordinateField_le_ellipticRationalCompositum σ τ
        (addTranslationMeroAlgEquiv_mem_rationalCoordinateField q hy)
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

/-- Inverse additive translation preserves the complete augmented carrier. -/
theorem addTranslationMeroAlgEquiv_symm_mem_ellipticRationalCompositum
    (σ τ q : ℂ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticRationalCompositum σ τ) :
    (addTranslationMeroAlgEquiv q).symm x ∈
      meromorphicEllipticRationalCompositum σ τ := by
  rw [addTranslationMeroAlgEquiv_symm_apply]
  exact addTranslationMeroAlgEquiv_mem_ellipticRationalCompositum
    σ τ (-q) hx

/-- Translation by `q` restricted to the augmented paired elliptic carrier. -/
noncomputable def meromorphicEllipticRationalCompositumTranslationAlgHom
    (σ τ q : ℂ) :
    meromorphicEllipticRationalCompositum σ τ →ₐ[ℂ]
      meromorphicEllipticRationalCompositum σ τ :=
  (((addTranslationMeroAlgEquiv q).toAlgHom.comp
      (meromorphicEllipticRationalCompositum σ τ).val).codRestrict
    (meromorphicEllipticRationalCompositum σ τ).toSubalgebra
    (fun x => addTranslationMeroAlgEquiv_mem_ellipticRationalCompositum
      σ τ q x.2))

theorem meromorphicEllipticRationalCompositumTranslationAlgHom_bijective
    (σ τ q : ℂ) :
    Function.Bijective
      (meromorphicEllipticRationalCompositumTranslationAlgHom σ τ q) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (addTranslationMeroAlgEquiv q).injective
    exact congrArg
      (fun z : meromorphicEllipticRationalCompositum σ τ =>
        (z : meroField Set.univ)) hxy
  · intro x
    let y : meromorphicEllipticRationalCompositum σ τ :=
      ⟨(addTranslationMeroAlgEquiv q).symm x,
        addTranslationMeroAlgEquiv_symm_mem_ellipticRationalCompositum
          σ τ q x.2⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (addTranslationMeroAlgEquiv q).apply_symm_apply x

/-- Every additive shift is a genuine algebra automorphism of the rationally augmented paired
elliptic carrier. -/
noncomputable def meromorphicEllipticRationalCompositumTranslationAlgEquiv
    (σ τ q : ℂ) :
    meromorphicEllipticRationalCompositum σ τ ≃ₐ[ℂ]
      meromorphicEllipticRationalCompositum σ τ :=
  AlgEquiv.ofBijective
    (meromorphicEllipticRationalCompositumTranslationAlgHom σ τ q)
    (meromorphicEllipticRationalCompositumTranslationAlgHom_bijective σ τ q)

/-- Every restricted additive shift commutes with the restricted meromorphic derivation. -/
theorem meromorphicEllipticRationalCompositumTranslation_deriv
    (σ τ q : ℂ) (x : meromorphicEllipticRationalCompositum σ τ) :
    letI : Differential (meromorphicEllipticRationalCompositum σ τ) :=
      derivationClosedDifferential _
        (meromorphicEllipticRationalCompositum_derivationClosed σ τ)
    meromorphicEllipticRationalCompositumTranslationAlgEquiv σ τ q x′ =
      (meromorphicEllipticRationalCompositumTranslationAlgEquiv σ τ q x)′ := by
  dsimp only [meromorphicEllipticRationalCompositumTranslationAlgEquiv]
  apply Subtype.ext
  change addTranslationMeroEquiv q ((x : meroField Set.univ)′) =
    (addTranslationMeroEquiv q (x : meroField Set.univ))′
  exact addTranslationMeroEquiv_deriv q x

end

end GaloisForLFunctions
