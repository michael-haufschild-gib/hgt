import GaloisForLFunctions.HTGeometry.MeromorphicTranslation
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Meromorphic elliptic fields and their paired compositum

This file constructs the concrete intermediate field of global meromorphic germs fixed by the
translations `1` and `τ`.  It proves that this elliptic field is closed under the ambient
derivation.  The compositum of two such elliptic fields inside the global meromorphic field is
therefore again a concrete derivation-closed intermediate field.

This is the field-theoretic carrier needed by the paired elliptic-gamma Ostrowski argument.  It
does not assert the still-open finite-type product-specialization presentation of the compositum.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicEllipticCompositumDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicEllipticCompositumComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicEllipticCompositumComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance ambientMeromorphicEllipticCompositumDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Every additive translation fixes the embedded complex constant field. -/
theorem addTranslationMeroEquiv_algebraMap_complex (q c : ℂ) :
    addTranslationMeroEquiv q (algebraMap ℂ (meroField Set.univ) c) =
      algebraMap ℂ (meroField Set.univ) c := by
  change addTranslationMeroEquiv q
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c)) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c)
  rw [addTranslationMeroEquiv_algebraMap]
  congr 1

/-- The intermediate field of global meromorphic germs fixed by one additive translation. -/
def meromorphicTranslationFixedField (q : ℂ) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) where
  carrier := {x | addTranslationMeroEquiv q x = x}
  zero_mem' := map_zero (addTranslationMeroEquiv q)
  add_mem' hx hy := by
    change addTranslationMeroEquiv q (_ + _) = _
    change addTranslationMeroEquiv q _ = _ at hx hy
    rw [(addTranslationMeroEquiv q).map_add, hx, hy]
  one_mem' := map_one (addTranslationMeroEquiv q)
  mul_mem' hx hy := by
    change addTranslationMeroEquiv q (_ * _) = _
    change addTranslationMeroEquiv q _ = _ at hx hy
    rw [(addTranslationMeroEquiv q).map_mul, hx, hy]
  algebraMap_mem' c := addTranslationMeroEquiv_algebraMap_complex q c
  inv_mem' x hx := by
    change addTranslationMeroEquiv q x⁻¹ = x⁻¹
    change addTranslationMeroEquiv q x = x at hx
    calc
      addTranslationMeroEquiv q x⁻¹ = (addTranslationMeroEquiv q x)⁻¹ :=
        map_inv₀ (addTranslationMeroEquiv q) x
      _ = x⁻¹ := congrArg Inv.inv hx

@[simp] theorem mem_meromorphicTranslationFixedField_iff (q : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    x ∈ meromorphicTranslationFixedField q ↔ addTranslationMeroEquiv q x = x :=
  Iff.rfl

/-- The `(1, τ)`-elliptic meromorphic function field inside the global meromorphic germ field. -/
def ellipticMeroField (τ : ℂ) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  meromorphicTranslationFixedField 1 ⊓ meromorphicTranslationFixedField τ

@[simp] theorem mem_ellipticMeroField_iff (τ : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    x ∈ ellipticMeroField τ ↔
      addTranslationMeroEquiv 1 x = x ∧ addTranslationMeroEquiv τ x = x := by
  rfl

/-- A translation-fixed meromorphic field is closed under the ambient derivation. -/
theorem meromorphicTranslationFixedField_derivationClosed (q : ℂ) :
    DerivationClosed (meromorphicTranslationFixedField q) := by
  intro x hx
  rw [mem_meromorphicTranslationFixedField_iff] at hx ⊢
  rw [addTranslationMeroEquiv_deriv, hx]

/-- The concrete elliptic meromorphic field is a differential subfield. -/
theorem ellipticMeroField_derivationClosed (τ : ℂ) :
    DerivationClosed (ellipticMeroField τ) := by
  intro x hx
  rw [mem_ellipticMeroField_iff] at hx ⊢
  constructor
  · rw [addTranslationMeroEquiv_deriv, hx.1]
  · rw [addTranslationMeroEquiv_deriv, hx.2]

/-- The compositum of two derivation-closed intermediate fields is derivation-closed. -/
theorem derivationClosed_sup
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {L₁ L₂ : IntermediateField F K}
    (h₁ : DerivationClosed L₁) (h₂ : DerivationClosed L₂) :
    DerivationClosed (L₁ ⊔ L₂) := by
  rw [IntermediateField.sup_def]
  intro x hx
  apply IntermediateField.adjoin_induction F
      (s := ((L₁ : Set K) ∪ (L₂ : Set K)))
      (p := fun y _ => y′ ∈ IntermediateField.adjoin F
        ((L₁ : Set K) ∪ (L₂ : Set K)))
  · intro y hy
    rcases hy with hy | hy
    · exact IntermediateField.subset_adjoin F _ (Or.inl (h₁ hy))
    · exact IntermediateField.subset_adjoin F _ (Or.inr (h₂ hy))
  · intro c
    exact IntermediateField.subset_adjoin F _
      (Or.inl (h₁ (IntermediateField.algebraMap_mem L₁ c)))
  · intro a b ha hb hda hdb
    rw [map_add]
    exact IntermediateField.add_mem _ hda hdb
  · intro a ha hda
    rw [Derivation.leibniz_inv]
    have hasq : a⁻¹ ^ (2 : ℕ) ∈ IntermediateField.adjoin F
        ((L₁ : Set K) ∪ (L₂ : Set K)) := by
      simpa [pow_two] using IntermediateField.mul_mem _
        (IntermediateField.inv_mem _ ha)
        (IntermediateField.inv_mem _ ha)
    exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ hasq) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ ha hdb)
      (IntermediateField.mul_mem _ hb hda)
  exact hx

/-- The concrete compositum `E_σ E_τ` of two elliptic meromorphic fields. -/
def meromorphicEllipticCompositum (σ τ : ℂ) :
    IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  ellipticMeroField σ ⊔ ellipticMeroField τ

/-- The paired elliptic compositum is closed under the ambient meromorphic derivation. -/
theorem meromorphicEllipticCompositum_derivationClosed (σ τ : ℂ) :
    DerivationClosed (meromorphicEllipticCompositum σ τ) :=
  derivationClosed_sup
    (ellipticMeroField_derivationClosed σ)
    (ellipticMeroField_derivationClosed τ)

/-- The restricted derivation on the concrete `(1, τ)`-elliptic field. -/
@[reducible] noncomputable def ellipticMeroFieldDifferential (τ : ℂ) :
    Differential (ellipticMeroField τ) :=
  derivationClosedDifferential _ (ellipticMeroField_derivationClosed τ)

/-- The restricted derivation on the concrete paired elliptic compositum. -/
@[reducible] noncomputable def meromorphicEllipticCompositumDifferential (σ τ : ℂ) :
    Differential (meromorphicEllipticCompositum σ τ) :=
  derivationClosedDifferential _
    (meromorphicEllipticCompositum_derivationClosed σ τ)

end

end GaloisForLFunctions
