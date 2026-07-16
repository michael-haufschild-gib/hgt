import GaloisForLFunctions.HTGeometry.CoprimePrimeResidueInteraction
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

namespace GaloisForLFunctions.HTGeometry

open Set Module
open scoped TensorProduct Function

noncomputable section

noncomputable def localAnchoredRepr
    (A : Type*) [Fintype A] [DecidableEq A] [One A] :
    (A → ℂ) ≃ₗ[ℂ] (A → ℂ) where
  toFun f a := if a = 1 then f 1 else f a - f 1
  invFun c a := if a = 1 then c 1 else c 1 + c a
  left_inv f := by
    funext a
    by_cases ha : a = 1
    · simp [ha]
    · simp [ha]
  right_inv c := by
    funext a
    by_cases ha : a = 1
    · simp [ha]
    · simp [ha]
  map_add' f g := by
    funext a
    by_cases ha : a = 1
    · simp [ha]
    · simp [ha]
      ring
  map_smul' c f := by
    funext a
    by_cases ha : a = 1
    · simp [ha]
    · simp [ha]
      ring

noncomputable def localAnchoredBasis
    (A : Type*) [Fintype A] [DecidableEq A] [One A] :
    Basis A ℂ (A → ℂ) :=
  Basis.ofEquivFun (localAnchoredRepr A)

theorem localAnchoredBasis_apply
    (A : Type*) [Fintype A] [DecidableEq A] [One A]
    (a b : A) :
    localAnchoredBasis A a b =
      if a = 1 then 1 else if b = a then 1 else 0 := by
  classical
  simp [localAnchoredBasis, Basis.coe_ofEquivFun, localAnchoredRepr,
    Pi.single_apply]
  by_cases ha : a = 1
  · subst a
    simp
  · have h1a : 1 ≠ a := Ne.symm ha
    by_cases hb : b = a <;> simp [ha, h1a, hb]

noncomputable def piTensorProductFunctionEquiv
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] :
    (⨂[ℂ] i, (A i → ℂ)) ≃ₗ[ℂ] ((∀ i, A i) → ℂ) := by
  classical
  exact
    (PiTensorProduct.congr fun i =>
        (Finsupp.linearEquivFunOnFinite ℂ ℂ (A i)).symm) ≪≫ₗ
      PiTensorProduct.ofFinsuppEquiv' ≪≫ₗ
      Finsupp.linearEquivFunOnFinite ℂ ℂ (∀ i, A i)

noncomputable def anchoredProductBasis
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] :
    Basis (∀ i, A i) ℂ ((∀ i, A i) → ℂ) :=
  (Basis.piTensorProduct (fun i => localAnchoredBasis (A i))).map
    (piTensorProductFunctionEquiv A)

theorem anchoredProductBasis_apply
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (x y : ∀ i, A i) :
    anchoredProductBasis A x y =
      ∏ i, if x i = 1 then 1 else if y i = x i then 1 else 0 := by
  classical
  simp [anchoredProductBasis, piTensorProductFunctionEquiv,
    localAnchoredBasis_apply]

def pointedSupport
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (x : ∀ i, A i) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 1

def anchoredSupportAtMost
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (k : ℕ) : Set (∀ i, A i) :=
  {x | (pointedSupport A x).card ≤ k}

def anchoredSupportExactly
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (k : ℕ) : Set (∀ i, A i) :=
  {x | (pointedSupport A x).card = k}

def anchoredInteractionFiltration
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Submodule ℂ ((∀ i, A i) → ℂ) :=
  Submodule.span ℂ (anchoredProductBasis A '' anchoredSupportAtMost A k)

def anchoredInteractionGrade
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Submodule ℂ ((∀ i, A i) → ℂ) :=
  Submodule.span ℂ (anchoredProductBasis A '' anchoredSupportExactly A k)

theorem anchoredSupportAtMost_union_exactly
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    {k : ℕ} (hk : 0 < k) :
    anchoredSupportAtMost A (k - 1) ∪ anchoredSupportExactly A k =
      anchoredSupportAtMost A k := by
  ext x
  simp only [anchoredSupportAtMost, anchoredSupportExactly, Set.mem_union,
    Set.mem_setOf_eq]
  omega

theorem anchoredInteractionFiltration_step
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] {k : ℕ} (hk : 0 < k) :
    Disjoint (anchoredInteractionFiltration A (k - 1))
        (anchoredInteractionGrade A k) ∧
      anchoredInteractionFiltration A (k - 1) ⊔
          anchoredInteractionGrade A k =
        anchoredInteractionFiltration A k := by
  constructor
  · apply (anchoredProductBasis A).linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro x hxle hxeq
    change (pointedSupport A x).card ≤ k - 1 at hxle
    change (pointedSupport A x).card = k at hxeq
    omega
  · rw [anchoredInteractionFiltration, anchoredInteractionGrade,
      ← Submodule.span_union, ← Set.image_union,
      anchoredSupportAtMost_union_exactly A hk]
    rfl

theorem anchoredInteractionFiltration_top
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] :
    anchoredInteractionFiltration A (Fintype.card ι) = ⊤ := by
  rw [anchoredInteractionFiltration]
  have hset : anchoredSupportAtMost A (Fintype.card ι) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change (pointedSupport A x).card ≤ Fintype.card ι
    simpa using (Finset.card_le_univ (pointedSupport A x))
  rw [hset, Set.image_univ, (anchoredProductBasis A).span_eq]

theorem anchoredInteractionGrade_finrank
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Module.finrank ℂ (anchoredInteractionGrade A k) =
      Nat.card (anchoredSupportExactly A k) := by
  classical
  letI : Fintype (anchoredSupportExactly A k) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  rw [anchoredInteractionGrade,
    finrank_span_set_eq_card
      (((anchoredProductBasis A).linearIndependent.linearIndepOn
        (anchoredSupportExactly A k)).id_image),
    Set.toFinset_card]
  exact (Fintype.card_congr
    (Equiv.Set.image (anchoredProductBasis A)
      (anchoredSupportExactly A k)
      (anchoredProductBasis A).injective)).symm

def exactPointedSupportEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (S : Finset ι) :
    {x : ∀ i, A i // pointedSupport A x = S} ≃
      ∀ i : S, {a : A i.1 // a ≠ 1} where
  toFun x i := by
    refine ⟨x.1 i.1, ?_⟩
    have hi : i.1 ∈ pointedSupport A x.1 := by
      rw [x.2]
      exact i.2
    exact (Finset.mem_filter.mp hi).2
  invFun z := ⟨fun i => dite (i ∈ S)
      (fun hi => (z ⟨i, hi⟩).1) (fun _ => (1 : A i)), by
    ext i
    simp only [pointedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S
    · simp [hi, (z ⟨i, hi⟩).2]
    · simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, dite_false]
      by_contra hxi
      have hisupp : i ∈ pointedSupport A x.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hxi⟩
      exact hi (by simpa [x.2] using hisupp)
  right_inv z := by
    funext i
    apply Subtype.ext
    simp [i.2]

theorem exactPointedSupport_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    Nat.card {x : ∀ i, A i // pointedSupport A x = S} =
      ∏ i ∈ S, (Fintype.card (A i) - 1) := by
  classical
  rw [Nat.card_congr (exactPointedSupportEquiv A S), Nat.card_pi]
  simp only [Nat.card_eq_fintype_card]
  have hlocal : ∀ i, Fintype.card {a : A i // a ≠ 1} =
      Fintype.card (A i) - 1 := by
    intro i
    rw [Fintype.card_subtype_compl (fun a : A i => a = 1),
      Fintype.card_subtype_eq]
  simp_rw [hlocal]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (A i) - 1)

def exactSupportSigmaEquiv
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (k : ℕ) :
    {x : ∀ i, A i // (pointedSupport A x).card = k} ≃
      Σ S : {S : Finset ι // S.card = k},
        {x : ∀ i, A i // pointedSupport A x = S.1} where
  toFun x := ⟨⟨pointedSupport A x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  invFun z := ⟨z.2.1, by rw [z.2.2]; exact z.1.2⟩
  left_inv x := by rfl
  right_inv z := by
    rcases z with ⟨⟨S, hS⟩, ⟨x, hx⟩⟩
    dsimp
    change pointedSupport A x = S at hx
    subst S
    rfl

theorem exactSupportOrder_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Nat.card {x : ∀ i, A i // (pointedSupport A x).card = k} =
      ∑ S : {S : Finset ι // S.card = k},
        ∏ i ∈ S.1, (Fintype.card (A i) - 1) := by
  rw [Nat.card_congr (exactSupportSigmaEquiv A k), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  exact exactPointedSupport_card A S.1

theorem anchoredInteractionGrade_finrank_eq_support_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Module.finrank ℂ (anchoredInteractionGrade A k) =
      ∑ S : {S : Finset ι // S.card = k},
        ∏ i ∈ S.1, (Fintype.card (A i) - 1) := by
  rw [anchoredInteractionGrade_finrank]
  change Nat.card {x : ∀ i, A i // (pointedSupport A x).card = k} = _
  rw [exactSupportOrder_card]

noncomputable def fullValueFunctionLinearEquiv (W : Type*) :
    (W → ℂ) ≃ₗ[ℂ] (FullValueSubtype W → ℂ) where
  toFun f x := f x.1
  invFun g w := g ⟨w, Set.mem_univ _⟩
  left_inv f := rfl
  right_inv g := by
    funext x
    exact congrArg g (Subtype.ext rfl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def anchoredRestrictedProductBasis
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] :
    Basis (∀ i, A i) ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  (anchoredProductBasis A).map (fullValueFunctionLinearEquiv (∀ i, A i))

theorem anchoredRestrictedProductBasis_apply
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (z : ∀ i, A i)
    (x : FullValueSubtype (∀ i, A i)) :
    anchoredRestrictedProductBasis A z x =
      ∏ i, if z i = 1 then 1 else if x.1 i = z i then 1 else 0 := by
  classical
  simp [anchoredRestrictedProductBasis, fullValueFunctionLinearEquiv,
    anchoredProductBasis_apply]

def coordinateRestriction
    {ι : Type*} (A : ι → Type*) (S : Finset ι)
    (x : ∀ i, A i) : ∀ i : S, A i.1 :=
  fun i => x i.1

def coordinateAgreementSetoid
    {ι : Type*} (A : ι → Type*) (S : Finset ι) :
    Setoid (∀ i, A i) :=
  Setoid.ker (coordinateRestriction A S)

theorem coordinateRestriction_surjective
    {ι : Type*} [DecidableEq ι]
    (A : ι → Type*) [∀ i, One (A i)] (S : Finset ι) :
    Function.Surjective (coordinateRestriction A S) := by
  intro z
  let x : ∀ i, A i := fun i => dite (i ∈ S)
    (fun hi => z ⟨i, hi⟩) (fun _ => 1)
  refine ⟨x, ?_⟩
  funext i
  simp [coordinateRestriction, x, i.2]

noncomputable instance coordinateAgreementQuotientFintype
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] (S : Finset ι) :
    Fintype (FiniteQuotientType (coordinateAgreementSetoid A S)) :=
  Fintype.ofFinite _

noncomputable def coordinateAgreementQuotientEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, One (A i)]
    (S : Finset ι) :
    FiniteQuotientType (coordinateAgreementSetoid A S) ≃
      ∀ i : S, A i.1 :=
  Setoid.quotientKerEquivOfSurjective (coordinateRestriction A S)
    (coordinateRestriction_surjective A S)

theorem coordinateAgreementQuotient_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, One (A i)]
    (S : Finset ι) :
    Fintype.card (FiniteQuotientType (coordinateAgreementSetoid A S)) =
      ∏ i ∈ S, Fintype.card (A i) := by
  rw [Fintype.card_congr (coordinateAgreementQuotientEquiv A S),
    Fintype.card_pi]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (A i))

def anchoredSubsetSupportSubmodule
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  Submodule.span ℂ (anchoredRestrictedProductBasis A ''
    {z | pointedSupport A z ⊆ S})

theorem anchoredSubsetSupportSubmodule_le_coordinateInvariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    anchoredSubsetSupportSubmodule A S ≤
      ClassInvariantRestricted (coordinateAgreementSetoid A S) := by
  apply Submodule.span_le.mpr
  rintro f ⟨z, hz, rfl⟩
  intro x y hxy
  change coordinateRestriction A S x.1 = coordinateRestriction A S y.1 at hxy
  rw [anchoredRestrictedProductBasis_apply,
    anchoredRestrictedProductBasis_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hzi : z i = 1
  · simp [hzi]
  · have hisupp : i ∈ pointedSupport A z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩
    have hiS : i ∈ S := hz hisupp
    have hxyi : x.1 i = y.1 i := congrFun hxy ⟨i, hiS⟩
    simp [hzi, hxyi]

def supportSubsetEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (S : Finset ι) :
    {x : ∀ i, A i // pointedSupport A x ⊆ S} ≃
      ∀ i : S, A i.1 where
  toFun x i := x.1 i.1
  invFun z := ⟨fun i => dite (i ∈ S)
      (fun hi => z ⟨i, hi⟩) (fun _ => 1), by
    intro i hi
    by_contra hiS
    have houtside : (dite (i ∈ S)
        (fun hi => z ⟨i, hi⟩) (fun _ => (1 : A i))) = 1 := by simp [hiS]
    exact (Finset.mem_filter.mp hi).2 houtside⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, dite_false]
      by_contra hxi
      have hisupp : i ∈ pointedSupport A x.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hxi⟩
      exact hi (x.2 hisupp)
  right_inv z := by
    funext i
    simp [i.2]

theorem supportSubset_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    Nat.card {x : ∀ i, A i // pointedSupport A x ⊆ S} =
      ∏ i ∈ S, Fintype.card (A i) := by
  rw [Nat.card_congr (supportSubsetEquiv A S), Nat.card_pi]
  simp only [Nat.card_eq_fintype_card]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (A i))

theorem anchoredSubsetSupportSubmodule_finrank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    Module.finrank ℂ (anchoredSubsetSupportSubmodule A S) =
      ∏ i ∈ S, Fintype.card (A i) := by
  classical
  let T : Set (∀ i, A i) := {z | pointedSupport A z ⊆ S}
  letI : Fintype T := Fintype.ofFinite _
  rw [anchoredSubsetSupportSubmodule,
    finrank_span_set_eq_card
      (((anchoredRestrictedProductBasis A).linearIndependent.linearIndepOn T).id_image),
    Set.toFinset_card]
  rw [(Fintype.card_congr
    (Equiv.Set.image (anchoredRestrictedProductBasis A) T
      (anchoredRestrictedProductBasis A).injective)).symm]
  rw [← Nat.card_eq_fintype_card]
  exact supportSubset_card A S

theorem anchoredSubsetSupportSubmodule_eq_coordinateInvariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (S : Finset ι) :
    anchoredSubsetSupportSubmodule A S =
      ClassInvariantRestricted (coordinateAgreementSetoid A S) := by
  let V := ClassInvariantRestricted (coordinateAgreementSetoid A S)
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (coordinateAgreementSetoid A S)
  apply Submodule.eq_of_le_of_finrank_eq
    (anchoredSubsetSupportSubmodule_le_coordinateInvariant A S)
  rw [anchoredSubsetSupportSubmodule_finrank,
    classInvariantRestricted_finrank, coordinateAgreementQuotient_card]

def anchoredRestrictedInteractionFiltration
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  Submodule.span ℂ
    (anchoredRestrictedProductBasis A '' anchoredSupportAtMost A k)

def intrinsicCoordinateInteractionFiltration
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) (k : ℕ) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  ⨆ S : {S : Finset ι // S.card ≤ k},
    ClassInvariantRestricted (coordinateAgreementSetoid A S.1)

theorem anchoredRestrictedInteractionFiltration_eq_intrinsic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    anchoredRestrictedInteractionFiltration A k =
      intrinsicCoordinateInteractionFiltration A k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨z, hz, rfl⟩
    let S : {S : Finset ι // S.card ≤ k} := ⟨pointedSupport A z, hz⟩
    apply (show ClassInvariantRestricted (coordinateAgreementSetoid A S.1) ≤
        intrinsicCoordinateInteractionFiltration A k from le_iSup (fun S =>
          ClassInvariantRestricted (coordinateAgreementSetoid A S.1)) S)
    rw [← anchoredSubsetSupportSubmodule_eq_coordinateInvariant A S.1]
    apply Submodule.subset_span
    exact ⟨z, Finset.Subset.rfl, rfl⟩
  · apply iSup_le
    intro S
    rw [← anchoredSubsetSupportSubmodule_eq_coordinateInvariant A S.1]
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    change (pointedSupport A z).card ≤ k
    exact (Finset.card_le_card hz).trans S.2

noncomputable def productFunctionBasis
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ)) :
    Basis (∀ i, A i) ℂ ((∀ i, A i) → ℂ) :=
  (Basis.piTensorProduct b).map (piTensorProductFunctionEquiv A)

noncomputable def productRestrictedFunctionBasis
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ)) :
    Basis (∀ i, A i) ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  (productFunctionBasis A b).map (fullValueFunctionLinearEquiv (∀ i, A i))

theorem productRestrictedFunctionBasis_apply
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ))
    (z : ∀ i, A i) (x : FullValueSubtype (∀ i, A i)) :
    productRestrictedFunctionBasis A b z x =
      ∏ i, b i (z i) (x.1 i) := by
  classical
  simp [productRestrictedFunctionBasis, productFunctionBasis,
    fullValueFunctionLinearEquiv, piTensorProductFunctionEquiv]

def basisSupportSubsetSubmodule
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ)) (S : Finset ι) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  Submodule.span ℂ (productRestrictedFunctionBasis A b ''
    {z | pointedSupport A z ⊆ S})

theorem basisSupportSubsetSubmodule_le_coordinateInvariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ))
    (hconst : ∀ i, b i 1 = fun _ => (1 : ℂ)) (S : Finset ι) :
    basisSupportSubsetSubmodule A b S ≤
      ClassInvariantRestricted (coordinateAgreementSetoid A S) := by
  apply Submodule.span_le.mpr
  rintro f ⟨z, hz, rfl⟩
  intro x y hxy
  change coordinateRestriction A S x.1 = coordinateRestriction A S y.1 at hxy
  rw [productRestrictedFunctionBasis_apply,
    productRestrictedFunctionBasis_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hzi : z i = 1
  · rw [hzi, hconst]
  · have hisupp : i ∈ pointedSupport A z :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩
    have hiS : i ∈ S := hz hisupp
    have hxyi : x.1 i = y.1 i := congrFun hxy ⟨i, hiS⟩
    rw [hxyi]

theorem basisSupportSubsetSubmodule_finrank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ)) (S : Finset ι) :
    Module.finrank ℂ (basisSupportSubsetSubmodule A b S) =
      ∏ i ∈ S, Fintype.card (A i) := by
  classical
  let T : Set (∀ i, A i) := {z | pointedSupport A z ⊆ S}
  letI : Fintype T := Fintype.ofFinite _
  rw [basisSupportSubsetSubmodule,
    finrank_span_set_eq_card
      (((productRestrictedFunctionBasis A b).linearIndependent.linearIndepOn T).id_image),
    Set.toFinset_card]
  rw [(Fintype.card_congr
    (Equiv.Set.image (productRestrictedFunctionBasis A b) T
      (productRestrictedFunctionBasis A b).injective)).symm]
  rw [← Nat.card_eq_fintype_card]
  exact supportSubset_card A S

theorem basisSupportSubsetSubmodule_eq_coordinateInvariant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ))
    (hconst : ∀ i, b i 1 = fun _ => (1 : ℂ)) (S : Finset ι) :
    basisSupportSubsetSubmodule A b S =
      ClassInvariantRestricted (coordinateAgreementSetoid A S) := by
  let V := ClassInvariantRestricted (coordinateAgreementSetoid A S)
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (coordinateAgreementSetoid A S)
  apply Submodule.eq_of_le_of_finrank_eq
    (basisSupportSubsetSubmodule_le_coordinateInvariant A b hconst S)
  rw [basisSupportSubsetSubmodule_finrank,
    classInvariantRestricted_finrank, coordinateAgreementQuotient_card]

def basisInteractionFiltration
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ)) (k : ℕ) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  Submodule.span ℂ
    (productRestrictedFunctionBasis A b '' anchoredSupportAtMost A k)

/-- Every tensor-product basis whose distinguished local vector is constant induces the same
intrinsic interaction-order filtration. -/
theorem basisInteractionFiltration_eq_intrinsic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ))
    (hconst : ∀ i, b i 1 = fun _ => (1 : ℂ)) (k : ℕ) :
    basisInteractionFiltration A b k =
      intrinsicCoordinateInteractionFiltration A k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨z, hz, rfl⟩
    let S : {S : Finset ι // S.card ≤ k} := ⟨pointedSupport A z, hz⟩
    apply (show ClassInvariantRestricted (coordinateAgreementSetoid A S.1) ≤
        intrinsicCoordinateInteractionFiltration A k from le_iSup (fun S =>
          ClassInvariantRestricted (coordinateAgreementSetoid A S.1)) S)
    rw [← basisSupportSubsetSubmodule_eq_coordinateInvariant A b hconst S.1]
    apply Submodule.subset_span
    exact ⟨z, Finset.Subset.rfl, rfl⟩
  · apply iSup_le
    intro S
    rw [← basisSupportSubsetSubmodule_eq_coordinateInvariant A b hconst S.1]
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    change (pointedSupport A z).card ≤ k
    exact (Finset.card_le_card hz).trans S.2

theorem basisInteractionFiltration_eq_anchored
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (b : ∀ i, Basis (A i) ℂ (A i → ℂ))
    (hconst : ∀ i, b i 1 = fun _ => (1 : ℂ)) (k : ℕ) :
    basisInteractionFiltration A b k =
      anchoredRestrictedInteractionFiltration A k := by
  rw [basisInteractionFiltration_eq_intrinsic A b hconst,
    anchoredRestrictedInteractionFiltration_eq_intrinsic]

theorem coordinateInvariant_mul_mem_union
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) (S T : Finset ι)
    {f g : FullValueSubtype (∀ i, A i) → ℂ}
    (hf : f ∈ ClassInvariantRestricted (coordinateAgreementSetoid A S))
    (hg : g ∈ ClassInvariantRestricted (coordinateAgreementSetoid A T)) :
    f * g ∈ ClassInvariantRestricted (coordinateAgreementSetoid A (S ∪ T)) := by
  intro x y hxy
  change coordinateRestriction A (S ∪ T) x.1 =
    coordinateRestriction A (S ∪ T) y.1 at hxy
  have hxyS : coordinateRestriction A S x.1 = coordinateRestriction A S y.1 := by
    funext i
    exact congrFun hxy ⟨i.1, Finset.mem_union_left T i.2⟩
  have hxyT : coordinateRestriction A T x.1 = coordinateRestriction A T y.1 := by
    funext i
    exact congrFun hxy ⟨i.1, Finset.mem_union_right S i.2⟩
  change f x * g x = f y * g y
  rw [hf x y hxyS, hg x y hxyT]

/-- The intrinsic interaction tower is a filtered algebra: multiplying order-at-most `k` and
order-at-most `l` observables creates no support beyond order `k+l`. -/
theorem anchoredRestrictedInteractionFiltration_mul_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] {k l : ℕ}
    {f g : FullValueSubtype (∀ i, A i) → ℂ}
    (hf : f ∈ anchoredRestrictedInteractionFiltration A k)
    (hg : g ∈ anchoredRestrictedInteractionFiltration A l) :
    f * g ∈ anchoredRestrictedInteractionFiltration A (k + l) := by
  let target := anchoredRestrictedInteractionFiltration A (k + l)
  apply Submodule.span_induction₂ (R := ℂ)
      (s := anchoredRestrictedProductBasis A '' anchoredSupportAtMost A k)
      (t := anchoredRestrictedProductBasis A '' anchoredSupportAtMost A l)
      (p := fun f g _ _ => f * g ∈ target)
  · rintro _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    let S := pointedSupport A z
    let T := pointedSupport A w
    have hzInv : anchoredRestrictedProductBasis A z ∈
        ClassInvariantRestricted (coordinateAgreementSetoid A S) := by
      rw [← anchoredSubsetSupportSubmodule_eq_coordinateInvariant A S]
      apply Submodule.subset_span
      exact ⟨z, Finset.Subset.rfl, rfl⟩
    have hwInv : anchoredRestrictedProductBasis A w ∈
        ClassInvariantRestricted (coordinateAgreementSetoid A T) := by
      rw [← anchoredSubsetSupportSubmodule_eq_coordinateInvariant A T]
      apply Submodule.subset_span
      exact ⟨w, Finset.Subset.rfl, rfl⟩
    have hmul := coordinateInvariant_mul_mem_union A S T hzInv hwInv
    dsimp only [target]
    rw [anchoredRestrictedInteractionFiltration_eq_intrinsic A (k + l)]
    let ST : {R : Finset ι // R.card ≤ k + l} := ⟨S ∪ T, by
      exact (Finset.card_union_le S T).trans
        (Nat.add_le_add hz hw)⟩
    exact (show ClassInvariantRestricted (coordinateAgreementSetoid A ST.1) ≤
        intrinsicCoordinateInteractionFiltration A (k + l) from
      le_iSup (fun R => ClassInvariantRestricted
        (coordinateAgreementSetoid A R.1)) ST) hmul
  · intro g _
    simp [target]
  · intro f _
    simp [target]
  · intro f₁ f₂ g _ _ _ hf₁ hf₂
    simpa [add_mul] using Submodule.add_mem target hf₁ hf₂
  · intro f g₁ g₂ _ _ _ hg₁ hg₂
    simpa [mul_add] using Submodule.add_mem target hg₁ hg₂
  · intro c f g _ _ hfg
    simpa [smul_mul_assoc] using Submodule.smul_mem target c hfg
  · intro c f g _ _ hfg
    simpa [mul_smul_comm] using Submodule.smul_mem target c hfg
  · exact hf
  · exact hg

def anchoredRestrictedInteractionGrade
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Submodule ℂ (FullValueSubtype (∀ i, A i) → ℂ) :=
  Submodule.span ℂ
    (anchoredRestrictedProductBasis A '' anchoredSupportExactly A k)

theorem anchoredRestrictedInteractionFiltration_step
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] {k : ℕ} (hk : 0 < k) :
    Disjoint (anchoredRestrictedInteractionFiltration A (k - 1))
        (anchoredRestrictedInteractionGrade A k) ∧
      anchoredRestrictedInteractionFiltration A (k - 1) ⊔
          anchoredRestrictedInteractionGrade A k =
        anchoredRestrictedInteractionFiltration A k := by
  constructor
  · apply (anchoredRestrictedProductBasis A).linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro x hxle hxeq
    change (pointedSupport A x).card ≤ k - 1 at hxle
    change (pointedSupport A x).card = k at hxeq
    omega
  · rw [anchoredRestrictedInteractionFiltration,
      anchoredRestrictedInteractionGrade, ← Submodule.span_union,
      ← Set.image_union, anchoredSupportAtMost_union_exactly A hk]
    rfl

theorem anchoredRestrictedInteractionFiltration_top
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] :
    anchoredRestrictedInteractionFiltration A (Fintype.card ι) = ⊤ := by
  rw [anchoredRestrictedInteractionFiltration]
  have hset : anchoredSupportAtMost A (Fintype.card ι) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change (pointedSupport A x).card ≤ Fintype.card ι
    simpa using (Finset.card_le_univ (pointedSupport A x))
  rw [hset, Set.image_univ, (anchoredRestrictedProductBasis A).span_eq]

theorem anchoredRestrictedInteractionFiltration_finrank_pos
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    0 < Module.finrank ℂ (anchoredRestrictedInteractionFiltration A k) := by
  let U := anchoredRestrictedInteractionFiltration A k
  letI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le le_top
  let x0 : ∀ i, A i := fun _ => 1
  have hx0 : x0 ∈ anchoredSupportAtMost A k := by
    change (pointedSupport A x0).card ≤ k
    have hsupp : pointedSupport A x0 = ∅ := by
      ext i
      simp [pointedSupport, x0]
    rw [hsupp]
    simp
  have hbmem : anchoredRestrictedProductBasis A x0 ∈ U := by
    apply Submodule.subset_span
    exact ⟨x0, hx0, rfl⟩
  rw [finrank_pos_iff]
  exact ⟨⟨anchoredRestrictedProductBasis A x0, hbmem⟩, 0, by
    simpa using (anchoredRestrictedProductBasis A).ne_zero x0⟩

theorem anchoredRestrictedInteractionGrade_finrank_eq_support_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] (k : ℕ) :
    Module.finrank ℂ (anchoredRestrictedInteractionGrade A k) =
      ∑ S : {S : Finset ι // S.card = k},
        ∏ i ∈ S.1, (Fintype.card (A i) - 1) := by
  classical
  letI : Fintype (anchoredSupportExactly A k) := Fintype.ofFinite _
  rw [anchoredRestrictedInteractionGrade,
    finrank_span_set_eq_card
      (((anchoredRestrictedProductBasis A).linearIndependent.linearIndepOn
        (anchoredSupportExactly A k)).id_image),
    Set.toFinset_card]
  rw [(Fintype.card_congr
    (Equiv.Set.image (anchoredRestrictedProductBasis A)
      (anchoredSupportExactly A k)
      (anchoredRestrictedProductBasis A).injective)).symm]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {x : ∀ i, A i // (pointedSupport A x).card = k} = _
  rw [exactSupportOrder_card]

/-- Every positive Boolean interaction grade of a finite pointed product is realized as an exact
relative hypertranscendental extension over all lower interaction orders. -/
theorem cofiniteTailDenseOn_anchoredInteractionGrade_relativeHT
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    {k : ℕ} (hk : 0 < k) (a : ℂ) :
    let U := anchoredRestrictedInteractionFiltration A (k - 1)
    let Q := anchoredRestrictedInteractionGrade A k
    let V := anchoredRestrictedInteractionFiltration A k
    ∃ q : Fin (Module.finrank ℂ Q) → (∀ i, A i) → ℂ,
      Disjoint U Q ∧ U ⊔ Q = V ∧
      Module.finrank ℂ Q =
        ∑ S : {S : Finset ι // S.card = k},
          ∏ i ∈ S.1, (Fintype.card (A i) - 1) ∧
      GaloisForLFunctions.DifferentialIndependent
        (↥(primeObservableSubspaceShiftField y U a))
        (fun j => tailDenseObservableShiftCarrier y (q j) a) ∧
      primeObservableSubspaceShiftField y U a ⊔
          tailDenseObservableShiftField y q a =
        primeObservableSubspaceShiftField y V a := by
  dsimp only
  let U := anchoredRestrictedInteractionFiltration A (k - 1)
  let Q := anchoredRestrictedInteractionGrade A k
  let V := anchoredRestrictedInteractionFiltration A k
  have hstep := anchoredRestrictedInteractionFiltration_step A hk
  have hUQ : Disjoint U Q := hstep.1
  have hsup : U ⊔ Q = V := hstep.2
  letI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le le_top
  letI : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le le_top
  letI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le le_top
  have hUpos : 0 < Module.finrank ℂ U := by
    let x0 : ∀ i, A i := fun _ => 1
    have hx0 : x0 ∈ anchoredSupportAtMost A (k - 1) := by
      change (pointedSupport A x0).card ≤ k - 1
      have hsupp : pointedSupport A x0 = ∅ := by
        ext i
        simp [pointedSupport, x0]
      rw [hsupp]
      simp
    have hbmem : anchoredRestrictedProductBasis A x0 ∈ U := by
      apply Submodule.subset_span
      exact ⟨x0, hx0, rfl⟩
    rw [finrank_pos_iff]
    exact ⟨⟨anchoredRestrictedProductBasis A x0, hbmem⟩, 0, by
      simpa using (anchoredRestrictedProductBasis A).ne_zero x0⟩
  let q : Fin (Module.finrank ℂ Q) → (∀ i, A i) → ℂ :=
    finiteSubmoduleObservable Q
  have hQfield :
      primeObservableSubspaceShiftField y Q a =
        tailDenseObservableShiftField y q a :=
    primeObservableSubspaceShiftField_eq_basis y Q a
  refine ⟨q, hUQ, hsup, ?_, ?_, ?_⟩
  · exact anchoredRestrictedInteractionGrade_finrank_eq_support_spectrum A k
  · exact cofiniteTailDenseOn_complementObservable_differentialIndependent
      y hy U Q hUpos hUQ a
  · calc
      primeObservableSubspaceShiftField y U a ⊔
          tailDenseObservableShiftField y q a =
        primeObservableSubspaceShiftField y U a ⊔
          primeObservableSubspaceShiftField y Q a := by rw [hQfield]
      _ = primeObservableSubspaceShiftField y (U ⊔ Q) a :=
        (primeObservableSubspaceShiftField_sup y U Q a).symm
      _ = primeObservableSubspaceShiftField y V a := by rw [hsup]

/-- A nonzero interaction grade forces a strict field extension: higher interaction order cannot
collapse into the differential field generated by lower orders. -/
theorem cofiniteTailDenseOn_anchoredInteractionField_strict
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    {k : ℕ} (hk : 0 < k)
    (hgrade : 0 < Module.finrank ℂ (anchoredRestrictedInteractionGrade A k))
    (a : ℂ) :
    primeObservableSubspaceShiftField y
        (anchoredRestrictedInteractionFiltration A (k - 1)) a <
      primeObservableSubspaceShiftField y
        (anchoredRestrictedInteractionFiltration A k) a := by
  let U := anchoredRestrictedInteractionFiltration A (k - 1)
  let Q := anchoredRestrictedInteractionGrade A k
  let V := anchoredRestrictedInteractionFiltration A k
  change 0 < Module.finrank ℂ Q at hgrade
  have hstep := anchoredRestrictedInteractionFiltration_step A hk
  have hdis : Disjoint U Q := hstep.1
  have hsup : U ⊔ Q = V := hstep.2
  have hUV : U ≤ V := by
    rw [← hsup]
    exact le_sup_left
  letI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le le_top
  letI : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le le_top
  letI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le le_top
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U Q
  rw [hsup, hdis.eq_bot] at hdim
  simp only [finrank_bot, add_zero] at hdim
  have hfinlt : Module.finrank ℂ U < Module.finrank ℂ V := by omega
  have hUpos : 0 < Module.finrank ℂ U :=
    anchoredRestrictedInteractionFiltration_finrank_pos A (k - 1)
  have hVpos : 0 < Module.finrank ℂ V := hUpos.trans hfinlt
  have hUVne : U ≠ V := by
    intro hEq
    rw [hEq] at hfinlt
    omega
  have hfieldne :
      primeObservableSubspaceShiftField y U a ≠
        primeObservableSubspaceShiftField y V a := by
    intro hEq
    exact hUVne ((cofiniteTailDenseOn_primeObservableSubspaceField_eq_iff
      y hy U V hUpos hVpos a).mp hEq)
  exact lt_of_le_of_ne (primeObservableSubspaceShiftField_mono y hUV a) hfieldne

noncomputable def pairwiseCoprimeUnitChineseRemainderEquiv
    {ι : Type*} [Fintype ι]
    (modulus : ι → ℕ) (h : Pairwise (Nat.Coprime on modulus)) :
    (ZMod (∏ i, modulus i))ˣ ≃* ∀ i, (ZMod (modulus i))ˣ :=
  (Units.mapEquiv (ZMod.prodEquivPi modulus h).toMulEquiv).trans
    MulEquiv.piUnits

noncomputable def pairwiseCoprimePrimeUnitResidueProfile
    {ι : Type*} [Fintype ι]
    (modulus : ι → ℕ) [NeZero (∏ i, modulus i)]
    (h : Pairwise (Nat.Coprime on modulus)) :
    Nat.Primes → ∀ i, (ZMod (modulus i))ˣ :=
  fun p => pairwiseCoprimeUnitChineseRemainderEquiv modulus h
    (primeUnitResidueProfile (∏ i, modulus i) p)

theorem recurringValueSet_pairwiseCoprimePrimeUnitResidueProfile
    {ι : Type*} [Fintype ι]
    (modulus : ι → ℕ) [NeZero (∏ i, modulus i)]
    (h : Pairwise (Nat.Coprime on modulus)) :
    recurringValueSet (pairwiseCoprimePrimeUnitResidueProfile modulus h) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  let e := pairwiseCoprimeUnitChineseRemainderEquiv modulus h
  have hrec :
      {p : Nat.Primes | primeUnitResidueProfile (∏ i, modulus i) p = e.symm a}.Infinite := by
    have hb : e.symm a ∈ recurringValueSet
        (primeUnitResidueProfile (∏ i, modulus i)) := by
      rw [recurringValueSet_primeUnitResidueProfile]
      exact Set.mem_univ _
    exact hb
  have heq :
      {p : Nat.Primes |
          pairwiseCoprimePrimeUnitResidueProfile modulus h p = a} =
        {p : Nat.Primes |
          primeUnitResidueProfile (∏ i, modulus i) p = e.symm a} := by
    ext p
    change e (primeUnitResidueProfile (∏ i, modulus i) p) = a ↔
      primeUnitResidueProfile (∏ i, modulus i) p = e.symm a
    constructor
    · intro hp
      apply e.injective
      simpa using hp
    · intro hp
      rw [hp, e.apply_symm_apply]
  change {p : Nat.Primes |
    pairwiseCoprimePrimeUnitResidueProfile modulus h p = a}.Infinite
  rw [heq]
  exact hrec

/-- Actual prime residues for an arbitrary pairwise-coprime finite family realize every Boolean
interaction order as an exact relative-HT layer of the predicted totient spectrum. -/
theorem pairwiseCoprimePrimeResidueInteractionSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (modulus : ι → ℕ) [∀ i, NeZero (modulus i)]
    [NeZero (∏ i, modulus i)]
    (h : Pairwise (Nat.Coprime on modulus))
    {k : ℕ} (hk : 0 < k) (a : ℂ) :
    let A := fun i => (ZMod (modulus i))ˣ
    let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
    let U := anchoredRestrictedInteractionFiltration A (k - 1)
    let Q := anchoredRestrictedInteractionGrade A k
    let V := anchoredRestrictedInteractionFiltration A k
    ∃ b : Fin (Module.finrank ℂ Q) → (∀ i, A i) → ℂ,
      Disjoint U Q ∧ U ⊔ Q = V ∧
      Module.finrank ℂ Q =
        ∑ S : {S : Finset ι // S.card = k},
          ∏ i ∈ S.1, (Nat.totient (modulus i) - 1) ∧
      GaloisForLFunctions.DifferentialIndependent
        (↥(primeObservableSubspaceShiftField y U a))
        (fun j => tailDenseObservableShiftCarrier y (b j) a) ∧
      primeObservableSubspaceShiftField y U a ⊔
          tailDenseObservableShiftField y b a =
        primeObservableSubspaceShiftField y V a := by
  dsimp only
  let A := fun i => (ZMod (modulus i))ˣ
  let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
  letI : TopologicalSpace (∀ i, A i) := ⊥
  letI : DiscreteTopology (∀ i, A i) := ⟨rfl⟩
  have hy : CofiniteTailDenseOn y Set.univ :=
    cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ y
      (recurringValueSet_pairwiseCoprimePrimeUnitResidueProfile modulus h)
  obtain ⟨b, hdis, hsup, hrank, hDI, hfield⟩ :=
    cofiniteTailDenseOn_anchoredInteractionGrade_relativeHT A y hy hk a
  refine ⟨b, hdis, hsup, ?_, hDI, hfield⟩
  dsimp [A] at hrank ⊢
  simpa only [ZMod.card_units_eq_totient] using hrank

end

end GaloisForLFunctions.HTGeometry
