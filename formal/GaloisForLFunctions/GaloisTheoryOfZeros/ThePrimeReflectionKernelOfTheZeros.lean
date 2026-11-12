import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeResidueFieldsOfTheZeros
import GaloisForLFunctions.GaloisTheoryOfZeros.TheKummerRelationsOfTheZeroWidths

/-!
# The full prime reflection kernel

The compositum of all reflection-pair residue fields is normal over the
complete prime-source trace field. Its kernel is the closed group of signs
annihilating every finite square-class relation among the actual prime
reflection discriminants. The classification retains the full Krull topology.

Uniform sign reversal lifts functional reflection precisely when every square
relation has even parity; any lift is unique and central. Conjugation acts on
kernel signs by conjugating zero labels, giving a square-class criterion for
centralizing the kernel. Neither the parity condition nor purity is assumed.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped BigOperators IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-- The compositum of the residue fields of all functional-reflection pairs. -/
def primeReflectionField : IntermediateField B E :=
  IntermediateField.adjoin B (Set.range fun i : Nat.Primes × XiDivisorSupport =>
    primeResiduePairValue i.1 i.2)

local notation "H" => primeReflectionField
local notation "K" => (E ≃ₐ[H] E)

theorem primeResiduePairValue_mem_reflectionField (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResiduePairValue p ρ ∈ H := IntermediateField.subset_adjoin B _ ⟨(p,ρ),rfl⟩

theorem primePairField_le_reflectionField (ρ : XiDivisorSupport) : primePairField ρ ≤ H := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨p,rfl⟩
  exact primeResiduePairValue_mem_reflectionField p ρ

/-- The definition retains every pair field, with no height restriction. -/
theorem primeReflectionField_eq_iSup : H = ⨆ ρ : XiDivisorSupport, primePairField ρ := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨⟨p,ρ⟩,rfl⟩
    exact (le_iSup (fun ρ : XiDivisorSupport => primePairField ρ) ρ)
      (primeResiduePairValue_mem p ρ)
  · exact iSup_le primePairField_le_reflectionField

private theorem fixing_reflection_generators (σ : G) :
    σ ∈ (H).fixingSubgroup ↔ ∀ p ρ, σ (primeResiduePairValue p ρ) = primeResiduePairValue p ρ := by
  constructor
  · intro h p ρ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h _
      (primeResiduePairValue_mem_reflectionField p ρ)
  · intro h
    have hext := IntermediateField.algHom_ext_of_eq_adjoin B (S := H) rfl
      (φ₁ := σ.toAlgHom.comp (IntermediateField.val H)) (φ₂ := IntermediateField.val H)
      (by rintro x ⟨⟨p,ρ⟩,rfl⟩; exact h p ρ)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx =>
      DFunLike.congr_fun hext ⟨x,hx⟩

/-- The intrinsic kernel consists precisely of pair-preserving arithmetic zero actions. -/
theorem primeReflectionField_fixing (σ : G) :
    σ ∈ (H).fixingSubgroup ↔ ∀ ρ : XiDivisorSupport,
      primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ := by
  constructor
  · intro h ρ
    apply (primePairField_fixing σ ρ).mp
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h x
      (primePairField_le_reflectionField ρ hx)
  · intro h
    apply (fixing_reflection_generators σ).mpr
    intro p ρ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp
      ((primePairField_fixing σ ρ).mpr (h ρ)) _ (primeResiduePairValue_mem p ρ)

instance primeReflectionField_fixing_normal : (H).fixingSubgroup.Normal := by
  constructor
  intro τ hτ σ
  apply (fixing_reflection_generators _).mpr
  intro p ρ
  have ht := (fixing_reflection_generators τ).mp hτ p (primeTraceZeroMap σ⁻¹ ρ)
  change σ (τ (σ.symm (primeResiduePairValue p ρ))) = primeResiduePairValue p ρ
  have hi : σ.symm (primeResiduePairValue p ρ) =
      primeResiduePairValue p (primeTraceZeroMap σ⁻¹ ρ) := primeResiduePairValue_map σ⁻¹ p ρ
  rw [hi,ht,← hi,σ.apply_symm_apply]

/-- Forgetting pair orientations leaves a normal arithmetic extension. -/
instance primeReflectionField_normal : Normal B H := by
  have hn : Normal B (IntermediateField.fixedField (H).fixingSubgroup) := inferInstance
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hn
  exact hn

instance primeReflectionField_isGalois : IsGalois H E := by infer_instance

/-- Restriction is the full arithmetic action on unordered reflection pairs. -/
def primeReflectionRestriction : G →* (H ≃ₐ[B] H) := AlgEquiv.restrictNormalHom H

theorem primeReflectionRestriction_surjective : Function.Surjective primeReflectionRestriction :=
  AlgEquiv.restrictNormalHom_surjective E

theorem primeReflectionRestriction_continuous : Continuous primeReflectionRestriction :=
  InfiniteGalois.restrictNormalHom_continuous H

theorem primeReflectionRestriction_ker : primeReflectionRestriction.ker = (H).fixingSubgroup := by
  ext σ
  change primeReflectionRestriction σ = 1 ↔ σ ∈ (H).fixingSubgroup
  constructor
  · intro h
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    have he := congrArg (fun τ : H ≃ₐ[B] H => (τ ⟨x,hx⟩ : E)) h
    exact (AlgEquiv.restrictNormal_commutes σ H ⟨x,hx⟩).symm.trans he
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ H x).trans
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mp h x x.property)

/-- Difference of the two prime values in a functional-reflection pair. -/
def primeReflectionDifference (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeResidueValue p ρ - primeResidueValue p (xiZeroReflectEquiv ρ)

private theorem reflection_twice (ρ : XiDivisorSupport) :
    xiZeroReflectEquiv (xiZeroReflectEquiv ρ) = ρ := by
  apply Subtype.ext
  simp only [xiZeroReflectEquiv_apply]
  ring

theorem primeReflectionDifference_reflection (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeReflectionDifference p (xiZeroReflectEquiv ρ) = -primeReflectionDifference p ρ := by
  simp only [primeReflectionDifference,reflection_twice,neg_sub]

theorem primeReflectionDifference_map (σ : G) (p : Nat.Primes) (ρ : XiDivisorSupport) :
    σ (primeReflectionDifference p ρ) = primeReflectionDifference p (primeTraceZeroMap σ ρ) := by
  simp only [primeReflectionDifference,map_sub,primeResidueValue_map,primeTraceZeroMap_reflection]

private theorem prime_values_product (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResidueValue p ρ * primeResidueValue p (xiZeroReflectEquiv ρ) = (p : ℕ) := by
  apply Subtype.ext
  change (primeResidueValue p ρ : ℂ) * (primeResidueValue p (xiZeroReflectEquiv ρ) : ℂ) = (p : ℕ)
  rw [primeResidueValue_coe,primeResidueValue_coe,xiZeroReflectEquiv_apply,
    ← Complex.exp_add,← mul_add,add_sub_cancel,mul_one,
    GaloisForLFunctions.RHTower.SixExponentials.exp_log_nat p.2.pos]

/-- The discriminant is the square of the actual reflection difference. -/
theorem primeReflectionDifference_sq (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeReflectionDifference p ρ ^ 2 = primeResiduePairValue p ρ ^ 2 - 4*(p : ℕ) := by
  rw [← prime_values_product p ρ]
  dsimp only [primeReflectionDifference,primeResiduePairValue]
  ring

/-- Only nonzero reflection differences carry signs. -/
def NonzeroPrimeReflection :=
  {i : Nat.Primes × XiDivisorSupport // primeReflectionDifference i.1 i.2 ≠ 0}

def primeReflectionRadical (i : NonzeroPrimeReflection) : E := primeReflectionDifference i.val.1 i.val.2

/-- A concrete discriminant in the full pair field. -/
def primeReflectionRadicand (i : NonzeroPrimeReflection) : H :=
  ⟨primeReflectionRadical i ^ 2,by
    change primeReflectionDifference i.val.1 i.val.2 ^ 2 ∈ H
    rw [primeReflectionDifference_sq]
    exact (H).sub_mem ((H).pow_mem (primeResiduePairValue_mem_reflectionField i.val.1 i.val.2) 2)
      ((H).mul_mem ((H).natCast_mem 4) ((H).natCast_mem (i.val.1 : ℕ)))⟩

theorem primeReflectionRadicand_value (i : NonzeroPrimeReflection) :
    (primeReflectionRadicand i : E) = primeResiduePairValue i.val.1 i.val.2 ^ 2 - 4*(i.val.1 : ℕ) :=
  primeReflectionDifference_sq i.val.1 i.val.2

private theorem reflection_radical_ne_zero (i : NonzeroPrimeReflection) : primeReflectionRadical i ≠ 0 :=
  i.property

private theorem reflection_radical_sq (i : NonzeroPrimeReflection) :
    primeReflectionRadical i ^ 2 = algebraMap H E (primeReflectionRadicand i) := rfl

/-- The complete prime spectral extension is generated by these actual radicals. -/
theorem primeReflectionRadicals_adjoin_top :
    IntermediateField.adjoin H (Set.range primeReflectionRadical) = ⊤ := by
  let A := IntermediateField.adjoin H (Set.range primeReflectionRadical)
  have hv (p : Nat.Primes) (ρ : XiDivisorSupport) : primeResidueValue p ρ ∈ A := by
    have hu : primeResiduePairValue p ρ ∈ A :=
      A.algebraMap_mem ⟨primeResiduePairValue p ρ,primeResiduePairValue_mem_reflectionField p ρ⟩
    have hd : primeReflectionDifference p ρ ∈ A := by
      by_cases h : primeReflectionDifference p ρ = 0
      · rw [h]; exact A.zero_mem
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨(p,ρ),h⟩,rfl⟩
    have he : primeResidueValue p ρ =
        (primeResiduePairValue p ρ + primeReflectionDifference p ρ)/2 := by
      dsimp only [primeResiduePairValue,primeReflectionDifference]
      ring
    rw [he]
    exact A.div_mem (A.add_mem hu hd) (A.natCast_mem 2)
  have htop : (⊤ : IntermediateField B E) ≤ A.restrictScalars B := by
    rw [← primeTraceExtension_two_prime_families ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ (by decide)]
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x (⟨ρ,rfl⟩ | ⟨ρ,rfl⟩)
    · exact hv _ ρ
    · exact hv _ ρ
  exact top_unique (fun x _ => htop (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField B E)))

/-- Arithmetic signs on all nonzero prime reflection radicals. -/
def primeReflectionSignAction : K →* (NonzeroPrimeReflection → ℤˣ) :=
  radicalSignAction primeReflectionRadical primeReflectionRadicand
    reflection_radical_sq reflection_radical_ne_zero

/-- All finite square-class relations characterize simultaneous signs on the entire extension. -/
theorem primeReflectionSignAction_unique_extension (ε : NonzeroPrimeReflection → ℤˣ) :
    (∃! σ : K, primeReflectionSignAction σ = ε) ↔
      ∀ S : Finset NonzeroPrimeReflection, IsSquare (∏ i ∈ S, primeReflectionRadicand i) →
        ∏ i ∈ S, ε i = 1 :=
  radicalSignAction_unique_extension primeReflectionRadical primeReflectionRadicand
    reflection_radical_sq reflection_radical_ne_zero primeReflectionRadicals_adjoin_top ε

theorem primeReflectionSignAction_injective : Function.Injective primeReflectionSignAction :=
  radicalSignAction_injective primeReflectionRadical primeReflectionRadicand
    reflection_radical_sq reflection_radical_ne_zero primeReflectionRadicals_adjoin_top

theorem primeReflectionSignAction_continuous : Continuous primeReflectionSignAction :=
  radicalSignAction_continuous primeReflectionRadical primeReflectionRadicand
    reflection_radical_sq reflection_radical_ne_zero

theorem primeReflectionSignAction_range_closed : IsClosed (Set.range primeReflectionSignAction) :=
  (isCompact_range primeReflectionSignAction_continuous).isClosed

/-- Changing primes does not change the reflection square class at a zero. -/
theorem primeReflectionDifference_product_mem_pair (p q : Nat.Primes) (ρ : XiDivisorSupport) :
    primeReflectionDifference p ρ * primeReflectionDifference q ρ ∈ primePairField ρ := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (primePairField ρ),IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [map_mul,primeReflectionDifference_map,primeReflectionDifference_map]
  rcases (primePairField_fixing σ ρ).mp hσ with h | h
  · rw [h]
  · rw [h,primeReflectionDifference_reflection,primeReflectionDifference_reflection,neg_mul_neg]

theorem primeReflectionRadicands_same_zero_square (i j : NonzeroPrimeReflection)
    (hρ : i.val.2 = j.val.2) : IsSquare (primeReflectionRadicand i * primeReflectionRadicand j) := by
  have hm : primeReflectionRadical i * primeReflectionRadical j ∈ H := by
    apply primePairField_le_reflectionField i.val.2
    change primeReflectionDifference i.val.1 i.val.2 * primeReflectionDifference j.val.1 j.val.2 ∈ _
    rw [← hρ]
    exact primeReflectionDifference_product_mem_pair _ _ _
  refine ⟨⟨primeReflectionRadical i * primeReflectionRadical j,hm⟩,?_⟩
  apply Subtype.ext
  change primeReflectionRadical i ^ 2 * primeReflectionRadical j ^ 2 =
    (primeReflectionRadical i * primeReflectionRadical j) * (primeReflectionRadical i * primeReflectionRadical j)
  ring

private def reflectionSignProduct (S : Finset NonzeroPrimeReflection) :
    (NonzeroPrimeReflection → ℤˣ) →* ℤˣ where
  toFun ε := ∏ i ∈ S, ε i
  map_one' := by simp
  map_mul' ε η := by simp only [Pi.mul_apply,Finset.prod_mul_distrib]

/-- The exact closed sign subgroup cut out by the actual discriminant relations. -/
def primeReflectionRelationSigns : Subgroup (NonzeroPrimeReflection → ℤˣ) where
  carrier := {ε | ∀ S : Finset NonzeroPrimeReflection,
    IsSquare (∏ i ∈ S, primeReflectionRadicand i) → ∏ i ∈ S, ε i = 1}
  one_mem' := by intro S _; simp only [Pi.one_apply,Finset.prod_const_one]
  mul_mem' := by
    intro ε η hε hη S hS
    change reflectionSignProduct S (ε*η) = 1
    rw [map_mul,show reflectionSignProduct S ε = 1 from hε S hS,
      show reflectionSignProduct S η = 1 from hη S hS,mul_one]
  inv_mem' := by
    intro ε hε S hS
    change reflectionSignProduct S ε⁻¹ = 1
    rw [map_inv,show reflectionSignProduct S ε = 1 from hε S hS,inv_one]

def primeReflectionSignCoordinates : K →* primeReflectionRelationSigns where
  toFun σ := ⟨primeReflectionSignAction σ,fun S hS =>
    (radical_product_trivial_iff_square primeReflectionRadical primeReflectionRadicand
      reflection_radical_sq reflection_radical_ne_zero S).mpr hS σ⟩
  map_one' := Subtype.ext (map_one primeReflectionSignAction)
  map_mul' σ τ := Subtype.ext (map_mul primeReflectionSignAction σ τ)

private theorem reflection_sign_coordinates_bijective : Function.Bijective primeReflectionSignCoordinates := by
  constructor
  · intro σ τ h
    exact primeReflectionSignAction_injective (congrArg Subtype.val h)
  · intro ε
    obtain ⟨σ,hσ,_⟩ := (primeReflectionSignAction_unique_extension ε.val).mpr ε.property
    exact ⟨σ,Subtype.ext hσ⟩

/-- The whole infinite radical kernel is the annihilator of all discriminant square relations. -/
def primeReflectionSignEquiv : K ≃* primeReflectionRelationSigns :=
  MulEquiv.ofBijective primeReflectionSignCoordinates reflection_sign_coordinates_bijective

/-- The sign classification retains the full Krull topology. -/
def primeReflectionSignHomeomorph : K ≃ₜ primeReflectionRelationSigns :=
  Continuous.homeoOfEquivCompactToT2 (f := primeReflectionSignEquiv.toEquiv)
    (primeReflectionSignAction_continuous.subtype_mk _)

/-- The pair-orientation kernel is abelian. -/
theorem primeReflectionKernel_comm (σ τ : K) : σ*τ = τ*σ := by
  apply primeReflectionSignAction_injective
  rw [map_mul,map_mul,mul_comm]

/-- Every element of the pair-orientation kernel is an involution or the identity. -/
theorem primeReflectionKernel_square (σ : K) : σ*σ = 1 := by
  apply primeReflectionSignAction_injective
  rw [map_mul,map_one]
  funext i
  change primeReflectionSignAction σ i * primeReflectionSignAction σ i = 1
  rcases Int.units_eq_one_or (primeReflectionSignAction σ i) with h | h
  · rw [h,one_mul]
  · rw [h,neg_mul_neg,one_mul]

/-- The radical group embeds in the original arithmetic group by its actual field action. -/
def primeReflectionKernelEmbedding : K →* G where
  toFun σ := σ.restrictScalars B
  map_one' := rfl
  map_mul' _ _ := rfl

theorem primeReflectionKernelEmbedding_injective : Function.Injective primeReflectionKernelEmbedding := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun g : G => g x) h

/-- This embedding identifies the radical group with the full restriction kernel. -/
theorem primeReflectionKernelEmbedding_range :
    primeReflectionKernelEmbedding.range = primeReflectionRestriction.ker := by
  rw [primeReflectionRestriction_ker]
  ext σ
  constructor
  · rintro ⟨τ,rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    exact τ.commutes (⟨x,hx⟩ : H)
  · intro h
    let τ : K :=
      { __ := σ.toRingEquiv
        commutes' x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp h x x.property }
    exact ⟨τ,by apply AlgEquiv.ext; intro x; rfl⟩

theorem primeReflectionSignAction_on_radical (σ : K) (i : NonzeroPrimeReflection) :
    σ (primeReflectionRadical i) = ((primeReflectionSignAction σ i : ℤ) : E)*primeReflectionRadical i :=
  sourceRootSign_action (primeReflectionRadical i) (primeReflectionRadicand i)
    (reflection_radical_sq i) (reflection_radical_ne_zero i) σ

private theorem prime_coordinates_ext {ρ τ : XiDivisorSupport}
    (h : ∀ p : Nat.Primes, primeResidueValue p ρ = primeResidueValue p τ) : ρ=τ := by
  apply Subtype.ext
  apply two_prime_exponential_injective Nat.prime_two Nat.prime_three (by decide)
  apply Prod.ext
  · simpa only [primeResidueValue_coe] using
      congrArg (fun x : E => (x : ℂ)) (h ⟨2,Nat.prime_two⟩)
  · simpa only [primeResidueValue_coe] using
      congrArg (fun x : E => (x : ℂ)) (h ⟨3,Nat.prime_three⟩)

/-- Uniform radical negation is precisely functional reflection on every actual zero. -/
theorem primeReflectionSignAction_negative_iff (σ : K) :
    primeReflectionSignAction σ = (fun _ => -1) ↔
      ∀ ρ : XiDivisorSupport,
        primeTraceZeroMap (primeReflectionKernelEmbedding σ) ρ = xiZeroReflectEquiv ρ := by
  constructor
  · intro h ρ
    apply prime_coordinates_ext
    intro p
    have hd : σ (primeReflectionDifference p ρ) = -primeReflectionDifference p ρ := by
      by_cases hz : primeReflectionDifference p ρ = 0
      · rw [hz,map_zero,neg_zero]
      · let i : NonzeroPrimeReflection := ⟨(p,ρ),hz⟩
        have he := primeReflectionSignAction_on_radical σ i
        rw [h] at he
        simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,primeReflectionRadical,i] using he
    have hu : σ (primeResiduePairValue p ρ) = primeResiduePairValue p ρ :=
      σ.commutes ⟨primeResiduePairValue p ρ,primeResiduePairValue_mem_reflectionField p ρ⟩
    rw [← primeResidueValue_map]
    change σ (primeResidueValue p ρ) = primeResidueValue p (xiZeroReflectEquiv ρ)
    dsimp only [primeReflectionDifference,primeResiduePairValue] at hd hu
    rw [map_sub] at hd
    rw [map_add] at hu
    linear_combination (1/2 : E)*hu + (1/2 : E)*hd
  · intro h
    funext i
    have hd : σ (primeReflectionRadical i) = -primeReflectionRadical i := by
      change primeReflectionKernelEmbedding σ (primeReflectionDifference i.val.1 i.val.2) =
        -primeReflectionDifference i.val.1 i.val.2
      rw [primeReflectionDifference_map,h i.val.2,primeReflectionDifference_reflection]
    have hn : primeReflectionSignAction σ i ≠ 1 := by
      intro he
      have ha := primeReflectionSignAction_on_radical σ i
      rw [he,Units.val_one,Int.cast_one,one_mul,hd] at ha
      apply reflection_radical_ne_zero i
      linear_combination (-1/2 : E)*ha
    exact (Int.units_eq_one_or _).resolve_left hn

/-- The precise arithmetic obstruction to lifting functional reflection to the whole prime field. -/
theorem primeFunctionalReflection_lifts_iff :
    (∃ σ : G, ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) ↔
      ∀ S : Finset NonzeroPrimeReflection,
        IsSquare (∏ i ∈ S, primeReflectionRadicand i) → Even S.card := by
  constructor
  · rintro ⟨σ,hσ⟩
    have hfix : σ ∈ (H).fixingSubgroup := (primeReflectionField_fixing σ).mpr fun ρ => Or.inr (hσ ρ)
    have hker : σ ∈ primeReflectionRestriction.ker := by rwa [primeReflectionRestriction_ker]
    rw [← primeReflectionKernelEmbedding_range] at hker
    obtain ⟨τ,hτ⟩ := hker
    have hneg : primeReflectionSignAction τ = (fun _ => -1) :=
      (primeReflectionSignAction_negative_iff τ).mpr (by simpa only [hτ] using hσ)
    intro S hS
    have he := (radical_product_trivial_iff_square primeReflectionRadical primeReflectionRadicand
      reflection_radical_sq reflection_radical_ne_zero S).mpr hS τ
    change (∏ i ∈ S, primeReflectionSignAction τ i) = 1 at he
    rw [hneg,Finset.prod_const] at he
    exact (neg_one_pow_eq_one_iff_even (by decide)).mp he
  · intro h
    have hs : ∀ S : Finset NonzeroPrimeReflection,
        IsSquare (∏ i ∈ S, primeReflectionRadicand i) → ∏ _i ∈ S, (-1 : ℤˣ) = 1 := by
      intro S hS
      rw [Finset.prod_const]
      exact (neg_one_pow_eq_one_iff_even (by decide)).mpr (h S hS)
    obtain ⟨σ,hσ,_⟩ := (primeReflectionSignAction_unique_extension (fun _ => -1)).mpr hs
    exact ⟨primeReflectionKernelEmbedding σ,(primeReflectionSignAction_negative_iff σ).mp hσ⟩

/-- Faithfulness forces uniqueness of any global functional-reflection lift. -/
theorem primeFunctionalReflection_unique (σ τ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (hτ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap τ ρ = xiZeroReflectEquiv ρ) : σ=τ := by
  apply primeTraceGaloisAction_injective
  apply Equiv.ext
  intro ρ
  exact (hσ ρ).trans (hτ ρ).symm

/-- Every global reflection lift is central in the entire arithmetic Galois group. -/
theorem primeFunctionalReflection_central (σ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) (τ : G) :
    σ*τ = τ*σ := by
  apply primeTraceGaloisAction_injective
  apply Equiv.ext
  intro ρ
  change primeTraceZeroMap (σ*τ) ρ = primeTraceZeroMap (τ*σ) ρ
  rw [primeTraceZeroMap_mul,primeTraceZeroMap_mul,hσ (primeTraceZeroMap τ ρ),hσ ρ,
    primeTraceZeroMap_reflection]

theorem primeFunctionalReflection_square (σ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) : σ*σ = 1 := by
  apply primeTraceGaloisAction_injective
  apply Equiv.ext
  intro ρ
  change primeTraceZeroMap (σ*σ) ρ = primeTraceZeroMap 1 ρ
  rw [primeTraceZeroMap_mul,hσ ρ,hσ (xiZeroReflectEquiv ρ),reflection_twice,primeTraceZeroMap_one]

/-- The parity criterion supplies exactly one global reflection automorphism. -/
theorem primeFunctionalReflection_unique_lift_iff :
    (∃! σ : G, ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) ↔
      ∀ S : Finset NonzeroPrimeReflection,
        IsSquare (∏ i ∈ S, primeReflectionRadicand i) → Even S.card := by
  constructor
  · rintro ⟨σ,hσ,_⟩
    exact primeFunctionalReflection_lifts_iff.mp ⟨σ,hσ⟩
  · intro h
    obtain ⟨σ,hσ⟩ := primeFunctionalReflection_lifts_iff.mpr h
    exact ⟨σ,hσ,fun τ hτ => primeFunctionalReflection_unique τ σ hτ hσ⟩

/-- The kernel embedding preserves Krull topology on the full infinite extensions. -/
theorem primeReflectionKernelEmbedding_continuous : Continuous primeReflectionKernelEmbedding := by
  apply continuous_of_continuousAt_one primeReflectionKernelEmbedding
  change Filter.Tendsto primeReflectionKernelEmbedding (nhds 1)
    (nhds (primeReflectionKernelEmbedding 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro U hU
  obtain ⟨F,hF,hFU⟩ := (krullTopology_mem_nhds_one_iff B E U).mp hU
  letI : FiniteDimensional B F := hF
  let pb := Field.powerBasisOfFiniteOfSeparable B F
  let x : E := (pb.gen : F)
  have hfix : ∀ᶠ σ in nhds (1 : K), σ x = x :=
    (stabilizer_isOpen_of_isIntegral («K» := H) (L := E) x).mem_nhds (Subgroup.one_mem _)
  apply hfix.mono
  intro σ hσ
  apply hFU
  apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
  intro z hz
  obtain ⟨p,_,hp⟩ := pb.exists_eq_aeval (⟨z,hz⟩ : F)
  have hzp : z = Polynomial.aeval x p := by
    have hv := congrArg (fun r : F => (r : E)) hp
    exact hv.trans (Polynomial.aeval_algHom_apply (IntermediateField.val F) pb.gen p).symm
  change primeReflectionKernelEmbedding σ z = z
  calc
    primeReflectionKernelEmbedding σ z =
        (primeReflectionKernelEmbedding σ).toAlgHom (Polynomial.aeval x p) :=
      congrArg (primeReflectionKernelEmbedding σ) hzp
    _ = Polynomial.aeval ((primeReflectionKernelEmbedding σ).toAlgHom x) p :=
      (Polynomial.aeval_algHom_apply (primeReflectionKernelEmbedding σ).toAlgHom x p).symm
    _ = Polynomial.aeval x p := congrArg (fun y : E => Polynomial.aeval y p) hσ
    _ = z := hzp.symm

/-- A functional-reflection lift cannot be the identity, since no actual zero is real. -/
theorem primeFunctionalReflection_ne_one (σ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) : σ ≠ 1 := by
  intro he
  obtain ⟨z,hz⟩ := xiDivisorSupport_infinite.nonempty
  let ρ : XiDivisorSupport := ⟨z,hz⟩
  have hz := hσ ρ
  rw [he,primeTraceZeroMap_one] at hz
  have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) hz
  change (ρ : ℂ).im = (1-(ρ : ℂ)).im at hi
  simp only [Complex.sub_im,Complex.one_im] at hi
  exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])

/-- The pair quotient is real exactly when every actual zero lies on the critical line. -/
theorem primeReflectionField_real_iff :
    (∀ x ∈ H, (x : ℂ).im = 0) ↔ ∀ ρ : XiDivisorSupport, (ρ : ℂ).re=1/2 := by
  constructor
  · intro h ρ
    exact (primePairField_real_iff ρ).mp fun x hx => h x (primePairField_le_reflectionField ρ hx)
  · intro h x hx
    have hc : primeTraceConjugation ∈ (H).fixingSubgroup := by
      apply (fixing_reflection_generators _).mpr
      intro p ρ
      apply Subtype.ext
      exact Complex.conj_eq_iff_im.mpr
        ((primePairField_real_iff ρ).mpr (h ρ) _ (primeResiduePairValue_mem p ρ))
    exact Complex.conj_eq_iff_im.mp (congrArg (fun v : E => (v : ℂ))
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hc x hx))

/-- Purity is precisely triviality of ordinary conjugation on the arithmetic pair quotient. -/
theorem primeReflectionRestriction_conjugation_iff :
    primeReflectionRestriction primeTraceConjugation = 1 ↔
      ∀ ρ : XiDivisorSupport, (ρ : ℂ).re=1/2 := by
  change primeTraceConjugation ∈ primeReflectionRestriction.ker ↔ _
  rw [primeReflectionRestriction_ker,IntermediateField.mem_fixingSubgroup_iff]
  have hc (x : E) : primeTraceConjugation x = x ↔ (x : ℂ).im=0 := by
    constructor
    · intro h
      exact Complex.conj_eq_iff_im.mp (congrArg (fun v : E => (v : ℂ)) h)
    · intro h
      exact Subtype.ext (Complex.conj_eq_iff_im.mpr h)
  simp_rw [hc]
  exact primeReflectionField_real_iff

/-- Existence of a reflection lift alone does not identify it with ordinary conjugation. -/
theorem primeFunctionalReflection_eq_conjugation_iff (σ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) :
    σ = primeTraceConjugation ↔ ∀ ρ : XiDivisorSupport, (ρ : ℂ).re=1/2 := by
  constructor
  · intro he
    apply primeReflectionRestriction_conjugation_iff.mp
    change primeTraceConjugation ∈ primeReflectionRestriction.ker
    rw [primeReflectionRestriction_ker,← he]
    exact (primeReflectionField_fixing σ).mpr fun ρ => Or.inr (hσ ρ)
  · intro h
    apply primeFunctionalReflection_unique σ primeTraceConjugation hσ
    intro ρ
    rw [primeTraceZeroMap_conjugation]
    apply Subtype.ext
    apply Complex.ext
    · change (starRingEnd ℂ (ρ : ℂ)).re = (1-(ρ : ℂ)).re
      simp only [Complex.conj_re,Complex.sub_re,Complex.one_re]
      linarith only [h ρ]
    · change (starRingEnd ℂ (ρ : ℂ)).im = (1-(ρ : ℂ)).im
      simp only [Complex.conj_im,Complex.sub_im,Complex.one_im,zero_sub]

/-- Two radical signs agree on the whole kernel exactly when their square classes agree. -/
theorem primeReflectionSigns_equal_iff_square (i j : NonzeroPrimeReflection) :
    (∀ σ : K, primeReflectionSignAction σ i = primeReflectionSignAction σ j) ↔
      IsSquare (primeReflectionRadicand i * primeReflectionRadicand j) := by
  classical
  by_cases hij : i=j
  · subst j
    exact ⟨fun _ => ⟨primeReflectionRadicand i,rfl⟩,fun _ _ => rfl⟩
  have h := radical_product_trivial_iff_square primeReflectionRadical primeReflectionRadicand
    reflection_radical_sq reflection_radical_ne_zero ({i,j} : Finset NonzeroPrimeReflection)
  have hsign (a b : ℤˣ) : a*b=1 ↔ a=b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide
  simpa only [primeReflectionSignAction,Finset.prod_insert,Finset.mem_singleton,hij,not_false_eq_true,
    Finset.prod_singleton,hsign] using h

private theorem prime_conjugation_twice (x : E) :
    primeTraceConjugation (primeTraceConjugation x) = x := Subtype.ext (star_star (x : ℂ))

private theorem prime_conjugation_square : primeTraceConjugation * primeTraceConjugation = 1 := by
  apply AlgEquiv.ext
  exact prime_conjugation_twice

/-- Conjugation permutes the actual nonzero reflection radicals. -/
def primeReflectionConjugateIndex (i : NonzeroPrimeReflection) : NonzeroPrimeReflection :=
  ⟨(i.val.1,xiZeroConjEquiv i.val.2),by
    intro h
    apply i.property
    apply primeTraceConjugation.injective
    change primeTraceConjugation (primeReflectionDifference i.val.1 i.val.2) = primeTraceConjugation 0
    rw [map_zero,primeReflectionDifference_map,primeTraceZeroMap_conjugation,h]⟩

theorem primeReflectionRadical_conjugate (i : NonzeroPrimeReflection) :
    primeTraceConjugation (primeReflectionRadical i) =
      primeReflectionRadical (primeReflectionConjugateIndex i) := by
  change primeTraceConjugation (primeReflectionDifference i.val.1 i.val.2) =
    primeReflectionDifference i.val.1 (xiZeroConjEquiv i.val.2)
  rw [primeReflectionDifference_map,primeTraceZeroMap_conjugation]

/-- Conjugation acts on the radical kernel because the full pair field is normal. -/
def primeReflectionKernelConjugate (τ : K) : K where
  __ := primeTraceConjugation.toRingEquiv.trans
    (τ.toRingEquiv.trans primeTraceConjugation.toRingEquiv)
  commutes' x := by
    have hm : primeTraceConjugation (x : E) ∈ H := by
      have he : ((primeTraceConjugation.restrictNormal H x : H) : E) =
          primeTraceConjugation (x : E) := AlgEquiv.restrictNormal_commutes primeTraceConjugation H x
      exact he ▸ (primeTraceConjugation.restrictNormal H x).property
    have ht : τ (primeTraceConjugation (x : E)) = primeTraceConjugation (x : E) :=
      τ.commutes ⟨primeTraceConjugation (x : E),hm⟩
    change primeTraceConjugation (τ (primeTraceConjugation (x : E))) = (x : E)
    rw [ht,prime_conjugation_twice]

theorem primeReflectionKernelConjugate_embedding (τ : K) :
    primeReflectionKernelEmbedding (primeReflectionKernelConjugate τ) =
      primeTraceConjugation * primeReflectionKernelEmbedding τ * primeTraceConjugation := by
  apply AlgEquiv.ext
  intro x
  rfl

/-- On the exact sign group, conjugation transports the zero label by complex conjugation. -/
theorem primeReflectionSignAction_conjugate (τ : K) (i : NonzeroPrimeReflection) :
    primeReflectionSignAction (primeReflectionKernelConjugate τ) i =
      primeReflectionSignAction τ (primeReflectionConjugateIndex i) := by
  have he : primeReflectionKernelConjugate τ (primeReflectionRadical i) =
      ((primeReflectionSignAction τ (primeReflectionConjugateIndex i) : ℤ) : E)*primeReflectionRadical i := by
    change primeTraceConjugation (τ (primeTraceConjugation (primeReflectionRadical i))) = _
    rw [primeReflectionRadical_conjugate,primeReflectionSignAction_on_radical,map_mul,map_intCast,
      ← primeReflectionRadical_conjugate,prime_conjugation_twice]
  have ha := primeReflectionSignAction_on_radical (primeReflectionKernelConjugate τ) i
  have hc := mul_right_cancel₀ (reflection_radical_ne_zero i) (ha.symm.trans he)
  apply Units.ext
  exact Int.cast_injective hc

private theorem prime_conjugation_commutes_iff (g : G) :
    primeTraceConjugation*g = g*primeTraceConjugation ↔
      primeTraceConjugation*g*primeTraceConjugation = g := by
  constructor
  · intro h
    rw [h,mul_assoc,prime_conjugation_square,mul_one]
  · intro h
    have he := congrArg (fun a : G => a*primeTraceConjugation) h
    simpa only [mul_assoc,prime_conjugation_square,mul_one] using he

/-- Conjugation centralizes the full orientation kernel precisely when it fixes
all discriminant square classes. This is weaker than locating it in that kernel. -/
theorem primeConjugation_centralizes_kernel_iff :
    (∀ τ : K, primeTraceConjugation * primeReflectionKernelEmbedding τ =
      primeReflectionKernelEmbedding τ * primeTraceConjugation) ↔
      ∀ i : NonzeroPrimeReflection,
        IsSquare (primeReflectionRadicand i * primeReflectionRadicand (primeReflectionConjugateIndex i)) := by
  constructor
  · intro h i
    apply (primeReflectionSigns_equal_iff_square i (primeReflectionConjugateIndex i)).mp
    intro τ
    have he : primeReflectionKernelConjugate τ = τ := by
      apply primeReflectionKernelEmbedding_injective
      rw [primeReflectionKernelConjugate_embedding]
      exact (prime_conjugation_commutes_iff _).mp (h τ)
    have hs := primeReflectionSignAction_conjugate τ i
    rw [he] at hs
    exact hs
  · intro h τ
    apply (prime_conjugation_commutes_iff _).mpr
    rw [← primeReflectionKernelConjugate_embedding]
    apply congrArg primeReflectionKernelEmbedding
    apply primeReflectionSignAction_injective
    funext i
    rw [primeReflectionSignAction_conjugate]
    exact ((primeReflectionSigns_equal_iff_square i (primeReflectionConjugateIndex i)).mpr (h i) τ).symm

/-- The conjugate index gives the actual coefficient-field conjugate discriminant. -/
theorem primeReflectionRadicand_conjugate (i : NonzeroPrimeReflection) :
    primeTraceConjugation.restrictNormal H (primeReflectionRadicand i) =
      primeReflectionRadicand (primeReflectionConjugateIndex i) := by
  apply Subtype.ext
  apply (AlgEquiv.restrictNormal_commutes primeTraceConjugation H (primeReflectionRadicand i)).trans
  change primeTraceConjugation (primeReflectionRadical i ^ 2) =
    primeReflectionRadical (primeReflectionConjugateIndex i) ^ 2
  rw [map_pow,primeReflectionRadical_conjugate]

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionField_eq_iSup
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionField_fixing
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionField_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRestriction_surjective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRestriction_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRestriction_ker
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionDifference_sq
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRadicals_adjoin_top
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignAction_unique_extension
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignAction_range_closed
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionDifference_product_mem_pair
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRadicands_same_zero_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignHomeomorph
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionKernel_comm
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionKernel_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionKernelEmbedding_range
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionKernelEmbedding_continuous
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignAction_negative_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_lifts_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_unique
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_central
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_unique_lift_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_ne_one
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionField_real_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRestriction_conjugation_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_eq_conjugation_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSigns_equal_iff_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRadical_conjugate
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionSignAction_conjugate
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeConjugation_centralizes_kernel_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRadicand_conjugate
