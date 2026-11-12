import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeTraceGaloisGroupOfTheZeros
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Prime residue fields and functional-reflection pairs

Over the complete prime-source trace field, each zero and its unordered
reflection pair define finite residue fields. Each has a primitive generator
among its coordinates at any two distinct primes. Each zero's residue field is
quadratic or trivial over its pair field, with degree detected by its arithmetic
orbit. Real places of the pair field detect the critical line and its arithmetic
conjugates. These constructions retain every zero and the full mixed-trace base.
-/

noncomputable section
set_option autoImplicit false
open Complex Polynomial Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

private def fixedByPrimeAut (σ : G) : IntermediateField B E where
  carrier := {x | σ x = x}
  zero_mem' := map_zero σ
  one_mem' := map_one σ
  add_mem' hx hy := by change σ (_ + _) = _ + _; rw [map_add, hx, hy]
  mul_mem' hx hy := by change σ (_ * _) = _ * _; rw [map_mul, hx, hy]
  inv_mem' x hx := by change σ x⁻¹ = x⁻¹; rw [map_inv₀, hx]
  algebraMap_mem' := σ.commutes

private theorem fixing_adjoin_iff (S : Set E) (σ : G) :
    σ ∈ (IntermediateField.adjoin B S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  constructor
  · intro h x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h x
      (IntermediateField.subset_adjoin B S hx)
  · intro h
    have hle : IntermediateField.adjoin B S ≤ fixedByPrimeAut σ :=
      IntermediateField.adjoin_le_iff.mpr h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => hle hx

private theorem field_mem_of_fixed (F : IntermediateField B E) (x : E)
    (h : ∀ σ ∈ F.fixingSubgroup, σ x = x) : x ∈ F := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
  exact h

/-- The prime coordinate of an actual zero in the normal spectral extension. -/
def primeResidueValue (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeTraceRootValue ρ (Finsupp.single p 1)

theorem primeResidueValue_coe (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeResidueValue p ρ : ℂ) = Complex.exp ((Real.log (p : ℕ) : ℂ) * (ρ : ℂ)) := by
  change primeRelationValue (ρ : ℂ) (Finsupp.single p 1) = _
  rw [primeRelationValue_single, zpow_one, mul_comm]

theorem primeResidueValue_map (σ : G) (p : Nat.Primes) (ρ : XiDivisorSupport) :
    σ (primeResidueValue p ρ) = primeResidueValue p (primeTraceZeroMap σ ρ) :=
  (primeTraceZeroMap_value σ ρ (Finsupp.single p 1)).symm

private theorem residue_two_injective (p q : Nat.Primes) (hpq : p ≠ q)
    {ρ τ : XiDivisorSupport}
    (hp : primeResidueValue p ρ = primeResidueValue p τ)
    (hq : primeResidueValue q ρ = primeResidueValue q τ) : ρ = τ := by
  apply Subtype.ext
  apply two_prime_exponential_injective p.2 q.2 (fun h => hpq (Subtype.ext h))
  apply Prod.ext
  · simpa only [primeResidueValue_coe] using congrArg (fun x : E => (x : ℂ)) hp
  · simpa only [primeResidueValue_coe] using congrArg (fun x : E => (x : ℂ)) hq

/-- Prime coordinates symmetrized under functional reflection. -/
def primePairCoordinate (p : Nat.Primes) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log (p : ℕ) : ℂ)*z) +
    Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-z))

private theorem prime_coordinate_product (p : Nat.Primes) (z : ℂ) :
    Complex.exp ((Real.log (p : ℕ) : ℂ)*z) *
      Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-z)) = (p : ℕ) := by
  rw [← Complex.exp_add, ← mul_add, add_sub_cancel,
    mul_one, GaloisForLFunctions.RHTower.SixExponentials.exp_log_nat p.2.pos]

private theorem prime_pair_branch (p : Nat.Primes) {z w : ℂ}
    (h : primePairCoordinate p z = primePairCoordinate p w) :
    Complex.exp ((Real.log (p : ℕ) : ℂ)*z) = Complex.exp ((Real.log (p : ℕ) : ℂ)*w) ∨
    Complex.exp ((Real.log (p : ℕ) : ℂ)*z) = Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-w)) := by
  have hz := prime_coordinate_product p z
  have hw := prime_coordinate_product p w
  dsimp only [primePairCoordinate] at h
  have he : (Complex.exp ((Real.log (p : ℕ) : ℂ)*z) -
      Complex.exp ((Real.log (p : ℕ) : ℂ)*w)) *
      (Complex.exp ((Real.log (p : ℕ) : ℂ)*z) -
      Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-w))) = 0 := by
    calc
      _ = Complex.exp ((Real.log (p : ℕ) : ℂ)*z)^2 -
          Complex.exp ((Real.log (p : ℕ) : ℂ)*z) *
            (Complex.exp ((Real.log (p : ℕ) : ℂ)*w) +
              Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-w))) +
          Complex.exp ((Real.log (p : ℕ) : ℂ)*w) *
            Complex.exp ((Real.log (p : ℕ) : ℂ)*(1-w)) := by ring
      _ = 0 := by rw [← h, hw, ← hz]; ring
  exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp

/-- Three distinct symmetrized prime coordinates determine the unordered reflection pair. -/
theorem primePairCoordinate_separates (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {z w : ℂ}
    (hp : primePairCoordinate p z = primePairCoordinate p w)
    (hq : primePairCoordinate q z = primePairCoordinate q w)
    (hr : primePairCoordinate r z = primePairCoordinate r w) : z = w ∨ z = 1-w := by
  have inj (a b : Nat.Primes) (hab : a ≠ b) {u v : ℂ}
      (ha : Complex.exp ((Real.log (a : ℕ) : ℂ)*u) = Complex.exp ((Real.log (a : ℕ) : ℂ)*v))
      (hb : Complex.exp ((Real.log (b : ℕ) : ℂ)*u) = Complex.exp ((Real.log (b : ℕ) : ℂ)*v)) : u=v :=
    two_prime_exponential_injective a.2 b.2 (fun h => hab (Subtype.ext h)) (Prod.ext ha hb)
  rcases prime_pair_branch p hp with hp | hp
  · rcases prime_pair_branch q hq with hq | hq
    · exact Or.inl (inj p q hpq hp hq)
    · rcases prime_pair_branch r hr with hr | hr
      · exact Or.inl (inj p r hpr hp hr)
      · exact Or.inr (inj q r hqr hq hr)
  · rcases prime_pair_branch q hq with hq | hq
    · rcases prime_pair_branch r hr with hr | hr
      · exact Or.inl (inj q r hqr hq hr)
      · exact Or.inr (inj p r hpr hp hr)
    · exact Or.inr (inj p q hpq hp hq)

/-- The complete prime-value field at one zero, over the full mixed-trace base. -/
def primeResidueField (ρ : XiDivisorSupport) : IntermediateField B E :=
  IntermediateField.adjoin B (Set.range (fun p : Nat.Primes => primeResidueValue p ρ))

theorem primeResidueValue_mem (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResidueValue p ρ ∈ primeResidueField ρ :=
  IntermediateField.subset_adjoin B _ ⟨p,rfl⟩

/-- Fixing the residue field is exactly fixing its actual zero. -/
theorem primeResidueField_fixing (σ : G) (ρ : XiDivisorSupport) :
    σ ∈ (primeResidueField ρ).fixingSubgroup ↔ primeTraceZeroMap σ ρ = ρ := by
  rw [primeResidueField, fixing_adjoin_iff]
  constructor
  · intro h
    exact residue_two_injective ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ (by decide)
      ((primeResidueValue_map σ _ ρ).symm.trans (h _ ⟨_,rfl⟩))
      ((primeResidueValue_map σ _ ρ).symm.trans (h _ ⟨_,rfl⟩))
  · rintro h x ⟨p,rfl⟩
    rw [primeResidueValue_map, h]

/-- Any two distinct prime values generate the complete residue field. -/
theorem primeResidueField_two_generators (p q : Nat.Primes) (hpq : p ≠ q)
    (ρ : XiDivisorSupport) :
    primeResidueField ρ = IntermediateField.adjoin B {primeResidueValue p ρ, primeResidueValue q ρ} := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨r,rfl⟩
    apply field_mem_of_fixed
    intro σ hσ
    have h := (fixing_adjoin_iff _ σ).mp hσ
    have hρ := residue_two_injective p q hpq
      ((primeResidueValue_map σ p ρ).symm.trans (h _ (by simp)))
      ((primeResidueValue_map σ q ρ).symm.trans (h _ (by simp)))
    rw [primeResidueValue_map, hρ]
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact primeResidueValue_mem p ρ
    · exact Set.mem_singleton_iff.mp hx ▸ primeResidueValue_mem q ρ

private theorem reflect_twice (ρ : XiDivisorSupport) :
    xiZeroReflectEquiv (xiZeroReflectEquiv ρ) = ρ := by
  apply Subtype.ext
  simp only [xiZeroReflectEquiv_apply]
  ring

/-- The symmetric prime coordinate in the spectral extension. -/
def primeResiduePairValue (p : Nat.Primes) (ρ : XiDivisorSupport) : E :=
  primeResidueValue p ρ + primeResidueValue p (xiZeroReflectEquiv ρ)

theorem primeResiduePairValue_coe (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeResiduePairValue p ρ : ℂ) = primePairCoordinate p (ρ : ℂ) := by
  change (primeResidueValue p ρ : ℂ) + (primeResidueValue p (xiZeroReflectEquiv ρ) : ℂ) = _
  rw [primeResidueValue_coe,primeResidueValue_coe,xiZeroReflectEquiv_apply]
  rfl

theorem primeResiduePairValue_reflection (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResiduePairValue p (xiZeroReflectEquiv ρ) = primeResiduePairValue p ρ := by
  simp only [primeResiduePairValue,reflect_twice,add_comm]

theorem primeResiduePairValue_map (σ : G) (p : Nat.Primes) (ρ : XiDivisorSupport) :
    σ (primeResiduePairValue p ρ) = primeResiduePairValue p (primeTraceZeroMap σ ρ) := by
  simp only [primeResiduePairValue,map_add,primeResidueValue_map,primeTraceZeroMap_reflection]

private theorem residue_pair_three (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {ρ τ : XiDivisorSupport}
    (hp : primeResiduePairValue p ρ = primeResiduePairValue p τ)
    (hq : primeResiduePairValue q ρ = primeResiduePairValue q τ)
    (hr : primeResiduePairValue r ρ = primeResiduePairValue r τ) :
    ρ = τ ∨ ρ = xiZeroReflectEquiv τ := by
  have hc (s : Nat.Primes) (h : primeResiduePairValue s ρ = primeResiduePairValue s τ) :
      primePairCoordinate s (ρ : ℂ) = primePairCoordinate s (τ : ℂ) := by
    simpa only [primeResiduePairValue_coe] using congrArg (fun x : E => (x : ℂ)) h
  rcases primePairCoordinate_separates p q r hpq hpr hqr (hc p hp) (hc q hq) (hc r hr) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The residue field of the unordered functional-reflection pair. -/
def primePairField (ρ : XiDivisorSupport) : IntermediateField B E :=
  IntermediateField.adjoin B (Set.range (fun p : Nat.Primes => primeResiduePairValue p ρ))

theorem primeResiduePairValue_mem (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResiduePairValue p ρ ∈ primePairField ρ :=
  IntermediateField.subset_adjoin B _ ⟨p,rfl⟩

/-- Its fixing subgroup is precisely the stabilizer of the unordered reflection pair. -/
theorem primePairField_fixing (σ : G) (ρ : XiDivisorSupport) :
    σ ∈ (primePairField ρ).fixingSubgroup ↔
      primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ := by
  rw [primePairField,fixing_adjoin_iff]
  constructor
  · intro h
    exact residue_pair_three ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ ⟨5,by decide⟩
      (by decide) (by decide) (by decide)
      ((primeResiduePairValue_map σ _ ρ).symm.trans (h _ ⟨_,rfl⟩))
      ((primeResiduePairValue_map σ _ ρ).symm.trans (h _ ⟨_,rfl⟩))
      ((primeResiduePairValue_map σ _ ρ).symm.trans (h _ ⟨_,rfl⟩))
  · rintro h x ⟨p,rfl⟩
    rw [primeResiduePairValue_map]
    rcases h with h | h
    · rw [h]
    · rw [h,primeResiduePairValue_reflection]

/-- Any three distinct symmetric prime coordinates generate the entire pair field. -/
theorem primePairField_three_generators (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (ρ : XiDivisorSupport) :
    primePairField ρ = IntermediateField.adjoin B
      {primeResiduePairValue p ρ,primeResiduePairValue q ρ,primeResiduePairValue r ρ} := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨s,rfl⟩
    apply field_mem_of_fixed
    intro σ hσ
    have h := (fixing_adjoin_iff _ σ).mp hσ
    have hρ := residue_pair_three p q r hpq hpr hqr
      ((primeResiduePairValue_map σ p ρ).symm.trans (h _ (by simp)))
      ((primeResiduePairValue_map σ q ρ).symm.trans (h _ (by simp)))
      ((primeResiduePairValue_map σ r ρ).symm.trans (h _ (by simp)))
    rw [primeResiduePairValue_map]
    rcases hρ with hρ | hρ
    · rw [hρ]
    · rw [hρ,primeResiduePairValue_reflection]
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact primeResiduePairValue_mem p ρ
    · exact primeResiduePairValue_mem q ρ
    · exact primeResiduePairValue_mem r ρ

/-- Functional reflection does not change the full prime residue field. -/
theorem primeResidueField_reflection (ρ : XiDivisorSupport) :
    primeResidueField (xiZeroReflectEquiv ρ) = primeResidueField ρ := by
  have hfix : (primeResidueField (xiZeroReflectEquiv ρ)).fixingSubgroup =
      (primeResidueField ρ).fixingSubgroup := by
    ext σ
    rw [primeResidueField_fixing,primeResidueField_fixing,primeTraceZeroMap_reflection]
    exact xiZeroReflectEquiv.injective.eq_iff
  rw [← InfiniteGalois.fixedField_fixingSubgroup (primeResidueField ρ),
    ← InfiniteGalois.fixedField_fixingSubgroup (primeResidueField (xiZeroReflectEquiv ρ)),hfix]

theorem primePairField_le_residue (ρ : XiDivisorSupport) :
    primePairField ρ ≤ primeResidueField ρ := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x ⟨p,rfl⟩
  apply (primeResidueField ρ).add_mem (primeResidueValue_mem p ρ)
  rw [← primeResidueField_reflection ρ]
  exact primeResidueValue_mem p (xiZeroReflectEquiv ρ)

private theorem zero_ne_reflection (ρ : XiDivisorSupport) : ρ ≠ xiZeroReflectEquiv ρ := by
  intro h
  have hi := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) h
  change (ρ : ℂ).im = (1-(ρ : ℂ)).im at hi
  simp only [Complex.sub_im,Complex.one_im] at hi
  exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])

/-- The quadratic step collapses exactly when reflection leaves the arithmetic orbit. -/
theorem primePairField_eq_residue_iff (ρ : XiDivisorSupport) :
    primePairField ρ = primeResidueField ρ ↔
      ¬ ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ := by
  constructor
  · rintro h ⟨σ,hσ⟩
    have hm := (primePairField_fixing σ ρ).mpr (Or.inr hσ)
    rw [h] at hm
    exact zero_ne_reflection ρ (((primeResidueField_fixing σ ρ).mp hm).symm.trans hσ)
  · intro h
    have hf : (primePairField ρ).fixingSubgroup = (primeResidueField ρ).fixingSubgroup := by
      ext σ
      rw [primePairField_fixing,primeResidueField_fixing]
      exact ⟨fun hs => hs.resolve_right (fun he => h ⟨σ,he⟩),Or.inl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup (primePairField ρ),
      ← InfiniteGalois.fixedField_fixingSubgroup (primeResidueField ρ),hf]

instance primeResidueField_finite (ρ : XiDivisorSupport) :
    FiniteDimensional B (primeResidueField ρ) := by
  rw [primeResidueField_two_generators ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ (by decide)]
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral (R := B) x)

instance primePairField_finite (ρ : XiDivisorSupport) :
    FiniteDimensional B (primePairField ρ) := by
  rw [primePairField_three_generators ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩ ⟨5,by decide⟩
    (by decide) (by decide) (by decide)]
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral (R := B) x)

/-- The original embedding of the pair field is real precisely on the critical line. -/
theorem primePairField_real_iff (ρ : XiDivisorSupport) :
    (∀ x ∈ primePairField ρ, (x : ℂ).im = 0) ↔ (ρ : ℂ).re = 1/2 := by
  have hc (x : E) : primeTraceConjugation x = x ↔ (x : ℂ).im = 0 := by
    constructor
    · intro h
      apply Complex.conj_eq_iff_im.mp
      exact congrArg (fun z : E => (z : ℂ)) h
    · intro h
      exact Subtype.ext (Complex.conj_eq_iff_im.mpr h)
  have hf : (∀ x ∈ primePairField ρ, (x : ℂ).im = 0) ↔
      primeTraceConjugation ∈ (primePairField ρ).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact forall₂_congr fun x _ => (hc x).symm
  rw [hf,primePairField_fixing,primeTraceZeroMap_conjugation]
  have hne : xiZeroConjEquiv ρ ≠ ρ := by
    intro h
    have hC := congrArg (fun z : XiDivisorSupport => (z : ℂ)) h
    exact xi_divisor_support_im_ne_zero ρ (Complex.conj_eq_iff_im.mp hC)
  rw [or_iff_right hne]
  constructor
  · intro h
    have hR := congrArg (fun z : XiDivisorSupport => (z : ℂ).re) h
    change (starRingEnd ℂ (ρ : ℂ)).re = (1-(ρ : ℂ)).re at hR
    simp only [Complex.conj_re,Complex.sub_re,Complex.one_re] at hR
    linarith only [hR]
  · intro h
    apply Subtype.ext
    apply Complex.ext
    · change (starRingEnd ℂ (ρ : ℂ)).re = (1-(ρ : ℂ)).re
      simp only [Complex.conj_re,Complex.sub_re,Complex.one_re]
      linarith only [h]
    · change (starRingEnd ℂ (ρ : ℂ)).im = (1-(ρ : ℂ)).im
      simp only [Complex.conj_im,Complex.sub_im,Complex.one_im,zero_sub]

/-- Transport of every element of a pair field along the arithmetic zero action. -/
theorem primePairField_map_mem (σ : G) (ρ : XiDivisorSupport) {x : E}
    (hx : x ∈ primePairField ρ) : σ x ∈ primePairField (primeTraceZeroMap σ ρ) := by
  let F : IntermediateField B E := (primePairField (primeTraceZeroMap σ ρ)).comap σ.toAlgHom
  have hle : primePairField ρ ≤ F := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨p,rfl⟩
    change σ (primeResiduePairValue p ρ) ∈ primePairField (primeTraceZeroMap σ ρ)
    rw [primeResiduePairValue_map]
    exact primeResiduePairValue_mem p _
  exact hle hx

/-- Every arithmetic conjugate place is real exactly when the entire orbit is critical. -/
theorem primePairField_all_conjugates_real_iff (ρ : XiDivisorSupport) :
    (∀ σ : G, ∀ x ∈ primePairField ρ, ((σ x : E) : ℂ).im = 0) ↔
      ∀ σ : G, (primeTraceZeroMap σ ρ : ℂ).re = 1/2 := by
  constructor
  · intro h σ
    apply (primePairField_real_iff _).mp
    intro x hx
    have hinv : primeTraceZeroMap σ⁻¹ (primeTraceZeroMap σ ρ) = ρ := by
      rw [← primeTraceZeroMap_mul,inv_mul_cancel,primeTraceZeroMap_one]
    have hm := primePairField_map_mem σ⁻¹ (primeTraceZeroMap σ ρ) hx
    rw [hinv] at hm
    have hr := h σ (σ⁻¹ x) hm
    change ((σ (σ.symm x) : E) : ℂ).im = 0 at hr
    simpa only [AlgEquiv.apply_symm_apply] using hr
  · intro h σ x hx
    exact (primePairField_real_iff _).mpr (h σ) _ (primePairField_map_mem σ ρ hx)

private theorem residue_adjoin_pair (p : Nat.Primes) (ρ : XiDivisorSupport)
    (hp : primeResidueValue p ρ ≠ primeResidueValue p (xiZeroReflectEquiv ρ)) :
    (IntermediateField.adjoin (primePairField ρ) {primeResidueValue p ρ}).restrictScalars B = primeResidueField ρ := by
  rw [IntermediateField.restrictScalars_adjoin]
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases hx with hx | hx
    · exact primePairField_le_residue ρ hx
    · exact Set.mem_singleton_iff.mp hx ▸ primeResidueValue_mem p ρ
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨q,rfl⟩
    apply field_mem_of_fixed
    intro σ hσ
    have h := (fixing_adjoin_iff _ σ).mp hσ
    have hh : σ ∈ (primePairField ρ).fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun y hy => h y (Or.inl hy)
    have hv := h (primeResidueValue p ρ) (Or.inr (Set.mem_singleton _))
    rw [primeResidueValue_map] at hv
    have hz : primeTraceZeroMap σ ρ = ρ := by
      rcases (primePairField_fixing σ ρ).mp hh with hz | hz
      · exact hz
      · exact (hp (hv.symm.trans (congrArg (primeResidueValue p) hz))).elim
    rw [primeResidueValue_map,hz]

/-- The residue field viewed over its reflection-pair field. -/
def primeResidueOverPair (ρ : XiDivisorSupport) : IntermediateField (primePairField ρ) E where
  __ := (primeResidueField ρ).toSubfield
  algebraMap_mem' x := primePairField_le_residue ρ x.property

private theorem residue_over_pair_adjoin (p : Nat.Primes) (ρ : XiDivisorSupport)
    (hp : primeResidueValue p ρ ≠ primeResidueValue p (xiZeroReflectEquiv ρ)) :
    primeResidueOverPair ρ = IntermediateField.adjoin (primePairField ρ) {primeResidueValue p ρ} := by
  ext x
  change x ∈ primeResidueField ρ ↔ x ∈ IntermediateField.adjoin (primePairField ρ) {primeResidueValue p ρ}
  rw [← residue_adjoin_pair p ρ hp]
  rfl

private theorem exists_distinguishing_prime (ρ : XiDivisorSupport) :
    ∃ p : Nat.Primes, primeResidueValue p ρ ≠ primeResidueValue p (xiZeroReflectEquiv ρ) := by
  by_contra h
  have hh : ∀ p : Nat.Primes, primeResidueValue p ρ = primeResidueValue p (xiZeroReflectEquiv ρ) := by
    intro p
    by_contra hp
    exact h ⟨p,hp⟩
  exact zero_ne_reflection ρ (residue_two_injective ⟨2,Nat.prime_two⟩ ⟨3,Nat.prime_three⟩
    (by decide) (hh _) (hh _))

/-- The quadratic equation of a prime coordinate over its reflection-pair field. -/
def primeResidueQuadratic (p : Nat.Primes) (ρ : XiDivisorSupport) : (primePairField ρ)[X] :=
  X^2 + (C (-⟨primeResiduePairValue p ρ,primeResiduePairValue_mem p ρ⟩) * X + C ((p : ℕ) : primePairField ρ))

private theorem residue_quadratic_degree (p : Nat.Primes) (ρ : XiDivisorSupport) :
    (primeResidueQuadratic p ρ).Monic ∧ (primeResidueQuadratic p ρ).natDegree = 2 := by
  let u : primePairField ρ := ⟨primeResiduePairValue p ρ,primeResiduePairValue_mem p ρ⟩
  have hd : (C (-u) * X + C ((p : ℕ) : primePairField ρ) : (primePairField ρ)[X]).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp only [Polynomial.natDegree_C, zero_le]
  have hdeg : (C (-u)*X + C ((p : ℕ) : primePairField ρ) : (primePairField ρ)[X]).degree < (2 : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hd)
  constructor
  · exact Polynomial.monic_X_pow_add hdeg
  · change (X^2 + (C (-u)*X + C ((p : ℕ) : primePairField ρ)) : (primePairField ρ)[X]).natDegree = 2
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt
      (by simpa only [Polynomial.degree_X_pow] using hdeg),Polynomial.natDegree_X_pow]

theorem primeResidueQuadratic_root (p : Nat.Primes) (ρ : XiDivisorSupport) :
    aeval (primeResidueValue p ρ) (primeResidueQuadratic p ρ) = 0 := by
  have hprod : primeResidueValue p ρ * primeResidueValue p (xiZeroReflectEquiv ρ) = (p : ℕ) := by
    apply Subtype.ext
    change (primeResidueValue p ρ : ℂ) * (primeResidueValue p (xiZeroReflectEquiv ρ) : ℂ) = (p : ℕ)
    rw [primeResidueValue_coe,primeResidueValue_coe,xiZeroReflectEquiv_apply]
    exact prime_coordinate_product p (ρ : ℂ)
  rw [primeResidueQuadratic,Polynomial.aeval_def,eval₂_add,eval₂_pow,eval₂_X,
    eval₂_add,eval₂_mul,eval₂_C,eval₂_X,eval₂_C,map_neg,map_natCast]
  change primeResidueValue p ρ ^ 2 +
    (-(primeResidueValue p ρ + primeResidueValue p (xiZeroReflectEquiv ρ)) * primeResidueValue p ρ + (p : ℕ)) = 0
  rw [← hprod]
  ring

instance primeResidueOverPair_finite (ρ : XiDivisorSupport) :
    FiniteDimensional (primePairField ρ) (primeResidueOverPair ρ) := by
  obtain ⟨p,hp⟩ := exists_distinguishing_prime ρ
  rw [residue_over_pair_adjoin p ρ hp]
  exact IntermediateField.adjoin.finiteDimensional
    ((Algebra.IsIntegral.isIntegral (R := B) (primeResidueValue p ρ)).tower_top)

/-- The complete prime residue field is quadratic or trivial over its pair field. -/
theorem primeResidueOverPair_degree_le_two (ρ : XiDivisorSupport) :
    Module.finrank (primePairField ρ) (primeResidueOverPair ρ) ≤ 2 := by
  obtain ⟨p,hp⟩ := exists_distinguishing_prime ρ
  rw [residue_over_pair_adjoin p ρ hp,IntermediateField.adjoin.finrank
    ((Algebra.IsIntegral.isIntegral (R := B) (primeResidueValue p ρ)).tower_top)]
  calc
    _ ≤ (primeResidueQuadratic p ρ).natDegree := Polynomial.natDegree_le_of_dvd
      (minpoly.dvd _ _ (primeResidueQuadratic_root p ρ)) (residue_quadratic_degree p ρ).1.ne_zero
    _ = 2 := (residue_quadratic_degree p ρ).2

private theorem pair_restrict_bot (ρ : XiDivisorSupport) :
    (⊥ : IntermediateField (primePairField ρ) E).restrictScalars B = primePairField ρ := by
  ext x
  change x ∈ (⊥ : IntermediateField (primePairField ρ) E) ↔ x ∈ primePairField ρ
  rw [IntermediateField.mem_bot]
  constructor
  · rintro ⟨y,rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

private theorem residue_pair_degree_one_iff (ρ : XiDivisorSupport) :
    Module.finrank (primePairField ρ) (primeResidueOverPair ρ) = 1 ↔
      primePairField ρ = primeResidueField ρ := by
  rw [IntermediateField.finrank_eq_one_iff]
  constructor
  · intro h
    have he := congrArg (IntermediateField.restrictScalars B) h
    change primeResidueField ρ = (⊥ : IntermediateField (primePairField ρ) E).restrictScalars B at he
    rw [pair_restrict_bot] at he
    exact he.symm
  · intro h
    apply IntermediateField.restrictScalars_injective B
    change primeResidueField ρ = (⊥ : IntermediateField (primePairField ρ) E).restrictScalars B
    rw [pair_restrict_bot,h]

/-- Degree two means exactly that functional reflection is present in this arithmetic orbit. -/
theorem primeResidueOverPair_degree_two_iff (ρ : XiDivisorSupport) :
    Module.finrank (primePairField ρ) (primeResidueOverPair ρ) = 2 ↔
      ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ := by
  have hle := primeResidueOverPair_degree_le_two ρ
  have hpos := Module.finrank_pos (R := primePairField ρ) (M := primeResidueOverPair ρ)
  have h1 := (residue_pair_degree_one_iff ρ).trans (primePairField_eq_residue_iff ρ)
  constructor
  · intro h2
    by_contra h
    have hone := h1.mpr h
    omega
  · intro h
    have hn : Module.finrank (primePairField ρ) (primeResidueOverPair ρ) ≠ 1 :=
      fun he => h1.mp he h
    omega

/-- Two entire prime-coordinate families generate the full infinite spectral extension. -/
theorem primeTraceExtension_two_prime_families (p q : Nat.Primes) (hpq : p ≠ q) :
    IntermediateField.adjoin B
      (Set.range (primeResidueValue p) ∪ Set.range (primeResidueValue q)) = (⊤ : IntermediateField B E) := by
  apply top_unique
  intro x _
  apply field_mem_of_fixed
  intro σ hσ
  have h := (fixing_adjoin_iff _ σ).mp hσ
  have hσone : σ = 1 := by
    apply primeTraceGaloisAction_injective
    apply Equiv.ext
    intro ρ
    change primeTraceZeroMap σ ρ = primeTraceZeroMap 1 ρ
    rw [primeTraceZeroMap_one]
    exact residue_two_injective p q hpq
      ((primeResidueValue_map σ p ρ).symm.trans (h _ (Or.inl ⟨ρ,rfl⟩)))
      ((primeResidueValue_map σ q ρ).symm.trans (h _ (Or.inr ⟨ρ,rfl⟩)))
  rw [hσone]
  rfl

private theorem conjugation_ne_fixed_zero (ρ : XiDivisorSupport) :
    primeTraceZeroMap primeTraceConjugation ρ ≠ ρ := by
  rw [primeTraceZeroMap_conjugation]
  intro h
  exact xi_divisor_support_im_ne_zero ρ
    (Complex.conj_eq_iff_im.mp (congrArg (fun z : XiDivisorSupport => (z : ℂ)) h))

private theorem conjugation_reflects_critical (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1/2) :
    primeTraceZeroMap primeTraceConjugation ρ = xiZeroReflectEquiv ρ := by
  have hc : primeTraceConjugation ∈ (primePairField ρ).fixingSubgroup := by
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    intro x hx
    apply Subtype.ext
    exact Complex.conj_eq_iff_im.mpr ((primePairField_real_iff ρ).mpr hρ x hx)
  exact ((primePairField_fixing _ ρ).mp hc).resolve_left (conjugation_ne_fixed_zero ρ)

/-- On the critical line the pair field is exactly the real part of the prime residue field. -/
theorem primePairField_real_part_iff (ρ : XiDivisorSupport) :
    (∀ x : E, x ∈ primePairField ρ ↔ x ∈ primeResidueField ρ ∧ (x : ℂ).im = 0) ↔
      (ρ : ℂ).re = 1/2 := by
  constructor
  · intro h
    exact (primePairField_real_iff ρ).mp fun x hx => ((h x).mp hx).2
  · intro hρ x
    constructor
    · intro hx
      exact ⟨primePairField_le_residue ρ hx,(primePairField_real_iff ρ).mpr hρ x hx⟩
    · rintro ⟨hx,hreal⟩
      have hc : primeTraceConjugation x = x := Subtype.ext (Complex.conj_eq_iff_im.mpr hreal)
      apply field_mem_of_fixed
      intro σ hσ
      rcases (primePairField_fixing σ ρ).mp hσ with hz | hz
      · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp
          ((primeResidueField_fixing σ ρ).mpr hz) x hx
      · have hcomp : primeTraceZeroMap (σ * primeTraceConjugation) ρ = ρ := by
          rw [primeTraceZeroMap_mul,conjugation_reflects_critical ρ hρ,
            primeTraceZeroMap_reflection,hz,reflect_twice]
        have he := (IntermediateField.mem_fixingSubgroup_iff _ _).mp
          ((primeResidueField_fixing _ ρ).mpr hcomp) x hx
        change σ (primeTraceConjugation x) = x at he
        rwa [hc] at he

/-- A critical zero gives a genuine quadratic extension of its real pair field. -/
theorem primeResidueOverPair_degree_two_of_critical (ρ : XiDivisorSupport)
    (hρ : (ρ : ℂ).re = 1/2) :
    Module.finrank (primePairField ρ) (primeResidueOverPair ρ) = 2 :=
  (primeResidueOverPair_degree_two_iff ρ).mpr
    ⟨primeTraceConjugation,conjugation_reflects_critical ρ hρ⟩

/-- One prime exponential determines the real part of its exponent. -/
private theorem prime_exp_real_part (p : Nat.Primes) {z w : ℂ}
    (h : Complex.exp ((Real.log (p : ℕ) : ℂ)*z) = Complex.exp ((Real.log (p : ℕ) : ℂ)*w)) :
    z.re = w.re := by
  have hn := congrArg norm h
  rw [Complex.norm_exp,Complex.norm_exp] at hn
  have hr := Real.exp_injective hn
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne' hr

private theorem complex_re_height {z w : ℂ} (hr : z.re = w.re) (hi : |z.im| = |w.im|) :
    z = w ∨ z = starRingEnd ℂ w := by
  rcases abs_eq_abs.mp hi with hi | hi
  · exact Or.inl (Complex.ext hr hi)
  · exact Or.inr (Complex.ext hr hi)

private theorem complex_conj_critical {w : ℂ} (hw : w.re = 1/2) :
    starRingEnd ℂ w = 1-w := by
  apply Complex.ext
  · simp only [Complex.conj_re,Complex.sub_re,Complex.one_re]
    linarith only [hw]
  · simp only [Complex.conj_im,Complex.sub_im,Complex.one_im,zero_sub]

private theorem pair_coordinate_conj (p : Nat.Primes) (z : ℂ) :
    primePairCoordinate p (starRingEnd ℂ z) = starRingEnd ℂ (primePairCoordinate p z) := by
  simp only [primePairCoordinate,map_add,← Complex.exp_conj,map_mul,Complex.conj_ofReal,map_sub,map_one]

private theorem pair_coordinate_reflect (p : Nat.Primes) (z : ℂ) :
    primePairCoordinate p (1-z) = primePairCoordinate p z := by
  have h : (1 : ℂ)-(1-z)=z := by ring
  simp only [primePairCoordinate,h,add_comm]

private theorem zero_map_height (σ : G) (ρ : XiDivisorSupport) :
    |(primeTraceZeroMap σ ρ : ℂ).im| = |(ρ : ℂ).im| :=
  primeTraceEmbeddingZero_height ((IntermediateField.val E).comp σ.toAlgHom) ρ

/-- At a fixed absolute height two symmetric prime coordinates separate reflection pairs. -/
theorem primePairCoordinate_two_at_height (p q : Nat.Primes) (hpq : p ≠ q) {z w : ℂ}
    (hi : |z.im| = |w.im|)
    (hp : primePairCoordinate p z = primePairCoordinate p w)
    (hq : primePairCoordinate q z = primePairCoordinate q w) : z=w ∨ z=1-w := by
  have hinj := two_prime_exponential_injective p.2 q.2 (fun h => hpq (Subtype.ext h))
  have hmix (hre : z.re=w.re) (hflip : z.re=(1-w).re) : z=w ∨ z=1-w := by
    have hc : w.re=1/2 := by
      simp only [Complex.sub_re,Complex.one_re] at hflip
      linarith only [hre,hflip]
    rcases complex_re_height hre hi with he | he
    · exact Or.inl he
    · exact Or.inr (he.trans (complex_conj_critical hc))
  rcases prime_pair_branch p hp with hp | hp
  · rcases prime_pair_branch q hq with hq | hq
    · exact Or.inl (hinj (Prod.ext hp hq))
    · exact hmix (prime_exp_real_part p hp) (prime_exp_real_part q hq)
  · rcases prime_pair_branch q hq with hq | hq
    · exact hmix (prime_exp_real_part q hq) (prime_exp_real_part p hp)
    · exact Or.inr (hinj (Prod.ext hp hq))

/-- Height preservation reduces the complete pair field to any two symmetric prime coordinates. -/
theorem primePairField_two_generators (p q : Nat.Primes) (hpq : p ≠ q) (ρ : XiDivisorSupport) :
    primePairField ρ = IntermediateField.adjoin B {primeResiduePairValue p ρ,primeResiduePairValue q ρ} := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨r,rfl⟩
    apply field_mem_of_fixed
    intro σ hσ
    have h := (fixing_adjoin_iff _ σ).mp hσ
    have he (s : Nat.Primes) (hs : σ (primeResiduePairValue s ρ)=primeResiduePairValue s ρ) :
        primePairCoordinate s (primeTraceZeroMap σ ρ : ℂ) = primePairCoordinate s (ρ : ℂ) := by
      have hv := (primeResiduePairValue_map σ s ρ).symm.trans hs
      simpa only [primeResiduePairValue_coe] using congrArg (fun v : E => (v : ℂ)) hv
    have hz := primePairCoordinate_two_at_height p q hpq (zero_map_height σ ρ)
      (he p (h _ (by simp))) (he q (h _ (by simp)))
    rw [primeResiduePairValue_map]
    rcases hz with hz | hz
    · rw [show primeTraceZeroMap σ ρ = ρ from Subtype.ext hz]
    · rw [show primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ from Subtype.ext hz,
        primeResiduePairValue_reflection]
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact primeResiduePairValue_mem p ρ
    · exact primeResiduePairValue_mem q ρ

private theorem value_conj_zero (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResidueValue p (xiZeroConjEquiv ρ) = primeTraceConjugation (primeResidueValue p ρ) := by
  rw [primeResidueValue_map,primeTraceZeroMap_conjugation]

/-- A prime value generates the complete residue field exactly when it is nonreal. -/
theorem primeResidueField_single_iff (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeResidueField ρ = IntermediateField.adjoin B {primeResidueValue p ρ} ↔
      (primeResidueValue p ρ : ℂ).im ≠ 0 := by
  constructor
  · intro h hreal
    have hc : primeTraceConjugation ∈ (IntermediateField.adjoin B {primeResidueValue p ρ}).fixingSubgroup := by
      apply (fixing_adjoin_iff _ _).mpr
      rintro x (rfl : x = primeResidueValue p ρ)
      exact Subtype.ext (Complex.conj_eq_iff_im.mpr hreal)
    rw [← h] at hc
    exact conjugation_ne_fixed_zero ρ ((primeResidueField_fixing _ ρ).mp hc)
  · intro hn
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro x ⟨q,rfl⟩
      apply field_mem_of_fixed
      intro σ hσ
      have hv := (fixing_adjoin_iff _ σ).mp hσ _ (Set.mem_singleton _)
      have he := congrArg (fun v : E => (v : ℂ)) ((primeResidueValue_map σ p ρ).symm.trans hv)
      simp only [primeResidueValue_coe] at he
      have hz : primeTraceZeroMap σ ρ = ρ := by
        rcases complex_re_height (prime_exp_real_part p he) (zero_map_height σ ρ) with hz | hz
        · exact Subtype.ext hz
        · have hconj : primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ := Subtype.ext hz
          rw [primeResidueValue_map,hconj,value_conj_zero] at hv
          exact (hn (Complex.conj_eq_iff_im.mp (congrArg (fun v : E => (v : ℂ)) hv))).elim
      rw [primeResidueValue_map,hz]
    · exact IntermediateField.adjoin_simple_le_iff.mpr (primeResidueValue_mem p ρ)

private theorem pair_single_height (p : Nat.Primes) {z w : ℂ}
    (hi : |z.im| = |w.im|) (he : primePairCoordinate p z = primePairCoordinate p w)
    (hgood : w.re=1/2 ∨ (primePairCoordinate p w).im ≠ 0) : z=w ∨ z=1-w := by
  have hbranch {v : ℂ} (hv : v=w ∨ v=1-w) :
      primePairCoordinate p v = primePairCoordinate p w := by
    rcases hv with rfl | rfl
    · rfl
    · exact pair_coordinate_reflect p w
  have hconj {v : ℂ} (hv : v=w ∨ v=1-w) (hz : z=starRingEnd ℂ v) : z=w ∨ z=1-w := by
    rcases hgood with hc | hn
    · have hcconj := complex_conj_critical hc
      rcases hv with rfl | rfl
      · exact Or.inr (hz.trans hcconj)
      · left
        rw [hz,map_sub,map_one,hcconj]
        ring
    · have hreal : starRingEnd ℂ (primePairCoordinate p w) = primePairCoordinate p w := by
        rw [← hbranch hv,← pair_coordinate_conj,← hz]
        exact he.trans (hbranch hv).symm
      exact (hn (Complex.conj_eq_iff_im.mp hreal)).elim
  rcases prime_pair_branch p he with hp | hp
  · rcases complex_re_height (prime_exp_real_part p hp) hi with hz | hz
    · exact Or.inl hz
    · exact hconj (Or.inl rfl) hz
  · have hi' : |z.im| = |(1-w).im| := by
      simpa only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg] using hi
    rcases complex_re_height (prime_exp_real_part p hp) hi' with hz | hz
    · exact Or.inr hz
    · exact hconj (Or.inr rfl) hz

/-- One symmetric coordinate generates the pair field exactly off its real resonance,
except that every prime works on the critical line. -/
theorem primePairField_single_iff (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primePairField ρ = IntermediateField.adjoin B {primeResiduePairValue p ρ} ↔
      (ρ : ℂ).re=1/2 ∨ (primeResiduePairValue p ρ : ℂ).im ≠ 0 := by
  constructor
  · intro h
    by_cases hr : (primeResiduePairValue p ρ : ℂ).im=0
    · left
      apply (primePairField_real_iff ρ).mp
      have hc : primeTraceConjugation ∈ (primePairField ρ).fixingSubgroup := by
        rw [h,fixing_adjoin_iff]
        rintro x (rfl : x = primeResiduePairValue p ρ)
        exact Subtype.ext (Complex.conj_eq_iff_im.mpr hr)
      intro x hx
      exact Complex.conj_eq_iff_im.mp (congrArg (fun v : E => (v : ℂ))
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hc x hx))
    · exact Or.inr hr
  · intro hg
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro x ⟨q,rfl⟩
      apply field_mem_of_fixed
      intro σ hσ
      have hv := (fixing_adjoin_iff _ σ).mp hσ _ (Set.mem_singleton _)
      have he := congrArg (fun v : E => (v : ℂ)) ((primeResiduePairValue_map σ p ρ).symm.trans hv)
      simp only [primeResiduePairValue_coe] at he
      have hgood : (ρ : ℂ).re=1/2 ∨ (primePairCoordinate p (ρ : ℂ)).im ≠ 0 := by
        simpa only [primeResiduePairValue_coe] using hg
      have hz := pair_single_height p (zero_map_height σ ρ) he hgood
      rw [primeResiduePairValue_map]
      rcases hz with hz | hz
      · rw [show primeTraceZeroMap σ ρ = ρ from Subtype.ext hz]
      · rw [show primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ from Subtype.ext hz,
          primeResiduePairValue_reflection]
    · exact IntermediateField.adjoin_simple_le_iff.mpr (primeResiduePairValue_mem p ρ)

/-- Among any two distinct primes, one coordinate is a primitive generator of the full residue field. -/
theorem primeResidueField_one_of_two (p q : Nat.Primes) (hpq : p ≠ q) (ρ : XiDivisorSupport) :
    primeResidueField ρ = IntermediateField.adjoin B {primeResidueValue p ρ} ∨
      primeResidueField ρ = IntermediateField.adjoin B {primeResidueValue q ρ} := by
  rw [primeResidueField_single_iff,primeResidueField_single_iff]
  by_cases hp : (primeResidueValue p ρ : ℂ).im ≠ 0
  · exact Or.inl hp
  · right
    intro hq
    have hp0 := not_ne_iff.mp hp
    have he (r : Nat.Primes) (hr : (primeResidueValue r ρ : ℂ).im=0) :
        primeResidueValue r (xiZeroConjEquiv ρ) = primeResidueValue r ρ := by
      rw [value_conj_zero]
      exact Subtype.ext (Complex.conj_eq_iff_im.mpr hr)
    have hz := residue_two_injective p q hpq (he p hp0) (he q hq)
    apply conjugation_ne_fixed_zero ρ
    rw [primeTraceZeroMap_conjugation]
    exact hz

/-- Among any two distinct primes, one symmetric coordinate generates the full pair field. -/
theorem primePairField_one_of_two (p q : Nat.Primes) (hpq : p ≠ q) (ρ : XiDivisorSupport) :
    primePairField ρ = IntermediateField.adjoin B {primeResiduePairValue p ρ} ∨
      primePairField ρ = IntermediateField.adjoin B {primeResiduePairValue q ρ} := by
  by_cases hcrit : (ρ : ℂ).re=1/2
  · exact Or.inl ((primePairField_single_iff p ρ).mpr (Or.inl hcrit))
  by_cases hp : (primeResiduePairValue p ρ : ℂ).im ≠ 0
  · exact Or.inl ((primePairField_single_iff p ρ).mpr (Or.inr hp))
  right
  apply (primePairField_single_iff q ρ).mpr
  right
  intro hq
  have hp0 := not_ne_iff.mp hp
  have hc : primeTraceConjugation ∈ (primePairField ρ).fixingSubgroup := by
    rw [primePairField_two_generators p q hpq,fixing_adjoin_iff]
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subtype.ext (Complex.conj_eq_iff_im.mpr hp0)
    · exact Subtype.ext (Complex.conj_eq_iff_im.mpr hq)
  apply hcrit
  apply (primePairField_real_iff ρ).mp
  intro x hx
  exact Complex.conj_eq_iff_im.mp (congrArg (fun v : E => (v : ℂ))
    ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hc x hx))

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairCoordinate_separates
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_fixing
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_two_generators
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_fixing
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_reflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_eq_residue_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_real_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_all_conjugates_real_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueQuadratic_root
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueOverPair_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueOverPair_degree_le_two
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueOverPair_degree_two_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExtension_two_prime_families
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_real_part_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueOverPair_degree_two_of_critical
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairCoordinate_two_at_height
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_two_generators
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_single_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_single_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueField_one_of_two
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_one_of_two
