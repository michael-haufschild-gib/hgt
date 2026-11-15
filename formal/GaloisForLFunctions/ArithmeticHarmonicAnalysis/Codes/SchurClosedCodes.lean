import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FiberPullbackCodes
import Mathlib.Algebra.Algebra.Subalgebra.Pi

/-!
# Classification of unital codes closed under coordinatewise multiplication

A subalgebra of functions on a finite set consists exactly of functions
constant on a partition. Coordinates lie in the same block when every
algebra element takes the same value there. Normalized separators and
their finite products construct the block indicators inside the algebra.

Divisibility is equivalent to divisibility of every block size. In
characteristic `p`, this is also equivalent to self-orthogonality for
every field endomorphism. The classification needs no finiteness
assumption on the coefficient field, and yields vanishing of arbitrary
unary observables and all higher coordinate moments.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
variable {K ι : Type*} [Field K] [Fintype ι]

/-- Coordinates indistinguishable by every element of the algebra. -/
def coordinateSetoid (A : Subalgebra K (ι → K)) : Setoid ι where
  r i j := ∀ f : A, f.val i = f.val j
  iseqv := ⟨fun _ _ => rfl, fun h f => (h f).symm,
    fun h₁ h₂ f => (h₁ f).trans (h₂ f)⟩

/-- The indicator of the canonical block containing a coordinate. -/
def coordinateBlock (A : Subalgebra K (ι → K)) (i : ι) : ι → K :=
  fun j => if (coordinateSetoid A).r i j then 1 else 0

omit [Fintype ι] in
/-- Distinguishable coordinates have an algebra element with prescribed values one and zero. -/
theorem coordinate_separator (A : Subalgebra K (ι → K)) (i j : ι)
    (hij : ¬ (coordinateSetoid A).r i j) :
    ∃ f : ι → K, f ∈ A ∧ f i = 1 ∧ f j = 0 := by
  change ¬ ∀ f : A, f.val i = f.val j at hij
  push Not at hij
  obtain ⟨f, hf⟩ := hij
  let g : ι → K := (f.val i - f.val j)⁻¹ • (f.val - fun _ => f.val j)
  have hconst : (fun _ : ι => f.val j) ∈ A := A.algebraMap_mem (f.val j)
  refine ⟨g, A.toSubmodule.smul_mem _ (A.sub_mem f.property hconst), ?_, ?_⟩
  · change (f.val i - f.val j)⁻¹ * (f.val i - f.val j) = 1
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hf)
  · change (f.val i - f.val j)⁻¹ * (f.val j - f.val j) = 0
    rw [sub_self, mul_zero]

/-- Multiplying normalized separators produces each exact block indicator. -/
theorem coordinateBlock_mem (A : Subalgebra K (ι → K)) (i : ι) :
    coordinateBlock A i ∈ A := by
  have hex (j : ι) : ∃ f : ι → K, f ∈ A ∧ f i = 1 ∧
      (¬ (coordinateSetoid A).r i j → f j = 0) := by
    by_cases hij : (coordinateSetoid A).r i j
    · exact ⟨1, A.one_mem, rfl, fun h => (h hij).elim⟩
    · obtain ⟨f, hf, hi, hj⟩ := coordinate_separator A i j hij
      exact ⟨f, hf, hi, fun _ => hj⟩
  choose f hf hi hj using hex
  have hprod : (∏ j, f j) ∈ A := A.prod_mem (fun j _ => hf j)
  have heq : (∏ j, f j) = coordinateBlock A i := by
    funext k
    rw [Finset.prod_apply]
    by_cases hik : (coordinateSetoid A).r i k
    · have hk (j : ι) : f j k = 1 := (hik ⟨f j, hf j⟩).symm.trans (hi j)
      simp only [hk, Finset.prod_const_one, coordinateBlock, if_pos hik]
    · rw [Finset.prod_eq_zero (f := fun j => f j k) (Finset.mem_univ k) (hj k hik)]
      exact (if_neg hik).symm
  exact heq ▸ hprod

/-- Projection onto the canonical coordinate partition. -/
def coordinateProjection (A : Subalgebra K (ι → K)) : ι → Quotient (coordinateSetoid A) :=
  Quotient.mk _

local instance coordinateQuotientFintype (A : Subalgebra K (ι → K)) :
    Fintype (Quotient (coordinateSetoid A)) := Fintype.ofFinite _

omit [Fintype ι] in
/-- Every canonical block has a representative coordinate. -/
theorem coordinateProjection_surjective (A : Subalgebra K (ι → K)) :
    Function.Surjective (coordinateProjection A) := Quotient.mk_surjective

/-- Indicators indexed by quotient blocks belong to the original algebra. -/
theorem coordinateFiberIndicator_mem (A : Subalgebra K (ι → K))
    (b : Quotient (coordinateSetoid A)) :
    (fun i => if coordinateProjection A i = b then (1 : K) else 0) ∈ A := by
  obtain ⟨j, rfl⟩ := coordinateProjection_surjective A b
  have heq : (fun i => if coordinateProjection A i = coordinateProjection A j then (1 : K) else 0) =
      coordinateBlock A j := by
    funext i
    have hrel : coordinateProjection A i = coordinateProjection A j ↔
        (coordinateSetoid A).r j i := by
      rw [coordinateProjection, Quotient.eq]
      exact ⟨fun h => (coordinateSetoid A).symm h, fun h => (coordinateSetoid A).symm h⟩
    simp only [coordinateBlock, hrel]
  rw [heq]
  exact coordinateBlock_mem A j

/-- Every finite coordinate algebra is precisely a full partition pullback code. -/
theorem subalgebra_eq_coordinateFiberCode (A : Subalgebra K (ι → K)) :
    A.toSubmodule = fiberCode (coordinateProjection A) := by
  apply le_antisymm
  · intro f hf
    refine ⟨Quotient.lift f (fun i j hij => hij ⟨f, hf⟩), ?_⟩
    rfl
  · rintro f ⟨g, rfl⟩
    have heq : pullbackLinear (coordinateProjection A) g =
        ∑ b, g b • (fun i => if coordinateProjection A i = b then (1 : K) else 0) := by
      funext i
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, pullbackLinear]
    rw [heq]
    exact A.toSubmodule.sum_mem fun b _ =>
      A.toSubmodule.smul_mem _ (coordinateFiberIndicator_mem A b)

#print axioms subalgebra_eq_coordinateFiberCode

/-- The dimension is the number of canonical coordinate blocks. -/
theorem coordinateSubalgebra_finrank (A : Subalgebra K (ι → K)) :
    Module.finrank K A = Nat.card (Quotient (coordinateSetoid A)) := by
  change Module.finrank K A.toSubmodule = _
  rw [subalgebra_eq_coordinateFiberCode,
    fiberCode_finrank _ (coordinateProjection_surjective A), Nat.card_eq_fintype_card]

section Fibers
variable {β : Type*} [Fintype β]

/-- Hamming weight of a pullback is the sum of sizes of its nonzero fibers. -/
theorem weight_pullback_eq_sum_fibers (π : ι → β) (f : β → K) :
    weight (f ∘ π) = ∑ b, if f b ≠ 0 then Nat.card {i // π i = b} else 0 := by
  have h := sum_comp_eq_sum_fiber_card (K := ℚ) π
    (fun b => if f b ≠ 0 then (1 : ℚ) else 0)
  have hc : (weight (f ∘ π) : ℚ) =
      ((∑ b, if f b ≠ 0 then Nat.card {i // π i = b} else 0 : ℕ) : ℚ) := by
    simpa only [weight, Function.comp_apply, Finset.sum_boole,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_one, mul_zero] using h
  exact_mod_cast hc

omit [Fintype β] in
/-- A fiber indicator has weight equal to its fiber size. -/
theorem fiberIndicator_weight (π : ι → β) (b : β) :
    weight (fun i => if π i = b then (1 : K) else 0) = Nat.card {i // π i = b} := by
  simp [weight, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Divisibility of a full pullback code is exactly divisibility of all its fibers. -/
theorem fiberCode_divisible_iff (π : ι → β) (Δ : ℕ) :
    Divisible Δ (fiberCode (K := K) π) ↔ ∀ b, Δ ∣ Nat.card {i // π i = b} := by
  constructor
  · intro h b
    have hm : (fun i => if π i = b then (1 : K) else 0) ∈ fiberCode π :=
      ⟨fun y => if y = b then 1 else 0, rfl⟩
    simpa only [fiberIndicator_weight] using h _ hm
  · intro h c hc
    obtain ⟨f, rfl⟩ := hc
    change Δ ∣ weight (f ∘ π)
    rw [weight_pullback_eq_sum_fibers]
    apply Finset.dvd_sum
    intro b _
    split_ifs
    · exact h b
    · exact dvd_zero Δ

omit [Fintype β] in
/-- Every field twist fixes a fiber indicator, whose self-pairing counts its support. -/
theorem fiberIndicator_pairing (π : ι → β) (b : β) (σ : K →+* K) :
    twistedPair σ (fun i => if π i = b then (1 : K) else 0)
      (fun i => if π i = b then (1 : K) else 0) = (Nat.card {i // π i = b} : K) := by
  have heq (i : ι) :
      (if π i = b then (1 : K) else 0) * σ (if π i = b then 1 else 0) =
        if π i = b then 1 else 0 := by
    split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero]
  simp only [twistedPair, heq, Finset.sum_boole,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Twisted self-orthogonality of a full pullback code is characterized by fiber cardinalities. -/
theorem fiberCode_selfOrthogonal_iff (p : ℕ) [CharP K p]
    (π : ι → β) (σ : K →+* K) :
    SelfOrthogonal σ (fiberCode (K := K) π) ↔ ∀ b, p ∣ Nat.card {i // π i = b} := by
  constructor
  · intro h b
    have hm : (fun i => if π i = b then (1 : K) else 0) ∈ fiberCode π :=
      ⟨fun y => if y = b then 1 else 0, rfl⟩
    have hz := h _ hm _ hm
    rw [fiberIndicator_pairing] at hz
    exact (CharP.cast_eq_zero_iff K p _).mp hz
  · intro h
    exact fiberCode_selfOrthogonal p π h σ

end Fibers

/-- The canonical block sizes completely determine divisibility of a coordinate algebra. -/
theorem coordinateSubalgebra_divisible_iff (A : Subalgebra K (ι → K)) (Δ : ℕ) :
    Divisible Δ A.toSubmodule ↔
      ∀ b, Δ ∣ Nat.card {i // coordinateProjection A i = b} := by
  rw [subalgebra_eq_coordinateFiberCode, fiberCode_divisible_iff]

/-- Self-orthogonality is equivalent to every canonical block size vanishing in the field. -/
theorem coordinateSubalgebra_selfOrthogonal_iff (A : Subalgebra K (ι → K))
    (p : ℕ) [CharP K p] (σ : K →+* K) :
    SelfOrthogonal σ A.toSubmodule ↔
      ∀ b, p ∣ Nat.card {i // coordinateProjection A i = b} := by
  rw [subalgebra_eq_coordinateFiberCode, fiberCode_selfOrthogonal_iff p]

/-- For coordinate algebras, characteristic divisibility suffices for every twist. -/
theorem coordinateSubalgebra_selfOrthogonal_iff_divisible (A : Subalgebra K (ι → K))
    (p : ℕ) [CharP K p] (σ : K →+* K) :
    SelfOrthogonal σ A.toSubmodule ↔ Divisible p A.toSubmodule := by
  rw [coordinateSubalgebra_selfOrthogonal_iff A p σ, coordinateSubalgebra_divisible_iff]

#print axioms coordinateSubalgebra_selfOrthogonal_iff_divisible

/-- Any unary observable of an algebra element remains constant on its canonical blocks. -/
theorem coordinateSubalgebra_comp_mem (A : Subalgebra K (ι → K))
    (f : ι → K) (hf : f ∈ A) (φ : K → K) : (φ ∘ f) ∈ A := by
  change (φ ∘ f) ∈ A.toSubmodule
  rw [subalgebra_eq_coordinateFiberCode]
  have hf' : f ∈ fiberCode (coordinateProjection A) := by
    rw [← subalgebra_eq_coordinateFiberCode]
    exact hf
  obtain ⟨g, rfl⟩ := hf'
  exact ⟨φ ∘ g, rfl⟩

/-- In a characteristic-divisible coordinate algebra every unary observable sums to zero. -/
theorem coordinateSubalgebra_observable_sum_eq_zero (A : Subalgebra K (ι → K))
    (p : ℕ) [CharP K p] (hA : Divisible p A.toSubmodule)
    (f : ι → K) (hf : f ∈ A) (φ : K → K) : ∑ i, φ (f i) = 0 := by
  have hself := (coordinateSubalgebra_selfOrthogonal_iff_divisible A p (RingHom.id K)).mpr hA
  simpa only [twistedPair, RingHom.id_apply, Pi.one_apply, mul_one, Function.comp_apply]
    using hself (φ ∘ f) (coordinateSubalgebra_comp_mem A f hf φ) 1 A.one_mem

/-- All coordinate moments vanish, including the empty product, without a degree bound. -/
theorem coordinateSubalgebra_moments_eq_zero (A : Subalgebra K (ι → K))
    (p : ℕ) [CharP K p] (hA : Divisible p A.toSubmodule)
    {ν : Type*} [Fintype ν] (f : ν → ι → K) (hf : ∀ j, f j ∈ A) :
    ∑ i, ∏ j, f j i = 0 := by
  have hm : (∏ j, f j) ∈ A := A.prod_mem (fun j _ => hf j)
  have h := coordinateSubalgebra_observable_sum_eq_zero A p hA _ hm id
  simpa only [id_eq, Finset.prod_apply] using h

#print axioms coordinateSubalgebra_moments_eq_zero
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
