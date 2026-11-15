import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Codes pulled back through divisible fibers

A map whose fibers have cardinality divisible by the characteristic produces
a divisible code by pulling back arbitrary functions. Its coordinate pairings
vanish for every field endomorphism, including the identity. This supplies
concrete applications of divisible-code orthogonality without requiring a
divisibility assumption on an unspecified code.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

variable {K ι β : Type*} [Field K] [Fintype ι] [Fintype β]

/-- Pullback of functions as a linear map. -/
def pullbackLinear (π : ι → β) : (β → K) →ₗ[K] (ι → K) where
  toFun f := f ∘ π
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Words constant on the fibers of a map. -/
def fiberCode (π : ι → β) : Submodule K (ι → K) := (pullbackLinear (K := K) π).range

/-- A surjective projection retains one independent coordinate per base point. -/
theorem fiberCode_finrank (π : ι → β) (hπ : Function.Surjective π) :
    Module.finrank K (fiberCode (K := K) π) = Fintype.card β :=
  (LinearMap.finrank_range_of_inj (f := pullbackLinear (K := K) π)
    hπ.injective_comp_right).trans (Module.finrank_pi K)

/-- Grouping a sum by its indexing map, expressed with intrinsic fiber cardinalities. -/
theorem sum_comp_eq_sum_fiber_card (π : ι → β) (f : β → K) :
    ∑ i, f (π i) = ∑ b, (Nat.card {i // π i = b} : K) * f b := by
  classical
  symm
  calc
    _ = ∑ b, ∑ i ∈ Finset.univ.filter (fun i => π i = b), f (π i) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ i ∈ Finset.univ.filter (fun i => π i = b), f (π i)) =
          ∑ _i ∈ Finset.univ.filter (fun i => π i = b), f b from
        Finset.sum_congr rfl (fun i hi => congrArg f (Finset.mem_filter.mp hi).2)]
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_const,
        nsmul_eq_mul]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

/-- Every unary observable on a pulled-back word sums to zero across divisible fibers. -/
theorem sum_comp_eq_zero (p : ℕ) [CharP K p] (π : ι → β)
    (hπ : ∀ b, p ∣ Nat.card {i // π i = b}) (f : β → K) :
    ∑ i, f (π i) = 0 := by
  rw [sum_comp_eq_sum_fiber_card]
  exact Finset.sum_eq_zero fun b _ => by
    rw [(CharP.cast_eq_zero_iff K p _).mpr (hπ b), zero_mul]

omit [Fintype ι] [Fintype β] in
/-- The constant word is always a pullback. -/
theorem one_mem_fiberCode (π : ι → β) : (fun _ => (1 : K)) ∈ fiberCode π :=
  ⟨fun _ => 1, rfl⟩

/-- Divisible fibers give a divisible code, for every function on the base. -/
theorem fiberCode_divisible (p : ℕ) [CharP K p] (π : ι → β)
    (hπ : ∀ b, p ∣ Nat.card {i // π i = b}) : Divisible p (fiberCode (K := K) π) := by
  rintro c ⟨f, rfl⟩
  apply (CharP.cast_eq_zero_iff K p _).mp
  have h := sum_comp_eq_zero p π hπ (fun b => if f b ≠ 0 then (1 : K) else 0)
  simpa only [Finset.sum_boole, weight, pullbackLinear, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply] using h

/-- The full pullback code is orthogonal for every twist, even the identity. -/
theorem fiberCode_selfOrthogonal (p : ℕ) [CharP K p] (π : ι → β)
    (hπ : ∀ b, p ∣ Nat.card {i // π i = b}) (σ : K →+* K) :
    SelfOrthogonal σ (fiberCode (K := K) π) := by
  rintro c ⟨f, rfl⟩ d ⟨g, rfl⟩
  exact sum_comp_eq_zero p π hπ (fun b => f b * σ (g b))

omit [Fintype β] in
/-- Every nonempty fiber of an additive map has the same cardinality as its kernel. -/
theorem additive_fiber_card_dvd [AddGroup ι] [AddGroup β]
    (p : ℕ) (π : ι →+ β) (hπ : p ∣ Nat.card π.ker) (b : β) :
    p ∣ Nat.card {i // π i = b} := by
  by_cases hb : ∃ i, π i = b
  · obtain ⟨i, rfl⟩ := hb
    have he := Nat.card_congr (π.fiberEquivKer i)
    simpa only [Set.preimage, Set.mem_singleton_iff] using he ▸ hπ
  · haveI : IsEmpty {i // π i = b} := ⟨fun i => hb ⟨i.val, i.property⟩⟩
    simp

/-- Repeating each coordinate exactly `p` times gives an unconditional divisible code. -/
theorem primeReplication_divisible (p : ℕ) [CharP K p] :
    Divisible p (fiberCode (K := K) (Prod.fst : β × Fin p → β)) := by
  apply fiberCode_divisible p
  intro b
  let e : {i : β × Fin p // i.1 = b} ≃ Fin p :=
    { toFun := fun i => i.val.2
      invFun := fun j => ⟨(b, j), rfl⟩
      left_inv := fun i => Subtype.ext (Prod.ext i.property.symm rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fin]

/-- Prime-fold replication is orthogonal for every field endomorphism. -/
theorem primeReplication_selfOrthogonal (p : ℕ) [CharP K p] (σ : K →+* K) :
    SelfOrthogonal σ (fiberCode (K := K) (Prod.fst : β × Fin p → β)) := by
  apply fiberCode_selfOrthogonal p
  intro b
  let e : {i : β × Fin p // i.1 = b} ≃ Fin p :=
    { toFun := fun i => i.val.2
      invFun := fun j => ⟨(b, j), rfl⟩
      left_inv := fun i => Subtype.ext (Prod.ext i.property.symm rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fin]

#print axioms fiberCode_divisible
#print axioms primeReplication_selfOrthogonal

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
