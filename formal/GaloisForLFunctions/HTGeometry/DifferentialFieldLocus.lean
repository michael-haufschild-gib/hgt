import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Intermediate-field loci of a derivation that does not kill the base

Two constructions are needed to propagate a differential identity from a generating set to the
whole field when the ambient derivation moves the base field.

`twistedLeibnizKernel` is the vanishing locus of an additive map obeying a Leibniz rule twisted by
a ring homomorphism.  It covers a commutator of derivations, the failure of an algebra
homomorphism to be differential, and the failure of a coordinate derivation to be intertwined.

`derivStableField` is the intermediate field of elements of a given intermediate field whose
derivative stays inside it.  Together with `IntermediateField.adjoin_le_iff` these reduce every
such statement to a check on generators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C F E : Type*} [Field C] [Field F] [Field E] [Algebra C F]

/-- The vanishing locus of an additive map obeying a Leibniz rule twisted by a ring
homomorphism. -/
def twistedLeibnizKernel (W : F → E) (σ : F →+* E)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hleib : ∀ x y, W (x * y) = σ x * W y + σ y * W x)
    (hbase : ∀ c : C, W (algebraMap C F c) = 0) : IntermediateField C F where
  carrier := {x | W x = 0}
  zero_mem' := by
    have h := hadd 0 0
    simp only [add_zero] at h
    simpa using h.symm
  one_mem' := by simpa using hbase (1 : C)
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [hadd, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [hleib, hx, hy, mul_zero, mul_zero, add_zero]
  algebraMap_mem' := hbase
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases eq_or_ne x 0 with rfl | hx0
    · have h := hadd 0 0
      simp only [add_zero] at h
      simpa using h.symm
    · have hone : W (1 : F) = 0 := by simpa using hbase (1 : C)
      have h := hleib x x⁻¹
      rw [mul_inv_cancel₀ hx0, hone, hx, mul_zero, add_zero] at h
      have hσ : σ x ≠ 0 := by
        simpa using fun hc => hx0 (σ.injective (by simpa using hc))
      exact (mul_eq_zero.1 h.symm).resolve_left hσ

@[simp]
theorem mem_twistedLeibnizKernel_iff {W : F → E} {σ : F →+* E}
    {hadd : ∀ x y, W (x + y) = W x + W y}
    {hleib : ∀ x y, W (x * y) = σ x * W y + σ y * W x}
    {hbase : ∀ c : C, W (algebraMap C F c) = 0} {x : F} :
    x ∈ twistedLeibnizKernel W σ hadd hleib hbase ↔ W x = 0 := Iff.rfl

/-- Elements of an intermediate field whose derivative stays inside it, for a derivation that need
not kill the base field. -/
def derivStableField [Differential F] (L : IntermediateField C F)
    (hbase : ∀ c : C, (algebraMap C F c)′ ∈ L) : IntermediateField C F where
  carrier := {y | y ∈ L ∧ y′ ∈ L}
  zero_mem' := ⟨zero_mem L, by rw [map_zero]; exact zero_mem L⟩
  one_mem' := ⟨one_mem L, by rw [Derivation.map_one_eq_zero]; exact zero_mem L⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx.1 hy.2) (mul_mem hy.1 hx.2)
  algebraMap_mem' := fun c => ⟨algebraMap_mem L c, hbase c⟩
  inv_mem' := by
    intro x hx
    refine ⟨inv_mem hx.1, ?_⟩
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem (inv_mem hx.1) 2)) hx.2

theorem mem_derivStableField_iff [Differential F] {L : IntermediateField C F}
    {hbase : ∀ c : C, (algebraMap C F c)′ ∈ L} {y : F} :
    y ∈ derivStableField L hbase ↔ y ∈ L ∧ y′ ∈ L := Iff.rfl

/-- An adjoined set whose members and derivatives lie in an intermediate field generates a
derivation-stable subfield of it. -/
theorem adjoin_le_derivStableField [Differential F] {S : Set F} {L : IntermediateField C F}
    {hbase : ∀ c : C, (algebraMap C F c)′ ∈ L} (h : ∀ x ∈ S, x ∈ L ∧ x′ ∈ L) :
    IntermediateField.adjoin C S ≤ derivStableField L hbase := by
  rw [IntermediateField.adjoin_le_iff]
  exact fun x hx => h x hx

end

end GaloisForLFunctions.HTGeometry
