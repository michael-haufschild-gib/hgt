import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Fraction presentation of a compositum

If two intermediate fields inside a common overfield have injective tensor multiplication, every
element of their compositum is a quotient of two tensors.  The statement is elementary, but this
explicit numerator-denominator interface is the bridge between `IntermediateField.sup` and the
finite-type product-specialization machinery.
-/

open scoped TensorProduct

namespace GaloisForLFunctions

noncomputable section

/-- Multiplication of the two concrete intermediate-field factors inside their common overfield. -/
def intermediateFieldTensorMulMap
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) : (A ⊗[C] B) →ₐ[C] E :=
  A.toSubalgebra.mulMap B.toSubalgebra

@[simp] theorem intermediateFieldTensorMulMap_tmul
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (a : A) (b : B) :
    intermediateFieldTensorMulMap C E A B (a ⊗ₜ[C] b) =
      (a : E) * (b : E) :=
  rfl

/-- Linear disjointness is exactly injectivity of concrete tensor multiplication. -/
theorem intermediateFieldTensorMulMap_injective_of_linearDisjoint
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (hAB : A.LinearDisjoint B) :
    Function.Injective (intermediateFieldTensorMulMap C E A B) := by
  rw [IntermediateField.linearDisjoint_iff',
    Subalgebra.linearDisjoint_iff_injective] at hAB
  simpa [intermediateFieldTensorMulMap] using hAB

/-- Every element of a linearly embedded compositum is a quotient of a tensor numerator by a
nonzero tensor denominator.  No finite-generation hypothesis is imposed on either field. -/
theorem exists_tensor_fraction_of_mem_sup
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E)
    (hmul : Function.Injective (intermediateFieldTensorMulMap C E A B))
    {x : E} (hx : x ∈ A ⊔ B) :
    ∃ N D : A ⊗[C] B, D ≠ 0 ∧
      intermediateFieldTensorMulMap C E A B N /
          intermediateFieldTensorMulMap C E A B D = x := by
  classical
  let mu := intermediateFieldTensorMulMap C E A B
  rw [IntermediateField.sup_def] at hx
  apply IntermediateField.adjoin_induction C
    (s := ((A : Set E) ∪ (B : Set E)))
    (p := fun y _ => ∃ N D : A ⊗[C] B, D ≠ 0 ∧ mu N / mu D = y)
  · rintro y (hy | hy)
    · refine ⟨(⟨y, hy⟩ : A) ⊗ₜ[C] (1 : B), 1, one_ne_zero, ?_⟩
      rw [show mu 1 = 1 from map_one mu, div_one]
      simp only [mu, intermediateFieldTensorMulMap_tmul,
        Subtype.coe_mk, Subtype.coe_one, mul_one]
    · refine ⟨(1 : A) ⊗ₜ[C] (⟨y, hy⟩ : B), 1, one_ne_zero, ?_⟩
      rw [show mu 1 = 1 from map_one mu, div_one]
      simp only [mu, intermediateFieldTensorMulMap_tmul,
        Subtype.coe_mk, Subtype.coe_one, one_mul]
  · intro c
    refine ⟨algebraMap C (A ⊗[C] B) c, 1, one_ne_zero, ?_⟩
    simp [mu]
  · intro y z hy hz hyRep hzRep
    obtain ⟨Ny, Dy, hDy, hyEq⟩ := hyRep
    obtain ⟨Nz, Dz, hDz, hzEq⟩ := hzRep
    have hmuDy : mu Dy ≠ 0 := by
      simpa only [map_zero] using hmul.ne hDy
    have hmuDz : mu Dz ≠ 0 := by
      simpa only [map_zero] using hmul.ne hDz
    have hden : Dy * Dz ≠ 0 := by
      intro hzero
      apply mul_ne_zero hmuDy hmuDz
      simpa only [map_mul, map_zero] using congrArg mu hzero
    refine ⟨Ny * Dz + Nz * Dy, Dy * Dz, hden, ?_⟩
    simp only [map_add, map_mul]
    calc
      (mu Ny * mu Dz + mu Nz * mu Dy) / (mu Dy * mu Dz) =
          mu Ny / mu Dy + mu Nz / mu Dz := by
        field_simp [hmuDy, hmuDz]
      _ = y + z := by rw [hyEq, hzEq]
  · intro y hy hyRep
    by_cases hy0 : y = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      simp [hy0]
    · obtain ⟨N, D, _hD, hEq⟩ := hyRep
      have hmuN : mu N ≠ 0 := by
        intro hzero
        apply hy0
        rw [← hEq, hzero, zero_div]
      have hN : N ≠ 0 := by
        intro hzero
        apply hmuN
        rw [hzero, map_zero]
      refine ⟨D, N, hN, ?_⟩
      simpa only [inv_div] using congrArg Inv.inv hEq
  · intro y z hy hz hyRep hzRep
    obtain ⟨Ny, Dy, hDy, hyEq⟩ := hyRep
    obtain ⟨Nz, Dz, hDz, hzEq⟩ := hzRep
    have hmuDy : mu Dy ≠ 0 := by
      simpa only [map_zero] using hmul.ne hDy
    have hmuDz : mu Dz ≠ 0 := by
      simpa only [map_zero] using hmul.ne hDz
    have hden : Dy * Dz ≠ 0 := by
      intro hzero
      apply mul_ne_zero hmuDy hmuDz
      simpa only [map_mul, map_zero] using congrArg mu hzero
    refine ⟨Ny * Nz, Dy * Dz, hden, ?_⟩
    simp only [map_mul]
    calc
      (mu Ny * mu Nz) / (mu Dy * mu Dz) =
          (mu Ny / mu Dy) * (mu Nz / mu Dz) := by
        field_simp [hmuDy, hmuDz]
      _ = y * z := by rw [hyEq, hzEq]
  exact hx

/-- Linear disjointness supplies the injective multiplication map needed by the fraction
presentation theorem. -/
theorem exists_tensor_fraction_of_mem_sup_of_linearDisjoint
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (hAB : A.LinearDisjoint B)
    {x : E} (hx : x ∈ A ⊔ B) :
    ∃ N D : A ⊗[C] B, D ≠ 0 ∧
      intermediateFieldTensorMulMap C E A B N /
          intermediateFieldTensorMulMap C E A B D = x := by
  apply exists_tensor_fraction_of_mem_sup C E A B
  · exact intermediateFieldTensorMulMap_injective_of_linearDisjoint
      C E A B hAB
  · exact hx

end

end GaloisForLFunctions
