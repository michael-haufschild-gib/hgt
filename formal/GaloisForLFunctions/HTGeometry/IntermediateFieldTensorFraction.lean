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
      have hmuOne : mu (1 : A ⊗[C] B) = 1 :=
        (intermediateFieldTensorMulMap C E A B).map_one
      rw [hmuOne, div_one]
      simp only [mu, intermediateFieldTensorMulMap_tmul]
      change y * 1 = y
      exact mul_one y
    · refine ⟨(1 : A) ⊗ₜ[C] (⟨y, hy⟩ : B), 1, one_ne_zero, ?_⟩
      have hmuOne : mu (1 : A ⊗[C] B) = 1 :=
        (intermediateFieldTensorMulMap C E A B).map_one
      rw [hmuOne, div_one]
      simp only [mu, intermediateFieldTensorMulMap_tmul]
      change 1 * y = y
      exact one_mul y
  · intro c
    refine ⟨(algebraMap C A c) ⊗ₜ[C] (1 : B), 1, one_ne_zero, ?_⟩
    have hmuOne : mu (1 : A ⊗[C] B) = 1 :=
      (intermediateFieldTensorMulMap C E A B).map_one
    rw [hmuOne, div_one]
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

/-- Tensor multiplication with codomain restricted to the concrete compositum. -/
def intermediateFieldTensorSupMap
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) :
    (A ⊗[C] B) →ₐ[C] ↥(A ⊔ B) :=
  (intermediateFieldTensorMulMap C E A B).codRestrict
    (A ⊔ B).toSubalgebra (by
      intro x
      induction x with
      | zero => exact (A ⊔ B).zero_mem
      | tmul a b =>
          show (a : E) * (b : E) ∈ (A ⊔ B).toSubalgebra
          exact (A ⊔ B).mul_mem
            ((show A ≤ A ⊔ B from le_sup_left) a.property)
            ((show B ≤ A ⊔ B from le_sup_right) b.property)
      | add x y hx hy =>
          show intermediateFieldTensorMulMap C E A B (x + y) ∈
            (A ⊔ B).toSubalgebra
          rw [map_add]
          exact (A ⊔ B).add_mem hx hy)

@[simp] theorem intermediateFieldTensorSupMap_tmul
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (a : A) (b : B) :
    intermediateFieldTensorSupMap C E A B (a ⊗ₜ[C] b) =
      (⟨(a : E) * (b : E), (A ⊔ B).mul_mem
        ((show A ≤ A ⊔ B from le_sup_left) a.property)
        ((show B ≤ A ⊔ B from le_sup_right) b.property)⟩ : ↥(A ⊔ B)) :=
  rfl

/-- Linear disjointness makes the tensor-to-compositum map injective. -/
theorem intermediateFieldTensorSupMap_injective_of_linearDisjoint
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (hAB : A.LinearDisjoint B) :
    Function.Injective (intermediateFieldTensorSupMap C E A B) := by
  intro x y hxy
  apply intermediateFieldTensorMulMap_injective_of_linearDisjoint C E A B hAB
  exact congrArg Subtype.val hxy

/-- A linearly disjoint compositum, equipped with tensor multiplication as its structure map, is
the fraction field of the tensor product. -/
theorem intermediateFieldTensorSup_isFractionRing
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    (A B : IntermediateField C E) (hAB : A.LinearDisjoint B) :
    letI : Algebra (A ⊗[C] B) ↥(A ⊔ B) :=
      (intermediateFieldTensorSupMap C E A B).toRingHom.toAlgebra
    IsFractionRing (A ⊗[C] B) ↥(A ⊔ B) := by
  let T := A ⊗[C] B
  let K := A ⊔ B
  let mu := intermediateFieldTensorSupMap C E A B
  letI : Algebra T K := mu.toRingHom.toAlgebra
  have hmu : Function.Injective mu :=
    intermediateFieldTensorSupMap_injective_of_linearDisjoint C E A B hAB
  letI : FaithfulSMul T K := ⟨by
    intro x y hxy
    apply hmu
    have h1 := hxy (1 : K)
    change mu x * (1 : K) = mu y * (1 : K) at h1
    exact mul_right_cancel₀ one_ne_zero h1⟩
  apply IsFractionRing.of_field T K
  intro z
  obtain ⟨N, D, _hD, hz⟩ :=
    exists_tensor_fraction_of_mem_sup_of_linearDisjoint C E A B hAB z.property
  refine ⟨N, D, ?_⟩
  apply Subtype.ext
  change (z : E) =
    intermediateFieldTensorMulMap C E A B N /
      intermediateFieldTensorMulMap C E A B D
  exact hz.symm

end

end GaloisForLFunctions
