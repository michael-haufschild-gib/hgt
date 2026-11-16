import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialSubfields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalBaseDegree

/-!
# Degrees of polynomial-coordinate Kummer covers

For an embedding whose rational coordinate pulls back to a polynomial,
the polynomial degree times the target radical degree equals the cover
degree times the source radical degree. Equal radical degrees cancel.
The statement uses the actual image and coordinate intermediate fields.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K]

/-- Comparing coordinate towers gives the exact degree identity for a polynomial Kummer cover. -/
theorem kummerBranchField_polynomial_cover_degree_mul
    (c₁ c₂ : Kˣ) (b₁ R₁ n₁ b₂ R₂ n₂ : ℕ)
    (f : KummerBranchField c₁ b₁ R₁ n₁ →ₐ[K] KummerBranchField c₂ b₂ R₂ n₂)
    (P : K[X])
    (hP : f (algebraMap K[X] _ X) = aeval (algebraMap K[X] _ X) P) :
    (n₁ + 1) * Module.finrank f.fieldRange (KummerBranchField c₂ b₂ R₂ n₂) =
      P.natDegree * (n₂ + 1) := by
  let L := KummerBranchField c₁ b₁ R₁ n₁
  let H := KummerBranchField c₂ b₂ R₂ n₂
  let x := algebraMap K[X] H X
  let A := K⟮aeval x P⟯
  let B := K⟮x⟯
  let J := f.fieldRange
  have hAB : A.relfinrank B = P.natDegree :=
    polynomialCoordinate_relfinrank (kummerBranchField_coordinate_transcendental c₂ b₂ R₂ n₂) P
  have hB : Module.finrank B H = n₂ + 1 :=
    kummerBranchField_coordinate_finrank c₂ b₂ R₂ n₂
  have hAJ : A.relfinrank J = n₁ + 1 := by
    have h := IntermediateField.relfinrank_map_map
      K⟮algebraMap K[X] L X⟯ (⊤ : IntermediateField K L) f
    rw [IntermediateField.adjoin_map, Set.image_singleton, hP,
      ← AlgHom.fieldRange_eq_map, IntermediateField.relfinrank_top_right,
      kummerBranchField_coordinate_finrank] at h
    exact h
  have hmem (g : K[X]) : aeval x g ∈ B := by
    induction g using Polynomial.induction_on' with
    | add g h hg hh =>
      rw [map_add]
      exact B.add_mem hg hh
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X]
      exact B.mul_mem (B.algebraMap_mem a)
        (pow_mem (IntermediateField.mem_adjoin_simple_self K x) i)
  have hleAB : A ≤ B := IntermediateField.adjoin_simple_le_iff.mpr (hmem P)
  have hleAJ : A ≤ J :=
    IntermediateField.adjoin_simple_le_iff.mpr ⟨algebraMap K[X] L X, hP⟩
  have h₁ := IntermediateField.relfinrank_mul_finrank_top hleAB
  have h₂ := IntermediateField.relfinrank_mul_finrank_top hleAJ
  rw [hAB, hB] at h₁
  rw [hAJ] at h₂
  exact h₂.trans h₁.symm

/-- Equal radical degrees cancel, leaving exactly the polynomial coordinate degree. -/
theorem kummerBranchField_polynomial_cover_finrank
    (c₁ c₂ : Kˣ) (b₁ R₁ b₂ R₂ n : ℕ)
    (f : KummerBranchField c₁ b₁ R₁ n →ₐ[K] KummerBranchField c₂ b₂ R₂ n)
    (P : K[X])
    (hP : f (algebraMap K[X] _ X) = aeval (algebraMap K[X] _ X) P) :
    Module.finrank f.fieldRange (KummerBranchField c₂ b₂ R₂ n) = P.natDegree := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  exact (kummerBranchField_polynomial_cover_degree_mul c₁ c₂ b₁ R₁ n b₂ R₂ n f P hP).trans
    (Nat.mul_comm P.natDegree (n + 1))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
