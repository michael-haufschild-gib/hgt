import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldGaussFrobenius
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Data.Complex.Basic

/-!
# Jacobi sums along a Frobenius character progression

The product of `χ` and `χ^(q^e-1)` is `χ^(q^e)`. Frobenius preserves
its Gauss sum and nontriviality. The Jacobi--Gauss identity therefore
cancels the first Gauss factor exactly, including when the second
character is trivial.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]

/-- A Frobenius-related Jacobi sum equals the Gauss sum of its second character. -/
theorem finiteField_jacobiSum_frobenius (χ : MulChar L ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (e : ℕ) :
    jacobiSum χ (χ ^ (Fintype.card K ^ e - 1)) =
      gaussSum (χ ^ (Fintype.card K ^ e - 1)) (finiteFieldTraceCharacter (L := L) ψ) := by
  have hn : 0 < Fintype.card K ^ e := pow_pos Fintype.card_pos e
  have hprod : χ * χ ^ (Fintype.card K ^ e - 1) = χ ^ (Fintype.card K ^ e) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hnon : χ ^ (Fintype.card K ^ e) ≠ 1 := by
    intro h
    apply hχ
    apply finiteField_mulChar_frobenius_injective (K := K) e
    simpa only [one_pow] using h
  have hprodnon : χ * χ ^ (Fintype.card K ^ e - 1) ≠ 1 := by rwa [hprod]
  have hc : (Fintype.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt Fintype.card_pos
  have hprim := finiteFieldTraceCharacter_primitive (L := L) ψ hψ
  rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hc hprodnon hprim,
    hprod, finiteField_gaussSum_frobenius]
  apply (div_eq_iff (gaussSum_ne_zero_of_nontrivial hc hχ hprim)).mpr
  exact mul_comm _ _

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
