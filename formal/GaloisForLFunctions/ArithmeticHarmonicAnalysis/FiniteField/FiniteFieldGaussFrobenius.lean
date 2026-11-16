import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldTraceCharacters
import Mathlib.NumberTheory.GaussSum

/-!
# Frobenius invariance of trace Gauss sums

Relative Frobenius permutes the extension field and fixes the trace
additive character. Reindexing therefore leaves the Gauss sum unchanged
when the multiplicative character is raised to any base-cardinality power.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L R : Type*} [Field K] [Field L] [CommRing R]
    [Fintype K] [Fintype L] [Algebra K L]

/-- Raising multiplicative characters to a relative Frobenius power is injective. -/
theorem finiteField_mulChar_frobenius_injective (e : ℕ) :
    Function.Injective (fun χ : MulChar L R => χ ^ (Fintype.card K ^ e)) := by
  induction e with
  | zero =>
    intro χ φ h
    simpa only [pow_zero, pow_one] using h
  | succ e ih =>
    intro χ φ h
    change χ ^ (Fintype.card K ^ (e + 1)) = φ ^ (Fintype.card K ^ (e + 1)) at h
    rw [pow_succ, pow_mul, pow_mul] at h
    apply ih
    apply MulChar.ext'
    intro x
    obtain ⟨y, rfl⟩ := (FiniteField.frobeniusAlgEquivOfAlgebraic K L).surjective x
    change (χ ^ (Fintype.card K ^ e)) (y ^ Fintype.card K) =
      (φ ^ (Fintype.card K ^ e)) (y ^ Fintype.card K)
    rw [map_pow, map_pow]
    have hy := DFunLike.congr_fun h y
    simpa only [MulChar.pow_apply' _ (Nat.ne_of_gt Fintype.card_pos)] using hy

private theorem trace_gauss_frobenius_step (χ : MulChar L R) (ψ : AddChar K R) :
    gaussSum (χ ^ Fintype.card K) (finiteFieldTraceCharacter (L := L) ψ) =
      gaussSum χ (finiteFieldTraceCharacter (L := L) ψ) := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  unfold gaussSum
  apply Fintype.sum_bijective σ σ.bijective
  intro x
  rw [finiteFieldTraceCharacter_algEquiv]
  change (χ ^ Fintype.card K) x * finiteFieldTraceCharacter ψ x =
    χ (x ^ Fintype.card K) * finiteFieldTraceCharacter ψ x
  rw [MulChar.pow_apply' (χ := χ) (Nat.ne_of_gt Fintype.card_pos), map_pow]

/-- Every relative Frobenius power leaves the trace Gauss sum unchanged when applied to its multiplicative character. -/
theorem finiteField_gaussSum_frobenius (χ : MulChar L R) (ψ : AddChar K R) (e : ℕ) :
    gaussSum (χ ^ (Fintype.card K ^ e)) (finiteFieldTraceCharacter (L := L) ψ) =
      gaussSum χ (finiteFieldTraceCharacter (L := L) ψ) := by
  induction e with
  | zero => rw [pow_zero, pow_one]
  | succ e ih => rw [pow_succ, pow_mul, trace_gauss_frobenius_step, ih]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
