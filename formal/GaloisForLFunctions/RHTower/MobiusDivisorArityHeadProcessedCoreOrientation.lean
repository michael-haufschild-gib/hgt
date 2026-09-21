import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreParity

/-!
# Positive orientation of processed-core coordinates

After multiplying a processed-core/residual-label coordinate by the parity of
its two prime sets, it is exactly an unsigned literal source channel. Thus
each coordinate is positive in this canonical orientation; only the
difference between the even and odd processed-core masses can retain a sign.
-/

noncomputable section
open Finset
namespace RHTower

/-- The canonical core-and-residual parity orientation turns every
processed-core coordinate into its unsigned literal source channel. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_oriented_eq_unsigned
    (M : ℕ) (P A R : Finset ℕ) :
    (-1 : ℝ) ^ (A.card + R.card) *
        mobiusDivisorSelectionProcessedCoreFibre M P A R =
      if (∏ q ∈ A ∪ R, q) ∈ mobiusDivisorSelectionIndices M ∧
          (∏ q ∈ A ∪ R, q).primeFactors \ P = R ∧
          (∏ q ∈ A ∪ R, q).primeFactors ∩ P = A then
        divisorUnsignedDilationChannel M (∏ q ∈ A ∪ R, q)
      else 0 := by
  let n := ∏ q ∈ A ∪ R, q
  rw [mobiusDivisorSelectionProcessedCoreFibre_eq_singleton]
  by_cases hn : n ∈ mobiusDivisorSelectionIndices M ∧
      n.primeFactors \ P = R ∧ n.primeFactors ∩ P = A
  · have hn' : (∏ q ∈ A ∪ R, q) ∈ mobiusDivisorSelectionIndices M ∧
        (∏ q ∈ A ∪ R, q).primeFactors \ P = R ∧
          (∏ q ∈ A ∪ R, q).primeFactors ∩ P = A := by
      simpa only [n] using hn
    rw [if_pos hn, if_pos hn']
    have hsq : Squarefree n := (mem_filter.mp hn.1).2
    have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ) =
        (-1 : ℝ) ^ n.primeFactors.card := by
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (Sieve.moebius_eq_neg_one_pow_card_primeFactors hsq)
      push_cast at h
      exact h
    have hcard : n.primeFactors.card = A.card + R.card := by
      calc
        n.primeFactors.card =
            (n.primeFactors \ P).card + (n.primeFactors ∩ P).card :=
          (card_sdiff_add_card_inter n.primeFactors P).symm
        _ = R.card + A.card := by rw [hn.2.1, hn.2.2]
        _ = A.card + R.card := by omega
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned, hmu, hcard]
    have hdouble : (-1 : ℝ) ^ ((A.card + R.card) + (A.card + R.card)) = 1 := by
      rw [show (A.card + R.card) + (A.card + R.card) =
          2 * (A.card + R.card) by omega, pow_mul]
      norm_num
    rw [← mul_assoc, ← pow_add, hdouble, one_mul]
  · have hn' : ¬((∏ q ∈ A ∪ R, q) ∈ mobiusDivisorSelectionIndices M ∧
        (∏ q ∈ A ∪ R, q).primeFactors \ P = R ∧
          (∏ q ∈ A ∪ R, q).primeFactors ∩ P = A) := by
      simpa only [n] using hn
    rw [if_neg hn, if_neg hn']
    ring

/-- Every processed-core coordinate is nonnegative after its canonical
core-and-residual parity orientation. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_oriented_nonneg
    (M : ℕ) (P A R : Finset ℕ) :
    0 ≤ (-1 : ℝ) ^ (A.card + R.card) *
      mobiusDivisorSelectionProcessedCoreFibre M P A R := by
  rw [mobiusDivisorSelectionProcessedCoreFibre_oriented_eq_unsigned]
  split_ifs
  exact divisorUnsignedDilationChannel_nonneg _ _
  exact le_rfl

end RHTower
