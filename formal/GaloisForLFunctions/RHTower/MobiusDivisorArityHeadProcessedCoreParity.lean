import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadProcessedCoreFibre

/-!
# Processed-core parity orientation of the arity-head charge

Every literal source pair in the arity-head prime increment has a sign fixed
by the parity of its two processed prime cores. The residual-label change
contributes one additional prime and therefore one negative Möbius factor.
Consequently, the only positive terms in the core-changing covariance are
exactly the opposite-parity core pairs.
-/

noncomputable section
open Finset
namespace RHTower

/-- A legal adjacent residual-label source pair has sign determined exactly by
the parity of its processed prime cores. -/
theorem mobiusDivisorArityHead_processedCorePair_product_eq_parity_unsigned
    (M : ℕ) (P : Finset ℕ) (p d e : ℕ)
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (he : e ∈ mobiusDivisorSelectionIndices M)
    (hpD : p ∉ d.primeFactors \ P)
    (hres : e.primeFactors \ P = insert p (d.primeFactors \ P)) :
    mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e =
      -(-1 : ℝ) ^ ((d.primeFactors ∩ P).card + (e.primeFactors ∩ P).card) *
        divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M e := by
  have hsqD : Squarefree d := (mem_filter.mp hd).2
  have hsqE : Squarefree e := (mem_filter.mp he).2
  have hmuD : ((ArithmeticFunction.moebius d : ℤ) : ℝ) =
      (-1 : ℝ) ^ d.primeFactors.card := by
    have h := congrArg (fun z : ℤ => (z : ℝ))
      (Sieve.moebius_eq_neg_one_pow_card_primeFactors hsqD)
    push_cast at h
    exact h
  have hmuE : ((ArithmeticFunction.moebius e : ℤ) : ℝ) =
      (-1 : ℝ) ^ e.primeFactors.card := by
    have h := congrArg (fun z : ℤ => (z : ℝ))
      (Sieve.moebius_eq_neg_one_pow_card_primeFactors hsqE)
    push_cast at h
    exact h
  have hdcard : d.primeFactors.card =
      (d.primeFactors \ P).card + (d.primeFactors ∩ P).card := by
    exact (card_sdiff_add_card_inter d.primeFactors P).symm
  have hecard : e.primeFactors.card =
      (d.primeFactors \ P).card + 1 + (e.primeFactors ∩ P).card := by
    rw [← card_sdiff_add_card_inter e.primeFactors P, hres,
      card_insert_of_notMem hpD]
  have hcards : d.primeFactors.card + e.primeFactors.card =
      2 * (d.primeFactors \ P).card + 1 +
        ((d.primeFactors ∩ P).card + (e.primeFactors ∩ P).card) := by
    omega
  have hdouble : (-1 : ℝ) ^ (2 * (d.primeFactors \ P).card) = 1 := by
    rw [pow_mul]
    norm_num
  have hsign : (-1 : ℝ) ^ d.primeFactors.card *
      (-1 : ℝ) ^ e.primeFactors.card =
      -(-1 : ℝ) ^ ((d.primeFactors ∩ P).card + (e.primeFactors ∩ P).card) := by
    rw [← pow_add, hcards, pow_add, pow_add, hdouble]
    ring
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    mobiusDivisorDilationChannel_eq_moebius_unsigned, hmuD, hmuE]
  calc
    (-1 : ℝ) ^ d.primeFactors.card * divisorUnsignedDilationChannel M d *
        ((-1 : ℝ) ^ e.primeFactors.card * divisorUnsignedDilationChannel M e) =
        ((-1 : ℝ) ^ d.primeFactors.card * (-1 : ℝ) ^ e.primeFactors.card) *
          divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M e := by ring
    _ = _ := by rw [hsign]

end RHTower
