import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadSourcePairs

/-!
# Empty-core orientation of the literal arity-head source charge

At the unprocessed core, every legal adjacent source pair is a prime shift of
a squarefree divisor.  Möbius multiplicativity then fixes its sign: the pair
is the negative product of two nonnegative unsigned dilation channels.  This
gives a genuine first-insertion dissipation law, while making no assertion for
nonempty processed cores, where the residual-label pairing changes.
-/

noncomputable section
open Finset
namespace RHTower

/-- Every legal empty-core prime-shift source pair has fixed negative
orientation in unsigned-channel coordinates. -/
theorem mobiusDivisorArityHead_primeShift_product_eq_neg_unsigned
    (M p d : ℕ) (hp : p.Prime)
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (hpD : p ∉ d.primeFactors) :
    mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d) =
      -divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M (p * d) := by
  have hds : Squarefree d := (mem_filter.mp hd).2
  have hd0 : d ≠ 0 := by
    have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1
    omega
  have hnotdvd : ¬p ∣ d := by
    intro hpd
    exact hpD (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩)
  have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr hnotdvd
  have hmu : (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hds
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  calc
    _ = -((((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M (p * d)) := by ring
    _ = _ := by rw [hmu]; ring

/-- The completed arity-head charge cannot increase at the first processed
prime.  This is an exact finite-cutoff theorem, with no asymptotic premise. -/
theorem mobiusDivisorArityHeadCharge_empty_nonpos (M : ℕ) {p : ℕ}
    (hp : p.Prime) :
    mobiusDivisorArityHeadCharge M ∅ p ≤ 0 := by
  rw [mobiusDivisorArityHeadCharge_empty_eq_prime_shift M hp]
  apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
  apply sum_nonpos
  intro d hd
  by_cases hlegal : p ∉ d.primeFactors ∧ p * d ∈ mobiusDivisorSelectionIndices M
  · rw [if_pos hlegal]
    have hw : 0 ≤ ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) := by
      split_ifs <;> positivity
    have hprod := mobiusDivisorArityHead_primeShift_product_eq_neg_unsigned M p d hp hd hlegal.1
    calc
      ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d) =
          ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
            (mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d)) := by ring
      _ = ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
            (-divisorUnsignedDilationChannel M d * divisorUnsignedDilationChannel M (p * d)) := by
              rw [hprod]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (divisorUnsignedDilationChannel_nonneg M d))
          (divisorUnsignedDilationChannel_nonneg M (p * d)))
  · rw [if_neg hlegal]

end RHTower
