import GaloisForLFunctions.RHTower.MobiusDivisorLateBlockBooleanTransport
import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeExtension
import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius
import GaloisForLFunctions.RHTower.UniformPrimeSubsetBooleanInversion
import GaloisForLFunctions.RHTower.UniformPrimeSubsetCompression

/-!
# All-order original-core sign law for Möbius divisor energy

At the unprocessed core, every finite alternating Boolean energy jet has the
Möbius-forced nonnegative sign.  The finite inversion theorem exposes the
exact reason: an order-`A` jet sees only source pairs with symmetric difference
`A`, and both coefficients have the same normalized parity after the outer
alternation is restored.

This does not assert the sign after a changing processed core.  The late-block
transport law identifies that separate term exactly.
-/

noncomputable section
open Finset
namespace RHTower

private theorem mobiusDivisorSelectionLabels (M : ℕ) :
    ∀ d ∈ mobiusDivisorSelectionIndices M,
      d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
  intro d hd p hp
  obtain ⟨hd, _⟩ := mem_filter.mp hd
  obtain ⟨hd1, hdM⟩ := mem_Icc.mp hd
  have hpd := Nat.le_of_mem_primeFactors hp
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hp).1⟩

private theorem mobiusDivisorDilationChannel_initial_parity_nonneg
    (M d : ℕ) (hd : d ∈ mobiusDivisorSelectionIndices M) :
    0 ≤ (-1 : ℝ) ^ d.primeFactors.card * mobiusDivisorDilationChannel M d := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]
  have hmu := congrArg (fun z : ℤ => (z : ℝ))
    (Sieve.moebius_eq_neg_one_pow_card_primeFactors (mem_filter.mp hd).2)
  push_cast at hmu
  rw [hmu]
  have hsquare : ((-1 : ℝ) ^ d.primeFactors.card) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul, show d.primeFactors.card * 2 = 2 * d.primeFactors.card by omega, pow_mul]
    norm_num
  rw [show (-1 : ℝ) ^ d.primeFactors.card *
      ((-1 : ℝ) ^ d.primeFactors.card * divisorUnsignedDilationChannel M d) =
      ((-1 : ℝ) ^ d.primeFactors.card) ^ (2 : ℕ) * divisorUnsignedDilationChannel M d by ring,
    hsquare, one_mul]
  exact divisorUnsignedDilationChannel_nonneg M d

/-- Every original-core Boolean energy jet has its forced Möbius sign. -/
theorem mobiusDivisorEnergyBooleanAlternating_empty_nonneg
    (M : ℕ) (A : Finset ℕ) :
    0 ≤ mobiusDivisorEnergyBooleanAlternating M ∅ A := by
  unfold mobiusDivisorEnergyBooleanAlternating mobiusDivisorBooleanAlternating
  simp only [empty_union]
  exact subsetLabelEnergy_booleanAlternating_nonneg_of_parity
    (mobiusDivisorSelectionPrimes M) (mobiusDivisorSelectionIndices M)
    Nat.primeFactors (mobiusDivisorDilationChannel M)
    (mobiusDivisorSelectionLabels M)
    (fun d hd => mobiusDivisorDilationChannel_initial_parity_nonneg M d hd) A

/-- In forward-difference normalization, an order-`A` original-core jet has
sign `(-1)^|A|`. -/
theorem mobiusDivisorEnergyBooleanDifference_empty_oriented_nonneg
    (M : ℕ) (A : Finset ℕ) :
    0 ≤ (-1 : ℝ) ^ A.card * mobiusDivisorEnergyBooleanDifference M ∅ A := by
  unfold mobiusDivisorEnergyBooleanDifference
  have hsquare : (-1 : ℝ) ^ A.card * (-1 : ℝ) ^ A.card = 1 := by
    rw [← pow_add, show A.card + A.card = 2 * A.card by omega, pow_mul]
    norm_num
  rw [← mul_assoc, hsquare, one_mul]
  exact mobiusDivisorEnergyBooleanAlternating_empty_nonneg M A

/-- Before the late-block residual head crosses negative, full fibre parity
orientation survives and therefore controls every finite future Boolean grade. -/
theorem mobiusDivisorEnergyBooleanAlternating_late_nonneg_of_head
    (M : ℕ) (L A : Finset ℕ)
    (hL : ∀ p ∈ L, p.Prime ∧ p < M ∧ M ≤ 2 * p)
    (hhead : 0 ≤ mobiusDivisorSelectionFibre M L ∅) :
    0 ≤ mobiusDivisorEnergyBooleanAlternating M L A := by
  unfold mobiusDivisorEnergyBooleanAlternating mobiusDivisorBooleanAlternating
  exact subsetLabelEnergy_booleanAlternating_union_nonneg_of_fibreParity
    (mobiusDivisorSelectionPrimes M) (mobiusDivisorSelectionIndices M)
    Nat.primeFactors (mobiusDivisorDilationChannel M)
    (mobiusDivisorSelectionLabels M) L A (fun R hR => by
      by_cases hR : R = ∅
      · subst R
        simp only [card_empty, pow_zero, one_mul]
        unfold mobiusDivisorSelectionFibre at hhead
        exact hhead
      · exact mobiusDivisorSelectionFibre_late_parity_nonneg M L hL R hR)

end RHTower
