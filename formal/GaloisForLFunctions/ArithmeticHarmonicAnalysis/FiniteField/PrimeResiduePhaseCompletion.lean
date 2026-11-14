import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueDistribution
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HyperbolaSumsOfAVonMangoldtTail

/-!
# Interval completion for complex prime-residue phases

Products of local phases have modulus one. Their centered complete-period
sum vanishes by CRT, so two boundary pieces cost at most twice the period.
This gives approximate independence directly for characteristic functions.
-/

open Finset Complex
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- A product of arbitrary local unit phases at a common integer parameter. -/
def primeResiduePhase (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) (n : ℕ) : ℂ :=
  ∏ p ∈ S, cexp ((θ p (n : ZMod p.val) : ℂ) * I)

/-- The product of the local complete phase averages. -/
def primeResiduePhaseMean (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) : ℂ :=
  ∏ p ∈ S, (∑ a : ZMod p.val, cexp ((θ p a : ℂ) * I)) / (p.val : ℂ)

theorem norm_primeResiduePhase (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) (n : ℕ) :
    ‖primeResiduePhase S θ n‖ = 1 := by
  simp only [primeResiduePhase, norm_prod, Complex.norm_exp_ofReal_mul_I, prod_const_one]

theorem primeResiduePhase_periodic (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) :
    Function.Periodic (primeResiduePhase S θ) (primeSetProduct S) := by
  intro n
  apply prod_congr rfl
  intro p hp
  have hP : (primeSetProduct S : ZMod p.val) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_prod_of_mem (fun p : Nat.Primes => p.val) hp)
  simp only [Nat.cast_add, hP, add_zero]

theorem sum_primeResiduePhase_eq_mean (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) :
    ∑ n ∈ range (primeSetProduct S), primeResiduePhase S θ n =
      (primeSetProduct S : ℂ) * primeResiduePhaseMean S θ := by
  rw [primeResiduePhase, sum_primeResidue_product,
    primeResiduePhaseMean, prod_div_distrib, ← Nat.cast_prod]
  have hP : (primeSetProduct S : ℂ) ≠ 0 := by exact_mod_cast (primeSetProduct_pos S).ne'
  change _ = (primeSetProduct S : ℂ) * (_ / (primeSetProduct S : ℂ))
  field_simp [hP]

theorem norm_primeResiduePhaseMean_le_one (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) :
    ‖primeResiduePhaseMean S θ‖ ≤ 1 := by
  have h := norm_sum_le (range (primeSetProduct S)) (primeResiduePhase S θ)
  rw [sum_primeResiduePhase_eq_mean, norm_mul] at h
  simp only [norm_primeResiduePhase, sum_const, card_range, nsmul_eq_mul, mul_one,
    Complex.norm_natCast] at h
  have hP : (0 : ℝ) < primeSetProduct S := by exact_mod_cast primeSetProduct_pos S
  nlinarith only [h, hP]

/-- Incomplete complex phase sums differ from the independent mean by at most `2P`. -/
theorem norm_sum_Ico_primeResiduePhase_sub_mean (S : Finset Nat.Primes)
    (θ : (p : Nat.Primes) → ZMod p.val → ℝ) (A B : ℕ) :
    ‖(∑ n ∈ Ico A B, primeResiduePhase S θ n) -
      ((B - A : ℕ) : ℂ) * primeResiduePhaseMean S θ‖ ≤ 2 * (primeSetProduct S : ℝ) := by
  have hper : ∀ n, primeResiduePhase S θ (n + primeSetProduct S) -
      primeResiduePhaseMean S θ = primeResiduePhase S θ n - primeResiduePhaseMean S θ :=
    fun n => congrArg (fun x => x - primeResiduePhaseMean S θ)
      (primeResiduePhase_periodic S θ n)
  have hmean : ∑ n ∈ range (primeSetProduct S),
      (primeResiduePhase S θ n - primeResiduePhaseMean S θ) = 0 := by
    rw [sum_sub_distrib, sum_primeResiduePhase_eq_mean]
    simp only [sum_const, card_range, nsmul_eq_mul, sub_self]
  have hshift : ∀ i, primeResiduePhase S θ (A + (i + primeSetProduct S)) -
      primeResiduePhaseMean S θ =
        primeResiduePhase S θ (A + i) - primeResiduePhaseMean S θ :=
    fun i => by simpa only [Nat.add_assoc] using hper (A + i)
  have hm := (ArithmeticHodgeTheoryOfDegenerations.sum_range_shift_periodic hper A).trans hmean
  have h := ArithmeticHodgeTheoryOfDegenerations.norm_sum_range_periodic_le
    (primeSetProduct_pos S) hshift hm (B - A)
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h
  rw [sum_Ico_eq_sum_range]
  refine h.trans ?_
  calc
    _ ≤ ∑ _i ∈ range (primeSetProduct S), (2 : ℝ) := by
      apply sum_le_sum
      intro i _
      exact (norm_sub_le _ _).trans (by
        rw [norm_primeResiduePhase]
        linarith only [norm_primeResiduePhaseMean_le_one S θ])
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

#print axioms norm_sum_Ico_primeResiduePhase_sub_mean

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
