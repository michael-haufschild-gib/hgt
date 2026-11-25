import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Reading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.FiniteWave
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-! # The finite spectrum selected by a largest-prime measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Set _root_.RHTower

/-- Every retained squarefree state divides this product. -/
def primeProduct (N : ℕ) := ∏ p ∈ N.primesLE, p

abbrev Retained (N : ℕ) := ↥(primeProduct N).divisors

private theorem squarefree_product (N : ℕ) : Squarefree (primeProduct N) :=
  _root_.Sieve.prodDistinctPrimes_squarefree N.primesLE fun _ => Nat.prime_of_mem_primesLE

theorem smooth_iff_dvd (N : ℕ) (j : SquarefreeLabel) :
    j.val.val ∈ (N+1).smoothNumbers ↔ j.val.val ∣ primeProduct N := by
  rw [Nat.mem_smoothNumbers_iff_primeFactors_subset]
  have hP : (primeProduct N).primeFactors = N.primesLE :=
    Nat.primeFactors_prod fun _ => Nat.prime_of_mem_primesLE
  constructor
  · rintro ⟨_,hsub⟩
    calc j.val.val = ∏ p ∈ j.val.val.primeFactors, p := (Nat.prod_primeFactors_of_squarefree j.property).symm
      _ ∣ primeProduct N := Finset.prod_dvd_prod_of_subset _ _ id hsub
  · intro hd
    refine ⟨j.val.ne_zero,?_⟩
    change j.val.val.primeFactors ⊆ N.primesLE
    simpa only [hP] using Nat.primeFactors_mono hd (squarefree_product N).ne_zero

/-- The divisor index, interpreted as an actual orientation label of the two-copy gas. -/
def retainedLabel (N : ℕ) (d : Retained N) : SquarefreeLabel :=
  ⟨⟨d.val,Nat.pos_of_mem_divisors d.property⟩,
    (squarefree_product N).squarefree_of_dvd (Nat.mem_divisors.mp d.property).1⟩

theorem retained_smooth (N : ℕ) (d : Retained N) :
    (retainedLabel N d).val.val ∈ (N+1).smoothNumbers :=
  (smooth_iff_dvd N _).mpr (Nat.mem_divisors.mp d.property).1

/-- The cutoff reduces an arbitrary spectral test to a finite sum, even for unbounded tests. -/
theorem retained_sum {E : Type*} [NormedAddCommGroup E] (N : ℕ) (f : SquarefreeLabel → E) :
    (∑' j : SquarefreeLabel, if j.val.val ∈ (N+1).smoothNumbers then f j else 0) =
      ∑ d : Retained N, f (retainedLabel N d) := by
  classical
  let g := fun j : SquarefreeLabel => if j.val.val ∈ (N+1).smoothNumbers then f j else 0
  have hi : Function.Injective (retainedLabel N) := fun _ _ h =>
    Subtype.ext (congrArg (fun j : SquarefreeLabel => j.val.val) h)
  have hs : Function.support g ⊆ range (retainedLabel N) := by
    intro j hj
    have hm : j.val.val ∈ (N+1).smoothNumbers := by
      by_contra hn
      exact hj (if_neg hn)
    exact ⟨⟨j.val.val,Nat.mem_divisors.mpr ⟨(smooth_iff_dvd N j).mp hm,(squarefree_product N).ne_zero⟩⟩,rfl⟩
  change ∑' j, g j = _
  rw [← hi.tsum_eq hs,tsum_fintype]
  exact Finset.sum_congr rfl (fun d _ => if_pos (retained_smooth N d))

/-- Finite divisor trace equals the binary prime product at every complex temperature. -/
theorem retained_trace (N : ℕ) (s : ℂ) :
    (∑ d : Retained N, Complex.exp (-s*(energy (retainedLabel N d).val:ℂ))) = Window.partition N s := by
  classical
  let H := fun n : ℕ => Complex.exp (-s*(Real.log n:ℂ))
  have hprime (p : ℕ) (hp : p.Prime) : H p = (p:ℂ)^(-s) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero),← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg p)]
    exact congrArg Complex.exp (mul_comm _ _)
  change (∑ d : Retained N, H d.val) = _
  rw [Finset.sum_coe_sort,primeProduct,
    Sieve.sum_divisors_prod_primes_eq (fun p hp => Nat.prime_of_mem_primesLE hp),
    Window.partition,Finset.prod_one_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hpr (p : ℕ) (hp : p ∈ T) := Nat.prime_of_mem_primesLE ((Finset.mem_powerset.mp hT) hp)
  change Complex.exp (-s*(Real.log ((∏ p ∈ T,p : ℕ):ℝ):ℂ)) = _
  rw [Nat.cast_prod,Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (hpr p hp).ne_zero),
    Complex.ofReal_sum,Finset.mul_sum,Complex.exp_sum]
  exact Finset.prod_congr rfl fun p hp => hprime p (hpr p hp)

#print axioms smooth_iff_dvd
#print axioms retained_smooth
#print axioms retained_sum
#print axioms retained_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
