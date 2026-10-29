import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheArithmeticCurvatureHasAnExactGramCompletion

/-!
# Completing conductors recovers the discrete bridge

Adding all nontrivial primitive orders dividing a period fills the missing
cyclic frequencies. The resulting centered kernel is exactly the discrete
bridge covariance. This identifies the positive survivor of the
fixed-conductor radical without discarding any mixed entry.
-/

noncomputable section

open Finset Polynomial

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticEffectivityTheory

/-- Completing primitive orders recovers the full cyclic prefix energy. -/
theorem sum_divisors_primitiveRootPrefixEnergy {Q : ℕ} (hQ : 0 < Q) (k : ℕ) :
    (∑ m ∈ Q.divisors, primitiveRootPrefixEnergy m k) =
      (k : ℝ) ^ 2 + (k % Q : ℕ) * ((Q : ℝ) - (k % Q : ℕ)) := by
  have h := congrArg Complex.re
    (sum_nthRoots_eq_sum_divisors Q
      (fun ζ => ((Complex.normSq (∑ j ∈ range k, ζ ^ j) : ℝ) : ℂ)))
  simp only [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  exact nthRoots_prefix_energy hQ k

theorem primitiveRootPrefixEnergy_one (k : ℕ) :
    primitiveRootPrefixEnergy 1 k = (k : ℝ) ^ 2 := by
  simp [primitiveRootPrefixEnergy, Complex.normSq_natCast]

/-- Removing the constant root leaves the exact bridge variance. -/
theorem sum_nontrivial_divisors_primitiveRootPrefixEnergy {Q : ℕ} (hQ : 0 < Q)
    {k : ℕ} (hk : k ≤ Q) :
    (∑ m ∈ Q.divisors.erase 1, primitiveRootPrefixEnergy m k) =
      (k : ℝ) * ((Q : ℝ) - k) := by
  have h1 : 1 ∈ Q.divisors := Nat.one_mem_divisors.mpr hQ.ne'
  have hs := sum_erase_add Q.divisors (fun m => primitiveRootPrefixEnergy m k) h1
  rw [primitiveRootPrefixEnergy_one, sum_divisors_primitiveRootPrefixEnergy hQ] at hs
  rcases lt_or_eq_of_le hk with hklt | rfl
  · rw [Nat.mod_eq_of_lt hklt] at hs
    linarith only [hs]
  · rw [Nat.mod_self, Nat.cast_zero, zero_mul, add_zero] at hs
    rw [sub_self, mul_zero]
    linarith only [hs]

/-- All nontrivial divisor conductors together give the exact full mixed
bridge kernel, rather than only its diagonal variance. -/
theorem sum_nontrivial_divisors_primitivePrefixGram {Q : ℕ} (hQ : 0 < Q)
    {i j : ℕ} (hi : i ≤ Q) (hj : j ≤ Q) :
    (∑ m ∈ Q.divisors.erase 1, primitivePrefixGram m i j) =
      (Q : ℝ) * min (i : ℝ) j - (i : ℝ) * j := by
  have hd : Nat.dist i j ≤ Q := by
    rcases le_total i j with hij | hji
    · rw [Nat.dist_eq_sub_of_le hij]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hji]
      omega
  simp only [primitivePrefixGram, ← sum_div, sum_sub_distrib, sum_add_distrib]
  rw [sum_nontrivial_divisors_primitiveRootPrefixEnergy hQ hi,
    sum_nontrivial_divisors_primitiveRootPrefixEnergy hQ hj,
    sum_nontrivial_divisors_primitiveRootPrefixEnergy hQ hd]
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij,
      min_eq_left (by exact_mod_cast hij)]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji,
      min_eq_right (by exact_mod_cast hji)]
    ring

/-- The conductor-completed bridge form is nonnegative on every finite
coefficient family in the period. -/
theorem discreteBridge_quadratic_nonneg {ι : Type*} (s : Finset ι)
    {Q : ℕ} (hQ : 0 < Q) (a : ι → ℝ) (k : ι → ℕ)
    (hk : ∀ i ∈ s, k i ≤ Q) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      a i * a j * ((Q : ℝ) * min (k i : ℝ) (k j) - (k i : ℝ) * k j) := by
  have he :
      (∑ i ∈ s, ∑ j ∈ s,
        a i * a j * ((Q : ℝ) * min (k i : ℝ) (k j) - (k i : ℝ) * k j)) =
      ∑ m ∈ Q.divisors.erase 1, ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * primitivePrefixGram m (k i) (k j) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, ∑ m ∈ Q.divisors.erase 1,
          a i * a j * primitivePrefixGram m (k i) (k j) := by
        refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
        rw [← mul_sum, sum_nontrivial_divisors_primitivePrefixGram hQ (hk i hi) (hk j hj)]
      _ = ∑ i ∈ s, ∑ m ∈ Q.divisors.erase 1, ∑ j ∈ s,
          a i * a j * primitivePrefixGram m (k i) (k j) :=
        sum_congr rfl fun _ _ => sum_comm
      _ = _ := sum_comm
  rw [he]
  exact sum_nonneg fun m hm =>
    primitivePrefixGram_quadratic_nonneg s
      (Nat.pos_of_mem_divisors (mem_erase.mp hm).2) a k

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_nontrivial_divisors_primitivePrefixGram
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.discreteBridge_quadratic_nonneg
