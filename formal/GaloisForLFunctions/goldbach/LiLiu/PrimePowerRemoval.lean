import GaloisForLFunctions.goldbach.LiLiu.FiniteProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime pairs in the support of the smoothed correlation

At each nonprime endpoint the other coefficient is at most log N. Summing
the two endpoint bounds costs at most 2 log N (ψ(N) − θ(N)). This gives a
finite lower bound on the number of ordered prime representations.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu

open Finset ArithmeticFunction Filter
open scoped Classical Topology
noncomputable section

/-- The support window for an individual summand. -/
def inWindow (N n : ℕ) : Prop := (n : ℝ) / N ∈ Set.Icc (1 / 3 : ℝ) (2 / 3)

/-- Ordered prime pairs in the central third, including the diagonal when present. -/
def centralPrimePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (antidiagonal N).filter fun p => p.1.Prime ∧ p.2.Prime ∧ inWindow N p.1 ∧ inWindow N p.2

private def nonprimeWeight (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

private theorem nonprimeWeight_nonneg (n : ℕ) : 0 ≤ nonprimeWeight n := by
  simp only [nonprimeWeight]
  split_ifs <;> positivity

private theorem sum_nonprimeWeight (N : ℕ) :
    ∑ n ∈ range (N + 1), nonprimeWeight n = Chebyshev.psi N - Chebyshev.theta N := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  have hr : range (N + 1) = Icc 0 N := by ext n; simp
  rw [hr, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
  simp [nonprimeWeight, ite_not]

private theorem coeff_bounds (φ : ℝ → ℝ) (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (N n : ℕ) : 0 ≤ coefficient φ N n ∧ coefficient φ N n ≤ Λ n :=
  ⟨mul_nonneg vonMangoldt_nonneg (hφ _).1,
   mul_le_of_le_one_right vonMangoldt_nonneg (hφ _).2⟩

private theorem mangoldt_le_target_log {N n : ℕ} (hn : n ≤ N) (hN : 1 ≤ N) :
    Λ n ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simpa using Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn))

private theorem pair_le (φ : ℝ → ℝ) (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hs : Function.support φ ⊆ Set.Icc (1 / 3 : ℝ) (2 / 3)) {N n m : ℕ}
    (hN : 1 ≤ N) (hnm : n + m = N) :
    (if n.Coprime N then coefficient φ N n * coefficient φ N m else 0) ≤
      (if n.Prime ∧ m.Prime ∧ inWindow N n ∧ inWindow N m then Real.log N ^ 2 else 0) +
        (nonprimeWeight n + nonprimeWeight m) * Real.log N := by
  have hn := coeff_bounds φ hφ N n
  have hm := coeff_bounds φ hφ N m
  have hnL := mangoldt_le_target_log (show n ≤ N by omega) hN
  have hmL := mangoldt_le_target_log (show m ≤ N by omega) hN
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  have hE := mul_nonneg (add_nonneg (nonprimeWeight_nonneg n) (nonprimeWeight_nonneg m)) hL
  have hI : 0 ≤ (if n.Prime ∧ m.Prime ∧ inWindow N n ∧ inWindow N m then
      Real.log N ^ 2 else 0) := by split_ifs <;> positivity
  by_cases hc : n.Coprime N
  case neg => simpa only [if_neg hc] using add_nonneg hI hE
  · rw [if_pos hc]
    by_cases h : n.Prime ∧ m.Prime ∧ inWindow N n ∧ inWindow N m
    · rw [if_pos h, pow_two]
      exact (mul_le_mul (hn.2.trans hnL) (hm.2.trans hmL) hm.1 hL).trans (le_add_of_nonneg_right hE)
    rw [if_neg h, zero_add]
    by_cases hp : n.Prime
    · by_cases hq : m.Prime
      · have hz (r : ℕ) (hr : ¬inWindow N r) : coefficient φ N r = 0 := by
          have hv := Function.notMem_support.mp fun hv => hr (hs hv)
          simp [coefficient, hv]
        by_cases hw : inWindow N n
        · rw [hz m (fun hv => h ⟨hp, hq, hw, hv⟩), mul_zero]
          exact hE
        · rw [hz n hw, zero_mul]
          exact hE
      · rw [nonprimeWeight, if_pos hp, nonprimeWeight, if_neg hq, zero_add, mul_comm (Λ m)]
        exact mul_le_mul (hn.2.trans hnL) hm.2 hm.1 hL
    · have he : Λ n ≤ nonprimeWeight n + nonprimeWeight m := by
        simpa only [nonprimeWeight, if_neg hp] using le_add_of_nonneg_right
          (a := Λ n) (nonprimeWeight_nonneg m)
      exact mul_le_mul (hn.2.trans he) (hm.2.trans hmL) hm.1
        (add_nonneg (nonprimeWeight_nonneg n) (nonprimeWeight_nonneg m))

/-- Finite prime-power removal, with both nonprime endpoint contributions explicit. -/
theorem correlation_mul_le_count_add_primePowers
    (φ : ℝ → ℝ) (hφ : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hs : Function.support φ ⊆ Set.Icc (1 / 3 : ℝ) (2 / 3)) {N : ℕ} (hN : 1 ≤ N) :
    correlation φ N * N ≤ (centralPrimePairs N).card * Real.log N ^ 2 +
      2 * (Chebyshev.psi N - Chebyshev.theta N) * Real.log N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [correlation, div_mul_cancel₀ _ hN0]
  apply (sum_le_sum (fun p hp => pair_le φ hφ hs hN (mem_antidiagonal.mp hp))).trans_eq
  rw [sum_add_distrib, ← sum_mul, sum_add_distrib,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun n _ => nonprimeWeight n),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ m => nonprimeWeight m),
    sum_flip, sum_nonprimeWeight, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, centralPrimePairs, two_mul]

#print axioms correlation_mul_le_count_add_primePowers

end
end GaloisForLFunctions.Goldbach.LiLiu
