import GaloisForLFunctions.RHTower.Sieve.VonMangoldtHarmonicSquareAsymptotic
import GaloisForLFunctions.HTGeometry.VonMangoldtSelfConvolution

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction

namespace RHTower.Sieve

theorem vonMangoldtSelfConv_nonneg (n : ℕ) : 0 ≤ (Λ * Λ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun q hq =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

theorem vonMangoldtSelfConv_le_log_sq_of_isPrimePow
    {n : ℕ} (hn : IsPrimePow n) :
    (Λ * Λ) n ≤ Real.log n ^ 2 := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff n).mp hn
  rw [← hpa, GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow hp ha,
    Nat.cast_pow, Real.log_pow]
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  nlinarith [sq_nonneg (Real.log (p : ℝ))]

theorem vonMangoldtSelfConv_eq_zero_of_prime {n : ℕ} (hn : n.Prime) :
    (Λ * Λ) n = 0 := by
  simpa using GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow
    (p := n) (a := 1) hn (by norm_num)

/-- The cross moment is supported on proper prime powers and is bounded by their existing
`Lambda log/id` budget. -/
theorem vonMangoldtSelfConvCrossHarmonicSum_le
    (N : ℕ) (hN : 1 ≤ N) :
    vonMangoldtSelfConvCrossHarmonicSum N ≤
      24 * Real.log N * (1 + Real.log N) := by
  let A : Finset ℕ := Finset.Icc 2 N
  let B : Finset ℕ := {n ∈ A | ¬ n.Prime}
  let W : ℕ → ℝ := fun n => Λ n * (Λ * Λ) n / (n : ℝ)
  have hprimezero : ∑ n ∈ {n ∈ A | n.Prime}, W n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    dsimp only [W]
    rw [vonMangoldtSelfConv_eq_zero_of_prime (Finset.mem_filter.mp hn).2]
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not A Nat.Prime W
  have hcrossB : vonMangoldtSelfConvCrossHarmonicSum N = ∑ n ∈ B, W n := by
    rw [vonMangoldtSelfConvCrossHarmonicSum]
    dsimp only [A, B, W]
    rw [← hsplit, hprimezero, zero_add]
  rw [hcrossB]
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hterm : ∀ n ∈ B,
      W n ≤ Real.log N * (Λ n * Real.log n / (n : ℝ)) := by
    intro n hn
    have hnA := (Finset.mem_filter.mp hn).1
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnA).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hnA).2
    have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn2)
    have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hn2))
    have hlognN : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hnR (by exact_mod_cast hnN)
    by_cases hΛ : Λ n = 0
    · simp [W, hΛ]
    · have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
      have hconv := vonMangoldtSelfConv_le_log_sq_of_isPrimePow hpp
      have hΛ0 : 0 ≤ Λ n := vonMangoldt_nonneg
      have hfirst : Λ n * (Λ * Λ) n ≤ Λ n * Real.log n ^ 2 :=
        mul_le_mul_of_nonneg_left hconv hΛ0
      have hsecond : Λ n * Real.log n ^ 2 ≤
          Real.log N * (Λ n * Real.log n) := by
        have hprodnonneg : 0 ≤ Λ n * Real.log n := mul_nonneg hΛ0 hlogn0
        calc
          Λ n * Real.log n ^ 2 =
              Real.log n * (Λ n * Real.log n) := by ring
          _ ≤ Real.log N * (Λ n * Real.log n) :=
            mul_le_mul_of_nonneg_right hlognN hprodnonneg
      dsimp only [W]
      calc
        Λ n * (Λ * Λ) n / (n : ℝ) ≤
            (Real.log N * (Λ n * Real.log n)) / (n : ℝ) :=
          div_le_div_of_nonneg_right (hfirst.trans hsecond) hnR.le
        _ = Real.log N * (Λ n * Real.log n / (n : ℝ)) := by ring
  calc
    ∑ n ∈ B, W n ≤
        Real.log N * ∑ n ∈ B, Λ n * Real.log n / (n : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ Real.log N *
        (∑ n ∈ {n ∈ Finset.Icc 1 N | ¬ n.Prime},
          Λ n * Real.log n / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hlogN0
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnB := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_trans (by omega : 1 ≤ 2)
            (Finset.mem_Icc.mp hnB.1).1, (Finset.mem_Icc.mp hnB.1).2⟩, hnB.2⟩
      · intro n hn hnot
        positivity
    _ ≤ Real.log N * (24 * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (sum_nonprime_vonMangoldt_log_div_le N) hlogN0
    _ = 24 * Real.log N * (1 + Real.log N) := by ring

end RHTower.Sieve
