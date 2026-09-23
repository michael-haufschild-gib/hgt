import GaloisForLFunctions.RHTower.Sieve.PairMainTermBound

/-!
# An explicit upper bound for the truncated pair sum

Combining the pair count with the bound on its main term, for squarefree `h`

`|∑_{n ∈ (t,t+L]} Q_R(n) Q_R(n+h)| ≤ 4L + R²`,

uniformly in the start `t`, the shift `h` and the truncation `R`.  Both constants are explicit and no
Euler product is evaluated.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Explicit upper bound for the truncated squarefree pair sum.** -/
theorem abs_truncated_pair_le {h : ℕ} (hh : Squarefree h) (t L R : ℕ) :
    |∑ n ∈ Finset.Ioc t (t + L),
        (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
          * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ))|
      ≤ 4 * (L : ℝ) + (R : ℝ) ^ (2 : ℕ) := by
  classical
  set A : ℝ := ∑ n ∈ Finset.Ioc t (t + L),
      (∑ d ∈ {d ∈ Finset.Icc 1 R | d ^ (2 : ℕ) ∣ n}, ((moebius d : ℤ) : ℝ))
        * (∑ e ∈ {e ∈ Finset.Icc 1 R | e ^ (2 : ℕ) ∣ (n + h)}, ((moebius e : ℤ) : ℝ)) with hA
  set M : ℝ := ∑ p ∈ {p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R | Nat.Coprime p.1 p.2},
      ((moebius p.1 : ℤ) : ℝ) * ((moebius p.2 : ℤ) : ℝ)
        / ((p.1 : ℝ) ^ (2 : ℕ) * (p.2 : ℝ) ^ (2 : ℕ)) with hM
  have hdiff : |A - (L : ℝ) * M| ≤ (R : ℝ) ^ (2 : ℕ) := abs_truncated_pair_sub_le hh t L R
  have hmain : |M| ≤ 4 := abs_main_pair_le R
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hprod : |(L : ℝ) * M| ≤ 4 * (L : ℝ) := by
    rw [abs_mul, abs_of_nonneg hL]
    calc (L : ℝ) * |M| ≤ (L : ℝ) * 4 := mul_le_mul_of_nonneg_left hmain hL
      _ = 4 * (L : ℝ) := by ring
  calc |A| = |(A - (L : ℝ) * M) + (L : ℝ) * M| := by ring_nf
    _ ≤ |A - (L : ℝ) * M| + |(L : ℝ) * M| := abs_add_le _ _
    _ ≤ (R : ℝ) ^ (2 : ℕ) + 4 * (L : ℝ) := add_le_add hdiff hprod
    _ = 4 * (L : ℝ) + (R : ℝ) ^ (2 : ℕ) := by ring

end RHTower.Sieve
