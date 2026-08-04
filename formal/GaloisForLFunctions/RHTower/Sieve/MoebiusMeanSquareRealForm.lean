import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareUnconditional

/-!
# The mean square in the real form step 1 consumes

`SquarefreeExceptional.card_le_good_add_explicit` takes its mean-square input as a real sum

    ∑_{t ∈ S} ( ∑_{t < n ≤ t+L} μ(n) )² ≤ V ,

while the development above produces `∑ ‖∑ μ(n)‖²` over complex coefficients.  The two are equal —
the Möbius sum is real — and reindexing `t = Y + k` turns the range sum into a sum over
`Ico Y (Y+K)`, which is the shape of `S`.
-/

namespace RHTower.Sieve

open Finset

/-- The complex and real window sums have the same square. -/
theorem normSq_moebiusC_eq_sq_real (T : Finset ℕ) :
    ‖∑ n ∈ T, moebiusC n‖ ^ 2
      = (∑ n ∈ T, ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2 := by
  have hcast : (∑ n ∈ T, moebiusC n)
      = (((∑ n ∈ T, ((ArithmeticFunction.moebius n : ℤ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [moebiusC]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The mean square in real form, over a range of integer starts.** -/
theorem sum_sq_real_moebius_Ico_eq (L Y K : ℕ) :
    (∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
      = ∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), moebiusC n‖ ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [normSq_moebiusC_eq_sq_real]

/-- **The mean square in real form, unconditionally.** -/
theorem exists_sum_sq_real_moebius_Ico_le :
    ∃ B : ℝ → ℝ, Filter.Tendsto B Filter.atTop (nhds 0) ∧
      ∀ᶠ N : ℝ in Filter.atTop, ∀ (L Y K J : ℕ) (ε W : ℝ),
        Y + K + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 ≤ ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J →
        (∑ t ∈ Finset.Ico Y (Y + K),
            (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
          ≤ ((Y : ℝ) * (1 + ε) ^ J)
              * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε ((B N * N) ^ 2)
                  ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ 2) W) := by
  obtain ⟨B, hB, hev⟩ := exists_sum_normSq_moebius_window_le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with N hN
  intro L Y K J ε W hM hL hY hε hW hWC hJ
  rw [sum_sq_real_moebius_Ico_eq]
  exact hN L Y K J ε W hM hL hY hε hW hWC hJ

end RHTower.Sieve
