import GaloisForLFunctions.HTGeometry.SmoothWeight

/-!
# The smoothing error without a boundedness hypothesis

Replacing the sharp cutoff `n ≤ K` by the smooth weight changes a sum only inside the transition window
`(K, K+H)`, where the weight lies in `[0,1]`; above `K+H` the weight vanishes and the sharp sum omits the
term as well.  So the difference is at most the `ℓ¹` mass of the coefficients in the window:

`‖∑_{n < m} a(n) w(n) − ∑_{n ≤ K} a(n)‖ ≤ ∑_{K < n ≤ ⌊K+H⌋} ‖a(n)‖`   whenever `K + H ≤ m`.

The corpus's `norm_weighted_sub_partialSum_le` is the case of unit-bounded coefficients, where the window
mass is at most `H + 1`.  The general form is what a convolution needs: the coefficients of a threefold
Dirichlet convolution are not bounded, and the window mass has to be estimated arithmetically instead.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Finset

/-- **The smoothing error, with no boundedness hypothesis.**  Replacing the sharp cutoff `n ≤ K` by the
smooth one changes the sum only inside the transition window `(K, K+H)`, so the difference is at most the
`ℓ¹` mass of the coefficients there. -/
theorem norm_weighted_sub_partialSum_le_window {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (K m : ℕ)
    (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), a n‖
      ≤ ∑ n ∈ Finset.Ioc K ⌊(K : ℝ) + H⌋₊, ‖a n‖ := by
  classical
  have hKm : K + 1 ≤ m := by
    have hlt : (K : ℝ) < (m : ℝ) := by linarith
    have : K < m := by exact_mod_cast hlt
    omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n : ℕ => a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)) hKm
  have hone : (∑ n ∈ Finset.range (K + 1), a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      = ∑ n ∈ Finset.range (K + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hnK : (n : ℝ) ≤ (K : ℝ) := by
      have : n ≤ K := by omega
      exact_mod_cast this
    rw [smoothWeight_eq_one hH hnK]
    simp
  have hdiff : (∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      - (∑ n ∈ Finset.range (K + 1), a n)
      = ∑ n ∈ Finset.Ico (K + 1) m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ) := by
    rw [← hsplit, hone]
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ico (K + 1) m,
      ‖a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        ≤ (if n ≤ ⌊(K : ℝ) + H⌋₊ then ‖a n‖ else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothWeight_nonneg _ _ _)]
    by_cases hle : n ≤ ⌊(K : ℝ) + H⌋₊
    · rw [if_pos hle]
      calc ‖a n‖ * smoothWeight (K : ℝ) H (n : ℝ) ≤ ‖a n‖ * 1 :=
            mul_le_mul_of_nonneg_left (smoothWeight_le_one _ _ _) (norm_nonneg _)
        _ = ‖a n‖ := mul_one _
    · rw [if_neg hle]
      have hge : (K : ℝ) + H ≤ (n : ℝ) := by
        rw [not_le] at hle
        have h1 : ⌊(K : ℝ) + H⌋₊ + 1 ≤ n := by omega
        have h2 : (K : ℝ) + H < (⌊(K : ℝ) + H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have h3 : ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
        linarith
      rw [smoothWeight_eq_zero hH hge, mul_zero]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => norm_nonneg _)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ico] at hn
  rw [Finset.mem_Ioc]
  exact ⟨by omega, hn.2⟩

end GaloisForLFunctions.HTGeometry
end
