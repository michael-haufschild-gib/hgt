import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-!
# The reciprocal dyadic polynomial from a partial-sum bound

Abel summation against the decreasing weight `1/n` turns a bound for the partial sums of a sequence into
a bound for its reciprocal-weighted dyadic sum:

```text
‖∑_{Y ≤ n ≤ 2Y} h(n)/n‖ ≤ 2·max_{Y−1 ≤ m ≤ 2Y} ‖∑_{k ≤ m} h(k)‖ / Y.
```

The factor two is the difference of the two endpoint partial sums; no other loss occurs, because the
weight is monotone and its value at the left endpoint is `1/Y`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex

/-- A half-open block sum is the difference of two initial segments. -/
theorem sum_Ico_eq_sub_sum_Icc (h : ℕ → ℂ) {Y m : ℕ} (hY : 1 ≤ Y) (hYm : Y ≤ m) :
    ∑ n ∈ Finset.Ico Y m, h n
      = (∑ n ∈ Finset.Icc 1 (m - 1), h n) - ∑ n ∈ Finset.Icc 1 (Y - 1), h n := by
  have hm1 : 1 ≤ m := le_trans hY hYm
  rw [← Finset.Ico_add_one_right_eq_Icc 1 (m - 1), ← Finset.Ico_add_one_right_eq_Icc 1 (Y - 1),
    show m - 1 + 1 = m by omega, show Y - 1 + 1 = Y by omega,
    eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_Ico_consecutive h hY hYm

/-- **The reciprocal dyadic bound.**  Abel summation against `1/n` charges the block only the endpoint
weight `1/Y` times twice the partial-sum bound. -/
theorem norm_sum_Ico_div_le_of_partialSum {h : ℕ → ℂ} {Y : ℕ} (hY : 1 ≤ Y) {E : ℝ}
    (hE : ∀ m : ℕ, m ≤ 2 * Y → ‖∑ n ∈ Finset.Icc 1 m, h n‖ ≤ E) :
    ‖∑ n ∈ Finset.Ico Y (2 * Y + 1), h n / (n : ℂ)‖ ≤ 2 * E / (Y : ℝ) := by
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hNM : Y ≤ 2 * Y + 1 := by omega
  have hw0 : (0 : ℝ) ≤ 1 / ((2 * Y + 1 : ℕ) : ℝ) := by positivity
  have hanti : ∀ m : ℕ, Y ≤ m → m < 2 * Y + 1 →
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m : ℕ) : ℝ) := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : (0 : ℝ) < (Y : ℝ) := hYR
      have hmY : (Y : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    refine one_div_le_one_div_of_le hm0 ?_
    push_cast
    linarith
  have hP : ∀ m : ℕ, Y ≤ m → m ≤ 2 * Y + 1 →
      ‖∑ n ∈ Finset.Ico Y m, h n‖ ≤ 2 * E := by
    intro m hm hm2
    rw [sum_Ico_eq_sub_sum_Icc h hY hm]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := hE (m - 1) (by omega)
    have h2 := hE (Y - 1) (by omega)
    linarith
  have habel := abel_block_bound h (fun n => 1 / ((n : ℕ) : ℝ)) Y (2 * Y + 1) hNM hw0 hanti
    (2 * E) hP
  have hcongr : ∀ n : ℕ, (((1 / ((n : ℕ) : ℝ) : ℝ) : ℂ)) * h n = h n / (n : ℂ) := by
    intro n
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun n _ => hcongr n)] at habel
  refine le_trans habel (le_of_eq ?_)
  field_simp

end RHTower.Sieve
end
