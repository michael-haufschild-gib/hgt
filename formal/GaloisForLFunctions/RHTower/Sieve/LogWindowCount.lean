import GaloisForLFunctions.RHTower.Sieve.SeparatedSampling
import GaloisForLFunctions.RHTower.Sieve.WindowToLogWindowSum

/-!
# How much a logarithmic window sum can change

A window sum is a step function, so the comparison that `sum_le_integral_of_separated` needs cannot
come from a derivative.  It comes from counting: the indices in a logarithmic window `(c, c+τ]` are
the integers in `(e^c, e^{c+τ}]`, of which there are at most

```text
e^c·(e^τ − 1) + 1 ,
```

so for unit-bounded coefficients the window sum is at most that.  Shifting the window from `u` to
`v ∈ [u, u+δ]` changes it by exactly the two boundary windows,

```text
W(u) − W(v) = (window of width v−u at u) − (window of width v−u at u+δ) ,
```

each of which is counted the same way.  At the scale of the fibres — width `v−u ≍ 1/√x`, heights
`≍ √x` — both counts are `O(1)`, which is what makes the sampling constant `c` absolute.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The logarithmic window sum, as a sum over a filtered index set. -/
theorem logWindowSum_eq_filter (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) :
    logWindowSum a s δ u
      = ∑ n ∈ s.filter (fun n : ℕ => u < Real.log n ∧ Real.log n ≤ u + δ), a n := by
  classical
  rw [logWindowSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : u < Real.log n ∧ Real.log n ≤ u + δ
  · rw [if_pos hc, Set.indicator_of_mem (mem_logWindow_iff.2 hc), one_smul]
  · rw [if_neg hc, Set.indicator_of_notMem (fun h => hc (mem_logWindow_iff.1 h)), zero_smul]

/-- **The window sum is at most the number of integers in the window.** -/
theorem norm_logWindowSum_le_count {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (u : ℝ) :
    ‖logWindowSum a s δ u‖ ≤ Real.exp u * (Real.exp δ - 1) + 1 := by
  classical
  set A : ℝ := Real.exp u with hA
  set B : ℝ := Real.exp (u + δ) with hB
  have hA0 : (0 : ℝ) < A := Real.exp_pos u
  have hAB : A ≤ B := by
    rw [hA, hB]
    exact Real.exp_le_exp.2 (by linarith)
  -- the index set sits inside an interval of integers
  have hsub : s.filter (fun n : ℕ => u < Real.log n ∧ Real.log n ≤ u + δ)
      ⊆ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hns, h1, h2⟩ := hn
    have hn1 : 1 ≤ n := hs n hns
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hexp1 : A < (n : ℝ) := by
      rw [hA, ← Real.exp_log hn0]
      exact Real.exp_lt_exp.2 h1
    have hexp2 : (n : ℝ) ≤ B := by
      rw [hB, ← Real.exp_log hn0]
      exact Real.exp_le_exp.2 h2
    rw [Finset.mem_Ioc]
    constructor
    · have hfl : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le hA0.le
      have : ((⌊A⌋₊ : ℕ) : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast this
    · exact Nat.le_floor hexp2
  -- and a sum of unit-bounded terms is at most the cardinality
  have hcard : ‖logWindowSum a s δ u‖
      ≤ (((Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).card : ℕ) : ℝ) := by
    rw [logWindowSum_eq_filter]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => ha n)) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have := Finset.card_le_card hsub
    exact_mod_cast this
  refine le_trans hcard ?_
  rw [Nat.card_Ioc]
  have hflB : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (le_trans hA0.le hAB)
  have hflA : A - 1 < ((⌊A⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one A
    linarith
  have hexpand : A * (Real.exp δ - 1) + 1 = B - A + 1 := by
    rw [hA, hB, Real.exp_add]
    ring
  rw [hexpand]
  rcases le_or_gt ⌊A⌋₊ ⌊B⌋₊ with hle | hgt
  · have hcast : (((⌊B⌋₊ - ⌊A⌋₊ : ℕ)) : ℝ) = ((⌊B⌋₊ : ℕ) : ℝ) - ((⌊A⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    linarith
  · have hzero : ⌊B⌋₊ - ⌊A⌋₊ = 0 := by omega
    rw [hzero]
    push_cast
    linarith

/-- **Shifting a window changes it by exactly the two boundary windows.** -/
theorem logWindowSum_sub_eq (a : ℕ → ℂ) (s : Finset ℕ) {δ u v : ℝ}
    (huv : u ≤ v) (hvu : v ≤ u + δ) :
    logWindowSum a s δ u - logWindowSum a s δ v
      = logWindowSum a s (v - u) u - logWindowSum a s (v - u) (u + δ) := by
  classical
  rw [logWindowSum_eq_filter, logWindowSum_eq_filter, logWindowSum_eq_filter,
    logWindowSum_eq_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  set L : ℝ := Real.log n with hL
  by_cases h1 : u < L
  · by_cases h2 : L ≤ v
    · rw [if_pos ⟨h1, by linarith⟩, if_neg (by rintro ⟨hc, -⟩; linarith),
        if_pos ⟨h1, by linarith⟩, if_neg (by rintro ⟨hc, -⟩; linarith)]
    · have h2' : v < L := not_le.1 h2
      by_cases h3 : L ≤ u + δ
      · rw [if_pos ⟨h1, h3⟩, if_pos ⟨h2', by linarith⟩,
          if_neg (by rintro ⟨-, hc⟩; linarith), if_neg (by rintro ⟨hc, -⟩; linarith)]
        ring
      · have h3' : u + δ < L := not_le.1 h3
        by_cases h4 : L ≤ v + δ
        · rw [if_neg (by rintro ⟨-, hc⟩; linarith), if_pos ⟨by linarith, h4⟩,
            if_neg (by rintro ⟨-, hc⟩; linarith), if_pos ⟨h3', by linarith⟩]
        · have h4' : v + δ < L := not_le.1 h4
          rw [if_neg (by rintro ⟨-, hc⟩; linarith), if_neg (by rintro ⟨-, hc⟩; linarith),
            if_neg (by rintro ⟨-, hc⟩; linarith), if_neg (by rintro ⟨-, hc⟩; linarith)]
  · have h1' : L ≤ u := not_lt.1 h1
    rw [if_neg (by rintro ⟨hc, -⟩; linarith), if_neg (by rintro ⟨hc, -⟩; linarith),
      if_neg (by rintro ⟨hc, -⟩; linarith), if_neg (by rintro ⟨hc, -⟩; linarith)]

/-- **The window sum changes by a bounded amount across a short shift.** -/
theorem norm_logWindowSum_sub_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) {δ u v : ℝ} (huv : u ≤ v) (hvu : v ≤ u + δ) :
    ‖logWindowSum a s δ u - logWindowSum a s δ v‖
      ≤ (Real.exp u * (Real.exp (v - u) - 1) + 1)
        + (Real.exp (u + δ) * (Real.exp (v - u) - 1) + 1) := by
  rw [logWindowSum_sub_eq a s huv hvu]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · exact norm_logWindowSum_le_count ha s hs (by linarith) u
  · exact norm_logWindowSum_le_count ha s hs (by linarith) (u + δ)

end RHTower.Sieve

end
