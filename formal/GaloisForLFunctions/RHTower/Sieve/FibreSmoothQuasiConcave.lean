import GaloisForLFunctions.RHTower.Sieve.FibreSmoothWeight
import GaloisForLFunctions.RHTower.Sieve.QuasiConcaveSeq
import GaloisForLFunctions.RHTower.Sieve.KernelVariationBound

/-!
# The smooth model has variation `O(h)`

The length of an intersection of two intervals is the least of the four endpoint differences,

```text
min B D − max A C = min (B−A, B−C, D−A, D−C) ,
```

and each of the four is monotone or unimodal in the inner variable: `B − A` rises then falls
(`kernelDiff_bimonotone`), `B − C` falls, `D − A` rises, `D − C` is constant.  Quasi-concavity is
stable under `min`, under adding a constant and under truncation at `0`, so the smooth model is
quasi-concave, and a quasi-concave sequence has variation at most twice its range.  Since the model
lies in `[0, 3h+1]`, its variation is at most `6h + 2` — the `O(h)` weight bound that
`abs_shift_sum_le` consumes.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The length of an intersection of intervals is the least endpoint difference. -/
theorem min_sub_max (B D A C : ℝ) :
    min B D - max A C = min (min (B - A) (B - C)) (min (D - A) (D - C)) := by
  have hb := min_le_left B D
  have hd := min_le_right B D
  have ha := le_max_left A C
  have hc := le_max_right A C
  refine le_antisymm
    (le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))) ?_
  rcases le_total B D with h1 | h1 <;> rcases le_total A C with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  · rw [min_eq_left h1, max_eq_left h2]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  · rw [min_eq_right h1, max_eq_right h2]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  · rw [min_eq_right h1, max_eq_left h2]
    exact le_trans (min_le_right _ _) (min_le_left _ _)

/-- The upper endpoint, with the shift cast out of the index. -/
theorem fibreHigh_shift_eq (x h : ℝ) (i k : ℕ) :
    fibreHigh x h (i + k)
      = min ((x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ))) (2 * Real.sqrt x) := by
  rw [fibreHigh]
  norm_cast

/-- **The smooth model is quasi-concave in the inner variable.** -/
theorem quasiConcaveOn_fibreSmooth {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k)
    (N : ℕ) : QuasiConcaveOn (fun j => fibreSmooth x h k (j + 1)) N := by
  set A : ℕ → ℝ := fun j => x / (((j + 1 : ℕ) : ℝ)) with hA
  set B : ℕ → ℝ := fun j => (x + h * Real.sqrt x) / ((((j + 1 : ℕ) : ℝ)) + (k : ℝ)) with hB
  set C : ℝ := Real.sqrt x with hC
  set D : ℝ := 2 * Real.sqrt x with hD
  have hnum : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith [hs0, hh]
  -- the four endpoint differences
  have h1 : QuasiConcaveOn (fun j => B j - A j) N := by
    refine quasiConcaveOn_congr (v := fun j => kernelDiff x h k (j + 1)) (fun j => rfl) ?_
    obtain ⟨c, hcN, hup, hdown⟩ := kernelDiff_bimonotone (by linarith : (0:ℝ) ≤ x) hh hk N
    exact quasiConcaveOn_of_bimonotone hcN hup hdown
  have h2 : QuasiConcaveOn (fun j => B j - C) N := by
    refine quasiConcaveOn_of_antitone fun j _ => ?_
    have hden : (0 : ℝ) < (((j + 1 : ℕ) : ℝ)) + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have : (0 : ℝ) < (((j + 1 : ℕ) : ℝ)) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have : B (j + 1) ≤ B j := by
      rw [hB]
      refine div_le_div_of_nonneg_left hnum hden ?_
      push_cast
      linarith
    linarith
  have h3 : QuasiConcaveOn (fun j => D - A j) N := by
    refine quasiConcaveOn_of_monotone fun j _ => ?_
    have hden : (0 : ℝ) < (((j + 1 : ℕ) : ℝ)) := by positivity
    have : A (j + 1) ≤ A j := by
      rw [hA]
      refine div_le_div_of_nonneg_left (by linarith) hden ?_
      push_cast
      linarith
    linarith
  have h4 : QuasiConcaveOn (fun _ : ℕ => D - C) N := quasiConcaveOn_const _ _
  have hF : QuasiConcaveOn
      (fun j => min (min (B j - A j) (B j - C)) (min (D - A j) (D - C))) N :=
    quasiConcaveOn_min (quasiConcaveOn_min h1 h2) (quasiConcaveOn_min h3 h4)
  have hF1 := quasiConcaveOn_max_const (quasiConcaveOn_add_const hF 1) 0
  refine quasiConcaveOn_congr (fun j => ?_) hF1
  rw [fibreSmooth, kernelSmooth, fibreLow, fibreHigh_shift_eq, ← min_sub_max]

/-- **The smooth model has variation at most `6h + 2`.** -/
theorem fibreSmooth_variation_le {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k)
    (N : ℕ) :
    ∑ j ∈ Finset.range N, |fibreSmooth x h k (j + 1 + 1) - fibreSmooth x h k (j + 1)|
      ≤ 2 * (3 * h + 1) := by
  have hqc := quasiConcaveOn_fibreSmooth hx hh hk N
  have hbase := variation_le_two_range_of_quasiConcave (w := fun j => fibreSmooth x h k (j + 1))
    hqc (L := 0) (U := 3 * h + 1)
    (fun j _ => fibreSmooth_nonneg x h k (j + 1))
    (fun j _ => fibreSmooth_le hx hh k (Nat.le_add_left 1 j))
  simpa using hbase

end RHTower.Sieve

end
