import GaloisForLFunctions.RHTower.Sieve.FibreMeanSquarePairs

/-!
# The fibre kernel is an interval, and it vanishes off a band

The kernel of `sum_fibreSq_eq_count` counts the outer indices `a` whose fibre contains both `m` and
`n`.  Since `b ∈ innerFibre x h a ↔ x ≤ ab ≤ x + h√x`, such an `a` satisfies

```text
x ≤ a·min(m,n)   and   a·max(m,n) ≤ x + h√x ,
```

so the admissible `a` form an interval, `⌈x/min(m,n)⌉ ≤ a ≤ ⌊(x + h√x)/max(m,n)⌋`, and there are
none at all unless

```text
x·max(m,n) ≤ (x + h√x)·min(m,n) ,
```

that is, unless `max/min ≤ 1 + h/√x` — the near-diagonal band, in the outer variable.  The kernel is
therefore supported on `|log m − log n| ≤ fibreWidth x h`, exactly as `overlap_card_le` gives
`|m − n| < ℓ` in the additive setting.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The admissible outer indices form an interval.** -/
theorem fibre_kernel_subset_Icc {x h : ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (outerBlock x h).filter (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)
      ⊆ Finset.Icc ⌈x / ((min m n : ℕ) : ℝ)⌉₊ ⌊(x + h * Real.sqrt x) / ((max m n : ℕ) : ℝ)⌋₊ := by
  classical
  intro a ha
  rw [Finset.mem_filter] at ha
  obtain ⟨-, hma, hna⟩ := ha
  rw [mem_innerFibre] at hma hna
  obtain ⟨-, hm1, hm2⟩ := hma
  obtain ⟨-, hn1, hn2⟩ := hna
  have hmR : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  have hnR : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hmR] at hm1 hm2
  rw [hnR] at hn1 hn2
  have hmin0 : (0 : ℝ) < ((min m n : ℕ) : ℝ) := by
    have : 1 ≤ min m n := le_min hm hn
    exact_mod_cast this
  have hmax0 : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by
    have : 1 ≤ max m n := le_trans hm (le_max_left _ _)
    exact_mod_cast this
  -- the two one-sided constraints
  have hlow : x ≤ (a : ℝ) * ((min m n : ℕ) : ℝ) := by
    rcases le_total m n with h | h
    · rw [min_eq_left h]; exact hm1
    · rw [min_eq_right h]; exact hn1
  have hhigh : (a : ℝ) * ((max m n : ℕ) : ℝ) ≤ x + h * Real.sqrt x := by
    rcases le_total m n with hle | hle
    · rw [max_eq_right hle]; exact hn2
    · rw [max_eq_left hle]; exact hm2
  rw [Finset.mem_Icc]
  constructor
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ hmin0]
    exact hlow
  · refine Nat.le_floor ?_
    rw [le_div_iff₀ hmax0]
    exact hhigh

/-- **The kernel vanishes off the near-diagonal band.** -/
theorem fibre_kernel_eq_empty {x h : ℝ} {m n : ℕ} (hm : 1 ≤ m) (_hn : 1 ≤ n)
    (hband : (x + h * Real.sqrt x) * ((min m n : ℕ) : ℝ) < x * ((max m n : ℕ) : ℝ)) :
    (outerBlock x h).filter (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
  rw [Finset.mem_filter] at ha
  obtain ⟨-, hma, hna⟩ := ha
  rw [mem_innerFibre] at hma hna
  obtain ⟨-, hm1, hm2⟩ := hma
  obtain ⟨-, hn1, hn2⟩ := hna
  have hmR : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  have hnR : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hmR] at hm1 hm2
  rw [hnR] at hn1 hn2
  have hmax0 : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by
    have : 1 ≤ max m n := le_trans hm (le_max_left _ _)
    exact_mod_cast this
  have hlow : x ≤ (a : ℝ) * ((min m n : ℕ) : ℝ) := by
    rcases le_total m n with hle | hle
    · rw [min_eq_left hle]; exact hm1
    · rw [min_eq_right hle]; exact hn1
  have hhigh : (a : ℝ) * ((max m n : ℕ) : ℝ) ≤ x + h * Real.sqrt x := by
    rcases le_total m n with hle | hle
    · rw [max_eq_right hle]; exact hn2
    · rw [max_eq_left hle]; exact hm2
  have hmin0 : (0 : ℝ) ≤ ((min m n : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [hlow, hhigh, hmin0, hmax0]

end RHTower.Sieve

end
