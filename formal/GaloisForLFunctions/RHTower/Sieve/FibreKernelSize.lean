import GaloisForLFunctions.RHTower.Sieve.FibreKernelBand

/-!
# The size of the fibre kernel

The admissible outer indices form an interval, so their number is its length plus one:

```text
#{ a ∈ outerBlock : m, n ∈ innerFibre a } ≤ ( (x + h√x)/max(m,n) − x/min(m,n) + 1 )₊ .
```

On the diagonal `m = n` this is `h√x/m + 1`, the expected count; off the diagonal it decreases and
reaches zero exactly at the band edge `max/min = 1 + h/√x`, in agreement with
`fibre_kernel_eq_empty`.  So the bilinear form of `sum_fibreSq_eq_count` has an explicit
near-diagonal kernel — the outer-variable analogue of Gallagher's triangular kernel, with no window
machinery and no integral.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The kernel is at most the length of its interval, plus one.** -/
theorem fibre_kernel_card_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((((outerBlock x h).filter
        (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℕ) : ℝ)
      ≤ max ((x + h * Real.sqrt x) / ((max m n : ℕ) : ℝ)
              - x / ((min m n : ℕ) : ℝ) + 1) 0 := by
  classical
  set A : ℝ := x / ((min m n : ℕ) : ℝ) with hAdef
  set B : ℝ := (x + h * Real.sqrt x) / ((max m n : ℕ) : ℝ) with hBdef
  set S := (outerBlock x h).filter
    (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a) with hSdef
  have hmax0 : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by
    have : 1 ≤ max m n := le_trans hm (le_max_left _ _)
    exact_mod_cast this
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    positivity
  rcases Finset.eq_empty_or_nonempty S with hemp | ⟨a₀, ha₀⟩
  · rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact le_max_right _ _
  · have hsub : S ⊆ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ := by
      rw [hSdef, hAdef, hBdef]
      exact fibre_kernel_subset_Icc hm hn
    have hmem := hsub ha₀
    rw [Finset.mem_Icc] at hmem
    have hle : ⌈A⌉₊ ≤ ⌊B⌋₊ := le_trans hmem.1 hmem.2
    have hcard : S.card ≤ ⌊B⌋₊ + 1 - ⌈A⌉₊ := by
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [Nat.card_Icc]
    have hcast : ((⌊B⌋₊ + 1 - ⌈A⌉₊ : ℕ) : ℝ) = (⌊B⌋₊ : ℝ) + 1 - (⌈A⌉₊ : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hcardR : ((S.card : ℕ) : ℝ) ≤ (⌊B⌋₊ : ℝ) + 1 - (⌈A⌉₊ : ℝ) := by
      rw [← hcast]
      exact_mod_cast hcard
    have hfl : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le hB0
    have hce : A ≤ ((⌈A⌉₊ : ℕ) : ℝ) := Nat.le_ceil A
    refine le_max_of_le_left ?_
    linarith

end RHTower.Sieve

end
