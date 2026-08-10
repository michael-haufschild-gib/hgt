import GaloisForLFunctions.RHTower.Sieve.DyadicPairExpansion

/-!
# The discrete overlap kernel

The kernel of the pair expansion is the number of common starting points of two windows of length
`ℓ` containing both `m` and `n`.  A starting point `z` works exactly when `z + 1 ≤ min(m,n)` and
`max(m,n) ≤ z + ℓ`, so the admissible `z` form an interval of length `ℓ − |m − n|`:

```text
#{ z ∈ [A,B] : m, n ∈ (z, z+ℓ] } ≤ (ℓ − |m − n|)₊ .
```

This is the integer analogue of `volume_real_logWindow_inter`, which gives
`(δ − |log m − log n|)₊` for the logarithmic windows of Gallagher's lemma.  The kernel vanishes for
`|m − n| ≥ ℓ`, so the pair expansion is supported on a band of width `ℓ` around the diagonal — the
near-diagonal structure the whole estimate rests on.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The distance of two naturals, as a real absolute value. -/
theorem cast_max_sub_min (m n : ℕ) :
    ((max m n - min m n : ℕ) : ℝ) = |(m : ℝ) - (n : ℝ)| := by
  rcases le_total m n with h | h
  · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
  · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h, abs_of_nonneg]
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    linarith

/-- **The overlap kernel is at most `(ℓ − |m − n|)₊`.** -/
theorem overlap_card_le (ℓ A B m n : ℕ) :
    (((Finset.Icc A B).filter
        (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ)
          ∧ n ∈ Finset.Icc (z + 1) (z + ℓ))).card : ℝ)
      ≤ max ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) 0 := by
  classical
  set S := (Finset.Icc A B).filter
    (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ) ∧ n ∈ Finset.Icc (z + 1) (z + ℓ)) with hSdef
  rcases Finset.eq_empty_or_nonempty S with hemp | ⟨z₀, hz₀⟩
  · rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact le_max_right _ _
  · -- the admissible starting points form an interval
    have hmem : ∀ z ∈ S, z + 1 ≤ m ∧ m ≤ z + ℓ ∧ z + 1 ≤ n ∧ n ≤ z + ℓ := by
      intro z hz
      rw [hSdef] at hz
      simp only [Finset.mem_filter, Finset.mem_Icc] at hz
      exact ⟨hz.2.1.1, hz.2.1.2, hz.2.2.1, hz.2.2.2⟩
    have hsub : S ⊆ Finset.Icc (max m n - ℓ) (min m n - 1) := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hmem z hz
      rw [Finset.mem_Icc]
      omega
    have hcard : S.card ≤ (min m n - 1) + 1 - (max m n - ℓ) := by
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [Nat.card_Icc]
    obtain ⟨h1, h2, h3, h4⟩ := hmem z₀ hz₀
    have hkey : S.card + (max m n - min m n) ≤ ℓ := by omega
    have hcast : ((S.card : ℕ) : ℝ) + ((max m n - min m n : ℕ) : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast hkey
    rw [cast_max_sub_min] at hcast
    refine le_max_of_le_left ?_
    linarith

end RHTower.Sieve

end
