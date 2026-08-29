import GaloisForLFunctions.RHTower.Sieve.DyadicTranslates

/-!
# Comparing window sums at nearby starts and lengths

For a weight bounded by one, a partial sum changes by at most the number of terms crossed, so two
window sums whose endpoints differ by a bounded amount differ by a bounded amount.  This is the
elementary half of the passage from the *fibre* normalisation of a short-interval mean square — where
the windows sit at the starts `x/a` and have lengths `h√x/a` — to the *integer-start* normalisation,
where the starts run over all integers of a range and the length is fixed: the two families of
endpoints interleave within `O(1)`, and squaring costs a factor two.

* `abs_partialSum_sub_le` — a partial sum moves by at most the number of terms;
* `abs_windowSum_sub_le` — window sums at nearby endpoints are close;
* `fixedWindowSq_le_of_close` — hence their squares are comparable.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

variable {f : ℕ → ℝ}

/-- **A partial sum moves by at most the number of terms crossed.** -/
theorem abs_partialSum_sub_le (hf : ∀ n, |f n| ≤ 1) (m n : ℕ) :
    |partialSum f n - partialSum f m| ≤ |(n : ℝ) - (m : ℝ)| := by
  rcases le_total m n with hmn | hmn
  · have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 n := Finset.Icc_subset_Icc_right hmn
    have hdiff : partialSum f n - partialSum f m
        = ∑ b ∈ Finset.Icc 1 n \ Finset.Icc 1 m, f b := by
      rw [partialSum, partialSum]
      exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
    rw [hdiff]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcard : ((Finset.Icc 1 n \ Finset.Icc 1 m).card : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
      have hsub2 : Finset.Icc 1 n \ Finset.Icc 1 m ⊆ Finset.Icc (m + 1) n := by
        intro b hb
        simp only [Finset.mem_sdiff, Finset.mem_Icc] at hb
        rw [Finset.mem_Icc]
        omega
      have hc : (Finset.Icc 1 n \ Finset.Icc 1 m).card ≤ n - m := by
        refine le_trans (Finset.card_le_card hsub2) ?_
        rw [Nat.card_Icc]
        omega
      have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
        push_cast [Nat.cast_sub hmn]
        ring
      have := (Nat.cast_le (α := ℝ)).mpr hc
      rw [hcast] at this
      refine le_trans this (le_abs_self _)
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun b _ => hf b) ?_
    rw [nsmul_eq_mul, mul_one]
    exact hcard
  · have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 m := Finset.Icc_subset_Icc_right hmn
    have hdiff : partialSum f m - partialSum f n
        = ∑ b ∈ Finset.Icc 1 m \ Finset.Icc 1 n, f b := by
      rw [partialSum, partialSum]
      exact (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
    rw [abs_sub_comm, hdiff, abs_sub_comm ((n : ℝ)) ((m : ℝ))]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hcard : ((Finset.Icc 1 m \ Finset.Icc 1 n).card : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
      have hsub2 : Finset.Icc 1 m \ Finset.Icc 1 n ⊆ Finset.Icc (n + 1) m := by
        intro b hb
        simp only [Finset.mem_sdiff, Finset.mem_Icc] at hb
        rw [Finset.mem_Icc]
        omega
      have hc : (Finset.Icc 1 m \ Finset.Icc 1 n).card ≤ m - n := by
        refine le_trans (Finset.card_le_card hsub2) ?_
        rw [Nat.card_Icc]
        omega
      have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
        push_cast [Nat.cast_sub hmn]
        ring
      have := (Nat.cast_le (α := ℝ)).mpr hc
      rw [hcast] at this
      refine le_trans this (le_abs_self _)
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun b _ => hf b) ?_
    rw [nsmul_eq_mul, mul_one]
    exact hcard

/-- **Window sums at nearby endpoints are close.** -/
theorem abs_windowSum_sub_le (hf : ∀ n, |f n| ≤ 1) (z ℓ z' ℓ' : ℕ) :
    |(partialSum f (z + ℓ) - partialSum f z) - (partialSum f (z' + ℓ') - partialSum f z')|
      ≤ |((z + ℓ : ℕ) : ℝ) - ((z' + ℓ' : ℕ) : ℝ)| + |(z : ℝ) - (z' : ℝ)| := by
  have hsplit : (partialSum f (z + ℓ) - partialSum f z)
      - (partialSum f (z' + ℓ') - partialSum f z')
      = (partialSum f (z + ℓ) - partialSum f (z' + ℓ')) - (partialSum f z - partialSum f z') := by
    ring
  rw [hsplit]
  refine le_trans (abs_sub _ _) ?_
  exact add_le_add (abs_partialSum_sub_le hf _ _) (abs_partialSum_sub_le hf _ _)

/-- **Squares of window sums at nearby endpoints are comparable.** -/
theorem fixedWindowSq_le_of_close (hf : ∀ n, |f n| ≤ 1) (z ℓ z' ℓ' : ℕ) :
    fixedWindowSq f ℓ z
      ≤ 2 * fixedWindowSq f ℓ' z'
        + 2 * (|((z + ℓ : ℕ) : ℝ) - ((z' + ℓ' : ℕ) : ℝ)| + |(z : ℝ) - (z' : ℝ)|) ^ 2 := by
  set u : ℝ := partialSum f (z + ℓ) - partialSum f z with hu
  set v : ℝ := partialSum f (z' + ℓ') - partialSum f z' with hv
  have hdiff := abs_windowSum_sub_le hf z ℓ z' ℓ'
  have hsq : (u - v) ^ 2
      ≤ (|((z + ℓ : ℕ) : ℝ) - ((z' + ℓ' : ℕ) : ℝ)| + |(z : ℝ) - (z' : ℝ)|) ^ 2 := by
    rw [← sq_abs (u - v)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hbase : u ^ 2 ≤ 2 * v ^ 2 + 2 * (u - v) ^ 2 := by nlinarith [sq_nonneg (u - 2 * v)]
  rw [fixedWindowSq, fixedWindowSq, ← hu, ← hv]
  nlinarith [hsq, sq_nonneg (u - v)]

end

end RHTower.Sieve
