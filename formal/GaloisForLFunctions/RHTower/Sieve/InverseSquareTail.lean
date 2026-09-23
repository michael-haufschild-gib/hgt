import GaloisForLFunctions.RHTower.Sieve.ReciprocalFibre

/-!
# The tail of the inverse-square series

`∑_{d > R} d^{-2} ≤ 1/R`, by the telescoping comparison `d^{-2} ≤ (d-1)^{-1} - d^{-1}`.

The partial sums are handled by induction with the sharper invariant `1/R - 1/(N+R)`, which makes
the inductive step the single inequality `(N+R)(N+R+1) ≤ (N+R+1)^(2 : ℕ)`.  Passing to the series then
only needs that every finite subset of the index set sits inside an initial segment.
-/

namespace RHTower.Sieve

open Finset

/-- Partial sums of the shifted inverse squares, with the telescoping invariant. -/
theorem sum_range_inv_sq_shift_le (R N : ℕ) (hR : 1 ≤ R) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ)
      ≤ 1 / (R : ℝ) - 1 / ((N : ℝ) + R) := by
  have hRR : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hNR : (0 : ℝ) < (N : ℝ) + R := by
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have hNR1 : (0 : ℝ) < (N : ℝ) + R + 1 := by linarith
      have hstep : (1 : ℝ) / ((N : ℝ) + R + 1) ^ (2 : ℕ)
          ≤ 1 / ((N : ℝ) + R) - 1 / ((N : ℝ) + R + 1) := by
        have hprod : (0 : ℝ) < ((N : ℝ) + R) * ((N : ℝ) + R + 1) := by positivity
        have hkey : (1 : ℝ) / ((N : ℝ) + R) - 1 / ((N : ℝ) + R + 1)
            = 1 / (((N : ℝ) + R) * ((N : ℝ) + R + 1)) := by
          field_simp
          ring
        rw [hkey, div_le_div_iff₀ (by positivity) hprod]
        nlinarith [hNR, hNR1]
      have hcast : ((N + 1 : ℕ) : ℝ) + R = (N : ℝ) + R + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, hcast]
      linarith [ih, hstep]

/-- The shifted inverse squares are summable. -/
theorem summable_inv_sq_shift (R : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ)) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) (R + 1)).2 hbase
  refine hshift.congr ?_
  intro n
  push_cast
  ring_nf

/-- **Inverse-square tail.**  Beyond `R` the series is at most `1/R`. -/
theorem tsum_inv_sq_shift_le {R : ℕ} (hR : 1 ≤ R) :
    ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ) ≤ 1 / (R : ℝ) := by
  refine (summable_inv_sq_shift R).tsum_le_of_sum_le ?_
  intro s
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N := ⟨s.sup id + 1, fun x hx =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))⟩
  have hsub : ∑ n ∈ s, (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ)
      ≤ ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + R + 1) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hN (fun n _ _ => by positivity)
  have hbound := sum_range_inv_sq_shift_le R N hR
  have hpos : (0 : ℝ) < (N : ℝ) + R := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have : (0 : ℝ) < 1 / ((N : ℝ) + R) := by positivity
  linarith

end RHTower.Sieve
