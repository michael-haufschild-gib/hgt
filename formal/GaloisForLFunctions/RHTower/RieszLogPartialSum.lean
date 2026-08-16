import GaloisForLFunctions.RHTower.RieszMellinPair

/-!
# The Riesz mean as a logarithmic average of partial sums

The second-order Riesz mean carries the weight `log(N/n)`.  Telescoping that weight,

```text
log N - log n = ∑_{m=n}^{N-1} ( log(m+1) - log m ) ,
```

and exchanging the two finite sums turns the weighted sum of coefficients into a weighted sum of
*partial* sums:

```text
∑_{n < N} aₙ ( log N - log(n+1) ) = ∑_{m < N} ( log(m+1) - log m ) · ∑_{n < m} aₙ .
```

The weights are nonnegative and add up to `log N`, so a uniform bound on the partial sums transfers
to the Riesz mean with the factor `log N`.  This is the discrete half of the Riesz-mean method,
requiring no contour integral; the analytic half is the kernel `1/w²` and its Mellin pair.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RHTower

/-- The logarithmic increments telescope to `log N`. -/
theorem sum_log_increment (N : ℕ) :
    ∑ m ∈ Finset.range N, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) = Real.log (N : ℝ) := by
  have h : ∑ m ∈ Finset.range N, (Real.log ((m : ℕ) + 1 : ℕ) - Real.log ((m : ℕ) : ℕ))
      = Real.log ((N : ℕ) : ℝ) - Real.log ((0 : ℕ) : ℝ) :=
    Finset.sum_range_sub (fun m : ℕ => Real.log ((m : ℕ) : ℝ)) N
  simpa using h

/-- Each logarithmic increment is nonnegative. -/
theorem log_increment_nonneg (m : ℕ) :
    0 ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
      Real.log_le_log hm0 (by linarith)
    linarith

/-- **The Riesz mean is a logarithmic average of the partial sums.** -/
theorem rieszLogSum_eq_sum_partialSum (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))
      = ∑ m ∈ Finset.range N,
          ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
            * (∑ n ∈ Finset.range m, a n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsplit : ∑ n ∈ Finset.range (N + 1),
          a n * ((Real.log ((N + 1 : ℕ) : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))
        = (∑ n ∈ Finset.range N,
            a n * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
          + ((Real.log ((N : ℝ) + 1) : ℂ) - (Real.log (N : ℝ) : ℂ))
            * (∑ n ∈ Finset.range N, a n) := by
      rw [Finset.sum_range_succ]
      have hlast : a N * ((Real.log ((N + 1 : ℕ) : ℝ) : ℂ)
          - (Real.log ((N : ℝ) + 1) : ℂ)) = 0 := by
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        ring
      have hterm : ∀ n ∈ Finset.range N,
          a n * ((Real.log ((N + 1 : ℕ) : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))
            = a n * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))
              + ((Real.log ((N : ℝ) + 1) : ℂ) - (Real.log (N : ℝ) : ℂ)) * a n := by
        intro n _
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hlast ⊢
      rw [hlast, add_zero]
    rw [hsplit, ih, Finset.sum_range_succ]

/-- **A uniform bound on the partial sums bounds the Riesz mean by `log N` times that bound.** -/
theorem norm_rieszLogSum_le {a : ℕ → ℂ} {B : ℝ} {N : ℕ}
    (h : ∀ m ∈ Finset.range N, ‖∑ n ∈ Finset.range m, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n * ((Real.log (N : ℝ) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))‖
      ≤ B * Real.log (N : ℝ) := by
  rw [rieszLogSum_eq_sum_partialSum]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ Finset.range N,
      ‖((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
        * (∑ n ∈ Finset.range m, a n)‖
        ≤ B * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
    intro m hm
    have hw : ((Real.log ((m : ℝ) + 1) : ℂ) - (Real.log (m : ℝ) : ℂ))
        = ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (log_increment_nonneg m)]
    calc (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * ‖∑ n ∈ Finset.range m, a n‖
        ≤ (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * B :=
          mul_le_mul_of_nonneg_left (h m hm) (log_increment_nonneg m)
      _ = B * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, sum_log_increment]

end GaloisForLFunctions.RHTower

end
