import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Cancelling a linear factor from an identity on a disc

An identity `(z − r)·F z = (z − r)·G z` holding throughout a disc gives `F = G` there: off `r` the
factor cancels, and at `r` itself continuity closes the gap, a punctured disc having `r` in its
closure.

This is the cancellation step of an induction that peels linear factors one at a time, which is how
divisibility by a product of linear factors is established without any order-of-vanishing
bookkeeping.

* `HTGeometry.eqOn_of_sub_mul_eqOn`.
-/

open Metric

namespace HTGeometry

/-- **A linear factor cancels from an identity on a disc.** -/
theorem eqOn_of_sub_mul_eqOn {c : ℂ} {R : ℝ} {r : ℂ} {F G : ℂ → ℂ}
    (hF : ContinuousOn F (ball c R)) (hG : ContinuousOn G (ball c R))
    (h : ∀ z ∈ ball c R, (z - r) * F z = (z - r) * G z) :
    ∀ z ∈ ball c R, F z = G z := by
  intro z hz
  by_cases hzr : z = r
  · -- approach `r` from inside the disc
    subst hzr
    have hrc : ‖z - c‖ < R := by
      have := mem_ball.1 hz
      rwa [Complex.dist_eq] at this
    set δ : ℝ := (R - ‖z - c‖) / 2 with hδ
    have hδ0 : 0 < δ := by
      rw [hδ]
      linarith
    have hmem : ∀ n : ℕ, z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ ball c R := by
      intro n
      have hpos : (0 : ℝ) < δ / ((n : ℝ) + 1) := by positivity
      have hle : δ / ((n : ℝ) + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      rw [mem_ball, Complex.dist_eq]
      have hsplit : z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) - c
          = (z - c) + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) := by ring
      rw [hsplit]
      have hb := norm_add_le (z - c) (((δ / ((n : ℝ) + 1) : ℝ) : ℂ))
      have hnorm : ‖((δ / ((n : ℝ) + 1) : ℝ) : ℂ)‖ = δ / ((n : ℝ) + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      rw [hnorm] at hb
      have : ‖z - c‖ + δ < R := by
        rw [hδ]
        linarith
      linarith
    have hne : ∀ n : ℕ, z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ z := by
      intro n hcon
      have hzero : ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) = 0 := by
        have := congrArg (fun w => w - z) hcon
        simpa using this
      have hpos : (0 : ℝ) < δ / ((n : ℝ) + 1) := by positivity
      rw [Complex.ofReal_eq_zero] at hzero
      linarith
    have heq : ∀ n : ℕ, F (z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ))
        = G (z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ)) := by
      intro n
      have hsub : z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ) - z ≠ 0 := sub_ne_zero.2 (hne n)
      have hid := h _ (hmem n)
      exact mul_left_cancel₀ hsub hid
    -- pass to the limit
    have htend : Filter.Tendsto (fun n : ℕ => z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhds z) := by
      have hzero : Filter.Tendsto (fun n : ℕ => ((δ / ((n : ℝ) + 1) : ℝ) : ℂ))
          Filter.atTop (nhds 0) := by
        have hr : Filter.Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
          have hbase : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have := hbase.const_mul δ
          simpa [div_eq_mul_inv] using this
        exact (Complex.continuous_ofReal.tendsto 0).comp hr
      simpa using Filter.Tendsto.const_add z hzero
    have hFt : Filter.Tendsto (fun n : ℕ => F (z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ)))
        Filter.atTop (nhds (F z)) :=
      ((hF z hz).tendsto).comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        htend (Filter.Eventually.of_forall hmem))
    have hGt : Filter.Tendsto (fun n : ℕ => G (z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ)))
        Filter.atTop (nhds (G z)) :=
      ((hG z hz).tendsto).comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        htend (Filter.Eventually.of_forall hmem))
    have hFG : Filter.Tendsto (fun n : ℕ => F (z + ((δ / ((n : ℝ) + 1) : ℝ) : ℂ)))
        Filter.atTop (nhds (G z)) := by
      refine hGt.congr fun n => (heq n).symm
    exact tendsto_nhds_unique hFt hFG
  · exact mul_left_cancel₀ (sub_ne_zero.2 hzr) (h z hz)

end HTGeometry
