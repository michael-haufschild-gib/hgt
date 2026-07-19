import GaloisForLFunctions.HTGeometry.DuhamelStrict

/-!
# The strictly-indexed Duhamel estimate

Taking norms in `monicOrthoC_duhamel_lt` at index `n+1`, whose inner sums run over `range (n+1)`,
bounds `‖Q_{n+1}(w)‖` in terms of `kernelRoot … w n` — strictly below the index on the left.

Stating it at `n+1` rather than `n` avoids truncated subtraction: the sum `∑_{j < n+1}` is exactly
the range `kernelRoot … n` sums over.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The Duhamel estimate at strictly lower index.** -/
theorem norm_monicOrthoC_duhamel_lt_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖monicOrthoC s (n + 1) w‖
      ≤ ‖monicOrthoC s (n + 1) z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => monicOrthoC s j w) n *
            (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  have hS1 := norm_weightedSum_le h n (fun j => monicOrthoC s j w) (fun j => secondKindC s j z)
  have hS2 := norm_weightedSum_le h n (fun j => monicOrthoC s j w) (fun j => monicOrthoC s j z)
  rw [monicOrthoC_duhamel_lt h (n + 1) z w]
  refine le_trans (norm_sub_le _ _) ?_
  gcongr
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)) ?_
  rw [norm_mul, norm_mul]
  have hnn : (0:ℝ) ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have hq : (0:ℝ) ≤ ‖monicOrthoC s (n + 1) z‖ := norm_nonneg _
  have hr : (0:ℝ) ≤ ‖secondKindC s (n + 1) z‖ := norm_nonneg _
  nlinarith [hS1, hS2, hq, hr, kernelRoot_nonneg s (fun j => monicOrthoC s j w) n,
    kernelRoot_nonneg s (fun j => secondKindC s j z) n,
    kernelRoot_nonneg s (fun j => monicOrthoC s j z) n]

/-- **The squared, divided form of the strict estimate.**  The kernel root on the right is still at
index `n`, so this is a summand of a recursion rather than of an absorption. -/
theorem normSq_duhamel_strict_div_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖monicOrthoC s (n + 1) w‖ ^ 2 /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
      ≤ 2 * (‖monicOrthoC s (n + 1) z‖ ^ 2 /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => monicOrthoC s j w) n ^ 2 *
            ((‖monicOrthoC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) n ^ 2
              + ‖secondKindC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) n ^ 2) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) := by
  have hpos : 0 < momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) :=
    monicOrtho_inner_self_pos h (n + 1)
  have hle := norm_monicOrthoC_duhamel_lt_le h n z w
  have hsq : ‖monicOrthoC s (n + 1) w‖ ^ 2
      ≤ (‖monicOrthoC s (n + 1) z‖
          + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => monicOrthoC s j w) n *
              (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
                + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hexp := sq_add_le_two (‖monicOrthoC s (n + 1) z‖)
    (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      (kernelRoot s (fun j => monicOrthoC s j w) n *
        (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
          + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)))
  have hinner :
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
        (kernelRoot s (fun j => monicOrthoC s j w) n *
          (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
            + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n))) ^ 2
      ≤ 2 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
          kernelRoot s (fun j => monicOrthoC s j w) n ^ 2 *
          (‖monicOrthoC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) n ^ 2
            + ‖secondKindC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) n ^ 2) := by
    have hab := sq_add_le_two
      (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n)
      (‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)
    nlinarith [hab, sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      kernelRoot s (fun j => monicOrthoC s j w) n),
      sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)),
      sq_nonneg (kernelRoot s (fun j => monicOrthoC s j w) n)]
  have hnum : ‖monicOrthoC s (n + 1) w‖ ^ 2
      ≤ 2 * ‖monicOrthoC s (n + 1) z‖ ^ 2
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => monicOrthoC s j w) n ^ 2 *
            (‖monicOrthoC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) n ^ 2
              + ‖secondKindC s (n + 1) z‖ ^ 2 *
                kernelRoot s (fun j => monicOrthoC s j z) n ^ 2) := by
    linarith [hsq, hexp, hinner]
  have hcollect :
      2 * (‖monicOrthoC s (n + 1) z‖ ^ 2 /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => monicOrthoC s j w) n ^ 2 *
            ((‖monicOrthoC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) n ^ 2
              + ‖secondKindC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) n ^ 2) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
      = (2 * ‖monicOrthoC s (n + 1) z‖ ^ 2
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => monicOrthoC s j w) n ^ 2 *
              (‖monicOrthoC s (n + 1) z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) n ^ 2
                + ‖secondKindC s (n + 1) z‖ ^ 2 *
                  kernelRoot s (fun j => monicOrthoC s j z) n ^ 2))
        / momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
    field_simp
  rw [hcollect]
  gcongr

end HTGeometry
