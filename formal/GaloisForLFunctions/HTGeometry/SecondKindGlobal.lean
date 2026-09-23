import GaloisForLFunctions.HTGeometry.GlobalTransfer

/-!
# The global transfer for the second kind

The second-kind Duhamel identity has the same shape as the first, with the second-kind kernel root at
`w` driving the inner sums in place of the first-kind one.  The bracket built from the centre data is
*identical*, so the same Gronwall weight governs both recursions.

Since `R₀ = 0` the constant is simply `2P²`, and the two global bounds together transfer boundedness
of the kernel from a single point to the whole plane.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The second-kind Duhamel estimate at strictly lower index.** -/
theorem norm_secondKindC_duhamel_lt_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖secondKindC s (n + 1) w‖
      ≤ ‖secondKindC s (n + 1) z‖
        + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
          (kernelRoot s (fun j => secondKindC s j w) n *
            (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
              + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)) := by
  have h0 : 0 ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    (monicOrtho_inner_self_pos h 0).le
  have hS1 := norm_weightedSum_le h n (fun j => secondKindC s j w) (fun j => secondKindC s j z)
  have hS2 := norm_weightedSum_le h n (fun j => monicOrthoC s j z) (fun j => secondKindC s j w)
  rw [secondKindC_duhamel_lt h (n + 1) z w]
  refine le_trans (norm_sub_le _ _) ?_
  gcongr
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)) ?_
  rw [norm_mul, norm_mul]
  have hnn : (0:ℝ) ≤ ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hnn
  have hq : (0:ℝ) ≤ ‖monicOrthoC s (n + 1) z‖ := norm_nonneg _
  have hr : (0:ℝ) ≤ ‖secondKindC s (n + 1) z‖ := norm_nonneg _
  nlinarith [hS1, hS2, hq, hr, kernelRoot_nonneg s (fun j => secondKindC s j w) n,
    kernelRoot_nonneg s (fun j => secondKindC s j z) n,
    kernelRoot_nonneg s (fun j => monicOrthoC s j z) n]

/-- The squared, divided form of the second-kind strict estimate. -/
theorem normSq_secondKind_duhamel_strict_div_le (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    ‖secondKindC s (n + 1) w‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
      ≤ 2 * (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) *
            ((‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
              + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) := by
  have hpos : 0 < momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) :=
    monicOrtho_inner_self_pos h (n + 1)
  have hle := norm_secondKindC_duhamel_lt_le h n z w
  have hsq : ‖secondKindC s (n + 1) w‖ ^ (2 : ℕ)
      ≤ (‖secondKindC s (n + 1) z‖
          + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => secondKindC s j w) n *
              (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
                + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hexp := sq_add_le_two (‖secondKindC s (n + 1) z‖)
    (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      (kernelRoot s (fun j => secondKindC s j w) n *
        (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
          + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)))
  have hinner :
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
        (kernelRoot s (fun j => secondKindC s j w) n *
          (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n
            + ‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n))) ^ (2 : ℕ)
      ≤ 2 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
          kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) *
          (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
            + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)) := by
    have hab := sq_add_le_two
      (‖monicOrthoC s (n + 1) z‖ * kernelRoot s (fun j => secondKindC s j z) n)
      (‖secondKindC s (n + 1) z‖ * kernelRoot s (fun j => monicOrthoC s j z) n)
    nlinarith [hab, sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      kernelRoot s (fun j => secondKindC s j w) n),
      sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)),
      sq_nonneg (kernelRoot s (fun j => secondKindC s j w) n)]
  have hnum : ‖secondKindC s (n + 1) w‖ ^ (2 : ℕ)
      ≤ 2 * ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ)
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) *
            (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
              + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) *
                kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)) := by
    linarith [hsq, hexp, hinner]
  have hcollect :
      2 * (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) *
            ((‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
              + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
      = (2 * ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ)
          + 4 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
              kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) *
              (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
                + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) *
                  kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)))
        / momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)) := by
    field_simp
  rw [hcollect]
  gcongr

/-- **The Gronwall recursion for the second-kind kernel roots.**  The weight is the same as in the
first-kind recursion, and the constant is `2P²` because `R₀` vanishes. -/
theorem secondKind_kernelRoot_sq_recursion (h : PositiveMomentForm s) (z w : ℂ) {P : ℝ}
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P) (N : ℕ) :
    kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ)
      ≤ 2 * P ^ (2 : ℕ)
        + ∑ n ∈ Finset.range N,
            gronwallWeight s z (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) n *
              kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hsplit : kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ)
      = ∑ n ∈ Finset.range N,
          ‖secondKindC s (n + 1) w‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
        + ‖secondKindC s 0 w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [kernelRoot_sq h, Finset.sum_range_succ']
  have hzero : ‖secondKindC s 0 w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s 0) (monicOrtho s 0) = 0 := by
    rw [secondKindC_zero]
    simp
  have hterm : ∀ n ∈ Finset.range N,
      ‖secondKindC s (n + 1) w‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
        ≤ 2 * (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
          + gronwallWeight s z (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) n *
              kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ) := by
    intro n _
    refine le_trans (normSq_secondKind_duhamel_strict_div_le h n z w) (le_of_eq ?_)
    rw [gronwallWeight]
    ring
  have hcentre : ∑ n ∈ Finset.range N,
      2 * (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) ≤ 2 * P ^ (2 : ℕ) := by
    have hle : ∑ n ∈ Finset.range N,
        (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        ≤ kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
      rw [kernelRoot_sq h, Finset.sum_range_succ']
      have : (0:ℝ) ≤ ‖secondKindC s 0 z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
        div_nonneg (sq_nonneg _) (hpos 0).le
      linarith
    have hKP : kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) ≤ P ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hP N) 2
    rw [← Finset.mul_sum]
    linarith
  rw [hsplit, hzero]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  linarith [hsum, hcentre]

/-- **The global transfer for the second-kind kernel.** -/
theorem secondKind_kernelRoot_sq_global (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P) (N : ℕ) :
    kernelRoot s (fun j => secondKindC s j w) N ^ (2 : ℕ)
      ≤ 2 * P ^ (2 : ℕ) *
          Real.exp (8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            S ^ (2 : ℕ) * P ^ (2 : ℕ)) := by
  set D : ℝ := ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) with hDdef
  have hc : (0:ℝ) ≤ 2 * P ^ (2 : ℕ) := by positivity
  have hb : ∀ n, 0 ≤ gronwallWeight s z D n := fun n => gronwallWeight_nonneg h z D n
  have hgron := discrete_gronwall (A := fun n => kernelRoot s (fun j => secondKindC s j w) n ^ (2 : ℕ))
    (b := gronwallWeight s z D) (c := 2 * P ^ (2 : ℕ)) hb
    (fun M => secondKind_kernelRoot_sq_recursion h z w hP M) N
  have hprod : ∏ n ∈ Finset.range N, (1 + gronwallWeight s z D n)
      ≤ Real.exp (∑ n ∈ Finset.range N, gronwallWeight s z D n) :=
    prod_one_add_le_exp_sum N hb
  have hexp : Real.exp (∑ n ∈ Finset.range N, gronwallWeight s z D n)
      ≤ Real.exp (8 * D ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)) :=
    Real.exp_le_exp.mpr (gronwallWeight_sum_le h z D hS hP N)
  exact le_trans hgron (mul_le_mul_of_nonneg_left (le_trans hprod hexp) hc)

/-- **Boundedness of the kernel transfers to the whole plane.**  If both kernel roots are bounded at
one point, they are bounded at every point.  There is no radius: the Gronwall solution is finite for
every displacement. -/
theorem boundedKernel_global (h : PositiveMomentForm s) {z : ℂ} (hz : BoundedKernel s z) (w : ℂ) :
    BoundedKernel s w := by
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := hz
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set E : ℝ := Real.exp (8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
    S ^ (2 : ℕ) * P ^ (2 : ℕ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hcQ : 0 < 2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    have h1 : (0:ℝ) < 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by positivity
    nlinarith [sq_nonneg S]
  have hcR : 0 < 2 * P ^ (2 : ℕ) := by positivity
  refine ⟨Real.sqrt ((2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) * E),
    Real.sqrt (2 * P ^ (2 : ℕ) * E), Real.sqrt_pos.mpr (by positivity),
    Real.sqrt_pos.mpr (by positivity), fun N => ?_, fun N => ?_⟩
  · rw [← Real.sqrt_sq (kernelRoot_nonneg s (fun j => monicOrthoC s j w) N)]
    exact Real.sqrt_le_sqrt (kernelRoot_sq_global h z w hS hP N)
  · rw [← Real.sqrt_sq (kernelRoot_nonneg s (fun j => secondKindC s j w) N)]
    exact Real.sqrt_le_sqrt (secondKind_kernelRoot_sq_global h z w hS hP N)

end HTGeometry
