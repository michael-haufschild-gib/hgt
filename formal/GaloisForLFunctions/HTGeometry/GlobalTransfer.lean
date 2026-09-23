import GaloisForLFunctions.HTGeometry.GronwallRecursion

/-!
# The global transfer

Solving the Gronwall recursion bounds the partial kernel roots at `w` by a constant times
`exp` of the accumulated weight, and the accumulated weight is at most `8D²S²P²` — finite for every
displacement.

So a uniform bound at one point gives a uniform bound at *every* point, with no radius and no
chaining.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The accumulated Gronwall weight is bounded by the centre data. -/
theorem gronwallWeight_sum_le (h : PositiveMomentForm s) (z : ℂ) (D : ℝ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P) (N : ℕ) :
    ∑ n ∈ Finset.range N, gronwallWeight s z D n ≤ 8 * D ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hD : (0:ℝ) ≤ 4 * D ^ (2 : ℕ) := by positivity
  -- termwise: replace the centre kernel roots by their bounds
  have hterm : ∀ n ∈ Finset.range N,
      gronwallWeight s z D n
        ≤ 4 * D ^ (2 : ℕ) *
          ((‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * P ^ (2 : ℕ)
            + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * S ^ (2 : ℕ)) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) := by
    intro n _
    rw [gronwallWeight]
    have hKz : kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hS n) 2
    have hPz : kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ) ≤ P ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hP n) 2
    have hnum :
        ‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
          + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)
        ≤ ‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * P ^ (2 : ℕ)
          + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * S ^ (2 : ℕ) := by
      have h1 := mul_le_mul_of_nonneg_left hPz (sq_nonneg ‖monicOrthoC s (n + 1) z‖)
      have h2 := mul_le_mul_of_nonneg_left hKz (sq_nonneg ‖secondKindC s (n + 1) z‖)
      linarith
    have hinv : (0:ℝ) ≤ (momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))⁻¹ :=
      inv_nonneg.mpr (hpos (n + 1)).le
    have hdiv := mul_le_mul_of_nonneg_right hnum hinv
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hdiv hD
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- split the sum and recognise the two kernel roots
  have hsplitQ : ∑ n ∈ Finset.range N,
      (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
      ≤ S ^ (2 : ℕ) := by
    have hle : ∑ n ∈ Finset.range N,
        (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        ≤ kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) := by
      rw [kernelRoot_sq h, Finset.sum_range_succ']
      have := div_nonneg (sq_nonneg ‖monicOrthoC s 0 z‖) (hpos 0).le
      linarith
    exact le_trans hle (pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hS N) 2)
  have hsplitR : ∑ n ∈ Finset.range N,
      (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
      ≤ P ^ (2 : ℕ) := by
    have hle : ∑ n ∈ Finset.range N,
        (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        ≤ kernelRoot s (fun j => secondKindC s j z) N ^ (2 : ℕ) := by
      rw [kernelRoot_sq h, Finset.sum_range_succ']
      have := div_nonneg (sq_nonneg ‖secondKindC s 0 z‖) (hpos 0).le
      linarith
    exact le_trans hle (pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hP N) 2)
  have hrewrite : ∑ n ∈ Finset.range N,
      4 * D ^ (2 : ℕ) *
        ((‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * P ^ (2 : ℕ)
          + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * S ^ (2 : ℕ)) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
      = 4 * D ^ (2 : ℕ) * P ^ (2 : ℕ) * ∑ n ∈ Finset.range N,
          (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        + 4 * D ^ (2 : ℕ) * S ^ (2 : ℕ) * ∑ n ∈ Finset.range N,
          (‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  rw [hrewrite]
  have hP2 : (0:ℝ) ≤ 4 * D ^ (2 : ℕ) * P ^ (2 : ℕ) := by positivity
  have hS2 : (0:ℝ) ≤ 4 * D ^ (2 : ℕ) * S ^ (2 : ℕ) := by positivity
  nlinarith [hsplitQ, hsplitR, hP2, hS2]

/-- **The global transfer for the first-kind kernel.**  A uniform bound on both kernel roots at a
single point bounds the first-kind kernel root at *every* point, with no restriction on the
displacement: the recursion is solved by the discrete Gronwall inequality, and the accumulated
weight is finite for every `w`. -/
theorem kernelRoot_sq_global (h : PositiveMomentForm s) (z w : ℂ) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P) (N : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ)
      ≤ (2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) *
          Real.exp (8 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ (2 : ℕ) *
            S ^ (2 : ℕ) * P ^ (2 : ℕ)) := by
  have h0 : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  set D : ℝ := ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) with hDdef
  have hc : (0:ℝ) ≤ 2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    have h1 : (0:ℝ) ≤ 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
      div_nonneg zero_le_one h0.le
    nlinarith [sq_nonneg S]
  have hb : ∀ n, 0 ≤ gronwallWeight s z D n := fun n => gronwallWeight_nonneg h z D n
  have hgron := discrete_gronwall (A := fun n => kernelRoot s (fun j => monicOrthoC s j w) n ^ (2 : ℕ))
    (b := gronwallWeight s z D)
    (c := 2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) hb
    (fun M => kernelRoot_sq_recursion h z w hS M) N
  have hprod : ∏ n ∈ Finset.range N, (1 + gronwallWeight s z D n)
      ≤ Real.exp (∑ n ∈ Finset.range N, gronwallWeight s z D n) :=
    prod_one_add_le_exp_sum N hb
  have hsum : ∑ n ∈ Finset.range N, gronwallWeight s z D n ≤ 8 * D ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ) :=
    gronwallWeight_sum_le h z D hS hP N
  have hexp : Real.exp (∑ n ∈ Finset.range N, gronwallWeight s z D n)
      ≤ Real.exp (8 * D ^ (2 : ℕ) * S ^ (2 : ℕ) * P ^ (2 : ℕ)) := Real.exp_le_exp.mpr hsum
  exact le_trans hgron
    (mul_le_mul_of_nonneg_left (le_trans hprod hexp) hc)

end HTGeometry
