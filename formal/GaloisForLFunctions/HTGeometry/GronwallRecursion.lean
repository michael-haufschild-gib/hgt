import GaloisForLFunctions.HTGeometry.DuhamelStrictNorm

/-!
# The kernel roots satisfy a Gronwall recursion

Summing the strictly-indexed estimate over `n + 1 ≤ N` and splitting off the `n = 0` term puts the
partial kernel roots into the form `A N ≤ c + ∑_{n<N} bₙ Aₙ`, with `c` independent of `N` once the
centre kernels are uniformly bounded, and `bₙ` independent of `N` throughout.

No absorption occurs: every `A` on the right has index strictly below `N`.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The Gronwall weight at step `n`, built from the data at the centre. -/
noncomputable def gronwallWeight (s : ℕ → ℝ) (z : ℂ) (D : ℝ) (n : ℕ) : ℝ :=
  4 * D ^ (2 : ℕ) *
    ((‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => secondKindC s j z) n ^ (2 : ℕ)
      + ‖secondKindC s (n + 1) z‖ ^ (2 : ℕ) * kernelRoot s (fun j => monicOrthoC s j z) n ^ (2 : ℕ)) /
      momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))

theorem gronwallWeight_nonneg (h : PositiveMomentForm s) (z : ℂ) (D : ℝ) (n : ℕ) :
    0 ≤ gronwallWeight s z D n := by
  have hpos := monicOrtho_inner_self_pos h (n + 1)
  rw [gronwallWeight]
  positivity

theorem monicOrthoC_zero_eq_one (s : ℕ → ℝ) (w : ℂ) : monicOrthoC s 0 w = 1 := by
  rw [monicOrthoC, monicOrtho_zero]
  simp

/-- **The Gronwall recursion for the partial kernel roots.** -/
theorem kernelRoot_sq_recursion (h : PositiveMomentForm s) (z w : ℂ) {S : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S) (N : ℕ) :
    kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ)
      ≤ (2 * S ^ (2 : ℕ) + 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))
        + ∑ n ∈ Finset.range N,
            gronwallWeight s z (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) n *
              kernelRoot s (fun j => monicOrthoC s j w) n ^ (2 : ℕ) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hsplit : kernelRoot s (fun j => monicOrthoC s j w) N ^ (2 : ℕ)
      = ∑ n ∈ Finset.range N,
          ‖monicOrthoC s (n + 1) w‖ ^ (2 : ℕ) /
            momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
        + ‖monicOrthoC s 0 w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [kernelRoot_sq h, Finset.sum_range_succ']
  have hzero : ‖monicOrthoC s 0 w‖ ^ (2 : ℕ) / momentInner s (monicOrtho s 0) (monicOrtho s 0)
      = 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0) := by
    rw [monicOrthoC_zero_eq_one]
    simp
  have hterm : ∀ n ∈ Finset.range N,
      ‖monicOrthoC s (n + 1) w‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))
        ≤ 2 * (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
              momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
          + gronwallWeight s z (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) n *
              kernelRoot s (fun j => monicOrthoC s j w) n ^ (2 : ℕ) := by
    intro n _
    refine le_trans (normSq_duhamel_strict_div_le h n z w) (le_of_eq ?_)
    rw [gronwallWeight]
    ring
  have hcentre : ∑ n ∈ Finset.range N,
      2 * (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
        momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1))) ≤ 2 * S ^ (2 : ℕ) := by
    have hle : ∑ n ∈ Finset.range N,
        (‖monicOrthoC s (n + 1) z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s (n + 1)) (monicOrtho s (n + 1)))
        ≤ kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) := by
      rw [kernelRoot_sq h, Finset.sum_range_succ']
      have : (0:ℝ) ≤ ‖monicOrthoC s 0 z‖ ^ (2 : ℕ) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
        div_nonneg (sq_nonneg _) (hpos 0).le
      linarith
    have hKS : kernelRoot s (fun j => monicOrthoC s j z) N ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
      pow_le_pow_left₀ (kernelRoot_nonneg _ _ _) (hS N) 2
    rw [← Finset.mul_sum]
    linarith
  rw [hsplit, hzero]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  linarith [hsum, hcentre]

end HTGeometry
