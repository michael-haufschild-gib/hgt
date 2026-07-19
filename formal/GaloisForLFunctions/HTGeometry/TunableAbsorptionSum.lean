import GaloisForLFunctions.HTGeometry.TunableAbsorptionStep

/-!
# The tunable absorption estimate

Summing the pointwise step over `n ≤ N` and evaluating the three resulting sums with `kernelRoot_sq`
gives the absorption inequality with leading constant `1 + ε` in place of the fixed `2`.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The absorption estimate with tunable leading constant.** -/
theorem kernelRoot_sq_le_absorption_tunable (h : PositiveMomentForm s) (N : ℕ) (z w : ℂ)
    {e : ℝ} (he : 0 < e) :
    kernelRoot s (fun j => monicOrthoC s j w) N ^ 2
      ≤ (1 + e) * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2
        + 4 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
          kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
          kernelRoot s (fun j => secondKindC s j z) N ^ 2 := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hshape : ∀ n ∈ Finset.range (N + 1),
      ‖monicOrthoC s n w‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ ((1 + e) + 2 * (1 + e⁻¹) *
              (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
              kernelRoot s (fun j => secondKindC s j z) N ^ 2) *
            (‖monicOrthoC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))
          + (2 * (1 + e⁻¹) *
              (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
              kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) *
            (‖secondKindC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n)) := by
    intro n hn'
    have hn : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
    refine le_trans (normSq_duhamel_div_le_tunable h hn z w he) (le_of_eq ?_)
    have hne : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 := (hpos n).ne'
    field_simp
    ring
  calc kernelRoot s (fun j => monicOrthoC s j w) N ^ 2
      = ∑ n ∈ Finset.range (N + 1),
          ‖monicOrthoC s n w‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n) :=
        kernelRoot_sq h _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (((1 + e) + 2 * (1 + e⁻¹) *
                (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
                kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
                kernelRoot s (fun j => secondKindC s j z) N ^ 2) *
              (‖monicOrthoC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))
            + (2 * (1 + e⁻¹) *
                (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
                kernelRoot s (fun j => monicOrthoC s j w) N ^ 2 *
                kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) *
              (‖secondKindC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))) :=
        Finset.sum_le_sum hshape
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← kernelRoot_sq h (fun j => monicOrthoC s j z) N,
          ← kernelRoot_sq h (fun j => secondKindC s j z) N]
        ring

end HTGeometry
