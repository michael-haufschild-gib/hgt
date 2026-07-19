import GaloisForLFunctions.HTGeometry.ProdOneAddBound

/-!
# The tunable transfer for the second-kind kernel

`BoundedKernel` constrains both kernel roots, so a chain must carry both bounds.  The second-kind
estimates of `ComplexSecondKind` have the same shape as the first-kind ones, with `secondKindC` in
place of `monicOrthoC` on the left, so the tunable versions mirror links 131--135 exactly.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The squared second-kind Duhamel estimate with tunable leading constant. -/
theorem normSq_secondKindC_duhamel_le_tunable (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) {e : ℝ} (he : 0 < e) :
    ‖secondKindC s n w‖ ^ 2
      ≤ (1 + e) * ‖secondKindC s n z‖ ^ 2
        + (1 + e⁻¹) *
          (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => secondKindC s j w) N *
              (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
                + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2 := by
  have hle := norm_secondKindC_duhamel_le_of_le h hn z w
  have hsq : ‖secondKindC s n w‖ ^ 2
      ≤ (‖secondKindC s n z‖
          + ‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
            (kernelRoot s (fun j => secondKindC s j w) N *
              (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
                + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  exact le_trans hsq (sq_add_le_tunable he)

/-- The pointwise summand bound for the second kind. -/
theorem normSq_secondKind_div_le_tunable (h : PositiveMomentForm s) {N n : ℕ} (hn : n ≤ N)
    (z w : ℂ) {e : ℝ} (he : 0 < e) :
    ‖secondKindC s n w‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n)
      ≤ (1 + e) * (‖secondKindC s n z‖ ^ 2 /
            momentInner s (monicOrtho s n) (monicOrtho s n))
        + 2 * (1 + e⁻¹) *
            (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
            ((‖monicOrthoC s n z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ 2
              + ‖secondKindC s n z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) /
              momentInner s (monicOrtho s n) (monicOrtho s n)) := by
  have hpos : 0 < momentInner s (monicOrtho s n) (monicOrtho s n) :=
    monicOrtho_inner_self_pos h n
  have hsq := normSq_secondKindC_duhamel_le_tunable h hn z w he
  have hinner :
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
        (kernelRoot s (fun j => secondKindC s j w) N *
          (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N
            + ‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N))) ^ 2
      ≤ 2 * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
          kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
          (‖monicOrthoC s n z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ 2
            + ‖secondKindC s n z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) := by
    have hab := sq_add_le_two (‖monicOrthoC s n z‖ * kernelRoot s (fun j => secondKindC s j z) N)
      (‖secondKindC s n z‖ * kernelRoot s (fun j => monicOrthoC s j z) N)
    nlinarith [hab, sq_nonneg (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0) *
      kernelRoot s (fun j => secondKindC s j w) N), sq_nonneg (‖w - z‖ *
      momentInner s (monicOrtho s 0) (monicOrtho s 0)),
      sq_nonneg (kernelRoot s (fun j => secondKindC s j w) N)]
  have hnum : ‖secondKindC s n w‖ ^ 2
      ≤ (1 + e) * ‖secondKindC s n z‖ ^ 2
        + 2 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
            (‖monicOrthoC s n z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ 2
              + ‖secondKindC s n z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) := by
    have hepos : (0:ℝ) < 1 + e⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinner hepos.le
    linarith [hsq, hmul]
  have hcollect :
      (1 + e) * (‖secondKindC s n z‖ ^ 2 /
            momentInner s (monicOrtho s n) (monicOrtho s n))
        + 2 * (1 + e⁻¹) *
            (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
            kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
            ((‖monicOrthoC s n z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ 2
              + ‖secondKindC s n z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) /
              momentInner s (monicOrtho s n) (monicOrtho s n))
      = ((1 + e) * ‖secondKindC s n z‖ ^ 2
          + 2 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
              (‖monicOrthoC s n z‖ ^ 2 * kernelRoot s (fun j => secondKindC s j z) N ^ 2
                + ‖secondKindC s n z‖ ^ 2 * kernelRoot s (fun j => monicOrthoC s j z) N ^ 2))
        / momentInner s (monicOrtho s n) (monicOrtho s n) := by
    field_simp
  rw [hcollect]
  gcongr

/-- **The second-kind absorption with tunable leading constant.** -/
theorem kernelRootR_sq_le_absorption_tunable (h : PositiveMomentForm s) (N : ℕ) (z w : ℂ)
    {e : ℝ} (he : 0 < e) :
    kernelRoot s (fun j => secondKindC s j w) N ^ 2
      ≤ (1 + e) * kernelRoot s (fun j => secondKindC s j z) N ^ 2
        + 4 * (1 + e⁻¹) * (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
          kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
          kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
          kernelRoot s (fun j => secondKindC s j z) N ^ 2 := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hshape : ∀ n ∈ Finset.range (N + 1),
      ‖secondKindC s n w‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n)
        ≤ (2 * (1 + e⁻¹) *
              (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
              kernelRoot s (fun j => secondKindC s j z) N ^ 2) *
            (‖monicOrthoC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))
          + ((1 + e) + 2 * (1 + e⁻¹) *
              (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
              kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
              kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) *
            (‖secondKindC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n)) := by
    intro n hn'
    have hn : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
    refine le_trans (normSq_secondKind_div_le_tunable h hn z w he) (le_of_eq ?_)
    have hne : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 := (hpos n).ne'
    field_simp
    ring
  calc kernelRoot s (fun j => secondKindC s j w) N ^ 2
      = ∑ n ∈ Finset.range (N + 1),
          ‖secondKindC s n w‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n) :=
        kernelRoot_sq h _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          ((2 * (1 + e⁻¹) *
                (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
                kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
                kernelRoot s (fun j => secondKindC s j z) N ^ 2) *
              (‖monicOrthoC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))
            + ((1 + e) + 2 * (1 + e⁻¹) *
                (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
                kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
                kernelRoot s (fun j => monicOrthoC s j z) N ^ 2) *
              (‖secondKindC s n z‖ ^ 2 / momentInner s (monicOrtho s n) (monicOrtho s n))) :=
        Finset.sum_le_sum hshape
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← kernelRoot_sq h (fun j => monicOrthoC s j z) N,
          ← kernelRoot_sq h (fun j => secondKindC s j z) N]
        ring

/-- **The second-kind propagate step.** -/
theorem kernelRootR_sq_le_tunable (h : PositiveMomentForm s) (z w : ℂ) {S P delta e : ℝ}
    (he : 0 < e)
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j z) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j z) N ≤ P)
    (hsmall : 4 * (1 + e⁻¹) *
      (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 * S ^ 2 * P ^ 2 ≤ delta)
    (N : ℕ) :
    kernelRoot s (fun j => secondKindC s j w) N ^ 2 * (1 - delta) ≤ (1 + e) * P ^ 2 := by
  have habs := kernelRootR_sq_le_absorption_tunable h N z w he
  have hKz0 : 0 ≤ kernelRoot s (fun j => monicOrthoC s j z) N := kernelRoot_nonneg _ _ _
  have hPz0 : 0 ≤ kernelRoot s (fun j => secondKindC s j z) N := kernelRoot_nonneg _ _ _
  have hKzS : kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ hKz0 (hS N) 2
  have hPzP : kernelRoot s (fun j => secondKindC s j z) N ^ 2 ≤ P ^ 2 :=
    pow_le_pow_left₀ hPz0 (hP N) 2
  have hdisp : 4 * (1 + e⁻¹) *
        (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
        kernelRoot s (fun j => secondKindC s j w) N ^ 2 *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
        kernelRoot s (fun j => secondKindC s j z) N ^ 2
      ≤ delta * kernelRoot s (fun j => secondKindC s j w) N ^ 2 := by
    have hstep : 4 * (1 + e⁻¹) *
        (‖w - z‖ * momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 *
        kernelRoot s (fun j => monicOrthoC s j z) N ^ 2 *
        kernelRoot s (fun j => secondKindC s j z) N ^ 2 ≤ delta := by
      refine le_trans ?_ hsmall
      gcongr
    have hmul := mul_le_mul_of_nonneg_right hstep
      (sq_nonneg (kernelRoot s (fun j => secondKindC s j w) N))
    nlinarith [hmul]
  have h1e : (1 + e) * kernelRoot s (fun j => secondKindC s j z) N ^ 2 ≤ (1 + e) * P ^ 2 := by
    have hpe : (0:ℝ) < 1 + e := by linarith
    exact mul_le_mul_of_nonneg_left hPzP hpe.le
  linarith [habs, hdisp, h1e]

end HTGeometry
