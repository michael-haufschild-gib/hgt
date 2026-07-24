import GaloisForLFunctions.RHTower.PerronEdgeBounds

/-!
# A low-height bound for `ζ′/ζ` left of the line `Re s = 1`

Inside the zero-free margin `[1-δ₀,1)×[-9,9]`, the split
`ζ′/ζ = Z′/Z - (s-1)⁻¹` with `Z = (s-1)ζ` entire and zero-free on the
compact closure bounds `‖ζ′/ζ(s)‖ ≤ M₀ + (1-Re s)⁻¹` for a single
constant `M₀` — the pole contributes the explicit `(1-Re s)⁻¹` and the
regular part is bounded by compactness.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- **Low-height `ζ′/ζ` bound**: a zero-free margin `δ₀` and a
constant `M₀` with `‖ζ′/ζ(s)‖ ≤ M₀ + (1-Re s)⁻¹` on
`[1-δ₀,1)×[-9,9]`. -/
theorem exists_low_height_logDeriv_bound :
    ∃ δ₀ M₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ 0 ≤ M₀ ∧
      (∀ s : ℂ, 1 - δ₀ ≤ s.re → |s.im| ≤ 9 → s ≠ 1 →
        riemannZeta s ≠ 0) ∧
      (∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re < 1 → |s.im| ≤ 9 →
        ‖deriv riemannZeta s / riemannZeta s‖
          ≤ M₀ + (1 - s.re)⁻¹) := by
  obtain ⟨δ₀, hδ0, hδ8, hzf⟩ := exists_low_height_zeta_zero_free
  -- the compact closure of the margin
  have hK : IsCompact {s : ℂ | (1 - δ₀ ≤ s.re ∧ s.re ≤ 1)
      ∧ |s.im| ≤ 9} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {s : ℂ | 1 - δ₀ ≤ s.re} :=
        isClosed_le continuous_const Complex.continuous_re
      have h2 : IsClosed {s : ℂ | s.re ≤ 1} :=
        isClosed_le Complex.continuous_re continuous_const
      have h3 : IsClosed {s : ℂ | |s.im| ≤ 9} :=
        isClosed_le (continuous_abs.comp Complex.continuous_im)
          continuous_const
      have hset : {s : ℂ | (1 - δ₀ ≤ s.re ∧ s.re ≤ 1) ∧ |s.im| ≤ 9}
          = ({s : ℂ | 1 - δ₀ ≤ s.re} ∩ {s : ℂ | s.re ≤ 1})
            ∩ {s : ℂ | |s.im| ≤ 9} := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hset]
      exact (h1.inter h2).inter h3
    · apply Bornology.IsBounded.subset
        (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 10))
      rintro s ⟨⟨ha, hb⟩, hc⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [show s = (s.re : ℂ) + (s.im : ℂ) * Complex.I from
        (Complex.re_add_im s).symm]
      rw [Complex.norm_add_mul_I]
      have hre2 : s.re ^ 2 ≤ 1 := by nlinarith
      have him2 : s.im ^ 2 ≤ 81 := by
        have h5 := abs_le.1 hc
        nlinarith [h5.1, h5.2]
      calc Real.sqrt (s.re ^ 2 + s.im ^ 2)
          ≤ Real.sqrt 100 := Real.sqrt_le_sqrt (by linarith)
        _ = 10 := by
          rw [show (100 : ℝ) = 10 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  -- the pole unit is zero-free on the closure
  have hZne : ∀ s ∈ {s : ℂ | (1 - δ₀ ≤ s.re ∧ s.re ≤ 1)
      ∧ |s.im| ≤ 9}, zetaPoleUnit s ≠ 0 := by
    intro s hs
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [zetaPoleUnit_one]
      exact one_ne_zero
    · exact zetaPoleUnit_ne_zero hs1 (hzf s hs.1.1 hs.2 hs1)
  -- `Z′/Z` is bounded on the closure
  have hcont : ContinuousOn
      (fun s : ℂ => deriv zetaPoleUnit s / zetaPoleUnit s)
      {s : ℂ | (1 - δ₀ ≤ s.re ∧ s.re ≤ 1) ∧ |s.im| ≤ 9} := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    exact ((differentiable_zetaPoleUnit.analyticAt s).deriv.continuousAt).div
      (differentiable_zetaPoleUnit s).continuousAt (hZne s hs)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨δ₀, max C 0, hδ0, hδ8, le_max_right _ _, hzf, ?_⟩
  intro s hs1 hs2 hs3
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs2
    exact lt_irrefl 1 hs2
  have hζ : riemannZeta s ≠ 0 := hzf s hs1 hs3 hsne1
  have hsplit : deriv riemannZeta s / riemannZeta s
      = deriv zetaPoleUnit s / zetaPoleUnit s - (s - 1)⁻¹ := by
    have h := neg_zeta_logDeriv_eq hsne1 hζ
    linear_combination -h
  rw [hsplit]
  calc ‖deriv zetaPoleUnit s / zetaPoleUnit s - (s - 1)⁻¹‖
      ≤ ‖deriv zetaPoleUnit s / zetaPoleUnit s‖ + ‖(s - 1)⁻¹‖ :=
        norm_sub_le _ _
    _ ≤ max C 0 + (1 - s.re)⁻¹ := by
        apply add_le_add
        · exact le_trans (hC s ⟨⟨hs1, hs2.le⟩, hs3⟩)
            (le_max_left _ _)
        · rw [norm_inv]
          have h4 : 1 - s.re ≤ ‖s - 1‖ := by
            have h5 := Complex.abs_re_le_norm (s - 1)
            rw [Complex.sub_re, Complex.one_re,
              abs_of_neg (by linarith : s.re - 1 < 0)] at h5
            linarith
          exact inv_anti₀ (by linarith) h4

end RHTower
