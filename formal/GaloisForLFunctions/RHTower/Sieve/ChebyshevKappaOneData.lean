import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform

/-!
# The contour data at the width-`1/log` rectangle

The Chebyshev contour integrand carries `ζ'/ζ`, whose regular part is bounded on the **full width**
of the exponent-one zero-free region.  The rectangle may therefore be taken with abscissae

```text
c(T) = 1 - (1/40000)/log T,      d(T) = 1 + 1/log T,      |Im s| ≤ T,
```

a width `≍ 1/log T` rather than the `log^{-2}T` a `1/ζ` contour is limited to.  Every one of the
five hypotheses of `norm_tsum_vonMangoldt_sub_full_main_le_explicit` holds there with the single
bound `C log²T`.
-/

namespace RHTower.Sieve

open Complex

/-- The left abscissa of the width-`1/log` rectangle. -/
noncomputable def chebLeftTwo (T : ℝ) : ℝ := 1 - 1 / 40000 / Real.log T

/-- The right abscissa of the width-`1/log` rectangle. -/
noncomputable def chebRightTwo (T : ℝ) : ℝ := 1 + 1 / Real.log T

theorem chebLeftTwo_lt_one {T : ℝ} (hT : 8 ≤ Real.log T) : chebLeftTwo T < 1 := by
  rw [chebLeftTwo]
  have : (0 : ℝ) < 1 / 40000 / Real.log T := div_pos (by norm_num) (by linarith)
  linarith

theorem one_lt_chebRightTwo {T : ℝ} (hT : 8 ≤ Real.log T) : 1 < chebRightTwo T := by
  rw [chebRightTwo]
  have : (0 : ℝ) < 1 / Real.log T := div_pos (by norm_num) (by linarith)
  linarith

theorem chebRightTwo_le {T : ℝ} (hT : 8 ≤ Real.log T) : chebRightTwo T ≤ 9 / 8 := by
  rw [chebRightTwo]
  have h : 1 / Real.log T ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem zero_lt_chebLeftTwo {T : ℝ} (hT : 8 ≤ Real.log T) : 0 < chebLeftTwo T := by
  rw [chebLeftTwo]
  have h : 1 / 40000 / Real.log T ≤ 1 / 40000 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

theorem chebLeftTwo_le_chebRightTwo {T : ℝ} (hT : 8 ≤ Real.log T) :
    chebLeftTwo T ≤ chebRightTwo T :=
  le_of_lt (lt_trans (chebLeftTwo_lt_one hT) (one_lt_chebRightTwo hT))

/-- The reciprocal of the left edge's distance from the abscissa. -/
theorem one_sub_chebLeftTwo_inv {T : ℝ} (hT : 8 ≤ Real.log T) :
    (1 - chebLeftTwo T)⁻¹ = 40000 * Real.log T := by
  rw [chebLeftTwo]
  have hL : (0 : ℝ) < Real.log T := by linarith
  field_simp
  ring

/-- Dividing by the left abscissa costs at most a factor two. -/
theorem half_le_chebLeftTwo {T : ℝ} (hT : 8 ≤ Real.log T) : 1 / 2 ≤ chebLeftTwo T := by
  rw [chebLeftTwo]
  have h : 1 / 40000 / Real.log T ≤ 1 / 40000 / 8 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- **The contour data at the width-`1/log` rectangle.**  One constant serves the left edge and
both horizontal edges, and the rectangle is zero-free. -/
theorem exists_cheb_kappa_one_data :
    ∃ Cr L₀ : ℝ, 0 < Cr ∧ 8 ≤ L₀ ∧ ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      (∀ s ∈ Set.uIcc (chebLeftTwo T) (chebRightTwo T) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
          riemannZeta s ≠ 0)
      ∧ (∀ y ∈ Set.uIcc (-T) T, riemannZeta ((chebLeftTwo T : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
      ∧ (∀ y ∈ Set.Icc (-T) T,
          ‖zetaLogDerivReg ((chebLeftTwo T : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftTwo T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Cr * Real.log T ^ 2)
      ∧ (∀ x ∈ Set.uIoc (chebLeftTwo T) (chebRightTwo T),
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Cr * Real.log T ^ 2) := by
  obtain ⟨Cr, L₁, hCr0, hL₁1, hreg⟩ := exists_bound_zetaLogDerivReg_uniform
  obtain ⟨L₂, hL₂1, hzf⟩ := exists_zeta_uniform_kappa_one_zero_free
  refine ⟨Cr, max 8 (max L₁ L₂), hCr0, le_max_left _ _, fun T hT1 hT => ?_⟩
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans (le_max_left _ _) hT
  have hL₁T : L₁ ≤ Real.log T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hL₂T : L₂ ≤ Real.log T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  have hcd := chebLeftTwo_le_chebRightTwo hT8
  have hTT : (-T : ℝ) ≤ T := by linarith
  have hcre : ∀ y : ℝ, ((chebLeftTwo T : ℂ) + (y : ℝ) * Complex.I).re = chebLeftTwo T := by
    intro y; simp
  have hcim : ∀ y : ℝ, ((chebLeftTwo T : ℂ) + (y : ℝ) * Complex.I).im = y := by
    intro y; simp
  have hxre : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).re = x := by
    intro x u; simp
  have hxim : ∀ x u : ℝ, ((x : ℂ) + ((u : ℝ) : ℂ) * Complex.I).im = u := by
    intro x u; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hne
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le hTT] at hs
    refine hzf s T hL₂T (le_trans (abs_le.mpr ⟨hs.2.1, hs.2.2⟩) le_rfl) ?_ hne
    simpa [chebLeftTwo] using hs.1.1
  · intro y hy
    rw [Set.uIcc_of_le hTT] at hy
    refine hzf _ T hL₂T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; simp [chebLeftTwo]
    · intro h
      have := hcre y
      rw [h] at this
      simp only [Complex.one_re] at this
      have := chebLeftTwo_lt_one hT8
      linarith
  · intro y hy
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hcim]; exact abs_le.mpr ⟨hy.1, hy.2⟩
    · rw [hcre]; simp [chebLeftTwo]
    · rw [hcre]; linarith [chebLeftTwo_lt_one hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd, chebLeftTwo] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim]; rw [abs_of_nonneg (by linarith)]
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]
  · intro x hx
    rw [Set.uIoc_of_le hcd, chebLeftTwo] at hx
    refine hreg _ T hL₁T ?_ ?_ ?_
    · rw [hxim]; rw [abs_of_nonpos (by linarith)]; linarith
    · rw [hxre]; linarith [hx.1]
    · rw [hxre]; linarith [hx.2, chebRightTwo_le hT8]

end RHTower.Sieve
