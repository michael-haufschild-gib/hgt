import GaloisForLFunctions.RHTower.Sieve.InvZetaStripBound
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox

/-!
# A uniform `1/ζ` bound on the width-`log^{-2}` strip

`exists_norm_invZeta_contour_le` bounds `invZeta` by `C log²K` on the strip `|x - 1| ≤ log^{-2}K`,
but only above the height `T` at which the zero-free region takes over.  Below that height the
strip meets a *compact* box, on which `invZeta` — continuous, the pole costing nothing since
`invZeta 1 = 0` — is bounded by a constant.

Combining the two branches removes the height restriction entirely: on the whole strip, at every
height up to `K`,

```text
‖invZeta(x + it)‖ ≤ C · log²K.
```

This is the shape a truncated rectangle consumes on its left edge, where the contour passes through
the real axis.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- **`invZeta` is bounded on a box of arbitrary height straddling the abscissa.**  Compactness
plus continuity; the constant depends on the height but carries no rate. -/
theorem exists_bound_invZeta_box (d T : ℝ) (hd : 1 ≤ d) (hT : 0 ≤ T) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ d → |s.im| ≤ T → ‖invZeta s‖ ≤ M := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect (T := T) hT
  refine ⟨δ, hδ, ?_⟩
  set c : ℝ := 1 - δ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hcd : c ≤ d := le_trans hc1 hd
  have hrect : Set.uIcc c d ×ℂ Set.uIcc (-T) T = Set.Icc c d ×ℂ Set.Icc (-T) T := by
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)]
  have hdiff : DifferentiableOn ℂ invZeta (Set.Icc c d ×ℂ Set.Icc (-T) T) := by
    rw [← hrect]
    exact differentiableOn_invZeta_rect (hzf c d (by rw [hcdef]) hc1 hd)
  have hK : IsCompact (Set.Icc c d ×ℂ Set.Icc (-T) T) := isCompact_reProdIm_Icc _ _ _ _
  have hne : (Set.Icc c d ×ℂ Set.Icc (-T) T).Nonempty := by
    refine ⟨1, ⟨by simpa using hc1, by simpa using hd⟩, ?_, ?_⟩
    · simp only [Complex.one_im]; linarith
    · simp only [Complex.one_im]; linarith
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hdiff.continuousOn.norm)
  refine ⟨‖invZeta z‖, norm_nonneg _, fun s hlo hhi him => ?_⟩
  exact hmax (show s ∈ Set.Icc c d ×ℂ Set.Icc (-T) T from
    ⟨⟨hlo, hhi⟩, (abs_le.1 him).1, (abs_le.1 him).2⟩)

/-- **The uniform strip bound.**  No height restriction: the region branch handles large heights,
the compact box handles the rest, and the box constant is absorbed because `log K ≥ 1`. -/
theorem exists_norm_invZeta_uniform_strip :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ x t K : ℝ, L₀ ≤ Real.log K → |t| ≤ K →
      1 - 1 / Real.log K ^ 2 ≤ x → x ≤ 1 + 1 / Real.log K ^ 2 →
      ‖invZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log K ^ 2 := by
  obtain ⟨C₁, T, hC₁0, hT4, hstrip⟩ := exists_norm_invZeta_contour_le
  obtain ⟨δ, hδ0, M₀, hM₀0, hbox⟩ := exists_bound_invZeta_box 2 T (by norm_num) (by linarith)
  refine ⟨C₁ + M₀ + 1, max 1 (1 / δ), by linarith, le_max_left _ _, ?_⟩
  intro x t K hL hK hx1 hx2
  have hL1 : (1 : ℝ) ≤ Real.log K := le_trans (le_max_left _ _) hL
  have hLδ : 1 / δ ≤ Real.log K := le_trans (le_max_right _ _) hL
  have hLsq : (1 : ℝ) ≤ Real.log K ^ 2 := by nlinarith
  have hinv : 1 / Real.log K ^ 2 ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hLsq
  rcases le_or_gt T |t| with hbig | hsmall
  · have hres := hstrip x t K hbig hK hx1 hx2
    nlinarith [hres, hM₀0, hLsq]
  · -- the compact branch
    have hδcmp : 1 / Real.log K ^ 2 ≤ δ := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : (1 : ℝ) ≤ δ * Real.log K := by
        rw [div_le_iff₀ hδ0] at hLδ
        nlinarith [hLδ, hδ0]
      nlinarith [h1, hL1, hδ0]
    have hre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have him : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      ring
    have hres := hbox ((x : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; linarith)
    nlinarith [hres, hM₀0, hLsq, hC₁0]

end RHTower.Sieve
