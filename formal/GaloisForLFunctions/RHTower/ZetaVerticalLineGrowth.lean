import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# Polynomial growth of zeta along a whole vertical line

The corpus's strip estimate is stated above unit height.  Below it the line segment is compact and
`ζ` is continuous there as soon as the abscissa is not `1`, so the two bounds combine into a single
polynomial majorant valid for *every* ordinate.

This is the form needed when a contour edge crosses the real axis.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

theorem continuousOn_riemannZeta_vertical {σ : ℝ} (hσ : σ ≠ 1) :
    ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) (Set.Icc (-1 : ℝ) 1) := by
  intro t _
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re] at hre
    exact hσ (by linarith)
  have hc : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t := by fun_prop
  have hz : ContinuousAt riemannZeta ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiableAt_riemannZeta hne).continuousAt
  have hcomp : ContinuousAt (riemannZeta ∘ fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t :=
    ContinuousAt.comp hz hc
  exact (by simpa [Function.comp_def] using hcomp : ContinuousAt
    (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) t).continuousWithinAt

/-- **Polynomial growth of `ζ` along a vertical line off the pole abscissa.** -/
theorem exists_bound_norm_riemannZeta_vertical (σ : ℝ) (hσ : σ ≠ 1) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ t : ℝ, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨C₁, N, hC₁0, hC₁⟩ := exists_bound_norm_riemannZeta_strip |σ|
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuousOn_riemannZeta_vertical hσ)
  refine ⟨C₁ + max C₂ 0, N, by positivity, fun t => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by
    have := abs_nonneg t
    linarith
  have hpow1 : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ hbase
  have hpow0 : (0 : ℝ) ≤ (1 + |t|) ^ N := by positivity
  rcases le_total 1 |t| with hbig | hsmall
  · have h1 := hC₁ σ t (le_refl _) hbig
    have hmono : |t| ^ N ≤ (1 + |t|) ^ N :=
      pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    have hstep : C₁ * |t| ^ N ≤ C₁ * (1 + |t|) ^ N :=
      mul_le_mul_of_nonneg_left hmono hC₁0
    have hextra : (0 : ℝ) ≤ max C₂ 0 * (1 + |t|) ^ N := by positivity
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * |t| ^ N := h1
      _ ≤ C₁ * (1 + |t|) ^ N := hstep
      _ ≤ (C₁ + max C₂ 0) * (1 + |t|) ^ N := by nlinarith
  · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le]
      exact hsmall
    have h2 := hC₂ t hmem
    have h2' : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 :=
      le_trans h2 (le_max_left _ _)
    have hmax0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 := h2'
      _ = max C₂ 0 * 1 := by ring
      _ ≤ max C₂ 0 * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left hpow1 hmax0
      _ ≤ (C₁ + max C₂ 0) * (1 + |t|) ^ N := by nlinarith

end RHTower

end
