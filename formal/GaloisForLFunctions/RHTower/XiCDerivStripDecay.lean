import GaloisForLFunctions.RHTower.XiHorizontalStripDecay

/-!
# Exponential substrip decay of the derivative of `XiC`

The Cauchy derivative estimate transfers the horizontal-substrip exponential decay of `XiC`
(`exists_norm_XiC_horizontal_le`) to its derivative: on every substrip `|Im z| ≤ A < 1` the
derivative decays exponentially in `|Re z|`, with the strip shrunk by the Cauchy radius and the
radius's exponential slack absorbed into the constant.

This is the vertical-edge input for the single-pole contour form of the eigen-pair
Guinand–Weil identity: on the rectangle's vertical segments the integrand is dominated by
`‖deriv XiC‖·‖F_β^*‖/‖z+α‖`, and the present bound makes the segments vanish as the rectangle
widens.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex

/-- **Cauchy transfer of substrip decay to the derivative.**  On every horizontal substrip
`|a| ≤ A < 1`, the derivative of `XiC` decays exponentially in the horizontal coordinate. -/
theorem exists_norm_XiC_deriv_horizontal_le {A δ : ℝ} (hA1 : A < 1)
    (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t a : ℝ, |a| ≤ A →
      ‖deriv XiC ((t : ℂ) + (a : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  have hA'1 : (A + 1) / 2 < 1 := by linarith
  obtain ⟨C, hC, hXi⟩ := exists_norm_XiC_horizontal_le hA'1 hδ0 hδ4
  set r : ℝ := (1 - A) / 2 with hr_def
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨C * Real.exp (δ * r) / r, by positivity, fun t a ha => ?_⟩
  set c : ℂ := (t : ℂ) + (a : ℂ) * Complex.I with hc_def
  have hsphere : ∀ w ∈ Metric.sphere c r,
      ‖XiC w‖ ≤ C * Real.exp (δ * r) * Real.exp (-(δ * |t|)) := by
    intro w hw
    have hdist : ‖w - c‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have him : |w.im| ≤ (A + 1) / 2 := by
      have h1 : |(w - c).im| ≤ r := by
        rw [← hdist]
        exact Complex.abs_im_le_norm _
      have h2 : (w - c).im = w.im - a := by
        simp [hc_def]
      have h3 : |w.im| ≤ |w.im - a| + |a| := by
        calc |w.im| = |(w.im - a) + a| := by ring_nf
        _ ≤ |w.im - a| + |a| := abs_add_le _ _
      rw [h2] at h1
      dsimp [r] at h1
      linarith
    have hre : |t| - r ≤ |w.re| := by
      have h1 : |(w - c).re| ≤ r := by
        rw [← hdist]
        exact Complex.abs_re_le_norm _
      have h2 : (w - c).re = w.re - t := by
        simp [hc_def]
      have h3 : |t| ≤ |w.re| + |t - w.re| := by
        calc |t| = |w.re + (t - w.re)| := by ring_nf
        _ ≤ |w.re| + |t - w.re| := abs_add_le _ _
      rw [h2] at h1
      rw [abs_sub_comm] at h1
      linarith
    have hXiw := hXi w.re w.im him
    rw [Complex.re_add_im] at hXiw
    refine hXiw.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    have hmono : -(δ * |w.re|) ≤ δ * r + -(δ * |t|) := by
      have := mul_le_mul_of_nonneg_left hre hδ0
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono) hC
  have hdiff : DiffContOnCl ℂ XiC (Metric.ball c r) :=
    XiC_differentiable.diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff hsphere
  calc ‖deriv XiC c‖ ≤ C * Real.exp (δ * r) * Real.exp (-(δ * |t|)) / r := hcauchy
    _ = C * Real.exp (δ * r) / r * Real.exp (-(δ * |t|)) := by ring

end

end RHTower
