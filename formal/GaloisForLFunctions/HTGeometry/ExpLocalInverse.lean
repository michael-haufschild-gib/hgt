import GaloisForLFunctions.HTGeometry.LipschitzCoveredDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The complex exponential has local Lipschitz inverses

Near any point the exponential is inverted by a translated branch of the logarithm, and on the ball
of radius `1/2` about `1` that branch has derivative bounded by `2`, hence is Lipschitz there.  So
the preimage under the exponential of a set covered by Lipschitz images of a cube is covered in the
same dimension.

This is what a parametric jet argument needs of a gauge `exp(g)`: the value slot of the jet is an
exponential, and a codimension bound has to be pulled back through it.
-/

open Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The unit-neighbourhood on which the principal logarithm is Lipschitz. -/
theorem norm_ge_half_of_mem_ball_one {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    (1 : ℝ) / 2 ≤ ‖z‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 : ‖(1 : ℂ)‖ - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at h1
  simp only [norm_one] at h1
  linarith

theorem mem_slitPlane_of_mem_ball_one {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    z ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hre : |(z - 1).re| ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hlt : |(z - 1).re| < 1 / 2 := lt_of_le_of_lt hre hz
  have := abs_lt.mp hlt
  simp only [Complex.sub_re, Complex.one_re] at this
  linarith [this.1]

/-- **The principal logarithm is Lipschitz on the ball of radius `1/2` about `1`.** -/
theorem lipschitzOnWith_log_ball_one :
    LipschitzOnWith 2 Complex.log (Metric.ball (1 : ℂ) (1 / 2)) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
  have hderiv : ∀ v ∈ Metric.ball (1 : ℂ) (1 / 2),
      HasDerivWithinAt Complex.log v⁻¹ (Metric.ball (1 : ℂ) (1 / 2)) v := fun v hv =>
    (Complex.hasDerivAt_log (mem_slitPlane_of_mem_ball_one hv)).hasDerivWithinAt
  have hbound : ∀ v ∈ Metric.ball (1 : ℂ) (1 / 2), ‖v⁻¹‖ ≤ (2 : ℝ) := by
    intro v hv
    rw [norm_inv]
    have hge := norm_ge_half_of_mem_ball_one hv
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (1 : ℂ) (1 / 2)) hw hz
  rw [dist_eq_norm, dist_eq_norm]
  simpa using hmv

/-- **A translated logarithm branch inverts the exponential near a point, and is Lipschitz on the
image.** -/
theorem exp_hasLocalLipschitzInverse (x : ℂ) :
    ∃ (u : Set ℂ), u ∈ nhds x ∧ ∃ (ψ : ℂ → ℂ) (C : NNReal),
      LipschitzOnWith C ψ (Complex.exp '' u) ∧ ∀ y ∈ u, ψ (Complex.exp y) = y := by
  classical
  set a := Complex.exp x with ha
  have hane : a ≠ 0 := Complex.exp_ne_zero x
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr hane
  have hρpos : 0 < ‖a‖ / 2 := by positivity
  have hcont : ContinuousAt Complex.exp x := Complex.continuous_exp.continuousAt
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.mp
    (hcont.preimage_mem_nhds (Metric.ball_mem_nhds a hρpos))
  set r := min r₀ (Real.pi / 2) with hr
  have hrpos : 0 < r := lt_min hr₀ (by positivity)
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds _ hrpos, fun z => x + Complex.log (z / a),
    Real.toNNReal (2 / ‖a‖), ?_, ?_⟩
  · have himg : ∀ v ∈ Complex.exp '' Metric.ball x r, v / a ∈ Metric.ball (1 : ℂ) (1 / 2) := by
      rintro _ ⟨y, hy, rfl⟩
      have hin : Complex.exp y ∈ Metric.ball a (‖a‖ / 2) :=
        hsub (Metric.ball_subset_ball (min_le_left _ _) hy)
      rw [Metric.mem_ball, dist_eq_norm] at hin ⊢
      have hcalc : Complex.exp y / a - 1 = (Complex.exp y - a) / a := by
        field_simp
      rw [hcalc, norm_div]
      rw [div_lt_iff₀ hapos]
      linarith
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    have hzb := himg z hz
    have hwb := himg w hw
    have hlip := lipschitzOnWith_log_ball_one.dist_le_mul _ hzb _ hwb
    have hdiv : dist (z / a) (w / a) = dist z w / ‖a‖ := by
      rw [dist_eq_norm, dist_eq_norm, ← sub_div, norm_div]
    rw [dist_eq_norm]
    have hsimp : x + Complex.log (z / a) - (x + Complex.log (w / a))
        = Complex.log (z / a) - Complex.log (w / a) := by ring
    rw [hsimp, ← dist_eq_norm]
    have hC : ((Real.toNNReal (2 / ‖a‖) : NNReal) : ℝ) = 2 / ‖a‖ := by
      rw [Real.coe_toNNReal]
      positivity
    rw [hC]
    calc dist (Complex.log (z / a)) (Complex.log (w / a))
        ≤ ((2 : NNReal) : ℝ) * dist (z / a) (w / a) := hlip
      _ = 2 * (dist z w / ‖a‖) := by rw [hdiv]; norm_num
      _ = 2 / ‖a‖ * dist z w := by ring
  · intro y hy
    show x + Complex.log (Complex.exp y / a) = y
    have hlog : Complex.log (Complex.exp y / a) = y - x := by
      have hdiv : Complex.exp y / a = Complex.exp (y - x) := by
        rw [ha, Complex.exp_sub]
      rw [hdiv]
      have hlt : ‖y - x‖ < Real.pi / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hy
        exact lt_of_lt_of_le hy (min_le_right _ _)
      have him : |(y - x).im| ≤ ‖y - x‖ := Complex.abs_im_le_norm _
      have hbound := abs_lt.mp (lt_of_le_of_lt him hlt)
      refine Complex.log_exp ?_ ?_
      · have := hbound.1
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
      · have := hbound.2
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith
    rw [hlog]
    ring

/-- **The preimage under the exponential of a covered set is covered.** -/
theorem isLipschitzCovered_exp_preimage {k : ℕ} {S : Set ℂ} (hS : IsLipschitzCovered k S) :
    IsLipschitzCovered k (Complex.exp ⁻¹' S) :=
  IsLipschitzCovered.preimage exp_hasLocalLipschitzInverse hS

end

end GaloisForLFunctions.HTGeometry
