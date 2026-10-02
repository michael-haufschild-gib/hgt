import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationProduct
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationMellin
import GaloisForLFunctions.Bottcher.SchwarzReflection

/-!
# Continuation of the actual correlation along the real interval

The two admitted boundary transforms are glued across the imaginary axis.
The reflected formula extends to each real point greater than `-1`, without
assuming exponential admission of the physical correlation there.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- Right physical transform and left reflected source formula. -/
def criticalAbelCorrelationContinuation (s : ℂ) : ℂ := by
  classical
  exact if 0 ≤ s.re then criticalAbelCorrelationLaplace s else
    criticalAbelLaplaceContinuation s * criticalAbelLaplaceContinuation (-s) -
      criticalAbelCorrelationLaplace (-s)

theorem criticalAbelCorrelationContinuation_eq_right {s : ℂ} (hs : 0 ≤ s.re) :
    criticalAbelCorrelationContinuation s = criticalAbelCorrelationLaplace s := by
  simp [criticalAbelCorrelationContinuation, hs]

theorem criticalAbelCorrelationContinuation_eq_left {s : ℂ} (hs : s.re < 0) :
    criticalAbelCorrelationContinuation s =
      criticalAbelLaplaceContinuation s * criticalAbelLaplaceContinuation (-s) -
        criticalAbelCorrelationLaplace (-s) := by
  simp [criticalAbelCorrelationContinuation, not_le.mpr hs]

private theorem analyticAt_correlation_right {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ criticalAbelCorrelationLaplace s :=
  differentiableOn_criticalAbelCorrelationLaplace.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

private theorem analyticAt_correlationContinuation_zero :
    AnalyticAt ℂ criticalAbelCorrelationContinuation 0 := by
  classical
  obtain ⟨r, hr, hL⟩ :=
    (analyticAt_criticalAbelLaplaceContinuation_real (x := 0) (by norm_num)).exists_ball_analyticOnNhd
  let U := Metric.ball (0 : ℂ) r
  let R : Set ℂ := {s : ℂ | 0 ≤ s.re}
  let F : ℂ → ℂ := fun s => criticalAbelLaplaceContinuation s *
    criticalAbelLaplaceContinuation (-s) - criticalAbelCorrelationLaplace (-s)
  have hnU : MapsTo (fun s : ℂ => -s) U U := by
    intro s hs
    simpa [U, Metric.mem_ball, Complex.dist_eq] using hs
  have hR : IsClosed R := isClosed_le continuous_const Complex.continuous_re
  have hneg : closure Rᶜ ⊆ {s : ℂ | s.re ≤ 0} := by
    apply closure_minimal
    · intro s hs
      change ¬0 ≤ s.re at hs
      exact (lt_of_not_ge hs).le
    · exact isClosed_le Complex.continuous_re continuous_const
  have hQc : ContinuousOn criticalAbelCorrelationLaplace R :=
    continuousOn_criticalAbelCorrelationLaplace
  have hFc : ContinuousOn F (U ∩ closure Rᶜ) := by
    apply ContinuousOn.sub
    · exact (hL.continuousOn.mono inter_subset_left).mul
        (hL.continuousOn.comp continuous_neg.continuousOn
          (fun s hs => hnU hs.1))
    · exact hQc.comp continuous_neg.continuousOn
        (fun s hs => by
          have hs0 : s.re ≤ 0 := hneg hs.2
          change 0 ≤ (-s).re
          simpa only [Complex.neg_re] using neg_nonneg.mpr hs0)
  have hG : criticalAbelCorrelationContinuation = R.piecewise criticalAbelCorrelationLaplace F := by
    funext s
    rfl
  have hcont : ContinuousOn criticalAbelCorrelationContinuation U := by
    rw [hG]
    apply ContinuousOn.piecewise
    · intro s hs
      have hs0 : s.re = 0 :=
        (frontier_le_subset_eq continuous_const Complex.continuous_re hs.2).symm
      have hb := criticalAbelCorrelationLaplace_boundary_product hs0
      rw [criticalAbelProfileLaplace_eq_continuation_boundary hs0 (hL s hs.1).continuousAt,
        criticalAbelProfileLaplace_eq_continuation_boundary (by simp [hs0])
          (hL (-s) (hnU hs.1)).continuousAt] at hb
      exact eq_sub_iff_add_eq.mpr hb
    · exact hQc.mono (fun s hs => by simpa [hR.closure_eq] using hs.2)
    · exact hFc
  have hdiff : DifferentiableOn ℂ criticalAbelCorrelationContinuation
      (U ∩ {s : ℂ | (Complex.I * s + 0).im ≠ 0}) := by
    intro s hs
    have hs0 : s.re ≠ 0 := by simpa [Complex.mul_im] using hs.2
    by_cases hp : 0 < s.re
    · apply ((analyticAt_correlation_right hp).differentiableAt.congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp] with z hz
      exact criticalAbelCorrelationContinuation_eq_right hz.le
    · have hn : s.re < 0 := lt_of_le_of_ne (le_of_not_gt hp) hs0
      have hF : AnalyticAt ℂ F s :=
        ((hL s hs.1).mul ((hL (-s) (hnU hs.1)).comp analyticAt_id.neg)).sub
          ((analyticAt_correlation_right (by simpa using neg_pos.mpr hn)).comp analyticAt_id.neg)
      apply (hF.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hn] with z hz
      exact criticalAbelCorrelationContinuation_eq_left hz
  exact (Bottcher.differentiableOn_of_off_line (c := Complex.I) (d := 0) (a := 0)
    Complex.I_ne_zero Metric.isOpen_ball hcont hdiff).analyticAt
      (Metric.isOpen_ball.mem_nhds (by simpa [U] using hr))

/-- The actual transform continues locally at every real point before its left pole. -/
theorem analyticAt_criticalAbelCorrelationContinuation_real {x : ℝ} (hx : -1 < x) :
    AnalyticAt ℂ criticalAbelCorrelationContinuation (x : ℂ) := by
  by_cases hx0 : x = 0
  · simpa [hx0] using analyticAt_correlationContinuation_zero
  by_cases hp : 0 < x
  · apply (analyticAt_correlation_right (by simpa using hp)).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 0 < (x : ℂ).re by simpa using hp)] with z hz
    exact (criticalAbelCorrelationContinuation_eq_right hz.le).symm
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx0
    have hLm : AnalyticAt ℂ criticalAbelLaplaceContinuation (-(x : ℂ)) := by
      simpa using (analyticAt_criticalAbelLaplaceContinuation_real (x := -x) (by linarith))
    have hQm := analyticAt_correlation_right (s := -(x : ℂ)) (by simp; linarith)
    apply (((analyticAt_criticalAbelLaplaceContinuation_real hx).mul
      (hLm.comp analyticAt_id.neg)).sub (hQm.comp analyticAt_id.neg)).congr
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      (show (x : ℂ).re < 0 by simpa using hn)] with z hz
    exact (criticalAbelCorrelationContinuation_eq_left hz).symm

/-- The signed residue is fixed by two positive physical source quantities. -/
def criticalCorrelationNegativeResidue : ℝ :=
  2 * criticalCorrelationUnitMean * (criticalAbelLaplaceContinuation 1).re

theorem criticalCorrelationNegativeResidue_pos : 0 < criticalCorrelationNegativeResidue :=
  mul_pos (mul_pos (by norm_num) criticalCorrelationUnitMean_pos)
    criticalAbelLaplaceContinuation_one_re_pos

/-- The continued actual correlation has a strictly negative real residue at `-1`. -/
theorem criticalAbelCorrelationContinuation_left_residue :
    Tendsto (fun x : ℝ => (x + 1) * (criticalAbelCorrelationContinuation (x : ℂ)).re)
      (𝓝[>] (-1 : ℝ)) (𝓝 (-criticalCorrelationNegativeResidue)) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (-1 : ℝ)).mono_left
      (show 𝓝[>] (-1 : ℝ) ≤ 𝓝 (-1 : ℝ) from nhdsWithin_le_nhds)
  have hn : Tendsto (fun x : ℝ => -(x : ℂ)) (𝓝[>] (-1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using hx.neg
  have hd : Tendsto (fun x : ℝ => ((x + 1 : ℝ) : ℂ))
      (𝓝[>] (-1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using hx.add_const 1
  have hL := (analyticAt_criticalAbelLaplaceContinuation_real
    (x := 1) (by norm_num)).continuousAt.tendsto.comp hn
  have hQ := (analyticAt_correlation_right (s := 1)
    (by norm_num)).continuousAt.tendsto.comp hn
  have h := (criticalAbelLaplaceContinuation_left_residue.mul hL).sub (hd.mul hQ)
  simp only [zero_mul, sub_zero] at h
  have hc : Tendsto (fun x : ℝ => ((x + 1 : ℝ) : ℂ) *
      criticalAbelCorrelationContinuation (x : ℂ)) (𝓝[>] (-1 : ℝ))
      (𝓝 ((-2 * (criticalCorrelationUnitMean : ℂ)) * criticalAbelLaplaceContinuation 1)) := by
    apply h.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 0)] with x hx
    rw [criticalAbelCorrelationContinuation_eq_left (by simpa using hx.2)]
    dsimp only [Function.comp_def]
    ring
  have hr := Complex.continuous_re.tendsto _ |>.comp hc
  simpa [Function.comp_def, Complex.mul_re, Complex.mul_im,
    criticalCorrelationNegativeResidue] using hr

end RHTower
