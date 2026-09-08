import GaloisForLFunctions.HTGeometry.FirstEndpointMellin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceEndpointGreen

/-! Source-faithful continuation of the actual horizon Green moment through the fundamental-QNM strip. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem horizonFirstRemainder_differentiableAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    DifferentiableAt ℂ (firstEndpointMellinRemainder (horizonMellinCore s chi a J K) b) w := by
  obtain ⟨R,C,hR,hC,hi,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hb hb1
  let R' := min R ((w.re+2)/2)
  have hR' : 0 < R' := lt_min hR (by linarith)
  have hsub : ball w R' ⊆ ball w R := ball_subset_ball (min_le_left _ _)
  apply firstEndpointMellinRemainder_differentiableAt hb.le hb1.le hR' hC
    (show -2 < (w.re-2)/2 by linarith)
  · intro u hu
    have hn : ‖u-w‖ < (w.re+2)/2 := by
      simpa only [dist_eq_norm] using (mem_ball.mp hu).trans_le (min_le_right _ _)
    have hh := neg_le_of_abs_le (Complex.abs_re_le_norm (u-w))
    simp only [Complex.sub_re] at hh
    linarith
  · intro u hu
    exact horizonMellinCore_measurable s chi a J K u
  · intro t ht u hu
    exact horizonMellinCore_frequency_differentiableAt s chi a J K u (hi u (hsub hu))
      (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2.trans_lt hb1)
  · intro u hu t ht
    exact hbound u (hsub hu) t ⟨ht.1.le,ht.2⟩

/-- The restored source endpoint moment is analytic throughout the larger nonreal strip. -/
theorem horizonFirstMellin_analyticAt (s chi a J K w : ℂ) (hw : w.im ≠ 0) (hwre : -2 < w.re)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    AnalyticAt ℂ (firstEndpointMellin (horizonMellinCore s chi a J K) b) w := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hi := Complex.continuous_im.continuousAt.eventually_ne hw
  have hr : ∀ᶠ u : ℂ in 𝓝 w, -2 < u.re := continuousAt_const.eventually_lt
    Complex.continuous_re.continuousAt hwre
  filter_upwards [hi,hr] with u hui hur
  have hf0 := horizonMellinCore_frequency_differentiableAt s chi a J K u hui
    (t := 0) (by simp)
  have hp : DifferentiableAt ℂ (fun v : ℂ => (b:ℂ)^(v+1)) u :=
    (differentiableAt_id.add_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hb)))
  have hn : u+1 ≠ 0 := by intro he; apply hui; have hh := congrArg Complex.im he; simpa using hh
  exact ((hf0.mul hp).div (differentiableAt_id.add_const 1) hn).add
    (horizonFirstRemainder_differentiableAt s chi a J K u hui hur hb hb1)

/-- The continued horizon moment retains the original normalization and fixed onset. -/
def continuedHorizonMoment (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  firstEndpointMellin (horizonMellinCore s chi a J K) b w *
    (1/(w-2*s)+onsetCorrection (2*s) w)/(-connection w chi)

/-- Meromorphy of the actual restored horizon moment, after integrating the endpoint tail. -/
theorem continuedHorizonMoment_meromorphicAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    MeromorphicAt (continuedHorizonMoment s chi a J K b) w := by
  have hm := (horizonFirstMellin_analyticAt s chi a J K w hw hwre hb hb1).meromorphicAt
  have hi : MeromorphicAt (fun u : ℂ => 1/(u-2*s)) w :=
    (show AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) w from analyticAt_const).meromorphicAt.div
      (show AnalyticAt ℂ (fun u : ℂ => u-2*s) w by fun_prop).meromorphicAt
  have hc := ((onsetCorrection_entire (2*s)).analyticAt w).meromorphicAt
  exact (hm.mul (hi.add hc)).div (connection_frequency_analyticAt w chi hw).meromorphicAt.neg

private theorem horizon_source_mellin (s chi a J K T w : ℂ) {t : ℝ} (ht : 0 < t) :
    horizon w chi t*sourceProfile s w a J K T t = (t:ℂ)^w*horizonMellinCore s chi a J K w t*T := by
  have hr : sourceRemainder s w a J K T t = sourceRemainder s w a J K 1 t*T := by
    unfold sourceRemainder
    ring
  have hp : power (w/2) t*power (w/2) t = (t:ℂ)^w := by
    rw [power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))]
    congr 1
    ring
  unfold horizon dress sourceProfile horizonMellinCore
  rw [hr]
  calc
    _ = (power (w/2) t*power (w/2) t)*
        (gaussFactor w chi false (t:ℂ)*sourceRemainder s w a J K 1 t)*T := by ring
    _ = _ := by rw [hp]

/-- In the genuine convergence chamber, the continued moment is exactly the original
endpoint Green integral of the fixed smoothly switched source. -/
theorem continuedHorizonMoment_eq_original (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwre : -1 < w.re) (hsource : (2*s).re < w.re)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    continuedHorizonMoment s chi a J K b w =
      horizonMoment w chi s a J K (onsetTransform (2*s) w) b := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hb hb1
  have he := firstEndpointMellin_eq_integral hb.le hwre (horizonMellinCore_measurable s chi a J K w)
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
  rw [continuedHorizonMoment,he,← onsetTransform_eq (2*s) w hsource,horizonMoment,
    intervalIntegral.integral_of_le hb.le]
  rw [← integral_mul_const,div_eq_mul_inv,← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [horizon_source_mellin s chi a J K (onsetTransform (2*s) w) w ht.1,div_eq_mul_inv]

end
end RHTower.D4BMLaplaceRadial
