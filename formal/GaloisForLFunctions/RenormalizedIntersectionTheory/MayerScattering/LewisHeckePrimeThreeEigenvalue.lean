import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.BarnesPrimeThreeHeckeRelation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisHeckeEisensteinEigenvalue

/-!
# Prime-three Hecke transport of the actual Lewis period

The seven determinant-three branches derive their scalar from the Barnes source cones.
Reciprocity folds the small `a/3` branch back into the original Mayer disc before continuation.
-/

noncomputable section
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerScatteringState MayerScatteringMellin MayerScatteringPeriod
open MayerParameter MayerGlobalPeriods

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The seven positive determinant-three branches of the period Hecke correspondence. -/
def lewisHeckeT3 (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (f (3 * a) + (3 : ℂ) ^ (-(2 * s)) * f (a / 3)) +
    ((3 : ℂ) ^ (-(2 * s)) * f ((a + 1) / 3) +
      ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f (3 * a / (a + 1))) +
    ((3 : ℂ) ^ (-(2 * s)) * f ((a + 2) / 3) +
      ((2 * a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f (3 * a / (2 * a + 1)) +
      ((a + 2 : ℝ) : ℂ) ^ (-(2 * s)) * f ((2 * a + 1) / (a + 2)))

private def reducedThree (w : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (f (3 * a) + (a : ℂ) ^ (-w) * f (3 / a)) +
    ((3 : ℂ) ^ (-w) * f ((a + 1) / 3) +
      ((a + 1 : ℝ) : ℂ) ^ (-w) * f (3 * a / (a + 1))) +
    ((3 : ℂ) ^ (-w) * f ((a + 2) / 3) +
      ((2 * a + 1 : ℝ) : ℂ) ^ (-w) * f (3 * a / (2 * a + 1)) +
      ((a + 2 : ℝ) : ℂ) ^ (-w) * f ((2 * a + 1) / (a + 2)))

private theorem heckeThree_eq_reduced (w : ℂ) (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a)
    (hrec : f (a / 3) = (((a / 3 : ℝ) : ℂ) ^ (-w)) * f (3 / a)) :
    lewisHeckeT3 (w / 2) f a = reducedThree w f a := by
  have hpow : (3 : ℂ) ^ (-w) * (((a / 3 : ℝ) : ℂ) ^ (-w)) = (a : ℂ) ^ (-w) := by
    change ((3 : ℝ) : ℂ) ^ (-w) * (((a / 3 : ℝ) : ℂ) ^ (-w)) = _
    rw [← Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (show 0 ≤ a / 3 by positivity)]
    congr 1
    push_cast
    ring
  rw [lewisHeckeT3, show 2 * (w / 2) = w by ring, hrec, ← mul_assoc, hpow]
  rfl

private theorem boundary_reciprocity (w : ℂ) {a : ℝ} (ha : 0 < a) :
    barnesBoundaryPeriod w a 1 = (a : ℂ) ^ (-w) * barnesBoundaryPeriod w a⁻¹ 1 := by
  have h := barnesBoundaryPeriod_scale w (c := a) (a := a⁻¹) (b := 1)
    ha (inv_pos.mpr ha) zero_lt_one
  rw [mul_inv_cancel₀ ha.ne', mul_one] at h
  have hswap : barnesBoundaryPeriod w 1 a = barnesBoundaryPeriod w a 1 := by
    unfold barnesBoundaryPeriod
    simp only [Complex.ofReal_one]
    rw [barnesDoubleZeta_symm 1 a w (1 : ℂ), barnesDoubleZeta_symm 1 a w (a : ℂ)]
    exact add_comm _ _
  rwa [hswap] at h

private theorem boundary_three_reduced {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 < w.re) :
    reducedThree w (fun x => barnesBoundaryPeriod w x 1) a =
      (1 + 3 * (3 : ℂ) ^ (-w)) * barnesBoundaryPeriod w a 1 := by
  have hrec := boundary_reciprocity w (div_pos ha (by norm_num : (0 : ℝ) < 3))
  rw [show (a / 3)⁻¹ = 3 / a by field_simp [ha.ne']] at hrec
  have h := barnesBoundaryPeriod_hecke_three ha hw
  have he : lewisHeckeT3 (w / 2) (fun x => barnesBoundaryPeriod w x 1) a =
      (1 + 3 * (3 : ℂ) ^ (-w)) * barnesBoundaryPeriod w a 1 := by
    simpa only [lewisHeckeT3, show 2 * (w / 2) = w by ring] using h
  rwa [heckeThree_eq_reduced w _ ha hrec] at he

private theorem three_segment {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6)) :
    3 * a ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧ 3 / a ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      (a + 1) / 3 ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      3 * a / (a + 1) ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      (a + 2) / 3 ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      3 * a / (2 * a + 1) ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      (2 * a + 1) / (a + 2) ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      a ∈ Ioo (1 / 2 : ℝ) (7 / 2) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have h2a1 : 0 < 2 * a + 1 := by linarith
  refine ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, ⟨?_, ?_⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, ⟨?_, ?_⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩⟩
  · exact (lt_div_iff₀ ha0).mpr (by linarith [ha.2])
  · exact (div_lt_iff₀ ha0).mpr (by linarith [ha.1])
  · exact (lt_div_iff₀ ha1).mpr (by linarith [ha.1])
  · exact (div_lt_iff₀ ha1).mpr (by linarith [ha.2])
  · exact (lt_div_iff₀ h2a1).mpr (by linarith [ha.1])
  · exact (div_lt_iff₀ h2a1).mpr (by linarith [ha.1])
  · exact (lt_div_iff₀ ha2).mpr (by linarith [ha.1])
  · exact (div_lt_iff₀ ha2).mpr (by linarith [ha.1])

private theorem periodValue_eq_boundary {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) :
    periodValue w a = barnesBoundaryPeriod w a 1 := by
  rw [periodValue_barnes hw ⟨ha.1.le, ha.2.le⟩, barnesBoundaryPeriod]
  simp only [Complex.ofReal_one]
  exact add_comm _ _

private theorem periodValue_three_reduced_absolute {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ Ioo (1 : ℝ) (7 / 6)) :
    reducedThree w (periodValue w) a =
      (1 + 3 * (3 : ℂ) ^ (-w)) * periodValue w a := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := three_segment ha
  rw [reducedThree, periodValue_eq_boundary hw h0, periodValue_eq_boundary hw h1,
    periodValue_eq_boundary hw h2, periodValue_eq_boundary hw h3, periodValue_eq_boundary hw h4,
    periodValue_eq_boundary hw h5, periodValue_eq_boundary hw h6, periodValue_eq_boundary hw h7]
  exact boundary_three_reduced (by linarith [ha.1]) hw

private def clearedValue (w : ℂ) (a : ℝ) : ℂ := plane (clearedState w) ((a : ℂ) - 1)

private theorem point_mem {a : ℝ} (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) :
    (a : ℂ) - 1 ∈ outer := by
  rw [outer, Metric.mem_closedBall, dist_eq_norm,
    show ((a : ℂ) - 1) - 1 = ((a - 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [ha.1, ha.2]

private theorem clearedValue_eq {w : ℂ} (hw : w ≠ 2) {a : ℝ}
    (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) :
    clearedValue w a = (w - 2) * periodValue w a := by
  have hc : clearedValue w a = evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (clearedState w) :=
    plane_eq (clearedState w) ⟨(a : ℂ) - 1, point_mem ha⟩
  have hp : periodValue w a = evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (state w) :=
    plane_eq (state w) ⟨(a : ℂ) - 1, point_mem ha⟩
  rw [hc, hp, clearedState_eq hw, map_smul, smul_eq_mul]

private theorem clearedValue_differentiable {a : ℝ} (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) :
    DifferentiableOn ℂ (fun w => clearedValue w a) {w : ℂ | 0 < w.re} := by
  have he : (fun w => clearedValue w a) =
      fun w => evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (clearedState w) :=
    funext fun w => plane_eq (clearedState w) ⟨(a : ℂ) - 1, point_mem ha⟩
  rw [he]
  intro w hw
  exact ((differentiableAt_const (evaluation ⟨(a : ℂ) - 1, point_mem ha⟩)).clm_apply
    (analyticAt_clearedState hw).differentiableAt).differentiableWithinAt

private def threeDefect (F : ℂ → ℝ → ℂ) (a : ℝ) (w : ℂ) : ℂ :=
  reducedThree w (F w) a - (1 + 3 * (3 : ℂ) ^ (-w)) * F w a

private theorem clearedDefect_analytic {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6)) :
    AnalyticOnNhd ℂ (threeDefect clearedValue a) {w : ℂ | 0 < w.re} := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := three_segment ha
  have hp (x : ℝ) (hx : 0 < x) :
      DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) {w : ℂ | 0 < w.re} := by
    have hd : Differentiable ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) := by
      simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
      fun_prop
    exact hd.differentiableOn
  have p3 : DifferentiableOn ℂ (fun w : ℂ => (3 : ℂ) ^ (-w))
      {w : ℂ | 0 < w.re} := hp 3 (by norm_num)
  have pa := hp a (by linarith [ha.1])
  have pa1 := hp (a + 1) (by linarith [ha.1])
  have p2a1 := hp (2 * a + 1) (by linarith [ha.1])
  have pa2 := hp (a + 2) (by linarith [ha.1])
  have hsum : DifferentiableOn ℂ (fun w => reducedThree w (clearedValue w) a)
      {w : ℂ | 0 < w.re} :=
    (((clearedValue_differentiable h0).add (pa.mul (clearedValue_differentiable h1))).add
      ((p3.mul (clearedValue_differentiable h2)).add
        (pa1.mul (clearedValue_differentiable h3)))).add
      (((p3.mul (clearedValue_differentiable h4)).add
        (p2a1.mul (clearedValue_differentiable h5))).add
        (pa2.mul (clearedValue_differentiable h6)))
  have hLambda : DifferentiableOn ℂ (fun w : ℂ => 1 + 3 * (3 : ℂ) ^ (-w))
      {w : ℂ | 0 < w.re} := (differentiableOn_const 1).add ((differentiableOn_const 3).mul p3)
  exact (hsum.sub (hLambda.mul (clearedValue_differentiable h7))).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

private theorem clearedDefect_eq {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6))
    {w : ℂ} (hw : w ≠ 2) :
    threeDefect clearedValue a w = (w - 2) * threeDefect periodValue a w := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := three_segment ha
  rw [threeDefect, threeDefect, reducedThree, reducedThree,
    clearedValue_eq hw h0, clearedValue_eq hw h1, clearedValue_eq hw h2,
    clearedValue_eq hw h3, clearedValue_eq hw h4, clearedValue_eq hw h5,
    clearedValue_eq hw h6, clearedValue_eq hw h7]
  ring

private theorem clearedDefect_absolute {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6))
    {w : ℂ} (hw : 2 < w.re) : threeDefect clearedValue a w = 0 := by
  have hw2 : w ≠ 2 := by intro h; norm_num [h] at hw
  rw [clearedDefect_eq ha hw2]
  have hz : threeDefect periodValue a w = 0 :=
    sub_eq_zero.mpr (periodValue_three_reduced_absolute hw ha)
  rw [hz, mul_zero]

private theorem clearedDefect_zero {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6))
    {w : ℂ} (hw : 0 < w.re) : threeDefect clearedValue a w = 0 := by
  have he : threeDefect clearedValue a =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact clearedDefect_absolute ha hv
  exact (clearedDefect_analytic ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

private theorem periodValue_three_reduced {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) {a : ℝ}
    (ha : a ∈ Ioo (1 : ℝ) (7 / 6)) :
    reducedThree w (periodValue w) a =
      (1 + 3 * (3 : ℂ) ^ (-w)) * periodValue w a := by
  have h := clearedDefect_zero ha hw
  rw [clearedDefect_eq ha hw2] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hw2))

private theorem eisenstein_state_equation {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    regularized (2 * s) (by simp; linarith) (state (2 * s)) =
      (1 : ℂ) • state (2 * s) + constant (-riemannZeta (2 * s)) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  have hn1 : 2 * s ≠ 1 := by intro h; rw [h, Complex.one_re] at hw1; exact lt_irrefl _ hw1
  have hn2 : 2 * s ≠ 2 := by intro h; rw [h] at hw1; norm_num at hw1
  have hst := state_equation hw0 hn1 hn2
  have hc : constant (-riemannZeta (2 * s)) = -(riemannZeta (2 * s) • constant 1) := by
    apply Subtype.ext
    ext z
    change -riemannZeta (2 * s) = -(riemannZeta (2 * s) * 1)
    ring
  rw [← source_eq hw0, one_smul, hc, ← hst]
  abel

private theorem eisenstein_eq_periodValue {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : a ∈ Ioo (1 / 2 : ℝ) (7 / 2)) :
    eisensteinLewisPeriod s (a : ℂ) = periodValue (2 * s) a := by
  have hi : (a : ℂ) - 1 ∈ MayerCutoff.inner := by
    rw [MayerCutoff.inner, Metric.mem_ball, dist_eq_norm,
      show ((a : ℂ) - 1) - 1 = ((a - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith only [ha.1, ha.2]
  change extension (2 * s) 1 (-riemannZeta (2 * s)) (state (2 * s)) ((a : ℂ) - 1) =
    plane (state (2 * s)) ((a : ℂ) - 1)
  exact extension_eq_plane (by simp; linarith) (by norm_num) (state (2 * s))
    (eisenstein_state_equation hs0 hs1) hi

private theorem eisenstein_three_local {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (7 / 6)) :
    lewisHeckeT3 s (fun x : ℝ => eisensteinLewisPeriod s x) a =
      (1 + 3 * (3 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s a := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hrec := (eisensteinLewisPeriod_properties hs0 hs1).2.2.1 (a / 3)
    (div_pos ha0 (by norm_num))
  simp only [lewisModularInversion] at hrec
  rw [show (a / 3)⁻¹ = 3 / a by field_simp [ha0.ne']] at hrec
  have hred := heckeThree_eq_reduced (2 * s) (fun x : ℝ => eisensteinLewisPeriod s x)
    ha0 hrec.symm
  rw [show (2 * s) / 2 = s by ring] at hred
  rw [hred]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := three_segment ha
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw2 : 2 * s ≠ 2 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have h := periodValue_three_reduced hw0 hw2 ha
  rw [reducedThree] at h ⊢
  rw [eisenstein_eq_periodValue hs0 hs1 h0, eisenstein_eq_periodValue hs0 hs1 h1,
    eisenstein_eq_periodValue hs0 hs1 h2, eisenstein_eq_periodValue hs0 hs1 h3,
    eisenstein_eq_periodValue hs0 hs1 h4, eisenstein_eq_periodValue hs0 hs1 h5,
    eisenstein_eq_periodValue hs0 hs1 h6, eisenstein_eq_periodValue hs0 hs1 h7]
  exact h

private theorem eisenstein_real_analytic {s : ℂ} (hs : 0 < s.re) :
    AnalyticOnNhd ℝ (fun a : ℝ => eisensteinLewisPeriod s a) (Ioi 0) := by
  have hw : 0 < (2 * s).re := by simp; linarith
  have ho : IsOpen MayerGlobalPeriods.domain :=
    isOpen_lt continuous_const Complex.continuous_re
  have hhol : AnalyticOnNhd ℂ (eisensteinLewisPeriod s) {a : ℂ | 0 < a.re} := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
    intro a ha
    change 0 < a.re at ha
    have hd : a - 1 ∈ MayerGlobalPeriods.domain := by
      change -1 < (a - 1).re
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hh := (extension_differentiableOn hw 1 (-riemannZeta (2 * s)) (state (2 * s))).differentiableAt
      (ho.mem_nhds hd)
    exact (hh.comp a (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z - 1) a)).differentiableWithinAt
  intro a ha
  have h := hhol (a : ℂ) (by simpa using ha)
  exact h.restrictScalars.comp (Complex.ofRealCLM.analyticAt a)

private theorem heckeThree_real_analytic (s : ℂ) {f : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f (Ioi 0)) :
    AnalyticOnNhd ℝ (lewisHeckeT3 s f) (Ioi 0) := by
  intro a ha
  have ha0 : 0 < a := ha
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have h2a1 : 0 < 2 * a + 1 := by linarith
  have htriple : AnalyticAt ℝ (fun x : ℝ => 3 * x) a := analyticAt_const.mul analyticAt_id
  have hthird : AnalyticAt ℝ (fun x : ℝ => x / 3) a := analyticAt_id.div_const
  have hshift1 : AnalyticAt ℝ (fun x : ℝ => x + 1) a := analyticAt_id.add analyticAt_const
  have hshift2 : AnalyticAt ℝ (fun x : ℝ => x + 2) a := analyticAt_id.add analyticAt_const
  have hshift3 : AnalyticAt ℝ (fun x : ℝ => 2 * x + 1) a :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hp {x : ℝ} (hx : 0 < x) :
      AnalyticAt ℝ (fun y : ℝ => (y : ℂ) ^ (-(2 * s))) x := by
    have hc : AnalyticAt ℂ (fun z : ℂ => z ^ (-(2 * s))) (x : ℂ) :=
      analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hx)
    exact hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have p1 := (hp ha1).comp (x := a) (f := fun x : ℝ => x + 1) hshift1
  have p2 := (hp ha2).comp (x := a) (f := fun x : ℝ => x + 2) hshift2
  have p3 := (hp h2a1).comp (x := a) (f := fun x : ℝ => 2 * x + 1) hshift3
  have b0 := (hf _ (by positivity : 0 < 3 * a)).comp
    (x := a) (f := fun x : ℝ => 3 * x) htriple
  have b1 := (hf _ (by positivity : 0 < a / 3)).comp
    (x := a) (f := fun x : ℝ => x / 3) hthird
  have b2 := (hf _ (by positivity : 0 < (a + 1) / 3)).comp
    (x := a) (f := fun x : ℝ => (x + 1) / 3) hshift1.div_const
  have b3 := (hf _ (by positivity : 0 < 3 * a / (a + 1))).comp
    (x := a) (f := fun x : ℝ => 3 * x / (x + 1)) (htriple.div hshift1 ha1.ne')
  have b4 := (hf _ (by positivity : 0 < (a + 2) / 3)).comp
    (x := a) (f := fun x : ℝ => (x + 2) / 3) hshift2.div_const
  have b5 := (hf _ (by positivity : 0 < 3 * a / (2 * a + 1))).comp
    (x := a) (f := fun x : ℝ => 3 * x / (2 * x + 1)) (htriple.div hshift3 h2a1.ne')
  have b6 := (hf _ (by positivity : 0 < (2 * a + 1) / (a + 2))).comp
    (x := a) (f := fun x : ℝ => (2 * x + 1) / (x + 2)) (hshift3.div hshift2 ha2.ne')
  exact ((b0.add (analyticAt_const.mul b1)).add
    ((analyticAt_const.mul b2).add (p1.mul b3))).add
    (((analyticAt_const.mul b4).add (p3.mul b5)).add (p2.mul b6))

/-- The completed Lewis period satisfies the seven-branch prime-three Hecke equation on
all positive arguments. Its eigenvalue is derived from the determinant-three Barnes cones. -/
theorem eisensteinLewisPeriod_hecke_three {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : 0 < a) :
    lewisHeckeT3 s (fun x : ℝ => eisensteinLewisPeriod s x) a =
      (1 + 3 * (3 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s a := by
  let D : ℝ → ℂ := fun x => lewisHeckeT3 s (fun y : ℝ => eisensteinLewisPeriod s y) x -
    (1 + 3 * (3 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s x
  have hE := eisenstein_real_analytic hs0
  have hD : AnalyticOnNhd ℝ D (Ioi 0) :=
    (heckeThree_real_analytic s hE).sub (analyticOnNhd_const.mul hE)
  have he : D =ᶠ[𝓝 (13 / 12 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (13 / 12 : ℝ) ∈ Ioo 1 (7 / 6) by norm_num)] with x hx
    exact sub_eq_zero.mpr (eisenstein_three_local hs0 hs1 hx)
  have hz := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
    (by norm_num : (13 / 12 : ℝ) ∈ Ioi 0) he ha
  exact sub_eq_zero.mp hz

/-- At each Mayer resonance the same source operator acts on the resonant period with
its prime-three scalar, without any spectral invariance premise. -/
theorem resonantLewisPeriod_hecke_three {s : ℂ} (hs : IsMayerScatteringResonance s)
    {a : ℝ} (ha : 0 < a) :
    lewisHeckeT3 s (fun x : ℝ => resonantLewisPeriod s x) a =
      (1 + 3 * (3 : ℂ) ^ (-(2 * s))) * resonantLewisPeriod s a := by
  have hz := (isMayerScatteringResonance_iff_zeta_zero hs.1 hs.2.1).mp hs
  have he : eisensteinLewisPeriod s = resonantLewisPeriod s := by
    funext z
    simp only [eisensteinLewisPeriod, resonantLewisPeriod, hz, neg_zero]
  simpa only [he] using eisensteinLewisPeriod_hecke_three hs.1 hs.2.1 ha

#print axioms eisensteinLewisPeriod_hecke_three
#print axioms resonantLewisPeriod_hecke_three

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
