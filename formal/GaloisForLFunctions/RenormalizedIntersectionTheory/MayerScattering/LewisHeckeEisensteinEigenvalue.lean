import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.BarnesHeckeRelation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringPeriod
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The source Hecke eigenvalue of the Eisenstein period

The Barnes-cone Hecke identity holds in the absolute chamber. Clearing the explicit pole of
the actual Mayer state continues that identity to the source half-plane. The four branch
values are evaluated in the same disc representative, preserving the scattering boundary terms.
-/

noncomputable section
open Complex Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerScatteringState MayerScatteringMellin MayerScatteringPeriod
open MayerParameter MayerGlobalPeriods

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem hecke_segment {a : ℝ} (ha : a ∈ Icc (1 : ℝ) (3 / 2)) :
    2 * a ∈ periodSegment ∧ a / 2 ∈ periodSegment ∧ (a + 1) / 2 ∈ periodSegment ∧
      2 * a / (a + 1) ∈ periodSegment ∧ a ∈ periodSegment := by
  have ha1 : 0 < a + 1 := by linarith [ha.1]
  refine ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, ⟨?_, ?_⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩⟩
  · exact (le_div_iff₀ ha1).mpr (by linarith [ha.1])
  · exact (div_le_iff₀ ha1).mpr (by linarith [ha.1])

private theorem periodValue_eq_boundary {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ periodSegment) : periodValue w a = barnesBoundaryPeriod w a 1 := by
  rw [periodValue_barnes hw ha, barnesBoundaryPeriod]
  simp only [Complex.ofReal_one]
  exact add_comm _ _

/-- The source cone partition gives the four-branch Hecke eigenvalue on the actual period. -/
theorem periodValue_hecke_absolute {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) (3 / 2)) :
    lewisHeckeT2 (w / 2) (periodValue w) a =
      (1 + 2 * (2 : ℂ) ^ (-w)) * periodValue w a := by
  obtain ⟨h2a, hah, has, haf, ha'⟩ := hecke_segment ha
  rw [lewisHeckeT2, show 2 * (w / 2) = w by ring,
    periodValue_eq_boundary hw h2a, periodValue_eq_boundary hw hah,
    periodValue_eq_boundary hw has, periodValue_eq_boundary hw haf,
    periodValue_eq_boundary hw ha']
  exact barnesBoundaryPeriod_hecke (by linarith [ha.1]) hw

private def clearedValue (w : ℂ) (a : ℝ) : ℂ := plane (clearedState w) ((a : ℂ) - 1)

private theorem point_mem {a : ℝ} (ha : a ∈ periodSegment) : (a : ℂ) - 1 ∈ outer := by
  rw [outer, Metric.mem_closedBall, dist_eq_norm,
    show ((a : ℂ) - 1) - 1 = ((a - 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [ha.1, ha.2]

private theorem clearedValue_eq {w : ℂ} (hw : w ≠ 2) {a : ℝ}
    (ha : a ∈ periodSegment) : clearedValue w a = (w - 2) * periodValue w a := by
  have hc : clearedValue w a = evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (clearedState w) :=
    plane_eq (clearedState w) ⟨(a : ℂ) - 1, point_mem ha⟩
  have hp : periodValue w a = evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (state w) :=
    plane_eq (state w) ⟨(a : ℂ) - 1, point_mem ha⟩
  rw [hc, hp, clearedState_eq hw, map_smul, smul_eq_mul]

private theorem clearedValue_differentiable {a : ℝ} (ha : a ∈ periodSegment) :
    DifferentiableOn ℂ (fun w => clearedValue w a) {w : ℂ | 0 < w.re} := by
  have he : (fun w => clearedValue w a) =
      fun w => evaluation ⟨(a : ℂ) - 1, point_mem ha⟩ (clearedState w) :=
    funext fun w => plane_eq (clearedState w) ⟨(a : ℂ) - 1, point_mem ha⟩
  rw [he]
  intro w hw
  exact ((differentiableAt_const (evaluation ⟨(a : ℂ) - 1, point_mem ha⟩)).clm_apply
    (analyticAt_clearedState hw).differentiableAt).differentiableWithinAt

private def heckeValueDefect (F : ℂ → ℝ → ℂ) (a : ℝ) (w : ℂ) : ℂ :=
  F w (2 * a) + (2 : ℂ) ^ (-w) * F w (a / 2) +
    (2 : ℂ) ^ (-w) * F w ((a + 1) / 2) +
    ((a + 1 : ℝ) : ℂ) ^ (-w) * F w (2 * a / (a + 1)) -
    (1 + 2 * (2 : ℂ) ^ (-w)) * F w a

private theorem clearedDefect_analytic {a : ℝ} (ha : a ∈ Icc (1 : ℝ) (3 / 2)) :
    AnalyticOnNhd ℂ (heckeValueDefect clearedValue a) {w : ℂ | 0 < w.re} := by
  obtain ⟨h2a, hah, has, haf, ha'⟩ := hecke_segment ha
  have hp (x : ℝ) (hx : 0 < x) : Differentiable ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    fun_prop
  have h2 : DifferentiableOn ℂ (fun w : ℂ => (2 : ℂ) ^ (-w))
      {w : ℂ | 0 < w.re} := (hp 2 (by norm_num)).differentiableOn
  have hshift : DifferentiableOn ℂ (fun w : ℂ => ((a + 1 : ℝ) : ℂ) ^ (-w))
      {w : ℂ | 0 < w.re} := (hp (a + 1) (by linarith [ha.1])).differentiableOn
  have hLambda : DifferentiableOn ℂ (fun w : ℂ => 1 + 2 * (2 : ℂ) ^ (-w))
      {w : ℂ | 0 < w.re} := (differentiableOn_const 1).add ((differentiableOn_const 2).mul h2)
  exact (((((clearedValue_differentiable h2a).add (h2.mul (clearedValue_differentiable hah))).add
    (h2.mul (clearedValue_differentiable has))).add
      (hshift.mul (clearedValue_differentiable haf))).sub
        (hLambda.mul (clearedValue_differentiable ha'))).analyticOnNhd
          (isOpen_lt continuous_const Complex.continuous_re)

private theorem clearedDefect_eq {a : ℝ} (ha : a ∈ Icc (1 : ℝ) (3 / 2))
    {w : ℂ} (hw : w ≠ 2) :
    heckeValueDefect clearedValue a w = (w - 2) * heckeValueDefect periodValue a w := by
  obtain ⟨h2a, hah, has, haf, ha'⟩ := hecke_segment ha
  rw [heckeValueDefect, heckeValueDefect,
    clearedValue_eq hw h2a, clearedValue_eq hw hah, clearedValue_eq hw has,
    clearedValue_eq hw haf, clearedValue_eq hw ha']
  ring

private theorem clearedDefect_absolute {a : ℝ} (ha : a ∈ Icc (1 : ℝ) (3 / 2))
    {w : ℂ} (hw : 2 < w.re) : heckeValueDefect clearedValue a w = 0 := by
  have hw2 : w ≠ 2 := by intro h; norm_num [h] at hw
  rw [clearedDefect_eq ha hw2]
  have h := periodValue_hecke_absolute hw ha
  rw [lewisHeckeT2, show 2 * (w / 2) = w by ring] at h
  have hz : heckeValueDefect periodValue a w = 0 := sub_eq_zero.mpr h
  rw [hz, mul_zero]

private theorem clearedDefect_zero {a : ℝ} (ha : a ∈ Icc (1 : ℝ) (3 / 2))
    {w : ℂ} (hw : 0 < w.re) : heckeValueDefect clearedValue a w = 0 := by
  have he : heckeValueDefect clearedValue a =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact clearedDefect_absolute ha hv
  exact (clearedDefect_analytic ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

/-- Pole clearing continues the actual source Hecke eigenvalue to every regular parameter
in the right half-plane. The four evaluations lie in the original Mayer disc. -/
theorem periodValue_hecke {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) (3 / 2)) :
    lewisHeckeT2 (w / 2) (periodValue w) a =
      (1 + 2 * (2 : ℂ) ^ (-w)) * periodValue w a := by
  have h := clearedDefect_zero ha hw
  rw [clearedDefect_eq ha hw2] at h
  have hz := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hw2)
  rw [heckeValueDefect] at hz
  rw [lewisHeckeT2, show 2 * (w / 2) = w by ring]
  exact sub_eq_zero.mp hz

#print axioms periodValue_hecke_absolute
#print axioms periodValue_hecke

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

private theorem hecke_segment_open {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (3 / 2)) :
    2 * a ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧ a / 2 ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      (a + 1) / 2 ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧
      2 * a / (a + 1) ∈ Ioo (1 / 2 : ℝ) (7 / 2) ∧ a ∈ Ioo (1 / 2 : ℝ) (7 / 2) := by
  have ha1 : 0 < a + 1 := by linarith [ha.1]
  refine ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, ⟨?_, ?_⟩,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩⟩
  · exact (lt_div_iff₀ ha1).mpr (by linarith [ha.1])
  · exact (div_lt_iff₀ ha1).mpr (by linarith [ha.1])

private theorem eisenstein_hecke_local {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : a ∈ Ioo (1 : ℝ) (3 / 2)) :
    lewisHeckeT2 s (fun x : ℝ => eisensteinLewisPeriod s x) a =
      (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s a := by
  obtain ⟨h2a, hah, has, haf, ha'⟩ := hecke_segment_open ha
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hn2 : 2 * s ≠ 2 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have h := periodValue_hecke hw0 hn2 ⟨ha.1.le, ha.2.le⟩
  rw [show (2 * s) / 2 = s by ring] at h
  rw [lewisHeckeT2] at h ⊢
  rw [eisenstein_eq_periodValue hs0 hs1 h2a, eisenstein_eq_periodValue hs0 hs1 hah,
    eisenstein_eq_periodValue hs0 hs1 has, eisenstein_eq_periodValue hs0 hs1 haf,
    eisenstein_eq_periodValue hs0 hs1 ha']
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

private theorem hecke_real_analytic (s : ℂ) {f : ℝ → ℂ}
    (hf : AnalyticOnNhd ℝ f (Ioi 0)) :
    AnalyticOnNhd ℝ (lewisHeckeT2 s f) (Ioi 0) := by
  intro a ha
  have ha0 : 0 < a := ha
  have ha1 : 0 < a + 1 := by linarith
  have hdouble : AnalyticAt ℝ (fun x : ℝ => 2 * x) a := analyticAt_const.mul analyticAt_id
  have hhalf : AnalyticAt ℝ (fun x : ℝ => x / 2) a := analyticAt_id.div_const
  have hshift : AnalyticAt ℝ (fun x : ℝ => (x + 1) / 2) a :=
    (analyticAt_id.add analyticAt_const).div_const
  have hfrac : AnalyticAt ℝ (fun x : ℝ => 2 * x / (x + 1)) a :=
    hdouble.div (analyticAt_id.add analyticAt_const) ha1.ne'
  have hpowC : AnalyticAt ℂ (fun z : ℂ => z ^ (-(2 * s))) ((a + 1 : ℝ) : ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr ha1)
  have hpowR : AnalyticAt ℝ (fun x : ℝ => (x : ℂ) ^ (-(2 * s))) (a + 1) :=
    hpowC.restrictScalars.comp (Complex.ofRealCLM.analyticAt (a + 1))
  have hpow : AnalyticAt ℝ (fun x : ℝ => ((x + 1 : ℝ) : ℂ) ^ (-(2 * s))) a :=
    hpowR.comp (x := a) (f := fun x : ℝ => x + 1) (analyticAt_id.add analyticAt_const)
  exact ((((hf _ (by positivity : 0 < 2 * a)).comp (x := a) (f := fun x : ℝ => 2 * x) hdouble).add
    (analyticAt_const.mul ((hf _ (by positivity : 0 < a / 2)).comp (x := a) (f := fun x : ℝ => x / 2) hhalf))).add
    (analyticAt_const.mul ((hf _ (by positivity : 0 < (a + 1) / 2)).comp (x := a) (f := fun x : ℝ => (x + 1) / 2) hshift))).add
    (hpow.mul ((hf _ (by positivity : 0 < 2 * a / (a + 1))).comp (x := a) (f := fun x : ℝ => 2 * x / (x + 1)) hfrac))

/-- The actual completed Eisenstein Lewis period is a Hecke eigenfunction on the whole
positive line. The proof derives the eigenvalue from the Barnes cones and continues twice. -/
theorem eisensteinLewisPeriod_hecke {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    {a : ℝ} (ha : 0 < a) :
    lewisHeckeT2 s (fun x : ℝ => eisensteinLewisPeriod s x) a =
      (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s a := by
  let D : ℝ → ℂ := fun x => lewisHeckeT2 s (fun y : ℝ => eisensteinLewisPeriod s y) x -
    (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * eisensteinLewisPeriod s x
  have hE := eisenstein_real_analytic hs0
  have hD : AnalyticOnNhd ℝ D (Ioi 0) :=
    (hecke_real_analytic s hE).sub (analyticOnNhd_const.mul hE)
  have he : D =ᶠ[𝓝 (5 / 4 : ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (5 / 4 : ℝ) ∈ Ioo 1 (3 / 2) by norm_num)] with x hx
    exact sub_eq_zero.mpr (eisenstein_hecke_local hs0 hs1 hx)
  have hz := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
    (by norm_num : (5 / 4 : ℝ) ∈ Ioi 0) he ha
  exact sub_eq_zero.mp hz

/-- The resonance specialization is still a source-derived Hecke eigen-equation; no
hypothesis of Hecke invariance or a spectral scalar action is added. -/
theorem resonantLewisPeriod_hecke {s : ℂ} (hs : IsMayerScatteringResonance s)
    {a : ℝ} (ha : 0 < a) :
    lewisHeckeT2 s (fun x : ℝ => resonantLewisPeriod s x) a =
      (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * resonantLewisPeriod s a := by
  have hz := (isMayerScatteringResonance_iff_zeta_zero hs.1 hs.2.1).mp hs
  have he : eisensteinLewisPeriod s = resonantLewisPeriod s := by
    funext z
    simp only [eisensteinLewisPeriod, resonantLewisPeriod, hz, neg_zero]
  simpa only [he] using eisensteinLewisPeriod_hecke hs.1 hs.2.1 ha

#print axioms eisensteinLewisPeriod_hecke
#print axioms resonantLewisPeriod_hecke


/-- The completed period has a canonical nonzero normalization throughout the open strip. -/
theorem eisensteinLewisPeriod_one_eq {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    eisensteinLewisPeriod s 1 = 2 * riemannZeta (2 * s - 1) := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s).re < 1 := by simp; linarith
  have hw2 : 2 * s ≠ 2 := by intro h; rw [h] at hw1; norm_num at hw1
  calc
    eisensteinLewisPeriod s 1 = periodValue (2 * s) 1 :=
      eisenstein_eq_periodValue hs0 hs1 (by norm_num)
    _ = plane (state (2 * s)) 0 := by simp only [periodValue, Complex.ofReal_one, sub_self]
    _ = (state (2 * s)).1 zeroPoint := plane_eq (state (2 * s)) zeroPoint
    _ = 2 * riemannZeta (2 * s - 1) := state_zero hw0 hw2

theorem eisensteinLewisPeriod_one_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    eisensteinLewisPeriod s 1 ≠ 0 := by
  rw [eisensteinLewisPeriod_one_eq hs0 hs1]
  exact mul_ne_zero (by norm_num)
    (MayerScatteringMultiplicity.shifted_zeta_ne_zero
      (by simp; linarith : 0 < (2 * s).re) (by simp; linarith : (2 * s).re < 1))

#print axioms eisensteinLewisPeriod_one_ne_zero

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
