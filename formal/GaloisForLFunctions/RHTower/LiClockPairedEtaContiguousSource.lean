import GaloisForLFunctions.RHTower.LiClockCentralTraceSineReflection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Filter Topology MeasureTheory Set Metric
open scoped ComplexConjugate

namespace RHTower
noncomputable section

/-- Literal filled transform of the contiguous interval. -/
def liClockPairedEtaContiguousPartition (L : ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ in 0..L, Complex.exp (-s*u)

theorem liClockPairedEtaContiguousPartition_zero (L : ℝ) :
    liClockPairedEtaContiguousPartition L 0 = (L : ℂ) := by
  simp [liClockPairedEtaContiguousPartition]

theorem liClockPairedEtaContiguousPartition_eq_div {L : ℝ} {s : ℂ} (hs : s ≠ 0) :
    liClockPairedEtaContiguousPartition L s = (1-Complex.exp (-(L:ℂ)*s))/s := by
  rw [liClockPairedEtaContiguousPartition, integral_exp_mul_complex (neg_ne_zero.mpr hs)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -s*(L:ℂ)=-(L:ℂ)*s by ring]
  field_simp
  ring

private theorem contiguousPartition_eq_dslope (L : ℝ) (s : ℂ) :
    liClockPairedEtaContiguousPartition L s = (L:ℂ)*dslope Complex.exp 0 (-(L:ℂ)*s) := by
  by_cases hL : L = 0
  · subst L
    simp [liClockPairedEtaContiguousPartition]
  by_cases hs : s = 0
  · subst s
    simp [liClockPairedEtaContiguousPartition_zero, dslope_same, Complex.deriv_exp]
  have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  rw [liClockPairedEtaContiguousPartition_eq_div hs,
    dslope_of_ne _ (mul_ne_zero (neg_ne_zero.mpr hl) hs), slope_def_module]
  simp only [sub_zero, Complex.exp_zero, smul_eq_mul]
  field_simp
  ring

private theorem analyticAt_dslope_exp_zero (s : ℂ) :
    AnalyticAt ℂ (dslope Complex.exp 0) s := by
  by_cases hs : s = 0
  · subst s
    obtain ⟨p,hp⟩ := analyticAt_cexp (z:=0)
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  have heq : dslope Complex.exp 0 =ᶠ[𝓝 s] fun z : ℂ => (Complex.exp z-1)/z := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    rw [dslope_of_ne _ hz, slope_def_module]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact ((analyticAt_cexp.sub analyticAt_const).div analyticAt_id hs).congr heq.symm

theorem analyticAt_liClockPairedEtaContiguousPartition (L : ℝ) (s : ℂ) :
    AnalyticAt ℂ (liClockPairedEtaContiguousPartition L) s := by
  have h := (analyticAt_dslope_exp_zero (-(L:ℂ)*s)).comp
    (analyticAt_const.mul analyticAt_id)
  exact (analyticAt_const.mul h).congr (Filter.Eventually.of_forall
    (fun z => (contiguousPartition_eq_dslope L z).symm))

private theorem exp_neg_ne_one {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : 0 < s.re) :
    Complex.exp (-(L:ℂ)*s) ≠ 1 := by
  intro he
  have hn := congrArg norm he
  rw [Complex.norm_exp, norm_one] at hn
  have hre : (-(L:ℂ)*s).re = -L*s.re := by simp
  rw [hre] at hn
  have hlt : Real.exp (-L*s.re) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

theorem liClockPairedEtaContiguousPartition_ne_zero {L : ℝ} {s : ℂ}
    (hL : 0 < L) (hs : 0 < s.re) : liClockPairedEtaContiguousPartition L s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [liClockPairedEtaContiguousPartition_eq_div hs0]
  exact div_ne_zero (sub_ne_zero.mpr (exp_neg_ne_one hL hs).symm) hs0

def liClockPairedEtaContiguousConnection (L : ℝ) (s : ℂ) : ℂ :=
  (L:ℂ)/(Complex.exp ((L:ℂ)*s)-1)

def liClockPairedEtaContiguousSourceTrace (L : ℝ) (z : ℂ) : ℂ :=
  I*liClockPairedEtaContiguousConnection L (1/2+z*I)

/-- Fixed regular reference circle; all smaller-than-half regular circles agree. -/
def liClockPairedEtaContiguousClock (L : ℝ) (t : ℂ) : ℂ :=
  -liClockCentralTraceSineContour (liClockPairedEtaContiguousSourceTrace L) (1/4) t

private theorem exp_pos_ne_one {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : 0 < s.re) :
    Complex.exp ((L:ℂ)*s) ≠ 1 := by
  intro he
  have hn := congrArg norm he
  rw [Complex.norm_exp,norm_one] at hn
  have hre : ((L:ℂ)*s).re=L*s.re := by simp
  rw [hre] at hn
  have hgt : 1 < Real.exp (L*s.re) := Real.one_lt_exp_iff.mpr (mul_pos hL hs)
  linarith

theorem logDeriv_liClockPairedEtaContiguousPartition {L : ℝ} {s : ℂ}
    (hL : 0 < L) (hs : 0 < s.re) :
    logDeriv (liClockPairedEtaContiguousPartition L) s =
      liClockPairedEtaContiguousConnection L s-1/s := by
  have hs0 : s ≠ 0 := by intro hh; simp [hh] at hs
  have heq : liClockPairedEtaContiguousPartition L =ᶠ[𝓝 s]
      fun z : ℂ => (1-Complex.exp (-(L:ℂ)*z))/z := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    exact liClockPairedEtaContiguousPartition_eq_div hz
  have hex := (Complex.hasDerivAt_exp (-(L:ℂ)*s)).comp s
    ((hasDerivAt_id s).const_mul (-(L:ℂ)))
  have hd := ((hasDerivAt_const s (1:ℂ)).sub hex).div (hasDerivAt_id s) hs0
  have hd' : HasDerivAt (fun z : ℂ => (1-Complex.exp (-(L:ℂ)*z))/z)
      (((L:ℂ)*Complex.exp (-(L:ℂ)*s)*s-(1-Complex.exp (-(L:ℂ)*s)))/s^2) s := by
    convert hd using 1 <;> first | rfl | (simp only [Function.comp_def, id_eq, Pi.sub_apply]; ring)
  rw [logDeriv_apply,heq.deriv_eq,hd'.deriv,liClockPairedEtaContiguousPartition_eq_div hs0,
    liClockPairedEtaContiguousConnection]
  have hv : Complex.exp (-(L:ℂ)*s)=(Complex.exp ((L:ℂ)*s))⁻¹ := by
    rw [show -(L:ℂ)*s=-((L:ℂ)*s) by ring,Complex.exp_neg]
  rw [hv]
  have hden : Complex.exp ((L:ℂ)*s)-1 ≠ 0 := sub_ne_zero.mpr (exp_pos_ne_one hL hs)
  field_simp [hs0,Complex.exp_ne_zero,hden]

theorem analyticAt_liClockPairedEtaContiguousConnection {L : ℝ} {s : ℂ}
    (hL : 0 < L) (hs : 0 < s.re) :
    AnalyticAt ℂ (liClockPairedEtaContiguousConnection L) s :=
  analyticAt_const.div
    ((analyticAt_const.mul analyticAt_id).cexp'.sub analyticAt_const)
    (sub_ne_zero.mpr (exp_pos_ne_one hL hs))

private theorem contiguous_strip {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re := by
  have hi := (abs_le.mp ((Complex.abs_im_le_norm z).trans hz)).2
  have heq : (1/2+z*I).re=(1/2:ℝ)-z.im := by
    norm_num [Complex.add_re,Complex.mul_re]
    ring
  rw [heq]
  linarith

theorem analyticAt_liClockPairedEtaContiguousSourceTrace {L : ℝ} (hL : 0 < L)
    {z : ℂ} (hs : 0 < (1/2+z*I).re) :
    AnalyticAt ℂ (liClockPairedEtaContiguousSourceTrace L) z := by
  have hq := analyticAt_liClockPairedEtaContiguousConnection hL hs
  exact analyticAt_const.mul (hq.comp (f := fun z : ℂ => 1/2+z*I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))

theorem diffContOnCl_liClockPairedEtaContiguousSourceTrace {L r : ℝ}
    (hL : 0 < L) (hr : r < 1/2) :
    DiffContOnCl ℂ (liClockPairedEtaContiguousSourceTrace L) (ball 0 r) := by
  have ha : AnalyticOnNhd ℂ (liClockPairedEtaContiguousSourceTrace L) (closedBall 0 r) := by
    intro z hz
    exact analyticAt_liClockPairedEtaContiguousSourceTrace hL (contiguous_strip hr
      (show ‖z‖ ≤ r by simpa only [mem_closedBall,dist_zero_right] using hz))
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

theorem liClockPairedEtaContiguousClock_eq_neg_contour {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaContiguousClock L t =
      -liClockCentralTraceSineContour (liClockPairedEtaContiguousSourceTrace L) r t := by
  rw [liClockPairedEtaContiguousClock,
    liClockCentralTraceSineContour_eq_neg_tsum (by norm_num : (0:ℝ)<1/4)
      (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL (by norm_num)),
    liClockCentralTraceSineContour_eq_neg_tsum hr
      (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL hrhalf)]

theorem liClockPairedEtaContiguousSourceTrace_reflection (L : ℝ) (z : ℂ) :
    liClockPairedEtaContiguousSourceTrace L (-conj z) =
      -conj (liClockPairedEtaContiguousSourceTrace L z) := by
  have hs : (1/2:ℂ)+(-conj z)*I=conj (1/2+z*I) := by
    simp only [map_add,map_mul,map_div₀,map_one,map_ofNat,Complex.conj_I]
    ring
  have hq (s : ℂ) : liClockPairedEtaContiguousConnection L (conj s) =
      conj (liClockPairedEtaContiguousConnection L s) := by
    unfold liClockPairedEtaContiguousConnection
    rw [map_div₀,map_sub,map_one,Complex.conj_ofReal,← Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal]
  unfold liClockPairedEtaContiguousSourceTrace
  rw [hs,hq]
  simp only [map_mul,Complex.conj_I]
  ring

theorem liClockPairedEtaContiguousClock_im_ofReal_eq_zero {L : ℝ}
    (hL : 0 < L) (t : ℝ) : (liClockPairedEtaContiguousClock L (t:ℂ)).im = 0 := by
  rw [liClockPairedEtaContiguousClock,Complex.neg_im]
  rw [liClockCentralTraceSineContour_im_ofReal_eq_zero
    (by norm_num : (0:ℝ)<1/4)
    (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL (by norm_num))
    (liClockPairedEtaContiguousSourceTrace_reflection L)]
  simp


def liClockPairedEtaContiguousSourceEnvelope (L : ℝ) : ℝ :=
  L*Real.exp (-L/4)/(1-Real.exp (-L/4))

private theorem sourceEnvelope_nonneg {L : ℝ} (hL : 0 < L) :
    0 ≤ liClockPairedEtaContiguousSourceEnvelope L := by
  have he : Real.exp (-L/4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold liClockPairedEtaContiguousSourceEnvelope
  exact div_nonneg (mul_nonneg hL.le (Real.exp_pos _).le) (by linarith)

private theorem norm_contiguousConnection_le {L : ℝ} (hL : 0 < L) {s : ℂ}
    (hs : (1/4:ℝ) ≤ s.re) :
    ‖liClockPairedEtaContiguousConnection L s‖ ≤ liClockPairedEtaContiguousSourceEnvelope L := by
  have hs0 : 0 < s.re := by linarith
  have hd : Complex.exp ((L:ℂ)*s)-1 ≠ 0 := sub_ne_zero.mpr (exp_pos_ne_one hL hs0)
  have heq : liClockPairedEtaContiguousConnection L s =
      (L:ℂ)*Complex.exp (-(L:ℂ)*s)/(1-Complex.exp (-(L:ℂ)*s)) := by
    unfold liClockPairedEtaContiguousConnection
    rw [show -(L:ℂ)*s=-((L:ℂ)*s) by ring,Complex.exp_neg]
    field_simp [hd,Complex.exp_ne_zero]
  have hn : ‖Complex.exp (-(L:ℂ)*s)‖ ≤ Real.exp (-L/4) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (-(L:ℂ)*s).re = -L*s.re := by simp
    rw [hr]
    nlinarith
  have he : Real.exp (-L/4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 1-Real.exp (-L/4) ≤ ‖1-Complex.exp (-(L:ℂ)*s)‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (Complex.exp (-(L:ℂ)*s))
    rw [norm_one] at hh
    linarith
  rw [heq,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  unfold liClockPairedEtaContiguousSourceEnvelope
  calc
    _ ≤ L*‖Complex.exp (-(L:ℂ)*s)‖/(1-Real.exp (-L/4)) :=
      div_le_div_of_nonneg_left (mul_nonneg hL.le (norm_nonneg _)) (by linarith) hden
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hL.le) (by linarith)

private theorem contour_zero (r : ℝ) (t : ℂ) :
    liClockCentralTraceSineContour (fun _ : ℂ => 0) r t = 0 := by
  simp [liClockCentralTraceSineContour, circleIntegral]

theorem norm_liClockPairedEtaContiguousClock_le_sourceEnvelope {L : ℝ}
    (hL : 0 < L) (t : ℂ) :
    ‖liClockPairedEtaContiguousClock L t‖ ≤
      liClockPairedEtaContiguousSourceEnvelope L*Real.sinh (4*‖t‖) := by
  have hT : ContinuousOn (liClockPairedEtaContiguousSourceTrace L) (sphere 0 (1/4)) :=
    (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL (by norm_num)).continuousOn_ball.mono
      sphere_subset_closedBall
  have hb (z : ℂ) (hz : z ∈ sphere 0 (1/4)) :
      ‖liClockPairedEtaContiguousSourceTrace L z-0‖ ≤ liClockPairedEtaContiguousSourceEnvelope L := by
    have hn : ‖z‖=1/4 := by simpa only [mem_sphere_iff_norm,sub_zero] using hz
    have hi := (abs_le.mp (Complex.abs_im_le_norm z)).2
    have hr : (1/2+z*I).re=(1/2:ℝ)-z.im := by
      norm_num [Complex.add_re,Complex.mul_re]
      ring
    rw [sub_zero,liClockPairedEtaContiguousSourceTrace,norm_mul,norm_I,one_mul]
    apply norm_contiguousConnection_le hL
    rw [hr]
    linarith
  have hc := norm_liClockCentralTraceSineContour_sub_le
    (by norm_num : (0:ℝ)<1/4) (sourceEnvelope_nonneg hL) hT continuousOn_const hb t
  rw [liClockPairedEtaContiguousClock,norm_neg]
  have ht : ‖t‖/(1/4)=4*‖t‖ := by ring
  simpa only [contour_zero,sub_zero,ht] using hc

theorem liClockPairedEtaContiguousSourceEnvelope_tendsto_zero :
    Tendsto liClockPairedEtaContiguousSourceEnvelope atTop (𝓝 0) := by
  have hs : Tendsto (fun L : ℝ => L/4) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,id_eq,one_mul] using
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<1/4))
  have he : Tendsto (fun L : ℝ => Real.exp (-L/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hb : Tendsto (fun L : ℝ => (L/4)*Real.exp (-(L/4))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hs
  have hn : Tendsto (fun L : ℝ => L*Real.exp (-L/4)) atTop (𝓝 0) := by
    convert hb.const_mul 4 using 1
    · funext L
      rw [neg_div]
      ring
    · simp
  have hd : Tendsto (fun L : ℝ => 1-Real.exp (-L/4)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub he)
  convert hn.div hd (by norm_num : (1:ℝ)≠0) using 1
  · funext L
    rfl
  · simp

theorem liClockPairedEtaContiguousClock_tendsto_zero (t : ℂ) :
    Tendsto (fun L : ℝ => liClockPairedEtaContiguousClock L t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hl : Tendsto (fun L : ℝ => liClockPairedEtaContiguousSourceEnvelope L*Real.sinh (4*‖t‖))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using liClockPairedEtaContiguousSourceEnvelope_tendsto_zero.mul_const
      (Real.sinh (4*‖t‖))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact norm_liClockPairedEtaContiguousClock_le_sourceEnvelope hL t

theorem liClockPairedEtaContiguousClock_log_two_mul_tendsto_zero (t : ℂ) :
    Tendsto (fun N : ℕ => liClockPairedEtaContiguousClock (Real.log (2*(N:ℝ))) t)
      atTop (𝓝 0) :=
  (liClockPairedEtaContiguousClock_tendsto_zero t).comp
    (Real.tendsto_log_atTop.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<2) tendsto_natCast_atTop_atTop))

end
end RHTower
