import GaloisForLFunctions.RHTower.ThetaCuspC5OuterClockCurrent

/-! Source action, rather than displacement alone, pays the complete clock
current in the inner chamber. The bounded-action remainder stays open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
set_option autoImplicit false

local notation "c" => thetaCuspLogCurvature
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "b" => curvatureShapeBeta
local notation "g" => curvatureShapeGamma
local notation "k" => denominatorClockRate
local notation "y" => completedFirstDenominator
local notation "d" => completedLocalDenominator

private theorem primitive_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)

private theorem slope_lt {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) : p u s < 2*e u s := by
  have hv := ThetaCurvature.velocityGap_pos (show 0 ≤ u+s by linarith)
  have hm := sourceVelocity_nonneg (sub_nonneg.mpr hsu)
  have hc := thetaCuspLogCurvature_pos (u-s)
  unfold shapeCurvatureSlope completedCurvatureEven
  linarith only [hv,hm,hc]

private theorem curvature_exp_bound {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    e u s ≤ c u*Real.exp (2*s) := by
  have hd (v : ℝ) : HasDerivAt (fun x => e u x*Real.exp (-2*x))
      ((p u v-2*e u v)*Real.exp (-2*v)) v := by
    have he : HasDerivAt (e u) (p u v) v := hasDerivAt_completedCurvatureEven u v
    have hx := (Real.hasDerivAt_exp (-2*v)).comp v ((hasDerivAt_id v).const_mul (-2))
    convert! (he.mul hx) using 1 <;> simp only [Function.comp_apply] <;> ring
  have hm : AntitoneOn (fun x => e u x*Real.exp (-2*x)) (Icc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
    · intro v _; exact (hd v).continuousAt.continuousWithinAt
    · intro v _; exact (hd v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (slope_lt hv.1.le (hv.2.le.trans hsu)).le) (Real.exp_pos _).le
  have hh := hm (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl,hs⟩) ⟨hs,le_rfl⟩ hs
  simp only [completedCurvatureEven,add_zero,sub_zero,add_self_div_two,mul_zero,
    Real.exp_zero,mul_one] at hh
  calc
    e u s = (e u s*Real.exp (-2*s))*Real.exp (2*s) := by
      rw [mul_assoc,←Real.exp_add,show -2*s+2*s=0 by ring,Real.exp_zero,mul_one]
    _ ≤ c u*Real.exp (2*s) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

/-- The actual source primitive on the entire inner displacement chamber. -/
theorem innerPrimitive_le_center_exp_four {u t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 2) (htu : t ≤ u) : E u t ≤ c u*t*Real.exp 4 := by
  have henv (s : ℝ) (hs : s ∈ Icc 0 t) : e u s ≤ c u*Real.exp 4 :=
    (curvature_exp_bound hs.1 (hs.2.trans htu)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hs.2]))
        (thetaCuspLogCurvature_pos u).le)
  have hd (s : ℝ) : HasDerivAt (fun x => c u*Real.exp 4*x-E u x)
      (c u*Real.exp 4-e u s) s := by
    convert! ((hasDerivAt_id s).const_mul (c u*Real.exp 4)).sub
      (hasDerivAt_completedDecayEvenPrimitive u s) using 1
    ring
  have hm : MonotoneOn (fun x => c u*Real.exp 4*x-E u x) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      exact sub_nonneg.mpr (henv s ⟨hs.1.le,hs.2.le⟩)
  have hh := hm (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩) ⟨ht.le,le_rfl⟩ ht.le
  simp only [mul_zero,completedDecayEvenPrimitive_zero,sub_zero] at hh
  nlinarith only [hh]

private theorem beta_lt {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : b u t < 2*t*a u t := by
  have hh := mul_lt_mul_of_pos_left (slope_lt ht.le htu)
    (div_pos (sq_pos_of_pos ht) (primitive_pos u ht))
  unfold curvatureShapeAlpha curvatureShapeBeta
  convert! hh using 1 <;> ring

private theorem gamma_ge_one {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 1 ≤ g u t := by
  have hh := two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
    (fun x _ => (thetaCuspLogCurvatureJetTwo_pos_all x).le)
  unfold thetaCuspReflectedActionVelocity at hh
  rw [show thetaCuspReflectedLogJetOne u t=2*E u t by
    rw [completedDecayEvenPrimitive_eq]; ring] at hh
  unfold curvatureShapeGamma
  exact (le_div_iff₀ (thetaCuspReflectedLogAction_pos (u:=u) ht)).mpr (by linarith only [hh])

private theorem clock_mass_le_action {u t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) (htu : t ≤ u)
    (hZ : 4050*Real.exp 4 ≤ Z u t) : 30*k u*E u t ≤ Z u t := by
  have hc := thetaCuspLogCurvature_pos u
  have hE := primitive_pos u ht
  have hz : 0 < Z u t := mul_pos ht hE
  have he := mul_le_mul_of_nonneg_right (innerPrimitive_le_center_exp_four ht ht2 htu) hE.le
  have hk : (k u)^2=9/(2*c u) := by
    unfold denominatorClockRate
    rw [Real.sq_sqrt (by positivity)]
  have hs : (30*k u*E u t)^2 ≤ 4050*Real.exp 4*Z u t := by
    calc
      _ = 4050*(E u t)^2/c u := by
        rw [mul_pow,mul_pow,hk]
        field_simp [hc.ne']
        ring
      _ ≤ _ := (div_le_iff₀ hc).mpr (by
        unfold curvatureShapeAction
        nlinarith only [he])
  have hp := mul_le_mul_of_nonneg_right hZ hz.le
  have hn : 0 ≤ 30*k u*E u t :=
    mul_nonneg (mul_nonneg (by norm_num) (denominatorClockRate_pos u).le) hE.le
  nlinarith only [hs,hp,hn,hz]

/-- Source action pays the literal clock on the unbounded-center part of the inner chamber. -/
theorem innerClock_lt_actionGrowth_of_large_action {u t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 2) (htu : t ≤ u) (hZ : 4050*Real.exp 4 ≤ Z u t) :
    intrinsicClockLogElasticity u t < 1+12*Z u t/5 := by
  have hE := primitive_pos u ht
  have ha0 : 0 < a u t := div_pos (mul_pos ht (completedCurvatureEven_pos u t)) hE
  have hb := beta_lt ht htu
  have ha := curvatureShapeAlpha_lt ht htu
  have hD : 2*a u t+b u t < 30 := by
    have hh := mul_lt_mul_of_pos_right ha (show 0 < 2*(1+t) by positivity)
    have haux : 2*(1+t)*(1+2*t) ≤ 30 := by nlinarith [sq_nonneg (2-t)]
    nlinarith only [hb,hh,haux]
  have hT : (2*a u t+b u t)/(1+a u t) < 6 := by
    apply (div_lt_iff₀ (by positivity : 0 < 1+a u t)).mpr
    have hp := mul_le_mul_of_nonneg_right ht2 ha0.le
    nlinarith only [hb,hp,ha0]
  have hratio : (2*a u t+b u t)/(1+a u t)=t*d u t/y u t := by
    have hy : 0 < E u t+t*e u t := add_pos hE (mul_pos ht (completedCurvatureEven_pos u t))
    unfold curvatureShapeAlpha curvatureShapeBeta completedFirstDenominator completedLocalDenominator shapeCurvatureSlope
    field_simp [hE.ne',hy.ne']
  have hT0 : 0 < (2*a u t+b u t)/(1+a u t) := by
    rw [hratio]
    exact div_pos (mul_pos ht (completedLocalDenominator_pos_nonneg u ht.le))
      (completedFirstDenominator_pos u ht)
  let z := k u*y u t
  have hz : 0 < z := mul_pos (denominatorClockRate_pos u) (completedFirstDenominator_pos u ht)
  have hlin : linearClockEnvelope z < z+3 := by
    unfold linearClockEnvelope
    apply (div_lt_iff₀ (by positivity : 0 < 15+3*z+z^2)).mpr
    nlinarith only [hz]
  have henv := mul_lt_mul_of_pos_left hlin hT0
  have heq : (2*a u t+b u t)/(1+a u t)*(z+3)=
      k u*t*d u t+3*((2*a u t+b u t)/(1+a u t)) := by
    rw [hratio]
    dsimp only [z]
    field_simp [(completedFirstDenominator_pos u ht).ne']
  rw [heq] at henv
  have hid : k u*t*d u t=k u*(2*a u t+b u t)*E u t := by
    unfold curvatureShapeAlpha curvatureShapeBeta completedLocalDenominator shapeCurvatureSlope
    field_simp [hE.ne']
  have hm := mul_lt_mul_of_pos_left hD (mul_pos (denominatorClockRate_pos u) hE)
  have hpay := clock_mass_le_action ht ht2 htu hZ
  have hC := intrinsicClockLogElasticity_lt_upper u ht
  unfold intrinsicClockUpperElasticity at hC
  have hclock : intrinsicClockLogElasticity u t < Z u t+18 := by
    rw [hid] at henv
    dsimp only [z] at henv
    nlinarith only [henv,hT,hm,hpay,hC]
  have hexp : 1 ≤ Real.exp (4 : ℝ) := Real.one_le_exp (by norm_num)
  have hbig : 4050 ≤ Z u t := by nlinarith only [hZ,hexp]
  linarith only [hclock,hbig]

/-- Unconditional actual theta-current sign at large action, including small displacement. -/
theorem enrichedClockCurrent_pos_inner_large_action {u t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 2) (htu : t ≤ u) (hZ : 4050*Real.exp 4 ≤ Z u t) :
    0 < enrichedClockCurrent u t := by
  have hg := gamma_ge_one ht htu
  have hclock := innerClock_lt_actionGrowth_of_large_action ht ht2 htu hZ
  have h16 : 0 < actionPowerReserve 16 u t := by
    rw [actionPowerReserve_sixteen u ht]
    exact normalizedActionInverseReserve_pos ht htu
  have h36 : 0 < actionPowerReserve 36 u t := by
    rw [actionPowerReserve_thirtysix u ht]
    exact add_pos (normalizedActionInverseReserve_pos ht htu) (enrichedInverseIncrementReserve_pos ht htu)
  have hf16 : 0 < actionPowerFlow 16 u t := by
    have hh := normalizedInverseReserveFlow_pos ht htu
    have hid : actionPowerFlow 16 u t=normalizedInverseReserveFlow u t := by
      unfold actionPowerFlow actionPowerFlowKernel normalizedInverseReserveFlow
      ring
    rwa [hid]
  have hf36 : 0 < actionPowerFlow 36 u t :=
    hf16.trans (actionPowerFlow_thirtysix_gt_sixteen ht htu)
  have hc16 : 0 < (9+12*Z u t+16*g u t)/5-4-intrinsicClockLogElasticity u t := by
    linarith only [hclock,hg]
  have hc36 : 0 < (9+12*Z u t+36*g u t)/5-4-intrinsicClockLogElasticity u t := by
    linarith only [hclock,hg]
  exact add_pos_of_pos_of_nonneg (add_pos (mul_pos hc16 h16) hf16)
    (mul_nonneg (by positivity) (add_pos (mul_pos hc36 h36) hf36).le)

end
end RHTower.ThetaCuspDefect
