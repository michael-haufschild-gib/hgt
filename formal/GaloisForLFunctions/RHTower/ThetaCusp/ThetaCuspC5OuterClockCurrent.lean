import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CurrentSchurCoupling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CommonDefectPropagation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5LinearClockEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
/-! Complete enriched clock-current positivity on the unbounded physical chamber.
The proof retains the actual center/displacement coupling and proves strict
growth of the action-squared source increment throughout the whole chamber.
The remaining current sign on 0 < t < 2 is not asserted here. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "Q" => thetaCuspReflectedLogAction
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "g" => curvatureShapeGamma
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "ep" => curvatureShapeEpsilon
local notation "y" => completedFirstDenominator
local notation "d" => completedLocalDenominator
local notation "k" => denominatorClockRate

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem beta_nonneg (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ b u t := by
  have hp : 0 ≤ p u t := by
    unfold shapeCurvatureSlope
    exact div_nonneg (sub_nonneg.mpr (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)
  unfold curvatureShapeBeta
  exact div_nonneg (mul_nonneg (sq_nonneg t) hp) (E_pos u ht).le
private theorem gamma_bounds {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    1 ≤ g u t ∧ g u t ≤ a u t := by
  have hQ:=thetaCuspReflectedLogAction_pos (u:=u) ht
  have hgpos : 0 < g u t := div_pos (mul_pos ht (E_pos u ht)) hQ
  have hg : 1 ≤ g u t := by
    have hh:=two_mul_action_le_velocity_of_jetTwo_nonneg ht htu
      (fun x _=>(thetaCuspLogCurvatureJetTwo_pos_all x).le)
    unfold thetaCuspReflectedActionVelocity at hh
    rw [show thetaCuspReflectedLogJetOne u t=2*E u t by rw [completedDecayEvenPrimitive_eq]; ring] at hh
    unfold curvatureShapeGamma
    exact (le_div_iff₀ hQ).mpr (by linarith only [hh])
  have hd : 0 < t*deriv (g u) t := by
    rw [(hasDerivAt_curvatureShapeGamma u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu) (sq_pos_of_pos hQ))
  rw [curvatureShapeGamma_evolution u ht] at hd
  have hi:=(mul_pos_iff_of_pos_left hgpos).mp hd
  exact ⟨hg,by linarith only [hg,hi]⟩
private theorem action_lower {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : 18*t^2 ≤ Z u t := by
  have hd (s : ℝ) : HasDerivAt (fun zv=>E u zv-18*zv) (e u s-18) s := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u s).sub ((hasDerivAt_id s).const_mul 18) using 1
    ring
  have hm : MonotoneOn (fun s=>E u s-18*s) (Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 u := by simpa only [interior_Icc] using hs
      rw [(hd s).deriv]
      have hp:=sourceCurvature_gt_eighteen (show 0≤u+s by linarith [hs'.1,hs'.2])
      have hm:=sourceCurvature_gt_eighteen (show 0≤u-s by linarith [hs'.2])
      unfold completedCurvatureEven
      linarith only [hp,hm]
  have hh:=hm (show (0:ℝ)∈Icc 0 u from ⟨le_rfl,ht.le.trans htu⟩) ⟨ht.le,htu⟩ ht.le
  simp only [completedDecayEvenPrimitive_zero,mul_zero,sub_zero] at hh
  have hp:=mul_nonneg ht.le hh
  unfold curvatureShapeAction
  nlinarith only [hp]
private theorem delta_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) : q u t ≤ a u t*Z u t/2 := by
  have hp:=source_projective_upper (show 0≤u+t by linarith)
  have hm:=source_projective_upper (sub_nonneg.mpr htu)
  have hr : r u t < 9*e u t := by
    unfold shapeCurvatureSecond completedCurvatureEven
    linarith only [hp,hm]
  have hh:=mul_le_mul_of_nonneg_left hr.le
    (div_nonneg (pow_nonneg ht.le 3) (E_pos u ht).le)
  have hq : q u t ≤ 9*a u t*t^2 := by
    unfold curvatureShapeDelta curvatureShapeAlpha
    convert! hh using 1 <;> field_simp [(E_pos u ht).ne']
  have ha : 0 ≤ a u t := by
    unfold curvatureShapeAlpha
    exact div_nonneg (mul_nonneg ht.le (completedCurvatureEven_pos u t).le) (E_pos u ht).le
  have hpay:=mul_le_mul_of_nonneg_left (action_lower ht htu) ha
  nlinarith only [hq,hpay]

/-- The action-squared enrichment contributes a strictly positive source flow. -/
theorem actionPowerFlow_thirtysix_gt_sixteen {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    actionPowerFlow 16 u t < actionPowerFlow 36 u t := by
  rcases gamma_bounds ht htu with ⟨hg,hga⟩
  have ha:=hg.trans hga
  have ha0 : 0<a u t := lt_of_lt_of_le (by norm_num) ha
  have hg0 : 0<g u t := lt_of_lt_of_le (by norm_num) hg
  have hb:=beta_nonneg u ht
  have hZ : 0<Z u t := mul_pos ht (E_pos u ht)
  have hq0 : 0≤q u t := by
    have hr : 0<r u t := by
      unfold shapeCurvatureSecond
      exact div_pos (add_pos (thetaCuspLogCurvatureJetTwo_pos_all (u+t))
        (thetaCuspLogCurvatureJetTwo_pos_all (u-t))) (by norm_num)
    exact div_nonneg (mul_nonneg (pow_nonneg ht.le 3) hr.le) (E_pos u ht).le
  have hq:=delta_upper ht htu
  have he : ep u t ≤ (83/9)*Z u t*b u t := by
    have hh:=curvatureShapeEpsilon_affine_upper ht htu
    have hz:=mul_le_mul_of_nonneg_right (action_lower ht htu) hb
    nlinarith only [hh,hz,pow_nonneg ht.le 4]
  let X:=a u t+b u t-(a u t)^2
  let Y:=(2-a u t)*b u t+q u t
  let V:=g u t*(1+a u t-2*g u t)
  let D:=2*a u t+b u t
  let B:=24*Z u t+42*g u t+13
  let H:=D*B-5*(3*b u t+q u t)
  have hX : 0<X := by
    dsimp only [X]
    rw [←curvatureShapeAlpha_evolution u ht,(hasDerivAt_curvatureShapeAlpha u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeAlpha_current_pos ht htu) (sq_pos_of_pos (E_pos u ht)))
  have hY : 0<Y := by
    have hh:=curvatureShapeBeta_growth ht htu
    rw [curvatureShapeBeta_evolution u ht] at hh
    exact hb.trans_lt hh
  have hV : 0<V := by
    dsimp only [V]
    rw [←curvatureShapeGamma_evolution u ht,(hasDerivAt_curvatureShapeGamma u ht).deriv]
    exact mul_pos ht (div_pos (curvatureShapeGamma_current_pos ht htu)
      (sq_pos_of_pos (thetaCuspReflectedLogAction_pos (u:=u) ht)))
  have hD : 0<D := by dsimp only [D]; positivity
  have hB : 0<B := by dsimp only [B]; positivity
  have hB15 : 0<B-15 := by dsimp only [B]; linarith only [hZ,hg]
  have hH : 0<H := by
    have hh:=enrichedInverseIncrementReserve_pos ht htu
    change 0<(4*g u t/5)*H at hh
    exact (mul_pos_iff_of_pos_left (by positivity : 0<4*g u t/5)).mp hh
  have hqstep : (3-a u t)*q u t ≤ a u t*Z u t := by
    have hh:=mul_nonneg (sub_nonneg.mpr ha) hq0
    nlinarith only [hh,hq]
  let T:=24*D*Z u t*(1+a u t)-5*(3-a u t)*q u t-5*ep u t
  let P:=(a u t*(43+48*a u t)+(24*a u t-199/9)*b u t)*Z u t
  have hP : 0<P := by
    have hc : 0<24*a u t-199/9 := by linarith only [ha]
    dsimp only [P]
    positivity
  have hPT : P≤T := by
    dsimp only [P,T,D]
    nlinarith only [hqstep,he]
  have hT : 0<T := hP.trans_le hPT
  have hid : actionPowerFlow 36 u t-actionPowerFlow 16 u t=
      (4/5)*(V*H+g u t*(2*B*X+(B-15)*Y+42*D*V+T)) := by
    unfold actionPowerFlow actionPowerFlowKernel
    dsimp only [X,Y,V,D,B,H,T]
    ring
  apply sub_pos.mp
  rw [hid]
  positivity

private theorem clock_center_outer {u t : ℝ} (ht : 2≤t) (htu : t≤u) :
    k u*(1+t)*(1+2*t)<t := by
  have ht0 : 0<t := by linarith only [ht]
  have hc : 1+2*t^2+(2/3)*t^4≤Real.cosh (2*t) := by
    have hh:=sum_le_hasSum (Finset.range 3)
      (fun n _=>div_nonneg ((even_two_mul n).pow_nonneg (2*t)) (by positivity)) (Real.hasSum_cosh (2*t))
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    nlinarith only [hh]
  have hpoly : (1+t)^2*(1+2*t)^2<4*t^2*(1+2*t^2+(2/3)*t^4) := by
    have hx : 0≤t-2 := sub_nonneg.mpr ht
    have hid : 4*t^2*(1+2*t^2+(2/3)*t^4)-(1+t)^2*(1+2*t)^2=
        (8/3)*(t-2)^6+32*(t-2)^5+164*(t-2)^4+(1340/3)*(t-2)^3+
          655*(t-2)^2+454*(t-2)+269/3 := by ring
    apply sub_pos.mp
    rw [hid]
    positivity
  have hmul:=mul_le_mul_of_nonneg_left hc (show 0≤4*t^2 by positivity)
  have hbase : (1+t)^2*(1+2*t)^2<4*t^2*Real.cosh (2*t) := hpoly.trans_le hmul
  have hk:=denominatorClockRate_cosh_control ht0.le htu
  have hp:=mul_lt_mul_of_pos_left hbase (sq_pos_of_pos (denominatorClockRate_pos u))
  have hq:=mul_lt_mul_of_pos_left hk (show 0<4*t^2 by positivity)
  have hs : (k u*(1+t)*(1+2*t))^2<t^2 := by nlinarith only [hp,hq]
  nlinarith only [hs,ht0]

private theorem beta_lt {u t : ℝ} (ht : 0<t) (htu : t≤u) : b u t<2*t*a u t := by
  have hv:=ThetaCurvature.velocityGap_pos (show 0≤u+t by linarith)
  have hm:=sourceVelocity_nonneg (sub_nonneg.mpr htu)
  have hc:=thetaCuspLogCurvature_pos (u-t)
  have hp : p u t<2*e u t := by
    unfold shapeCurvatureSlope completedCurvatureEven
    linarith only [hv,hm,hc]
  have hh:=mul_lt_mul_of_pos_left hp (div_pos (sq_pos_of_pos ht) (E_pos u ht))
  unfold curvatureShapeAlpha curvatureShapeBeta
  convert! hh using 1 <;> ring

/-- Rational upper clock with the literal center, displacement and reflected source. -/
def intrinsicClockUpperElasticity (u t : ℝ) : ℝ :=
  (2*a u t+b u t)/(1+a u t)*linearClockEnvelope (k u*y u t)

private theorem clock_ratio (u : ℝ) {t : ℝ} (ht : 0<t) :
    (2*a u t+b u t)/(1+a u t)=t*d u t/y u t := by
  have hE:=E_pos u ht
  have hy : 0<E u t+t*e u t := add_pos hE (mul_pos ht (completedCurvatureEven_pos u t))
  unfold curvatureShapeAlpha curvatureShapeBeta completedFirstDenominator completedLocalDenominator shapeCurvatureSlope
  field_simp [hE.ne',hy.ne']

theorem intrinsicClockLogElasticity_lt_upper (u : ℝ) {t : ℝ} (ht : 0<t) :
    intrinsicClockLogElasticity u t < intrinsicClockUpperElasticity u t := by
  have hT : 0<(2*a u t+b u t)/(1+a u t) := by
    rw [clock_ratio u ht]
    exact div_pos (mul_pos ht (completedLocalDenominator_pos_nonneg u ht.le))
      (completedFirstDenominator_pos u ht)
  let z:=k u*y u t
  have hz : 0<z := mul_pos (denominatorClockRate_pos u) (completedFirstDenominator_pos u ht)
  have hh:=mul_lt_mul_of_pos_left (clock_coth_lt_linearEnvelope hz) hT
  have hid : (2*a u t+b u t)/(1+a u t)*(z*Real.cosh z/Real.sinh z)=intrinsicClockLogElasticity u t := by
    rw [clock_ratio u ht]
    unfold intrinsicClockLogElasticity denominatorClockProfileJet denominatorClockProfile
    dsimp only [z]
    field_simp [(completedFirstDenominator_pos u ht).ne',(denominatorClockProfile_pos u ht).ne']
  rw [hid] at hh
  exact hh

/-- Center propagation makes the complete clock factor favorable on the unbounded chamber. -/
theorem intrinsicClockUpperElasticity_lt_actionGrowth {u t : ℝ} (ht : 2≤t) (htu : t≤u) :
    intrinsicClockUpperElasticity u t<1+12*Z u t/5 := by
  have ht0 : 0<t := by linarith only [ht]
  have ha0 : 0<a u t := div_pos (mul_pos ht0 (completedCurvatureEven_pos u t)) (E_pos u ht0)
  have hb:=beta_nonneg u ht0
  have hD : 0<2*a u t+b u t := by positivity
  have hsmall:=beta_lt ht0 htu
  have ha:=curvatureShapeAlpha_lt ht0 htu
  have hd1 : 2*a u t+b u t<2*a u t*(1+t) := by nlinarith only [hsmall]
  have hd2:=mul_lt_mul_of_pos_right ha (show 0<2*(1+t) by positivity)
  have hd3 : 2*a u t+b u t<2*(1+t)*(1+2*t) := by nlinarith only [hd1,hd2]
  have hdk:=mul_lt_mul_of_pos_left hd3 (denominatorClockRate_pos u)
  have hcenter:=clock_center_outer ht htu
  have hclock : k u*(2*a u t+b u t)<2*t := by nlinarith only [hdk,hcenter]
  have hsource:=mul_lt_mul_of_pos_right hclock (E_pos u ht0)
  have hid : k u*(2*a u t+b u t)*E u t=k u*t*d u t := by
    unfold curvatureShapeAlpha curvatureShapeBeta completedLocalDenominator shapeCurvatureSlope
    field_simp [(E_pos u ht0).ne']
  rw [hid] at hsource
  have hmass : k u*t*d u t<2*Z u t := by
    change k u*t*d u t<2*(t*E u t)
    nlinarith only [hsource]
  have hratio : (2*a u t+b u t)/(1+a u t)<2*(1+t) := by
    apply (div_lt_iff₀ (by positivity : 0<1+a u t)).mpr
    nlinarith only [hd1,ht0]
  let z:=k u*y u t
  have hz : 0<z := mul_pos (denominatorClockRate_pos u) (completedFirstDenominator_pos u ht0)
  have hlin : linearClockEnvelope z<z+3 := by
    unfold linearClockEnvelope
    apply (div_lt_iff₀ (by positivity : 0<15+3*z+z^2)).mpr
    nlinarith only [hz]
  have hT : 0<(2*a u t+b u t)/(1+a u t) := by positivity
  have henv:=mul_lt_mul_of_pos_left hlin hT
  have heq : (2*a u t+b u t)/(1+a u t)*(z+3)=
      k u*t*d u t+3*((2*a u t+b u t)/(1+a u t)) := by
    rw [clock_ratio u ht0]
    dsimp only [z]
    field_simp [(completedFirstDenominator_pos u ht0).ne']
  rw [heq] at henv
  have henv' : intrinsicClockUpperElasticity u t<2*Z u t+6*(1+t) := by
    change (2*a u t+b u t)/(1+a u t)*linearClockEnvelope z<2*Z u t+6*(1+t)
    nlinarith only [henv,hmass,hratio]
  have hZ:=action_lower ht0 htu
  have hs:=mul_nonneg ht0.le (sub_nonneg.mpr ht)
  have hpay : 2*Z u t+6*(1+t)<1+12*Z u t/5 := by nlinarith only [hZ,hs,ht]
  exact henv'.trans hpay

/-- Complete current with the upper clock inserted before separating source terms. -/
def enrichedClockUpperCurrent (u t : ℝ) : ℝ :=
  actionPowerCurrentKernel 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t) (intrinsicClockUpperElasticity u t)+
    (Q u t)^2/15*actionPowerCurrentKernel 36 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t)
      (intrinsicClockUpperElasticity u t)

private theorem reserve_pos {u t : ℝ} (ht : 0<t) (htu : t≤u) :
    0<actionPowerReserve 16 u t ∧ 0<actionPowerReserve 36 u t := by
  rw [actionPowerReserve_sixteen u ht,actionPowerReserve_thirtysix u ht]
  exact ⟨normalizedActionInverseReserve_pos ht htu,
    add_pos (normalizedActionInverseReserve_pos ht htu) (enrichedInverseIncrementReserve_pos ht htu)⟩

theorem enrichedClockCurrent_gt_upperCurrent {u t : ℝ} (ht : 0<t) (htu : t≤u) :
    enrichedClockUpperCurrent u t<enrichedClockCurrent u t := by
  rcases reserve_pos ht htu with ⟨h16,h36⟩
  have hC:=intrinsicClockLogElasticity_lt_upper u ht
  have hid : enrichedClockCurrent u t-enrichedClockUpperCurrent u t=
      (intrinsicClockUpperElasticity u t-intrinsicClockLogElasticity u t)*
        (actionPowerReserve 16 u t+(Q u t)^2/15*actionPowerReserve 36 u t) := by
    unfold enrichedClockCurrent enrichedClockUpperCurrent actionPowerCurrentKernel actionPowerReserve
    ring
  apply sub_pos.mp
  rw [hid]
  positivity

/-- The entire rational-envelope current is positive on every 2 <= t <= u. -/
theorem enrichedClockUpperCurrent_pos_outer {u t : ℝ} (ht : 2≤t) (htu : t≤u) :
    0<enrichedClockUpperCurrent u t := by
  have ht0 : 0<t := by linarith only [ht]
  have hg:=(gamma_bounds ht0 htu).1
  have hclock:=intrinsicClockUpperElasticity_lt_actionGrowth ht htu
  rcases reserve_pos ht0 htu with ⟨h16,h36⟩
  have hf16 : 0<actionPowerFlow 16 u t := by
    have hh:=normalizedInverseReserveFlow_pos ht0 htu
    have hid : actionPowerFlow 16 u t=normalizedInverseReserveFlow u t := by
      unfold actionPowerFlow actionPowerFlowKernel normalizedInverseReserveFlow
      ring
    rw [hid]
    exact hh
  have hf36 : 0<actionPowerFlow 36 u t := hf16.trans (actionPowerFlow_thirtysix_gt_sixteen ht0 htu)
  have hc16 : 0<(9+12*Z u t+16*g u t)/5-4-intrinsicClockUpperElasticity u t := by
    linarith only [hclock,hg]
  have hc36 : 0<(9+12*Z u t+36*g u t)/5-4-intrinsicClockUpperElasticity u t := by
    linarith only [hclock,hg]
  have hp16:=add_pos (mul_pos hc16 h16) hf16
  have hp36:=add_pos (mul_pos hc36 h36) hf36
  exact add_pos_of_pos_of_nonneg hp16 (mul_nonneg (by positivity) hp36.le)

/-- Full actual enriched current, with no source-sign or clock-order premise. -/
theorem enrichedClockCurrent_pos_outer {u t : ℝ} (ht : 2≤t) (htu : t≤u) :
    0<enrichedClockCurrent u t :=
  (enrichedClockUpperCurrent_pos_outer ht htu).trans
    (enrichedClockCurrent_gt_upperCurrent (by linarith only [ht]) htu)

end
end RHTower.ThetaCuspDefect
