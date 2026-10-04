import GaloisForLFunctions.RHTower.ThetaCuspC5InverseClockOperator
/-! Exact positive clock-mass debt. The full inverse-clock force must absorb this
adverse correction; its global positivity is not asserted here. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "E" => completedDecayEvenPrimitive
local notation "Z" => curvatureShapeAction
local notation "d" => completedLocalDenominator
local notation "k" => denominatorClockRate

/-- The positive weight governing the clock mass beyond its exact leading term. -/
def clockMassDebtKernel (t s : ℝ) : ℝ := 5*t/2-s-s^2/(2*t)

theorem clockMassDebtKernel_pos {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc 0 t) :
    0 < clockMassDebtKernel t s := by
  have hst := mul_le_mul_of_nonneg_right hs.2 ht.le
  have hs2 : s^2 ≤ t^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs.2) (add_nonneg ht.le hs.1)]
  have hi : 2*t*clockMassDebtKernel t s=5*t^2-2*t*s-s^2 := by
    unfold clockMassDebtKernel
    field_simp [ht.ne']
  have ht2 := sq_pos_of_pos ht
  have hp : 0 < 2*t*clockMassDebtKernel t s := by nlinarith only [hi,hst,hs2,ht2]
  exact pos_of_mul_pos_right hp (show 0 ≤ 2*t by positivity)

private theorem p_deriv (u s : ℝ) : HasDerivAt (p u) (r u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem r_pos (u s : ℝ) : 0 < r u s := by
  unfold shapeCurvatureSecond
  exact div_pos (add_pos (thetaCuspLogCurvatureJetTwo_pos_all (u+s))
    (thetaCuspLogCurvatureJetTwo_pos_all (u-s))) (by norm_num)
private theorem r_continuous (u : ℝ) : Continuous (r u) := by
  have hc : Continuous thetaCuspLogCurvatureJetTwo :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_thetaCuspLogCurvatureJetTwo x).continuousAt)
  exact ((hc.comp (continuous_const.add continuous_id)).add
    (hc.comp (continuous_const.sub continuous_id))).div_const 2
private theorem debtKernel_deriv (t s : ℝ) :
    HasDerivAt (clockMassDebtKernel t) (-1-s/t) s := by
  convert! ((hasDerivAt_const s (5*t/2)).sub (hasDerivAt_id s)).sub
    (((hasDerivAt_id s).pow 2).div_const (2*t)) using 1
  dsimp only [id_eq]
  ring
private def clockDebtPrimitive (u t s : ℝ) : ℝ :=
  clockMassDebtKernel t s*p u s+(1+s/t)*e u s-E u s/t
private theorem clockDebtPrimitive_deriv (u t s : ℝ) :
    HasDerivAt (clockDebtPrimitive u t) (clockMassDebtKernel t s*r u s) s := by
  have hh := (((debtKernel_deriv t s).mul (p_deriv u s)).add
    ((((hasDerivAt_id s).div_const t).const_add 1).mul
      (hasDerivAt_completedCurvatureEven u s))).sub
    ((hasDerivAt_completedDecayEvenPrimitive u s).div_const t)
  convert! hh using 1
  dsimp only [shapeCurvatureSlope,id_eq]
  ring

/-- Exact linear clock debt, written as one positive source integral. -/
theorem clockMassDebt_integral_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ s in 0..t, clockMassDebtKernel t s*r u s)=d u t-c u-E u t/t := by
  have hc := (continuous_iff_continuousAt.mpr (fun s => (debtKernel_deriv t s).continuousAt)).mul
    (r_continuous u)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => clockDebtPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)
  simp only [clockDebtPrimitive,clockMassDebtKernel,shapeCurvatureSlope,completedCurvatureEven,
    completedDecayEvenPrimitive_zero,add_zero,sub_zero,sub_self,mul_zero,zero_div,zero_add] at hh
  unfold clockMassDebtKernel
  rw [hh]
  unfold completedLocalDenominator completedCurvatureEven
  field_simp [ht.ne']
  ring

theorem clockMassDebt_integral_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < ∫ s in 0..t, clockMassDebtKernel t s*r u s := by
  have hm : StrictMonoOn (clockDebtPrimitive u t) (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s _; exact (clockDebtPrimitive_deriv u t s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      rw [(clockDebtPrimitive_deriv u t s).deriv]
      exact mul_pos (clockMassDebtKernel_pos ht ⟨hs'.1.le,hs'.2.le⟩) (r_pos u s)
  have hh := sub_pos.mpr (hm ⟨le_rfl,ht.le⟩ ⟨ht.le,le_rfl⟩ ht)
  have hc := (continuous_iff_continuousAt.mpr (fun s => (debtKernel_deriv t s).continuousAt)).mul
    (r_continuous u)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => clockDebtPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)]
  exact hh

/-- Exact positive mass correction that the full supersolution must absorb. -/
def intrinsicClockMassDebt (u t : ℝ) : ℝ :=
  18*t^2*(∫ s in 0..t, clockMassDebtKernel t s*r u s)+
    (9/(2*c u))*t^2*(d u t-2*c u)^2

theorem intrinsicClockMassDebt_pos (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < intrinsicClockMassDebt u t := by
  have hh := clockMassDebt_integral_pos u ht
  have hc := thetaCuspLogCurvature_pos u
  unfold intrinsicClockMassDebt
  positivity

theorem intrinsicClockMassDebt_eq (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (k u)^2*t^2*(d u t)^2-18*Z u t=intrinsicClockMassDebt u t := by
  have hk : (k u)^2=9/(2*c u) :=
    (eq_div_iff (mul_ne_zero (by norm_num) (thetaCuspLogCurvature_pos u).ne')).mpr (denominatorClockRate_sq u)
  unfold intrinsicClockMassDebt curvatureShapeAction
  rw [clockMassDebt_integral_identity u ht,hk]
  field_simp [ht.ne',(thetaCuspLogCurvature_pos u).ne']
  ring

/-- The flat clock mass is strictly below the actual mass at every positive displacement. -/
theorem intrinsicClockMass_gt_leading (u : ℝ) {t : ℝ} (ht : 0 < t) :
    18*Z u t < (k u)^2*t^2*(d u t)^2 := by
  have hh := intrinsicClockMassDebt_pos u ht
  rw [←intrinsicClockMassDebt_eq u ht] at hh
  exact sub_pos.mp hh

/-- The full force retains the exact adverse integral and quadratic clock debt. -/
theorem intrinsicClockForce_exact_massDebt (u : ℝ) {t : ℝ} (ht : 0 < t) :
    intrinsicClockForce u t+normalizedActionInverseReserve u t*intrinsicClockMassDebt u t=
      intrinsicClockForceKernel (Z u t) (curvatureShapeAlpha u t) (curvatureShapeGamma u t)
        (curvatureShapeBeta u t) (curvatureShapeDelta u t) (curvatureShapeEpsilon u t)
        (curvatureShapeZeta u t) (18*Z u t) := by
  rw [intrinsicClockForce_eq_kernel u ht,←intrinsicClockMassDebt_eq u ht,
    normalizedActionInverseReserve_polynomial u ht]
  unfold intrinsicClockForceKernel
  ring

end
end RHTower.ThetaCuspDefect
