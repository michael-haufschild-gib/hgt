import GaloisForLFunctions.RHTower.ThetaCuspC5CoupledShapeDynamics
/-! Exact common-defect propagation for the full reflected source.
Curvature, slope, primitive and action are moments of the same literal
positive defect c''-4c. Center propagation retains that defect and gives
a source-derived relation between clock mass and physical displacement.
The complete inverse-clock forcing sign remains open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "c" => thetaCuspLogCurvature
local notation "c1" => thetaCuspLogCurvatureJet
local notation "e" => completedCurvatureEven
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction

/-- One common positive defect source for all reflected profile moments. -/
def reflectedCurvatureDefect (u s : ℝ) : ℝ :=
  (curvatureDefect (u+s)+curvatureDefect (u-s))/2

theorem reflectedCurvatureDefect_eq (u s : ℝ) :
    reflectedCurvatureDefect u s=r u s-4*e u s := by
  unfold reflectedCurvatureDefect curvatureDefect shapeCurvatureSecond completedCurvatureEven
  ring

theorem reflectedCurvatureDefect_pos {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    0 < reflectedCurvatureDefect u s := by
  unfold reflectedCurvatureDefect
  exact div_pos (add_pos (curvatureDefect_pos (show 0 ≤ u+s by linarith))
    (curvatureDefect_pos (sub_nonneg.mpr hsu))) (by norm_num)

private theorem defect_continuous : Continuous curvatureDefect :=
  continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_curvatureDefect s).continuousAt)
private theorem reflected_continuous (u : ℝ) : Continuous (reflectedCurvatureDefect u) :=
  ((defect_continuous.comp (continuous_const.add continuous_id)).add
    (defect_continuous.comp (continuous_const.sub continuous_id))).div_const 2
private theorem p_deriv (u s : ℝ) : HasDerivAt (p u) (r u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem Q_deriv (u s : ℝ) : HasDerivAt (Q u) (2*E u s) s := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u s using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring
private theorem c1_zero : c1 0=0 := by
  have hh := thetaCuspLogCurvatureJet_neg 0
  simp only [neg_zero] at hh
  linarith only [hh]

private def curvaturePropagatorPrimitive (u t s : ℝ) : ℝ :=
  Real.sinh (2*(t-s))*p u s/2+Real.cosh (2*(t-s))*e u s
private theorem curvaturePropagatorPrimitive_deriv (u t s : ℝ) :
    HasDerivAt (curvaturePropagatorPrimitive u t)
      (Real.sinh (2*(t-s))*reflectedCurvatureDefect u s/2) s := by
  have hs := (Real.hasDerivAt_sinh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hc := (Real.hasDerivAt_cosh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hh := ((hs.mul (p_deriv u s)).div_const 2).add (hc.mul (hasDerivAt_completedCurvatureEven u s))
  convert! hh using 1
  rw [reflectedCurvatureDefect_eq]
  dsimp only [id_eq,Function.comp_def,Pi.sub_apply,shapeCurvatureSlope]
  ring

/-- Exact common-defect representation of the reflected curvature. -/
theorem reflectedCurvature_defect_propagation (u t : ℝ) :
    e u t=c u*Real.cosh (2*t)+
      ∫ s in 0..t, Real.sinh (2*(t-s))*reflectedCurvatureDefect u s/2 := by
  have hc : Continuous (fun s => Real.sinh (2*(t-s))*reflectedCurvatureDefect u s/2) :=
    ((Real.continuous_sinh.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (reflected_continuous u)).div_const 2
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => curvaturePropagatorPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)
  simp only [curvaturePropagatorPrimitive,sub_self,mul_zero,Real.sinh_zero,Real.cosh_zero,
    zero_mul,zero_div,zero_add,one_mul,shapeCurvatureSlope,completedCurvatureEven,
    add_zero,sub_zero] at hh
  dsimp only [completedCurvatureEven]
  nlinarith only [hh]

private def primitivePropagatorPrimitive (u t s : ℝ) : ℝ :=
  (Real.cosh (2*(t-s))-1)*p u s/4+Real.sinh (2*(t-s))*e u s/2+E u s
private theorem primitivePropagatorPrimitive_deriv (u t s : ℝ) :
    HasDerivAt (primitivePropagatorPrimitive u t)
      ((Real.cosh (2*(t-s))-1)*reflectedCurvatureDefect u s/4) s := by
  have hs := (Real.hasDerivAt_sinh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hc := (Real.hasDerivAt_cosh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hh := ((((hc.sub_const 1).mul (p_deriv u s)).div_const 4).add
    ((hs.mul (hasDerivAt_completedCurvatureEven u s)).div_const 2)).add
    (hasDerivAt_completedDecayEvenPrimitive u s)
  convert! hh using 1
  rw [reflectedCurvatureDefect_eq]
  dsimp only [id_eq,Function.comp_def,Pi.sub_apply,shapeCurvatureSlope]
  ring

/-- Exact common-defect representation of the primitive; all moments stay coupled. -/
theorem reflectedPrimitive_defect_propagation (u t : ℝ) :
    E u t=c u*Real.sinh (2*t)/2+
      ∫ s in 0..t, (Real.cosh (2*(t-s))-1)*reflectedCurvatureDefect u s/4 := by
  have hc : Continuous (fun s => (Real.cosh (2*(t-s))-1)*reflectedCurvatureDefect u s/4) :=
    (((Real.continuous_cosh.comp (continuous_const.mul (continuous_const.sub continuous_id))).sub
      continuous_const).mul (reflected_continuous u)).div_const 4
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => primitivePropagatorPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)
  simp only [primitivePropagatorPrimitive,sub_self,mul_zero,Real.sinh_zero,Real.cosh_zero,
    zero_mul,zero_div,zero_add,one_mul,shapeCurvatureSlope,completedCurvatureEven,
    add_zero,sub_zero,completedDecayEvenPrimitive_zero] at hh
  nlinarith only [hh]

private def actionPropagatorPrimitive (u t s : ℝ) : ℝ :=
  (Real.sinh (2*(t-s))-2*(t-s))*p u s/4+
    (Real.cosh (2*(t-s))-1)*e u s/2+2*(t-s)*E u s+Q u s
private theorem actionPropagatorPrimitive_deriv (u t s : ℝ) :
    HasDerivAt (actionPropagatorPrimitive u t)
      ((Real.sinh (2*(t-s))-2*(t-s))*reflectedCurvatureDefect u s/4) s := by
  have hlin := ((hasDerivAt_id s).const_sub t).const_mul 2
  have hs := (Real.hasDerivAt_sinh (2*(t-s))).comp s hlin
  have hc := (Real.hasDerivAt_cosh (2*(t-s))).comp s hlin
  have hh := (((((hs.sub hlin).mul (p_deriv u s)).div_const 4).add
    (((hc.sub_const 1).mul (hasDerivAt_completedCurvatureEven u s)).div_const 2)).add
    (hlin.mul (hasDerivAt_completedDecayEvenPrimitive u s))).add (Q_deriv u s)
  convert! hh using 1
  rw [reflectedCurvatureDefect_eq]
  dsimp only [id_eq,Function.comp_def,Pi.sub_apply,shapeCurvatureSlope]
  ring

/-- Exact common-defect representation of the action. -/
theorem reflectedAction_defect_propagation (u t : ℝ) :
    Q u t=c u*(Real.cosh (2*t)-1)/2+
      ∫ s in 0..t, (Real.sinh (2*(t-s))-2*(t-s))*reflectedCurvatureDefect u s/4 := by
  have hc : Continuous (fun s => (Real.sinh (2*(t-s))-2*(t-s))*reflectedCurvatureDefect u s/4) :=
    (((Real.continuous_sinh.comp (continuous_const.mul (continuous_const.sub continuous_id))).sub
      (continuous_const.mul (continuous_const.sub continuous_id))).mul (reflected_continuous u)).div_const 4
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => actionPropagatorPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)
  simp only [actionPropagatorPrimitive,sub_self,mul_zero,Real.sinh_zero,Real.cosh_zero,
    zero_mul,zero_div,zero_add,one_mul,shapeCurvatureSlope,completedCurvatureEven,
    add_zero,sub_zero,completedDecayEvenPrimitive_zero,Q_zero] at hh
  nlinarith only [hh]

private def slopePropagatorPrimitive (u t s : ℝ) : ℝ :=
  Real.cosh (2*(t-s))*p u s+2*Real.sinh (2*(t-s))*e u s
private theorem slopePropagatorPrimitive_deriv (u t s : ℝ) :
    HasDerivAt (slopePropagatorPrimitive u t)
      (Real.cosh (2*(t-s))*reflectedCurvatureDefect u s) s := by
  have hs := (Real.hasDerivAt_sinh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hc := (Real.hasDerivAt_cosh (2*(t-s))).comp s (((hasDerivAt_id s).const_sub t).const_mul 2)
  have hh := (hc.mul (p_deriv u s)).add ((hs.const_mul 2).mul (hasDerivAt_completedCurvatureEven u s))
  convert! hh using 1
  rw [reflectedCurvatureDefect_eq]
  dsimp only [id_eq,Function.comp_def,Pi.sub_apply,shapeCurvatureSlope]
  ring

/-- Exact common-defect representation of the reflected curvature slope. -/
theorem reflectedSlope_defect_propagation (u t : ℝ) :
    p u t=2*c u*Real.sinh (2*t)+
      ∫ s in 0..t, Real.cosh (2*(t-s))*reflectedCurvatureDefect u s := by
  have hc : Continuous (fun s => Real.cosh (2*(t-s))*reflectedCurvatureDefect u s) :=
    (Real.continuous_cosh.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (reflected_continuous u)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => slopePropagatorPrimitive_deriv u t s) (hc.intervalIntegrable 0 t)
  simp only [slopePropagatorPrimitive,sub_self,mul_zero,Real.sinh_zero,Real.cosh_zero,
    zero_mul,zero_add,one_mul,shapeCurvatureSlope,completedCurvatureEven,add_zero,sub_zero] at hh
  dsimp only [shapeCurvatureSlope]
  nlinarith only [hh]

/-- Actual center propagation, retaining the full positive curvature defect. -/
theorem sourceCurvature_defect_propagation (x : ℝ) :
    c x=c 0*Real.cosh (2*x)+∫ s in 0..x, Real.sinh (2*(x-s))*curvatureDefect s/2 := by
  let F := fun s => Real.sinh (2*(x-s))*c1 s/2+Real.cosh (2*(x-s))*c s
  have hd (s : ℝ) : HasDerivAt F (Real.sinh (2*(x-s))*curvatureDefect s/2) s := by
    have hs := (Real.hasDerivAt_sinh (2*(x-s))).comp s (((hasDerivAt_id s).const_sub x).const_mul 2)
    have hc := (Real.hasDerivAt_cosh (2*(x-s))).comp s (((hasDerivAt_id s).const_sub x).const_mul 2)
    convert! ((hs.mul (hasDerivAt_thetaCuspLogCurvatureJet s)).div_const 2).add
      (hc.mul (hasDerivAt_thetaCuspLogCurvature s)) using 1
    dsimp only [curvatureDefect,id_eq,Function.comp_def,Pi.sub_apply]
    ring
  have hc : Continuous (fun s => Real.sinh (2*(x-s))*curvatureDefect s/2) :=
    ((Real.continuous_sinh.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      defect_continuous).div_const 2
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable 0 x)
  simp only [F,c1_zero,sub_self,mul_zero,Real.sinh_zero,Real.cosh_zero,
    zero_mul,zero_div,zero_add,one_mul,sub_zero] at hh
  linarith only [hh]

/-- The center grows with displacement; its clock rate cannot be chosen independently. -/
theorem sourceCurvature_gt_eighteen_cosh {x : ℝ} (hx : 0 ≤ x) :
    18*Real.cosh (2*x) < c x := by
  have hp : 0 ≤ ∫ s in 0..x, Real.sinh (2*(x-s))*curvatureDefect s/2 := by
    apply intervalIntegral.integral_nonneg hx
    intro s hs
    exact div_nonneg (mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith [hs.2]))
      (curvatureDefect_pos hs.1).le) (by norm_num)
  have hmul := mul_lt_mul_of_pos_right (sourceCurvature_gt_eighteen (x := 0) le_rfl)
    (Real.cosh_pos (2*x))
  rw [sourceCurvature_defect_propagation x]
  linarith only [hp,hmul]

/-- A source-derived constraint coupling the clock mass to physical displacement. -/
theorem denominatorClockRate_cosh_control {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    (denominatorClockRate u)^2*Real.cosh (2*t)<1/4 := by
  have hc := sourceCurvature_gt_eighteen_cosh (ht.trans htu)
  have hcosh : Real.cosh (2*t) ≤ Real.cosh (2*u) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*t),abs_of_nonneg (by linarith : 0 ≤ 2*u)]
    linarith only [htu]
  have hh := mul_lt_mul_of_pos_left hc (sq_pos_of_pos (denominatorClockRate_pos u))
  have hk := denominatorClockRate_sq u
  have hcmp := mul_le_mul_of_nonneg_left hcosh (sq_nonneg (denominatorClockRate u))
  nlinarith only [hh,hk,hcmp]

end
end RHTower.ThetaCuspDefect
