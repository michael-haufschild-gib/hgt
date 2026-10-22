import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CoupledShapeDynamics
/-! Exact fourth-source cancellation for the intrinsic clock supersolution.
The coupled low-order shape block equals a negative variance and a complete
fourth-curvature quadrature, including its endpoint term. Both source
weights are positive, so the actual affine curvature theorem controls the
entire fourth-source debt. The nonlinear supersolution sign remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
local notation "e" => completedCurvatureEven
local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
local notation "w" => quadratureCurvatureThird

/-- Literal fourth displacement derivative, retaining both reflected sources. -/
def supersolutionCurvatureFourth (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJetFour (u+s)+thetaCuspLogCurvatureJetFour (u-s))/2
local notation "v" => supersolutionCurvatureFourth
private theorem he_deriv (u s : ℝ) : HasDerivAt (e u) (p u s) s := hasDerivAt_completedCurvatureEven u s
private theorem hp_deriv (u s : ℝ) : HasDerivAt (p u) (r u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem hr_deriv (u s : ℝ) : HasDerivAt (r u) (w u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.add hm).div_const 2 using 1
  unfold quadratureCurvatureThird
  ring
theorem hasDerivAt_quadratureCurvatureThird (u s : ℝ) : HasDerivAt (w u) (v u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetThree (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetThree (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold supersolutionCurvatureFourth
  ring
private theorem hQ_deriv (u s : ℝ) : HasDerivAt (Q u) (2*E u s) s := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u s using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring
private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem v_continuous (u : ℝ) : Continuous (v u) := by
  have h6 := (HTGeometry.contDiff_top_iteratedDeriv_real thetaCuspLogSource contDiff_thetaCuspLogSource 6).continuous
  unfold supersolutionCurvatureFourth thetaCuspLogCurvatureJetFour
  fun_prop

theorem supersolutionCurvatureFourth_affine_upper {u s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    v u s < 166*r u s-648*e u s := by
  have hp := source_fourth_curvature_affine_upper (show 0 ≤ u+s by linarith)
  have hm := source_fourth_curvature_affine_upper (show 0 ≤ u-s by linarith)
  unfold supersolutionCurvatureFourth thetaCuspLogCurvatureJetFour shapeCurvatureSecond completedCurvatureEven
  linarith

/-- Positive quadrature weight for the coupled supersolution cancellation. -/
def inverseForcePeanoKernel (t s : ℝ) : ℝ :=
  (1053/5)*t^4-(170/3)*t^2*s^2+16*s^5/(15*t)
private def h1 (t s : ℝ) : ℝ := -(340/3)*t^2*s+16*s^4/(3*t)
private def h2 (t s : ℝ) : ℝ := -(340/3)*t^2+64*s^3/(3*t)
private def h3 (t s : ℝ) : ℝ := 64*s^2/t
private def h4 (t s : ℝ) : ℝ := 128*s/t
private theorem dh0 (t s : ℝ) : HasDerivAt (inverseForcePeanoKernel t) (h1 t s) s := by
  have h := hasDerivAt_id s
  convert! ((((h.pow 2).const_mul ((170/3)*t^2)).const_sub ((1053/5)*t^4)).add
    ((h.pow 5).const_mul 16 |>.div_const (15*t))) using 1
  dsimp only [id_eq]
  unfold h1
  ring
private theorem dh1 (t s : ℝ) : HasDerivAt (h1 t) (h2 t s) s := by
  have h := hasDerivAt_id s
  convert! ((h.const_mul (-(340/3)*t^2)).add ((h.pow 4).const_mul 16 |>.div_const (3*t))) using 1
  dsimp only [id_eq]
  unfold h2
  ring
private theorem dh2 (t s : ℝ) : HasDerivAt (h2 t) (h3 t s) s := by
  convert! (((hasDerivAt_id s).pow 3).const_mul 64 |>.div_const (3*t)).const_add (-(340/3)*t^2) using 1
  dsimp only [id_eq]
  unfold h3
  ring
private theorem dh3 (t s : ℝ) : HasDerivAt (h3 t) (h4 t s) s := by
  convert! (((hasDerivAt_id s).pow 2).const_mul 64).div_const t using 1
  dsimp only [id_eq]
  unfold h4
  ring
private theorem dh4 (t s : ℝ) : HasDerivAt (h4 t) (128/t) s := by
  convert! ((hasDerivAt_id s).const_mul 128).div_const t using 1
  simp only [mul_one]

theorem inverseForcePeanoKernel_pos {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc 0 t) :
    0 < inverseForcePeanoKernel t s := by
  have hs2 : s^2 ≤ t^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hs.2) (add_nonneg ht.le hs.1)]
  have hh := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ (170/3:ℝ)*t^2 by positivity)
  have hs0 := hs.1
  have hr : 0 ≤ 16*s^5/(15*t) := by positivity
  have hp : 0 < (2309/15:ℝ)*t^4 := by positivity
  unfold inverseForcePeanoKernel
  nlinarith only [hh,hr,hp]

private def forcePrimitive (u t s : ℝ) : ℝ :=
  inverseForcePeanoKernel t s*w u s-h1 t s*r u s+h2 t s*p u s-h3 t s*e u s+
    h4 t s*E u s-(64/t)*Q u s
private theorem forcePrimitive_deriv (u t s : ℝ) :
    HasDerivAt (forcePrimitive u t) (inverseForcePeanoKernel t s*v u s) s := by
  convert! ((((((dh0 t s).mul (hasDerivAt_quadratureCurvatureThird u s)).sub ((dh1 t s).mul (hr_deriv u s))).add
    ((dh2 t s).mul (hp_deriv u s))).sub ((dh3 t s).mul (he_deriv u s))).add
    ((dh4 t s).mul (hasDerivAt_completedDecayEvenPrimitive u s))).sub
    ((hQ_deriv u s).const_mul (64/t)) using 1
  ring

private theorem force_integral (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, inverseForcePeanoKernel t s*v u s)=
      155*t^4*w u t+108*t^3*r u t-92*t^2*p u t-64*t*e u t+128*E u t-64*Q u t/t := by
  have hcH := continuous_iff_continuousAt.mpr (fun s => (dh0 t s).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => forcePrimitive_deriv u t s)
    ((hcH.mul (v_continuous u)).intervalIntegrable 0 t)]
  simp only [forcePrimitive,inverseForcePeanoKernel,h1,h2,h3,h4,quadratureCurvatureThird,
    shapeCurvatureSlope,completedDecayEvenPrimitive_zero,Q_zero,pow_succ,zero_mul,mul_zero,
    zero_div,sub_self,add_zero,sub_zero]
  field_simp [ht.ne']
  ring

/-- The source-coupled low-order block of the complete inverse supersolution forcing. -/
def inverseForceShapeBlock (u t : ℝ) : ℝ :=
  64*(curvatureShapeAlpha u t-curvatureShapeGamma u t)+92*curvatureShapeBeta u t-
    108*curvatureShapeDelta u t-155*curvatureShapeEpsilon u t-25*t^5*v u t/E u t

/-- Exact removal of the apparent second-order debt, retaining the complete
fourth source derivative, its endpoint contribution and the actual variance. -/
theorem inverseForceShapeBlock_fourth_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    E u t*inverseForceShapeBlock u t+64*(t*E u t-Q u t)^2/(t*Q u t)+
      25*t^5*v u t+(∫ s in (0:ℝ)..t, inverseForcePeanoKernel t s*v u s)=0 := by
  rw [force_integral u ht]
  unfold inverseForceShapeBlock curvatureShapeAlpha curvatureShapeGamma curvatureShapeBeta
    curvatureShapeDelta curvatureShapeEpsilon
  field_simp [ht.ne',(E_pos u ht).ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  ring

/-- The actual affine fourth-curvature source pays both positive weights.
Every lower source term and the adverse variance remain explicit. -/
theorem inverseForceShapeBlock_affine_reserve {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < E u t*inverseForceShapeBlock u t+64*(t*E u t-Q u t)^2/(t*Q u t)+
      25*t^5*(166*r u t-648*e u t)+
      (∫ s in (0:ℝ)..t, inverseForcePeanoKernel t s*(166*r u s-648*e u s)) := by
  have hcH := continuous_iff_continuousAt.mpr (fun s => (dh0 t s).continuousAt)
  have hcR := continuous_iff_continuousAt.mpr (fun s => (hr_deriv u s).continuousAt)
  have hcE := continuous_iff_continuousAt.mpr (fun s => (he_deriv u s).continuousAt)
  have hcA := hcH.mul (v_continuous u)
  have hcB : Continuous (fun s => inverseForcePeanoKernel t s*(166*r u s-648*e u s)) :=
    hcH.mul ((continuous_const.mul hcR).sub (continuous_const.mul hcE))
  have hpoint {s : ℝ} (hs : s ∈ Icc 0 t) :
      inverseForcePeanoKernel t s*v u s < inverseForcePeanoKernel t s*(166*r u s-648*e u s) :=
    mul_lt_mul_of_pos_left (supersolutionCurvatureFourth_affine_upper hs.1 (hs.2.trans htu))
      (inverseForcePeanoKernel_pos ht hs)
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht.le (hcA.intervalIntegrable 0 t)
    (hcB.intervalIntegrable 0 t) (fun s hs => (hpoint hs).le)
  have hp := mul_lt_mul_of_pos_left (supersolutionCurvatureFourth_affine_upper ht.le htu)
    (show 0 < 25*t^5 by positivity)
  have heq := inverseForceShapeBlock_fourth_identity u ht
  simp only [Pi.mul_apply] at hi
  linarith only [hi,hp,heq]

end
end RHTower.ThetaCuspDefect
