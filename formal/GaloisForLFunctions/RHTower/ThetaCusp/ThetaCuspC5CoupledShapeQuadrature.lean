import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5IntrinsicActionProfile
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5FrozenJetGate
/-! Finite coupled shape cancellation in the N16 inverse-source comparison.
The full-source shape block has an exact nonnegative square minus a
positive-kernel quadrature remainder. One-sided fourth-curvature control
bounds this entire coupled remainder throughout the physical chamber.
This controls one adverse block; the full inverse-source/clock order and
complete C5 compensation are not asserted. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "Q" => thetaCuspReflectedLogAction
private def qp (u s : ℝ) : ℝ := (thetaCuspLogCurvatureJet (u+s)-thetaCuspLogCurvatureJet (u-s))/2
private def qr (u s : ℝ) : ℝ := (thetaCuspLogCurvatureJetTwo (u+s)+thetaCuspLogCurvatureJetTwo (u-s))/2
/-- Third displacement derivative of the reflected even curvature. -/
def quadratureCurvatureThird (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJetThree (u+s)-thetaCuspLogCurvatureJetThree (u-s))/2
private def qfour (u s : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJetFour (u+s)+thetaCuspLogCurvatureJetFour (u-s))/2
local notation "w" => quadratureCurvatureThird
private theorem he_deriv (u s : ℝ) : HasDerivAt (e u) (qp u s) s := hasDerivAt_completedCurvatureEven u s
private theorem hp_deriv (u s : ℝ) : HasDerivAt (qp u) (qr u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold qr
  ring
private theorem hr_deriv (u s : ℝ) : HasDerivAt (qr u) (w u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.add hm).div_const 2 using 1
  unfold quadratureCurvatureThird
  ring
private theorem hw_deriv (u s : ℝ) : HasDerivAt (w u) (qfour u s) s := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetThree (u+s)).comp s ((hasDerivAt_id s).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetThree (u-s)).comp s ((hasDerivAt_id s).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold qfour
  ring
private theorem hQ_deriv (u s : ℝ) : HasDerivAt (Q u) (2*E u s) s := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u s using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring
private theorem E_pos (u : ℝ) {s : ℝ} (hs : 0 < s) : 0 < E u s := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u hs) (by norm_num)

private theorem E_chord (u : ℝ) {s t : ℝ} (ht : 0 < t) (hs : s ∈ Icc 0 t) :
    E u s ≤ s/t*E u t := by
  have hc : ConvexOn ℝ (Icc 0 t) (E u) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 t)
    · intro r _; exact (hasDerivAt_completedDecayEvenPrimitive u r).continuousAt.continuousWithinAt
    · intro r _; exact (hasDerivAt_completedDecayEvenPrimitive u r).differentiableAt.differentiableWithinAt
    · intro a ha b hb hab
      rw [(hasDerivAt_completedDecayEvenPrimitive u a).deriv,(hasDerivAt_completedDecayEvenPrimitive u b).deriv]
      exact completedCurvatureEven_monotoneOn u
        (interior_subset ha).1 (interior_subset hb).1 hab
  have hst : s/t ≤ 1 := (div_le_one ht).mpr hs.2
  have h := hc.2 (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩)
    (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩)
    (sub_nonneg.mpr hst) (div_nonneg hs.1 ht.le) (by ring : 1-s/t+s/t=1)
  simpa only [smul_eq_mul,mul_zero,zero_add,completedDecayEvenPrimitive_zero,
    add_zero,div_mul_cancel₀ _ ht.ne'] using h

theorem quadratureCurvatureThird_lt_primitive {u s : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    w u s < 846*E u s := by
  have hd (r : ℝ) : HasDerivAt (fun x => 846*E u x-w u x) (846*e u r-qfour u r) r :=
    ((hasDerivAt_completedDecayEvenPrimitive u r).const_mul 846).sub (hw_deriv u r)
  have hm : StrictMonoOn (fun r => 846*E u r-w u r) (Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro r _; exact (hd r).continuousAt.continuousWithinAt
    · intro r hr
      have hr0 : r ∈ Ioo 0 u := by simpa only [interior_Icc] using hr
      rw [(hd r).deriv]
      have hp := source_fourth_curvature_upper (show 0 ≤ u+r by linarith [hr0.1,hr0.2])
      have hn := source_fourth_curvature_upper (show 0 ≤ u-r by linarith [hr0.2])
      unfold qfour thetaCuspLogCurvatureJetFour completedCurvatureEven
      linarith
  have h := hm (show (0:ℝ) ∈ Icc 0 u from ⟨le_rfl,hs.le.trans hsu⟩) ⟨hs.le,hsu⟩ hs
  simpa only [completedDecayEvenPrimitive_zero,quadratureCurvatureThird,add_zero,sub_zero,sub_self,
    zero_div,mul_zero,sub_zero,sub_pos] using h

/-- Positive Peano weight retaining the first coupled shape cancellation. -/
def coupledShapeKernel (t s : ℝ) : ℝ := (170/3)*t^2*s-7*s^3+16*s^4/(3*t)
private def k1 (t s : ℝ) : ℝ := (170/3)*t^2-21*s^2+64*s^3/(3*t)
private def k2 (t s : ℝ) : ℝ := -42*s+64*s^2/t
private def k3 (t s : ℝ) : ℝ := -42+128*s/t
private theorem hk0 (t s : ℝ) : HasDerivAt (coupledShapeKernel t) (k1 t s) s := by
  have h := hasDerivAt_id s
  convert! (((h.const_mul ((170/3)*t^2)).sub ((h.pow 3).const_mul 7)).add
    ((h.pow 4).const_mul 16 |>.div_const (3*t))) using 1
  simp only [id_eq]
  unfold k1
  ring
private theorem hk1 (t s : ℝ) : HasDerivAt (k1 t) (k2 t s) s := by
  have h := hasDerivAt_id s
  convert! ((((h.pow 2).const_mul 21).const_sub ((170/3)*t^2)).add
    ((h.pow 3).const_mul 64 |>.div_const (3*t))) using 1
  simp only [id_eq]
  unfold k2
  ring
private theorem hk2 (t s : ℝ) : HasDerivAt (k2 t) (k3 t s) s := by
  have h := hasDerivAt_id s
  convert! ((h.const_mul (-42)).add ((h.pow 2).const_mul 64 |>.div_const t)) using 1
  simp only [id_eq]
  unfold k3
  ring
private theorem hk3 (t s : ℝ) : HasDerivAt (k3 t) (128/t) s := by
  convert! (((hasDerivAt_id s).const_mul 128).div_const t).const_add (-42) using 1
  simp only [mul_one]

private def shapePrimitive (u t s : ℝ) : ℝ :=
  coupledShapeKernel t s*qr u s-k1 t s*qp u s+k2 t s*e u s-k3 t s*E u s+(64/t)*Q u s
private theorem shapePrimitive_deriv (u t s : ℝ) :
    HasDerivAt (shapePrimitive u t) (coupledShapeKernel t s*w u s) s := by
  convert! (((((hk0 t s).mul (hr_deriv u s)).sub ((hk1 t s).mul (hp_deriv u s))).add
    ((hk2 t s).mul (he_deriv u s))).sub ((hk3 t s).mul (hasDerivAt_completedDecayEvenPrimitive u s))).add
    ((hQ_deriv u s).const_mul (64/t)) using 1
  ring

private theorem shape_integral (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, coupledShapeKernel t s*w u s)=
      55*t^3*qr u t-57*t^2*qp u t+22*t*e u t-86*E u t+64*Q u t/t := by
  have hi : IntervalIntegrable (fun s => coupledShapeKernel t s*w u s) volume 0 t :=
    ((continuous_iff_continuousAt.mpr (fun s => (hk0 t s).continuousAt)).mul
      (continuous_iff_continuousAt.mpr (fun s => (hw_deriv u s).continuousAt))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => shapePrimitive_deriv u t s) hi]
  simp only [shapePrimitive,coupledShapeKernel,k1,k2,k3,qp,completedDecayEvenPrimitive_zero,Q_zero,
    pow_succ,zero_mul,mul_zero,zero_div,sub_self,add_zero,sub_zero]
  field_simp [ht.ne']
  ring

/-- Coupled shape block in the normalized inverse-source comparison. -/
def coupledShapeBlock (u t : ℝ) : ℝ :=
  64*(t*E u t/Q u t-1)-22*(t*e u t/E u t-1)+
    57*(t^2*qp u t/E u t)-55*(t^3*qr u t/E u t)

theorem coupledShapeBlock_variance_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    E u t*coupledShapeBlock u t+(∫ s in (0:ℝ)..t, coupledShapeKernel t s*w u s)=
      64*(t*E u t-Q u t)^2/(t*Q u t) := by
  rw [shape_integral u ht]
  unfold coupledShapeBlock
  field_simp [ht.ne',(E_pos u ht).ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  ring

theorem coupledShapeKernel_pos {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : 0 < coupledShapeKernel t s := by
  have hid : coupledShapeKernel t s=s*(54*t^2+s^2+(8/(3*t))*(t+2*s)*(t-s)^2) := by
    unfold coupledShapeKernel
    field_simp [ht.ne']
    ring
  rw [hid]
  positivity

private def shapeWeightPrimitive (t s : ℝ) : ℝ := (170/9)*t*s^3-7*s^5/(5*t)+8*s^6/(9*t^2)
private theorem shapeWeightPrimitive_deriv {t : ℝ} (ht : t ≠ 0) (s : ℝ) :
    HasDerivAt (shapeWeightPrimitive t) (coupledShapeKernel t s*(s/t)) s := by
  have h := hasDerivAt_id s
  convert! ((((h.pow 3).const_mul ((170/9)*t)).sub ((h.pow 5).const_mul 7 |>.div_const (5*t))).add
    ((h.pow 6).const_mul 8 |>.div_const (9*t^2))) using 1
  simp only [id_eq]
  unfold coupledShapeKernel
  field_simp [ht]
  ring

private theorem shapeWeightIntegral {t : ℝ} (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, coupledShapeKernel t s*(s/t))=(827/45)*t^4 := by
  have hc : Continuous (fun s => coupledShapeKernel t s*(s/t)) :=
    (continuous_iff_continuousAt.mpr (fun s => (hk0 t s).continuousAt)).mul (continuous_id.div_const t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => shapeWeightPrimitive_deriv ht.ne' s) (hc.intervalIntegrable _ _)]
  unfold shapeWeightPrimitive
  simp only [zero_pow (by decide : (3:ℕ) ≠ 0),zero_pow (by decide : (5:ℕ) ≠ 0),
    zero_pow (by decide : (6:ℕ) ≠ 0),mul_zero,zero_div,sub_zero,zero_add]
  field_simp [ht.ne']
  ring

theorem coupledShapeBlock_lower_reserve {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < coupledShapeBlock u t+(827*846/45)*t^4 := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hcK := continuous_iff_continuousAt.mpr (fun s => (hk0 t s).continuousAt)
  have hcW := continuous_iff_continuousAt.mpr (fun s => (hw_deriv u s).continuousAt)
  have hcA : ContinuousOn (fun s => coupledShapeKernel t s*w u s) (Icc 0 t) := (hcK.mul hcW).continuousOn
  have hcB : ContinuousOn (fun s => (846*E u t)*(coupledShapeKernel t s*(s/t))) (Icc 0 t) :=
    (continuous_const.mul (hcK.mul (continuous_id.div_const t))).continuousOn
  have hpoint {s : ℝ} (hs : s ∈ Ioc 0 t) :
      coupledShapeKernel t s*w u s < (846*E u t)*(coupledShapeKernel t s*(s/t)) := by
    have hw := quadratureCurvatureThird_lt_primitive hs.1 (hs.2.trans htu)
    have he := E_chord u ht ⟨hs.1.le,hs.2⟩
    have h := mul_lt_mul_of_pos_left
      (hw.trans_le (mul_le_mul_of_nonneg_left he (by norm_num))) (coupledShapeKernel_pos ht hs.1)
    nlinarith only [h]
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    hcA hcB (fun s hs => (hpoint hs).le)
    ⟨t/2,⟨by linarith,by linarith⟩,hpoint ⟨by linarith,by linarith⟩⟩
  rw [intervalIntegral.integral_const_mul,shapeWeightIntegral ht] at hi
  have hid := coupledShapeBlock_variance_identity u ht
  have hsq : 0 ≤ 64*(t*E u t-Q u t)^2/(t*Q u t) := by positivity
  have hprod : 0 < E u t*(coupledShapeBlock u t+(827*846/45)*t^4) := by nlinarith only [hi,hid,hsq]
  exact (mul_pos_iff_of_pos_left hE).mp hprod

end
end RHTower.ThetaCuspDefect
