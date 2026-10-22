import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CoupledShapeQuadrature
/-! Coupled finite-displacement dynamics of the intrinsic inverse source.
The actual curvature and action elasticities increase on the physical
chamber. The third normalized shape has strictly positive growth, and the
fourth-jet transport retains the affine curvature-defect cancellation.
The exact inverse-reserve polynomial is identified; its full comparison
with the denominator clock and endpoint recovery remain open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "Q" => thetaCuspReflectedLogAction
local notation "w" => quadratureCurvatureThird

def shapeCurvatureSlope (u t : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJet (u+t)-thetaCuspLogCurvatureJet (u-t))/2
def shapeCurvatureSecond (u t : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJetTwo (u+t)+thetaCuspLogCurvatureJetTwo (u-t))/2
local notation "p" => shapeCurvatureSlope
local notation "r" => shapeCurvatureSecond
private def shapeFourth (u t : ℝ) : ℝ :=
  (thetaCuspLogCurvatureJetFour (u+t)+thetaCuspLogCurvatureJetFour (u-t))/2

private theorem he_deriv (u t : ℝ) : HasDerivAt (e u) (p u t) t := hasDerivAt_completedCurvatureEven u t
private theorem hp_deriv (u t : ℝ) : HasDerivAt (p u) (r u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeCurvatureSecond
  ring
private theorem hr_deriv (u t : ℝ) : HasDerivAt (r u) (w u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetTwo (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.add hm).div_const 2 using 1
  unfold quadratureCurvatureThird
  ring
private theorem hw_deriv (u t : ℝ) : HasDerivAt (w u) (shapeFourth u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJetThree (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJetThree (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  convert! (hp.sub hm).div_const 2 using 1
  unfold shapeFourth
  ring
private theorem hQ_deriv (u t : ℝ) : HasDerivAt (Q u) (2*E u t) t := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
  rw [completedDecayEvenPrimitive_eq]
  ring
private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem Q_zero (u : ℝ) : Q u 0=0 := by unfold thetaCuspReflectedLogAction; simp; ring
private theorem p_nonneg (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p u t := by
  unfold shapeCurvatureSlope
  exact div_nonneg (sub_nonneg.mpr (thetaCuspLogCurvatureJet_strictMono.monotone (by linarith))) (by norm_num)
private theorem p_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < p u t := by
  unfold shapeCurvatureSlope
  exact div_pos (sub_pos.mpr (thetaCuspLogCurvatureJet_strictMono (by linarith))) (by norm_num)
private theorem p_lt_two_mul_e {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : p u t < 2*e u t := by
  have ha : 0 ≤ u-t := sub_nonneg.mpr htu
  have hb : 0 ≤ u+t := by linarith
  have hv := ThetaCurvature.velocityGap_pos hb
  have hva := sourceVelocity_nonneg ha
  have hca := thetaCuspLogCurvature_pos (u-t)
  unfold shapeCurvatureSlope completedCurvatureEven
  linarith
private theorem four_mul_e_lt_r {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : 4*e u t < r u t := by
  have ha := curvatureDefect_pos (show 0 ≤ u-t from sub_nonneg.mpr htu)
  have hb := curvatureDefect_pos (show 0 ≤ u+t by linarith)
  unfold curvatureDefect at ha hb
  unfold shapeCurvatureSecond completedCurvatureEven
  linarith

private theorem chamber_pos {f g : ℝ → ℝ} {a t : ℝ} (ht : 0 < t) (hta : t ≤ a)
    (h0 : f 0=0) (hd : ∀ s, HasDerivAt f (g s) s)
    (hg : ∀ s, 0 < s → s < a → 0 < g s) : 0 < f t := by
  have hm : StrictMonoOn f (Icc 0 a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 a := by simpa only [interior_Icc] using hs
      rw [(hd s).deriv]
      exact hg s hs'.1 hs'.2
  simpa only [h0] using hm ⟨le_rfl,ht.le.trans hta⟩ ⟨ht.le,hta⟩ ht

private def shapeLogSlope (u t : ℝ) : ℝ := p u t/e u t
private theorem shapeLogSlope_deriv (u t : ℝ) :
    HasDerivAt (shapeLogSlope u) ((r u t*e u t-(p u t)^2)/(e u t)^2) t := by
  convert! (hp_deriv u t).div (he_deriv u t) (completedCurvatureEven_pos u t).ne' using 1
  ring
private theorem shapeLogSlope_strictMonoOn (u : ℝ) : StrictMonoOn (shapeLogSlope u) (Icc 0 u) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro s _; exact (shapeLogSlope_deriv u s).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc 0 u := interior_subset hs
    rw [(shapeLogSlope_deriv u s).deriv]
    apply div_pos _ (sq_pos_of_pos (completedCurvatureEven_pos u s))
    have he := completedCurvatureEven_pos u s
    have hp := p_nonneg u hs'.1
    have hp2 := p_lt_two_mul_e hs'.1 hs'.2
    have hr := mul_lt_mul_of_pos_right (four_mul_e_lt_r hs'.1 hs'.2) he
    have hsqr := mul_pos (sub_pos.mpr hp2) (show 0 < 2*e u s+p u s by positivity)
    nlinarith only [hr,hsqr]

def curvatureShapeAlpha (u t : ℝ) : ℝ := t*e u t/E u t
def curvatureShapeGamma (u t : ℝ) : ℝ := t*E u t/Q u t
def curvatureShapeBeta (u t : ℝ) : ℝ := t^2*p u t/E u t

/-- The complete curvature elasticity has a strictly positive derivative numerator. -/
theorem curvatureShapeAlpha_current_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < (e u t+t*p u t)*E u t-t*(e u t)^2 := by
  let F := fun s => (e u t+t*p u t)*E u s-e u t*s*e u s
  have hd (s : ℝ) : HasDerivAt F (t*p u t*e u s-s*e u t*p u s) s := by
    convert! ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul (e u t+t*p u t)).sub
      (((hasDerivAt_id s).const_mul (e u t)).mul (he_deriv u s)) using 1
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    ring
  have hF : 0 < F t := by
    apply chamber_pos ht le_rfl (by simp [F,completedDecayEvenPrimitive_zero]) hd
    intro s hs hst
    have hc := shapeLogSlope_strictMonoOn u ⟨hs.le,hst.le.trans htu⟩ ⟨ht.le,htu⟩ hst
    have hcross := (div_lt_div_iff₀ (completedCurvatureEven_pos u s) (completedCurvatureEven_pos u t)).mp hc
    have h1 := mul_lt_mul_of_pos_left hcross hs
    have h2 := mul_lt_mul_of_pos_right hst (mul_pos (p_pos u ht) (completedCurvatureEven_pos u s))
    nlinarith only [h1,h2]
  dsimp only [F] at hF
  nlinarith only [hF]

theorem hasDerivAt_curvatureShapeAlpha (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curvatureShapeAlpha u)
      (((e u t+t*p u t)*E u t-t*(e u t)^2)/(E u t)^2) t := by
  convert! ((hasDerivAt_id t).mul (he_deriv u t)).div
    (hasDerivAt_completedDecayEvenPrimitive u t) (E_pos u ht).ne' using 1
  dsimp only [Pi.mul_apply,id_eq]
  ring

theorem curvatureShapeAlpha_strictMonoOn (u : ℝ) : StrictMonoOn (curvatureShapeAlpha u) (Ioc 0 u) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro s hs; exact (hasDerivAt_curvatureShapeAlpha u hs.1).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 u := by simpa only [interior_Ioc] using hs
    rw [(hasDerivAt_curvatureShapeAlpha u hs'.1).deriv]
    exact div_pos (curvatureShapeAlpha_current_pos hs'.1 hs'.2.le) (sq_pos_of_pos (E_pos u hs'.1))

/-- The complete action elasticity has a strictly positive derivative numerator. -/
theorem curvatureShapeGamma_current_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < (E u t+t*e u t)*Q u t-2*t*(E u t)^2 := by
  let F := fun s => (E u t+t*e u t)*Q u s-2*E u t*s*E u s
  have hd (s : ℝ) : HasDerivAt F (2*(t*e u t*E u s-s*E u t*e u s)) s := by
    convert! ((hQ_deriv u s).const_mul (E u t+t*e u t)).sub
      (((hasDerivAt_id s).const_mul (2*E u t)).mul (hasDerivAt_completedDecayEvenPrimitive u s)) using 1
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    ring
  have hF : 0 < F t := by
    apply chamber_pos ht le_rfl (by simp [F,Q_zero]) hd
    intro s hs hst
    have hc := curvatureShapeAlpha_strictMonoOn u ⟨hs,hst.le.trans htu⟩ ⟨ht,htu⟩ hst
    have hcross := (div_lt_div_iff₀ (E_pos u hs) (E_pos u ht)).mp hc
    nlinarith only [hcross]
  dsimp only [F] at hF
  nlinarith only [hF]

theorem hasDerivAt_curvatureShapeGamma (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curvatureShapeGamma u)
      (((E u t+t*e u t)*Q u t-2*t*(E u t)^2)/(Q u t)^2) t := by
  convert! ((hasDerivAt_id t).mul (hasDerivAt_completedDecayEvenPrimitive u t)).div
    (hQ_deriv u t) (thetaCuspReflectedLogAction_pos (u := u) ht).ne' using 1
  dsimp only [Pi.mul_apply,id_eq]
  ring

theorem curvatureShapeGamma_strictMonoOn (u : ℝ) : StrictMonoOn (curvatureShapeGamma u) (Ioc 0 u) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro s hs; exact (hasDerivAt_curvatureShapeGamma u hs.1).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 u := by simpa only [interior_Ioc] using hs
    rw [(hasDerivAt_curvatureShapeGamma u hs'.1).deriv]
    exact div_pos (curvatureShapeGamma_current_pos hs'.1 hs'.2.le)
      (sq_pos_of_pos (thetaCuspReflectedLogAction_pos (u := u) hs'.1))

private theorem alphaUpper_reserve {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < (1+2*t)*E u t-t*e u t := by
  have hd (s : ℝ) : HasDerivAt (fun x => (1+2*x)*E u x-x*e u x)
      (2*E u s+s*(2*e u s-p u s)) s := by
    convert! ((((hasDerivAt_id s).const_mul 2).const_add 1).mul
      (hasDerivAt_completedDecayEvenPrimitive u s)).sub ((hasDerivAt_id s).mul (he_deriv u s)) using 1
    dsimp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    ring
  apply chamber_pos ht htu (by simp [completedDecayEvenPrimitive_zero]) hd
  intro s hs hsu
  exact add_pos (mul_pos (by norm_num) (E_pos u hs))
    (mul_pos hs (sub_pos.mpr (p_lt_two_mul_e hs.le hsu.le)))

theorem curvatureShapeAlpha_lt {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeAlpha u t < 1+2*t := by
  unfold curvatureShapeAlpha
  exact (div_lt_iff₀ (E_pos u ht)).mpr (by linarith only [alphaUpper_reserve ht htu])

theorem hasDerivAt_curvatureShapeBeta (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curvatureShapeBeta u)
      ((((2*t*p u t+t^2*r u t)*E u t)-t^2*p u t*e u t)/(E u t)^2) t := by
  convert! (((hasDerivAt_id t).pow 2).mul (hp_deriv u t)).div
    (hasDerivAt_completedDecayEvenPrimitive u t) (E_pos u ht).ne' using 1
  dsimp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  ring

/-- Coupled beta growth keeps the source derivative relation intact. -/
theorem curvatureShapeBeta_growth {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeBeta u t < t*deriv (curvatureShapeBeta u) t := by
  have hp := p_pos u ht
  have hE := E_pos u ht
  have hr : 0 < r u t-2*p u t := by
    have h1 := four_mul_e_lt_r ht.le htu
    have h2 := p_lt_two_mul_e ht.le htu
    linarith
  have hA := alphaUpper_reserve ht htu
  have hid : t*deriv (curvatureShapeBeta u) t-curvatureShapeBeta u t=
      t^2/(E u t)^2*(t*(r u t-2*p u t)*E u t+p u t*((1+2*t)*E u t-t*e u t)) := by
    rw [(hasDerivAt_curvatureShapeBeta u ht).deriv]
    unfold curvatureShapeBeta
    field_simp [hE.ne']
    ring
  apply sub_pos.mp
  rw [hid]
  exact mul_pos (div_pos (sq_pos_of_pos ht) (sq_pos_of_pos hE))
    (add_pos (mul_pos (mul_pos ht hr) hE) (mul_pos hp hA))

/-- Reflected third-jet transport retains the affine curvature-defect relation. -/
theorem quadratureCurvatureThird_lt_affine {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    w u t < 166*p u t-648*E u t := by
  have hd (s : ℝ) : HasDerivAt (fun x => 166*p u x-648*E u x-w u x)
      (166*r u s-648*e u s-shapeFourth u s) s :=
    (((hp_deriv u s).const_mul 166).sub ((hasDerivAt_completedDecayEvenPrimitive u s).const_mul 648)).sub
      (hw_deriv u s)
  have hF : 0 < 166*p u t-648*E u t-w u t := by
    apply chamber_pos ht htu
      (by simp [shapeCurvatureSlope,completedDecayEvenPrimitive_zero,quadratureCurvatureThird]) hd
    intro s hs hsu
    have hp := source_fourth_curvature_affine_upper (show 0 ≤ u+s by linarith)
    have hn := source_fourth_curvature_affine_upper (show 0 ≤ u-s by linarith)
    unfold shapeCurvatureSecond completedCurvatureEven shapeFourth thetaCuspLogCurvatureJetFour
    linarith
  linarith

/-- Normalized variables for the literal inverse-source dynamics. -/
def curvatureShapeAction (u t : ℝ) : ℝ := t*E u t
def curvatureShapeDelta (u t : ℝ) : ℝ := t^3*r u t/E u t
def curvatureShapeEpsilon (u t : ℝ) : ℝ := t^4*w u t/E u t

theorem hasDerivAt_curvatureShapeDelta (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (curvatureShapeDelta u)
      (((3*t^2*r u t+t^3*w u t)*E u t-t^3*r u t*e u t)/(E u t)^2) t := by
  convert! (((hasDerivAt_id t).pow 3).mul (hr_deriv u t)).div
    (hasDerivAt_completedDecayEvenPrimitive u t) (E_pos u ht).ne' using 1
  dsimp only [Pi.mul_apply,Pi.pow_apply,id_eq]
  ring

theorem curvatureShapeAction_evolution (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*deriv (curvatureShapeAction u) t=curvatureShapeAction u t*(1+curvatureShapeAlpha u t) := by
  have hd : deriv (curvatureShapeAction u) t=completedFirstDenominator u t :=
    (hasDerivAt_mul_completedDecayEvenPrimitive u t).deriv
  rw [hd]
  unfold curvatureShapeAction curvatureShapeAlpha completedFirstDenominator
  field_simp [(E_pos u ht).ne']

theorem curvatureShapeAlpha_evolution (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*deriv (curvatureShapeAlpha u) t=curvatureShapeAlpha u t+curvatureShapeBeta u t-(curvatureShapeAlpha u t)^2 := by
  rw [(hasDerivAt_curvatureShapeAlpha u ht).deriv]
  unfold curvatureShapeAlpha curvatureShapeBeta
  field_simp [(E_pos u ht).ne']

theorem curvatureShapeGamma_evolution (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*deriv (curvatureShapeGamma u) t=
      curvatureShapeGamma u t*(1+curvatureShapeAlpha u t-2*curvatureShapeGamma u t) := by
  rw [(hasDerivAt_curvatureShapeGamma u ht).deriv]
  unfold curvatureShapeGamma curvatureShapeAlpha
  field_simp [(E_pos u ht).ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']

theorem curvatureShapeBeta_evolution (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*deriv (curvatureShapeBeta u) t=
      (2-curvatureShapeAlpha u t)*curvatureShapeBeta u t+curvatureShapeDelta u t := by
  rw [(hasDerivAt_curvatureShapeBeta u ht).deriv]
  unfold curvatureShapeAlpha curvatureShapeBeta curvatureShapeDelta
  field_simp [(E_pos u ht).ne']
  ring

theorem curvatureShapeDelta_evolution (u : ℝ) {t : ℝ} (ht : 0 < t) :
    t*deriv (curvatureShapeDelta u) t=
      (3-curvatureShapeAlpha u t)*curvatureShapeDelta u t+curvatureShapeEpsilon u t := by
  rw [(hasDerivAt_curvatureShapeDelta u ht).deriv]
  unfold curvatureShapeAlpha curvatureShapeDelta curvatureShapeEpsilon
  field_simp [(E_pos u ht).ne']
  ring

theorem curvatureShapeEpsilon_affine_upper {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    curvatureShapeEpsilon u t < 166*t^2*curvatureShapeBeta u t-648*t^4 := by
  have h := mul_lt_mul_of_pos_left (quadratureCurvatureThird_lt_affine ht htu)
    (div_pos (pow_pos ht 4) (E_pos u ht))
  unfold curvatureShapeEpsilon curvatureShapeBeta
  convert! h using 1 <;> field_simp [(E_pos u ht).ne']

/-- Normalized reserve without the two cancelling primitive factors. -/
def normalizedActionInverseReserve (u t : ℝ) : ℝ := actionProfileInverseReserve u t*t^2/(E u t)^2

theorem normalizedActionInverseReserve_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < normalizedActionInverseReserve u t := by
  unfold normalizedActionInverseReserve
  exact div_pos (mul_pos (actionProfileInverseReserve_pos ht htu) (sq_pos_of_pos ht))
    (sq_pos_of_pos (E_pos u ht))

theorem normalizedActionInverseReserve_polynomial (u : ℝ) {t : ℝ} (ht : 0 < t) :
    normalizedActionInverseReserve u t=
      let Z := curvatureShapeAction u t
      let a := curvatureShapeAlpha u t
      let g := curvatureShapeGamma u t
      let b := curvatureShapeBeta u t
      let d := curvatureShapeDelta u t
      (2*a+b)*(144*Z^2+384*Z*g+96*g^2+156*Z+208*g-9+5*a+25*b)/25-
        (3*b+d)*(9+12*Z+16*g)/5 := by
  have hd : completedLocalDenominator u t=2*e u t+t*p u t := rfl
  have hj : descentDenominatorJet u t=3*p u t+t*r u t := rfl
  unfold normalizedActionInverseReserve actionProfileInverseReserve actionProfileLogRate actionProfileLogRateJet
  rw [hd,hj]
  dsimp only [curvatureShapeAction,curvatureShapeAlpha,curvatureShapeGamma,curvatureShapeBeta,
    curvatureShapeDelta,completedFirstDenominator,descentDenominator]
  field_simp [ht.ne',(E_pos u ht).ne',(thetaCuspReflectedLogAction_pos (u := u) ht).ne']
  ring

theorem intrinsicActionInverseSource_eq_normalized (u : ℝ) {t : ℝ} (ht : 0 < t) :
    intrinsicActionInverseSource u t=
      intrinsicActionProfile u t*normalizedActionInverseReserve u t/(4*t^4) := by
  unfold intrinsicActionInverseSource normalizedActionInverseReserve descentDenominator
  field_simp [ht.ne',(E_pos u ht).ne']


end
end RHTower.ThetaCuspDefect
