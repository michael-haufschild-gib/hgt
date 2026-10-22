import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CurrentSourceOrientation
/-! Actual curvature Schur coupling in the complete enriched current.
At fixed clock elasticity the extracted nonlinear slope/source reserve is
positive. Actual clock dependence is retained in the remaining expression;
the complete current sign remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section

def peanoSlopeQuadratic (A a C : ℝ) : ℝ :=
  A/5+31/5-2*a-C+A*(5*C-9)/(25*a)

def actionPowerPeanoSlopeLinear (m Z a g C : ℝ) : ℝ :=
  let A:=9+12*Z+m*g
  let P:=144*Z^2+24*m*Z*g+m*(m-10)*g^2+156*Z+13*m*g-9+5*a
  let G:=24*m*Z+2*m*(m-10)*g+13*m
  let H:=288*Z+24*m*g+156
  (A/5-4-C)*(P/25+2*a-3*A/5)+
    (2*P+65*a-55*a^2+(P+50*a-15*A)*(2-a)+
      (G-15*m)*g*(1+a-2*g)+(H-180)*Z*(1+a))/25-57*A/125

theorem actionPowerPeanoRemainder_schur (m Z a g b q C : ℝ) (ha : a ≠ 0) :
    actionPowerPeanoRemainderKernel m Z a g b q C=
      actionPowerPeanoRemainderKernel m Z a g 0 0 C+b*actionPowerPeanoSlopeLinear m Z a g C+
      b^2*peanoSlopeQuadratic (9+12*Z+m*g) a C+2/a*b^3+
        ((9+12*Z+m*g)*(5*C-9)/25+2*(2*a+b))*(q-b^2/a) := by
  unfold actionPowerPeanoRemainderKernel actionPowerCurrentKernel actionPowerReserveKernel
    actionPowerFlowKernel actionPowerPeanoSlopeLinear peanoSlopeQuadratic
  field_simp [ha]
  ring

private theorem peanoSlopeQuadratic_positive {Z a A C : ℝ}
    (hZ : 0 < Z) (ha : 1 ≤ a) (hcone : 9*(a-1)^2 ≤ 2*Z)
    (hA : 25+12*Z ≤ A)
    (hC : 2*a/(1+a)*(1+12*Z)/(1+6*Z) ≤ C) :
    0 < peanoSlopeQuadratic A a C := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hx : 0 ≤ a-1 := sub_nonneg.mpr ha
  let A0:=25+12*Z
  let C0:=2*a/(1+a)*(1+12*Z)/(1+6*Z)
  let den:=(1+a)*(1+6*Z)
  have hden : 0 < den := by dsimp only [den]; positivity
  have ha1 : 1+a ≠ 0 := by positivity
  have hz1 : 1+6*Z ≠ 0 := by positivity
  have hC0 : 1 ≤ C0 := by
    have hid : (C0-1)*den=(a-1)+(18*a-6)*Z := by
      dsimp only [C0,den]
      field_simp [ha1,hz1]
      ring
    have hp : 0 ≤ (a-1)+(18*a-6)*Z := by
      have hr : 0 < 18*a-6 := by linarith only [ha]
      positivity
    rw [←hid] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hden).mp hp)
  have hCC : C0 ≤ C := hC
  have hC1 : 1 ≤ C := hC0.trans hCC
  have hA0 : 0 < A0-5*a := by
    dsimp only [A0]
    nlinarith only [hcone,sq_nonneg (a-2)]
  let N:=210+515*(a-1)+30*(a-1)^2-50*(a-1)^3+
    Z*(2484+4182*(a-1)-60*(a-1)^2-300*(a-1)^3)+
    Z^2*(864+1872*(a-1)+360*(a-1)^2)
  have hn1:=mul_le_mul_of_nonneg_right hcone hx
  have hn2:=mul_le_mul_of_nonneg_right hcone hZ.le
  have hn3:=mul_le_mul_of_nonneg_right hcone (mul_nonneg hx hZ.le)
  let B:=210+515*(a-1)+30*(a-1)^2+
    Z*(2484+(4182-100/9)*(a-1))+
    Z^2*((864-40/3)+(1872-200/3)*(a-1)+360*(a-1)^2)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBN : B ≤ N := by
    dsimp only [B,N]
    nlinarith only [hn1,hn2,hn3]
  have hN : 0 < N := hB.trans_le hBN
  have hid : peanoSlopeQuadratic A0 a C0*(25*a*den)=N := by
    dsimp only [peanoSlopeQuadratic,A0,C0,den,N]
    field_simp [ha0.ne',ha1,hz1]
    ring
  have hbase : 0 < peanoSlopeQuadratic A0 a C0 := by
    rw [←hid] at hN
    exact (mul_pos_iff_of_pos_right (by positivity : 0 < 25*a*den)).mp hN
  have he1 : peanoSlopeQuadratic A0 a C-peanoSlopeQuadratic A0 a C0=
      (A0-5*a)/(5*a)*(C-C0) := by
    unfold peanoSlopeQuadratic
    field_simp [ha0.ne']
    ring
  have hg1 : 0 ≤ peanoSlopeQuadratic A0 a C-peanoSlopeQuadratic A0 a C0 := by
    rw [he1]
    exact mul_nonneg (div_nonneg hA0.le (by positivity)) (sub_nonneg.mpr hCC)
  have he2 : peanoSlopeQuadratic A a C-peanoSlopeQuadratic A0 a C=
      (A-A0)*(5*a-9+5*C)/(25*a) := by
    unfold peanoSlopeQuadratic
    field_simp [ha0.ne']
    ring
  have hg2 : 0 ≤ peanoSlopeQuadratic A a C-peanoSlopeQuadratic A0 a C := by
    rw [he2]
    have hcoef : 0 < 5*a-9+5*C := by linarith only [ha,hC1]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hA) hcoef.le) (by positivity)
  linarith only [hbase,hg1,hg2]

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
local notation "C" => intrinsicClockLogElasticity
private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem p_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < p u t := by
  unfold shapeCurvatureSlope
  exact div_pos (sub_pos.mpr (thetaCuspLogCurvatureJet_strictMono (by linarith))) (by norm_num)
private theorem beta_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < b u t := by
  unfold curvatureShapeBeta
  exact div_pos (mul_pos (sq_pos_of_pos ht) (p_pos u ht)) (E_pos u ht)
private theorem alpha_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < a u t := by
  unfold curvatureShapeAlpha
  exact div_pos (mul_pos ht (completedCurvatureEven_pos u t)) (E_pos u ht)

/-- Strict determinant positivity couples the reflected slope to its second source. -/
theorem reflectedCurvature_schur_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < e u t*r u t-(p u t)^2 := by
  have he:=completedCurvatureEven_pos u t
  have hp:=p_pos u ht
  have hr:=reflectedCurvatureDefect_pos ht.le htu
  rw [reflectedCurvatureDefect_eq] at hr
  have hlow : p u t < 2*e u t := by
    have hv:=ThetaCurvature.velocityGap_pos (show 0≤u+t by linarith)
    have hm:=sourceVelocity_nonneg (sub_nonneg.mpr htu)
    have hc:=thetaCuspLogCurvature_pos (u-t)
    unfold shapeCurvatureSlope completedCurvatureEven
    linarith only [hv,hm,hc]
  have hid : e u t*r u t-(p u t)^2=e u t*(r u t-4*e u t)+
      (2*e u t-p u t)*(2*e u t+p u t) := by ring
  rw [hid]
  exact add_pos (mul_pos he hr) (mul_pos (sub_pos.mpr hlow) (by positivity))

/-- The actual second source strictly exceeds the nonlinear slope square. -/
theorem curvatureShapeDelta_gt_schur {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    (b u t)^2/a u t < q u t := by
  have ha:=alpha_pos u ht
  have hid : a u t*q u t-(b u t)^2=
      t^4/(E u t)^2*(e u t*r u t-(p u t)^2) := by
    unfold curvatureShapeAlpha curvatureShapeDelta curvatureShapeBeta
    field_simp [(E_pos u ht).ne']
  have hp:=mul_pos (div_pos (pow_pos ht 4) (sq_pos_of_pos (E_pos u ht)))
    (reflectedCurvature_schur_pos ht htu)
  rw [←hid] at hp
  apply (div_lt_iff₀ ha).mpr
  nlinarith only [hp]

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
  have hinner := (mul_pos_iff_of_pos_left hgpos).mp hd
  exact ⟨hg,by linarith only [hg,hinner]⟩

private theorem center_floor (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    thetaCuspLogCurvature u*t ≤ E u t := by
  have hd (s : ℝ) : HasDerivAt (fun zv=>E u zv-thetaCuspLogCurvature u*zv)
      (e u s-thetaCuspLogCurvature u) s := by
    convert! (hasDerivAt_completedDecayEvenPrimitive u s).sub
      ((hasDerivAt_id s).const_mul (thetaCuspLogCurvature u)) using 1
    ring
  have hm : MonotoneOn (fun s=>E u s-thetaCuspLogCurvature u*s) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s).deriv]
      exact sub_nonneg.mpr (centerCurvature_le_completedCurvatureEven u (interior_subset hs))
  have hh:=hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht ht
  simpa only [completedDecayEvenPrimitive_zero,mul_zero,sub_zero,sub_nonneg] using hh

private theorem shape_cone {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    9*(a u t-1)^2 ≤ 2*Z u t := by
  have ha : 1 ≤ a u t := (gamma_bounds ht htu).1.trans (gamma_bounds ht htu).2
  have hal:=curvatureShapeAlpha_lt ht htu
  have hz : 18*t^2 < Z u t := by
    have hf:=mul_le_mul_of_nonneg_left (center_floor u ht.le) ht.le
    have hp:=mul_pos (sub_pos.mpr (sourceCurvature_gt_eighteen (ht.le.trans htu))) (sq_pos_of_pos ht)
    unfold curvatureShapeAction
    nlinarith only [hf,hp]
  have hm:=mul_pos (show 0 < 2*t-(a u t-1) by linarith only [hal])
    (show 0 < 2*t+(a u t-1) by linarith only [ht,ha])
  nlinarith only [hm,hz]

private theorem clock_lower_without_slope {u t : ℝ} (ht : 0 < t) :
    2*a u t/(1+a u t)*(1+12*Z u t)/(1+6*Z u t) ≤ C u t := by
  have ha:=alpha_pos u ht
  have hb:=beta_pos u ht
  have hZ : 0 < Z u t := mul_pos ht (E_pos u ht)
  have hC:=intrinsicClockLogElasticity_lower u ht
  have hpos : 0 ≤ b u t/(1+a u t)*((1+12*Z u t)/(1+6*Z u t)) := by positivity
  have hid : (2*a u t+b u t)/(1+a u t)*(1+12*Z u t)/(1+6*Z u t)-
      2*a u t/(1+a u t)*(1+12*Z u t)/(1+6*Z u t)=
        b u t/(1+a u t)*((1+12*Z u t)/(1+6*Z u t)) := by ring
  rw [←hid] at hpos
  linarith only [hC,hpos]

/-- The complete quadratic slope coefficient after source Schur extraction. -/
def enrichedPeanoSlopeQuadratic (u t : ℝ) : ℝ :=
  peanoSlopeQuadratic (9+12*Z u t+16*g u t) (a u t) (C u t)+
    (Q u t)^2/15*peanoSlopeQuadratic (9+12*Z u t+36*g u t) (a u t) (C u t)

theorem enrichedPeanoSlopeQuadratic_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < enrichedPeanoSlopeQuadratic u t := by
  rcases gamma_bounds ht htu with ⟨hg,hga⟩
  have ha:=hg.trans hga
  have hZ : 0 < Z u t := mul_pos ht (E_pos u ht)
  have h16:=peanoSlopeQuadratic_positive hZ ha (shape_cone ht htu)
    (show 25+12*Z u t ≤ 9+12*Z u t+16*g u t by linarith only [hg])
    (clock_lower_without_slope ht)
  have h36:=peanoSlopeQuadratic_positive hZ ha (shape_cone ht htu)
    (show 25+12*Z u t ≤ 9+12*Z u t+36*g u t by linarith only [hg])
    (clock_lower_without_slope ht)
  unfold enrichedPeanoSlopeQuadratic
  exact add_pos_of_pos_of_nonneg h16 (mul_nonneg (by positivity) h36.le)

/-- Affine slope part with the actual, unaltered clock elasticity. -/
def enrichedCurrentSlopeAffinePart (u t : ℝ) : ℝ :=
  actionPowerPeanoRemainderKernel 16 (Z u t) (a u t) (g u t) 0 0 (C u t)+
    (Q u t)^2/15*actionPowerPeanoRemainderKernel 36 (Z u t) (a u t) (g u t) 0 0 (C u t)+
      b u t*(actionPowerPeanoSlopeLinear 16 (Z u t) (a u t) (g u t) (C u t)+
        (Q u t)^2/15*actionPowerPeanoSlopeLinear 36 (Z u t) (a u t) (g u t) (C u t))

def enrichedCurrentSchurReserve (u t : ℝ) : ℝ :=
  (b u t)^2*enrichedPeanoSlopeQuadratic u t+2*(1+(Q u t)^2/15)/a u t*(b u t)^3+
    enrichedPeanoDeltaCoefficient u t*(q u t-(b u t)^2/a u t)

/-- Exact coupled decomposition of all nonlinear slope and second-source terms. -/
theorem enrichedCurrentPeanoRemainder_schur_identity (u : ℝ) {t : ℝ} (ht : 0 < t) :
    enrichedCurrentPeanoRemainder u t=enrichedCurrentSlopeAffinePart u t+enrichedCurrentSchurReserve u t := by
  have h16:=actionPowerPeanoRemainder_schur 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (C u t)
    (alpha_pos u ht).ne'
  have h36:=actionPowerPeanoRemainder_schur 36 (Z u t) (a u t) (g u t) (b u t) (q u t) (C u t)
    (alpha_pos u ht).ne'
  unfold enrichedCurrentPeanoRemainder enrichedCurrentSlopeAffinePart enrichedCurrentSchurReserve
    enrichedPeanoSlopeQuadratic enrichedPeanoDeltaCoefficient
  linear_combination h16+(Q u t)^2/15*h36

/-- The extracted Schur reserve is strictly positive at the actual clock.
The remaining expression retains its own slope dependence through that clock. -/
theorem enrichedCurrentSchurReserve_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < enrichedCurrentSchurReserve u t := by
  have hb:=beta_pos u ht
  have ha:=alpha_pos u ht
  have hquad:=enrichedPeanoSlopeQuadratic_pos ht htu
  have hdelta:=enrichedPeanoDeltaCoefficient_pos ht htu
  have hgap:=sub_pos.mpr (curvatureShapeDelta_gt_schur ht htu)
  unfold enrichedCurrentSchurReserve
  positivity

theorem enrichedClockCurrent_schur_identity {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    E u t*enrichedClockCurrent u t=
      E u t*enrichedCurrentSlopeAffinePart u t+E u t*enrichedCurrentSchurReserve u t+
        enrichedCurrentPeanoWeight u t*
          (64*(Z u t-Q u t)^2/(t*Q u t)-currentModelSourceQuadrature u t+
            (∫ s in 0..t, currentSourceGapKernel t s*reflectedSourceModelGapDensity u s)) := by
  rw [enrichedClockCurrent_model_peano_identity ht htu,enrichedCurrentPeanoRemainder_schur_identity u ht]
  ring

end
end RHTower.ThetaCuspDefect
