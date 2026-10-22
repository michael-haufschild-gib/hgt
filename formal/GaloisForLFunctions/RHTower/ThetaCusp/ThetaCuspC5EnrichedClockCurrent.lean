import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5EnrichedActionInverse
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5InverseReserveGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectModelDomination
/-! The complete enriched inverse-source/clock current and its actual source-model
comparison. Both adverse source coefficients are exact; the clock elasticity is
retained. Positivity of the complete current remains an open obligation. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section

def actionPowerReserveKernel (m Z a g b q : ℝ) : ℝ :=
  (2*a+b)*(144*Z^2+24*m*Z*g+m*(m-10)*g^2+156*Z+13*m*g-9+5*a+25*b)/25-
    (3*b+q)*(9+12*Z+m*g)/5

def actionPowerFlowKernel (m Z a g b q ep : ℝ) : ℝ :=
  let D:=2*a+b
  let M:=3*b+q
  let A:=9+12*Z+m*g
  let P:=144*Z^2+24*m*Z*g+m*(m-10)*g^2+156*Z+13*m*g-9+5*a+25*b
  ((2*P+5*D)*(a+b-a^2)+(P+25*D-15*A)*((2-a)*b+q)+
    (D*(24*m*Z+2*m*(m-10)*g+13*m)-5*m*M)*g*(1+a-2*g)+
    (D*(288*Z+24*m*g+156)-60*M)*Z*(1+a)-5*A*((3-a)*q+ep))/25

def actionPowerCurrentKernel (m Z a g b q ep C : ℝ) : ℝ :=
  ((9+12*Z+m*g)/5-4-C)*actionPowerReserveKernel m Z a g b q+
    actionPowerFlowKernel m Z a g b q ep

/-- Both adverse derivative coefficients in the complete first-order current. -/
theorem actionPowerCurrentKernel_source_difference (m Z a g b q q' ep ep' C : ℝ) :
    actionPowerCurrentKernel m Z a g b q ep C-actionPowerCurrentKernel m Z a g b q' ep' C=
      ((9+12*Z+m*g)*(C-4)+10*(2*a+b))/5*(q-q')-(9+12*Z+m*g)/5*(ep-ep') := by
  unfold actionPowerCurrentKernel actionPowerReserveKernel actionPowerFlowKernel
  ring

local notation "E" => completedDecayEvenPrimitive
local notation "Q" => thetaCuspReflectedLogAction
local notation "F" => intrinsicActionProfile
local notation "psi" => denominatorClockProfile
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "g" => curvatureShapeGamma
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "ep" => curvatureShapeEpsilon

def actionPowerReserve (m u t : ℝ) : ℝ :=
  actionPowerReserveKernel m (Z u t) (a u t) (g u t) (b u t) (q u t)
def actionPowerFlow (m u t : ℝ) : ℝ :=
  actionPowerFlowKernel m (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t)

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  rw [completedDecayEvenPrimitive_eq]
  exact div_pos (thetaCuspReflectedLogJetOne_pos u ht) (by norm_num)
private theorem Q_deriv (u t : ℝ) : HasDerivAt (Q u) (2*E u t) t := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
  rw [completedDecayEvenPrimitive_eq]
  ring

theorem actionPowerReserve_sixteen (u : ℝ) {t : ℝ} (ht : 0 < t) :
    actionPowerReserve 16 u t=normalizedActionInverseReserve u t := by
  rw [normalizedActionInverseReserve_polynomial u ht]
  unfold actionPowerReserve actionPowerReserveKernel
  ring

theorem actionPowerReserve_thirtysix (u : ℝ) {t : ℝ} (ht : 0 < t) :
    actionPowerReserve 36 u t=normalizedActionInverseReserve u t+enrichedInverseIncrementReserve u t := by
  rw [normalizedActionInverseReserve_polynomial u ht]
  unfold actionPowerReserve actionPowerReserveKernel enrichedInverseIncrementReserve
  ring

theorem hasDerivAt_actionPowerReserve (m u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (actionPowerReserve m u) (actionPowerFlow m u t/t) t := by
  let z:=Z u
  let al:=a u
  let ga:=g u
  let be:=b u
  let de:=q u
  let D:=fun s=>2*al s+be s
  let M:=fun s=>3*be s+de s
  let A:=fun s=>9+12*z s+m*ga s
  let P:=fun s=>144*(z s)^2+24*m*z s*ga s+m*(m-10)*(ga s)^2+
    156*z s+13*m*ga s-9+5*al s+25*be s
  have hz : HasDerivAt z (deriv z t) t :=
    (hasDerivAt_mul_completedDecayEvenPrimitive u t).congr_deriv
      (hasDerivAt_mul_completedDecayEvenPrimitive u t).deriv.symm
  have ha : HasDerivAt al (deriv al t) t := (hasDerivAt_curvatureShapeAlpha u ht).congr_deriv
    (hasDerivAt_curvatureShapeAlpha u ht).deriv.symm
  have hg : HasDerivAt ga (deriv ga t) t := (hasDerivAt_curvatureShapeGamma u ht).congr_deriv
    (hasDerivAt_curvatureShapeGamma u ht).deriv.symm
  have hb : HasDerivAt be (deriv be t) t := (hasDerivAt_curvatureShapeBeta u ht).congr_deriv
    (hasDerivAt_curvatureShapeBeta u ht).deriv.symm
  have hq : HasDerivAt de (deriv de t) t := (hasDerivAt_curvatureShapeDelta u ht).congr_deriv
    (hasDerivAt_curvatureShapeDelta u ht).deriv.symm
  have hD:=(ha.const_mul 2).add hb
  have hM:=(hb.const_mul 3).add hq
  have hA:=((hz.const_mul 12).const_add 9).add (hg.const_mul m)
  have hP:=((((((((hz.pow 2).const_mul 144).add (((hz.const_mul (24*m)).mul hg))).add
    ((hg.pow 2).const_mul (m*(m-10)))).add (hz.const_mul 156)).add (hg.const_mul (13*m))).sub_const 9).add
    (ha.const_mul 5)).add (hb.const_mul 25)
  let slope:=((2*P t+5*D t)*deriv al t+(P t+25*D t-15*A t)*deriv be t+
    (D t*(24*m*z t+2*m*(m-10)*ga t+13*m)-5*m*M t)*deriv ga t+
    (D t*(288*z t+24*m*ga t+156)-60*M t)*deriv z t-5*A t*deriv de t)/25
  have hpoly : HasDerivAt (actionPowerReserve m u) slope t := by
    change HasDerivAt (fun s=>D s*P s/25-M s*A s/5) slope t
    convert! ((hD.mul hP).div_const 25).sub ((hM.mul hA).div_const 5) using 1
    dsimp only [D,M,A,P,slope,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
    ring
  have hs : t*slope=actionPowerFlow m u t := by
    have he1:=curvatureShapeAlpha_evolution u ht
    have he2:=curvatureShapeBeta_evolution u ht
    have he3:=curvatureShapeGamma_evolution u ht
    have he4:=curvatureShapeAction_evolution u ht
    have he5:=curvatureShapeDelta_evolution u ht
    change t*deriv al t=al t+be t-(al t)^2 at he1
    change t*deriv be t=(2-al t)*be t+de t at he2
    change t*deriv ga t=ga t*(1+al t-2*ga t) at he3
    change t*deriv z t=z t*(1+al t) at he4
    change t*deriv de t=(3-al t)*de t+ep u t at he5
    change t*slope=((2*P t+5*D t)*(al t+be t-(al t)^2)+
      (P t+25*D t-15*A t)*((2-al t)*be t+de t)+
      (D t*(24*m*z t+2*m*(m-10)*ga t+13*m)-5*m*M t)*ga t*(1+al t-2*ga t)+
      (D t*(288*z t+24*m*ga t+156)-60*M t)*z t*(1+al t)-
      5*A t*((3-al t)*de t+ep u t))/25
    dsimp only [slope]
    linear_combination ((2*P t+5*D t)/25)*he1+((P t+25*D t-15*A t)/25)*he2+
      ((D t*(24*m*z t+2*m*(m-10)*ga t+13*m)-5*m*M t)/25)*he3+
      ((D t*(288*z t+24*m*ga t+156)-60*M t)/25)*he4-(A t/5)*he5
  apply hpoly.congr_deriv
  exact (eq_div_iff ht.ne').mpr (by nlinarith only [hs])

private def currentPrefactor (u t : ℝ) : ℝ := F u t/(4*t^4)
private theorem currentPrefactor_deriv (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (currentPrefactor u) (currentPrefactor u t*(actionProfileLogRate u t-4/t)) t := by
  have hh:=(hasDerivAt_intrinsicActionProfile u ht).div
    (((hasDerivAt_id t).pow 4).const_mul 4) (by positivity : (4:ℝ)*t^4 ≠ 0)
  convert! hh using 1
  dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply]
  unfold currentPrefactor
  field_simp [ht.ne']
  ring

private theorem enriched_source_factor (u : ℝ) {t : ℝ} (ht : 0 < t) :
    enrichedActionInverseSource u t=currentPrefactor u t*
      (actionPowerReserve 16 u t+(Q u t)^2*actionPowerReserve 36 u t/15) := by
  rw [enrichedActionInverseSource_eq_normalized u ht,actionPowerReserve_sixteen u ht,
    actionPowerReserve_thirtysix u ht]
  unfold currentPrefactor
  ring

def enrichedSourceEuler (u t : ℝ) : ℝ :=
  actionPowerCurrentKernel 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t) 0+
    (Q u t)^2/15*actionPowerCurrentKernel 36 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t) 0

theorem hasDerivAt_enrichedActionInverseSource (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (enrichedActionInverseSource u) ((F u t/(4*t^4))/t*enrichedSourceEuler u t) t := by
  have heq : enrichedActionInverseSource u =ᶠ[nhds t]
      (fun s=>currentPrefactor u s*(actionPowerReserve 16 u s+(Q u s)^2*actionPowerReserve 36 u s/15)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact enriched_source_factor u hs
  have hh:=(currentPrefactor_deriv u ht).mul
    ((hasDerivAt_actionPowerReserve 16 u ht).add
      ((((Q_deriv u t).pow 2).mul (hasDerivAt_actionPowerReserve 36 u ht)).div_const 15))
  apply (hh.congr_of_eventuallyEq heq).congr_deriv
  dsimp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
  unfold enrichedSourceEuler actionPowerCurrentKernel
  change currentPrefactor u t*(actionProfileLogRate u t-4/t)*
      (actionPowerReserve 16 u t+(Q u t)^2*actionPowerReserve 36 u t/15)+
    currentPrefactor u t*(actionPowerFlow 16 u t/t+
      ((2*(Q u t)^(2-1)*(2*E u t))*actionPowerReserve 36 u t+
        (Q u t)^2*(actionPowerFlow 36 u t/t))/15)=
    currentPrefactor u t/t*(((9+12*Z u t+16*g u t)/5-4-0)*actionPowerReserve 16 u t+
      actionPowerFlow 16 u t+(Q u t)^2/15*
        (((9+12*Z u t+36*g u t)/5-4-0)*actionPowerReserve 36 u t+actionPowerFlow 36 u t))
  unfold actionProfileLogRate curvatureShapeAction curvatureShapeGamma
  field_simp [ht.ne',(thetaCuspReflectedLogAction_pos (u:=u) ht).ne']
  ring

/-- Actual logarithmic clock elasticity; no clock-mass approximation is used. -/
def intrinsicClockLogElasticity (u t : ℝ) : ℝ := t*denominatorClockProfileJet u t/psi u t

def enrichedClockCurrent (u t : ℝ) : ℝ :=
  actionPowerCurrentKernel 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t) (intrinsicClockLogElasticity u t)+
    (Q u t)^2/15*actionPowerCurrentKernel 36 (Z u t) (a u t) (g u t) (b u t) (q u t) (ep u t)
      (intrinsicClockLogElasticity u t)

private theorem enrichedClockCurrent_eq (u t : ℝ) :
    enrichedClockCurrent u t=enrichedSourceEuler u t-intrinsicClockLogElasticity u t*
      (actionPowerReserve 16 u t+(Q u t)^2*actionPowerReserve 36 u t/15) := by
  unfold enrichedClockCurrent enrichedSourceEuler actionPowerCurrentKernel actionPowerReserve
  ring

/-- Exact complete derivative of the enriched inverse-source/clock ratio. -/
theorem hasDerivAt_enrichedInverseClockRatio (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s=>enrichedActionInverseSource u s/psi u s)
      (F u t/(4*t^5*psi u t)*enrichedClockCurrent u t) t := by
  have hh:=(hasDerivAt_enrichedActionInverseSource u ht).div (hasDerivAt_denominatorClockProfile u t)
    (denominatorClockProfile_pos u ht).ne'
  apply hh.congr_deriv
  rw [enrichedClockCurrent_eq,enriched_source_factor u ht]
  unfold currentPrefactor intrinsicClockLogElasticity
  field_simp [ht.ne',(denominatorClockProfile_pos u ht).ne']

/-- Highest source derivative with both actual first-atom endpoints retained. -/
def modelDifferenceEpsilon (u t : ℝ) : ℝ :=
  4*t^2*b u t+t^4*(sourceDefectFactor (thetaCuspLikelihoodCoordinate (u-t))-
    sourceDefectFactor (thetaCuspLikelihoodCoordinate (u+t)))/(2*E u t)

theorem curvatureShapeEpsilon_lt_modelDifference {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    ep u t < modelDifferenceEpsilon u t := by
  have hh:=mul_lt_mul_of_pos_left (quadratureCurvatureThird_lt_modelDifference ht htu)
    (div_pos (pow_pos ht 4) (E_pos u ht))
  unfold curvatureShapeEpsilon modelDifferenceEpsilon curvatureShapeBeta
  convert! hh using 1 <;> field_simp [(E_pos u ht).ne']

def enrichedClockModelCurrent (u t : ℝ) : ℝ :=
  actionPowerCurrentKernel 16 (Z u t) (a u t) (g u t) (b u t) (q u t) (modelDifferenceEpsilon u t)
      (intrinsicClockLogElasticity u t)+
    (Q u t)^2/15*actionPowerCurrentKernel 36 (Z u t) (a u t) (g u t) (b u t) (q u t)
      (modelDifferenceEpsilon u t) (intrinsicClockLogElasticity u t)

/-- The complete current strictly exceeds its actual endpoint-model expression. -/
theorem enrichedClockCurrent_gt_modelCurrent {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    enrichedClockModelCurrent u t < enrichedClockCurrent u t := by
  have hZ : 0 < Z u t := by unfold curvatureShapeAction; exact mul_pos ht (E_pos u ht)
  have hg : 0 < g u t := by
    unfold curvatureShapeGamma
    exact div_pos (mul_pos ht (E_pos u ht)) (thetaCuspReflectedLogAction_pos (u:=u) ht)
  have hcap:=curvatureShapeEpsilon_lt_modelDifference ht htu
  have heq : enrichedClockCurrent u t-enrichedClockModelCurrent u t=
      ((9+12*Z u t+16*g u t)/5+(Q u t)^2/15*(9+12*Z u t+36*g u t)/5)*
        (modelDifferenceEpsilon u t-ep u t) := by
    have h16:=actionPowerCurrentKernel_source_difference 16 (Z u t) (a u t) (g u t) (b u t)
      (q u t) (q u t) (ep u t) (modelDifferenceEpsilon u t) (intrinsicClockLogElasticity u t)
    have h36:=actionPowerCurrentKernel_source_difference 36 (Z u t) (a u t) (g u t) (b u t)
      (q u t) (q u t) (ep u t) (modelDifferenceEpsilon u t) (intrinsicClockLogElasticity u t)
    unfold enrichedClockCurrent enrichedClockModelCurrent
    linear_combination h16+(Q u t)^2/15*h36
  apply sub_pos.mp
  rw [heq]
  exact mul_pos (by positivity) (sub_pos.mpr hcap)

end
end RHTower.ThetaCuspDefect
