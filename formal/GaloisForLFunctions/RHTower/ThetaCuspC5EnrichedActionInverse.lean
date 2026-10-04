import GaloisForLFunctions.RHTower.ThetaCuspC5EnrichedActionProfile
import GaloisForLFunctions.RHTower.ThetaCuspC5CoupledShapeDynamics
/-! Exact positive Green inverse of the Bose-enriched action profile. The added
source is strictly positive throughout the physical chamber. Its complete
comparison with the denominator clock remains open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
noncomputable section
local notation "F" => intrinsicActionProfile
local notation "Q" => thetaCuspReflectedLogAction
local notation "E" => completedDecayEvenPrimitive
local notation "e" => completedCurvatureEven
local notation "d" => completedLocalDenominator
local notation "d₁" => descentDenominatorJet
local notation "y" => completedFirstDenominator
local notation "Z" => curvatureShapeAction
local notation "a" => curvatureShapeAlpha
local notation "g" => curvatureShapeGamma
local notation "b" => curvatureShapeBeta
local notation "q" => curvatureShapeDelta
local notation "R" => normalizedActionInverseReserve

private theorem E_pos (u : ℝ) {t : ℝ} (ht : 0 < t) : 0 < E u t := by
  have hh := descentDenominator_pos u ht
  unfold descentDenominator at hh
  exact (mul_pos_iff_of_pos_left ht).mp hh
private theorem Q_deriv (u t : ℝ) : HasDerivAt (Q u) (2*E u t) t := by
  convert! hasDerivAt_thetaCuspReflectedLogAction u t using 1
  rw [completedDecayEvenPrimitive_eq]
  ring

private theorem enrichedProfileJet_deriv (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => F u s*(actionProfileLogRate u s*(1+(Q u s)^2/15)+4*Q u s*E u s/15))
      (F u t*(((actionProfileLogRate u t)^2+actionProfileLogRateJet u t)*(1+(Q u t)^2/15)+
        8*actionProfileLogRate u t*Q u t*E u t/15+(8*(E u t)^2+4*Q u t*e u t)/15)) t := by
  have hQ := Q_deriv u t
  have hE := hasDerivAt_completedDecayEvenPrimitive u t
  have hh := (hasDerivAt_intrinsicActionProfile u ht).mul
    (((hasDerivAt_actionProfileLogRate u ht).mul (((hQ.pow 2).div_const 15).const_add 1)).add
      ((((hQ.const_mul 4).mul hE).div_const 15)))
  convert! hh using 1
  dsimp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
  ring

theorem iteratedDeriv_two_enrichedActionProfile (u : ℝ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (enrichedActionProfile u) t=
      F u t*(((actionProfileLogRate u t)^2+actionProfileLogRateJet u t)*(1+(Q u t)^2/15)+
        8*actionProfileLogRate u t*Q u t*E u t/15+(8*(E u t)^2+4*Q u t*e u t)/15) := by
  conv_lhs => rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have heq : deriv (enrichedActionProfile u) =ᶠ[nhds t]
      (fun s => F u s*(actionProfileLogRate u s*(1+(Q u s)^2/15)+4*Q u s*E u s/15)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hasDerivAt_enrichedActionProfile u hs).deriv
  rw [heq.deriv_eq]
  exact (enrichedProfileJet_deriv u ht).deriv

/-- Exact additional normalized inverse reserve supplied by the squared-action factor. -/
def enrichedInverseIncrementReserve (u t : ℝ) : ℝ :=
  (4*g u t/5)*((2*a u t+b u t)*(24*Z u t+42*g u t+13)-5*(3*b u t+q u t))

theorem enrichedInverseIncrementReserve_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < enrichedInverseIncrementReserve u t := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hg : 0 < g u t := by unfold curvatureShapeGamma; positivity
  have hZ : 0 < Z u t := by unfold curvatureShapeAction; positivity
  have hD : 0 < 2*a u t+b u t := by
    have hh := mul_pos (div_pos ht hE) (completedLocalDenominator_pos_nonneg u ht.le)
    convert! hh using 1
    unfold curvatureShapeAlpha curvatureShapeBeta completedLocalDenominator shapeCurvatureSlope
    ring
  have hM : 3*b u t+q u t < (2*a u t+b u t)*(1+3*Z u t/8) := by
    have hh := mul_lt_mul_of_pos_left (actionProfile_denominator_budget ht htu) (div_pos ht hE)
    unfold curvatureShapeBeta curvatureShapeDelta curvatureShapeAlpha curvatureShapeAction
    convert! hh using 1 <;>
      dsimp [descentDenominatorJet,completedLocalDenominator,shapeCurvatureSlope,shapeCurvatureSecond] <;>
      field_simp [hE.ne']
  have hh : 0 < (2*a u t+b u t)*((177/8:ℝ)*Z u t+42*g u t+8) := by positivity
  have hb : 0 < (2*a u t+b u t)*(24*Z u t+42*g u t+13)-5*(3*b u t+q u t) := by
    nlinarith only [hM,hh]
  unfold enrichedInverseIncrementReserve
  exact mul_pos (by positivity) hb

/-- The literal inverse-Green differential operator of the enriched action profile. -/
def enrichedActionInverseSource (u t : ℝ) : ℝ :=
  (d u t*descentDenominator u t*iteratedDeriv 2 (enrichedActionProfile u) t-
    (d₁ u t*descentDenominator u t+d u t*y u t)*deriv (enrichedActionProfile u) t+
    (d u t)^2*enrichedActionProfile u t)/(4*(descentDenominator u t)^2)

theorem enrichedActionInverseSource_eq_normalized (u : ℝ) {t : ℝ} (ht : 0 < t) :
    enrichedActionInverseSource u t=
      F u t*(R u t*(1+(Q u t)^2/15)+(Q u t)^2*enrichedInverseIncrementReserve u t/15)/(4*t^4) := by
  have hE := E_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  unfold enrichedActionInverseSource
  rw [iteratedDeriv_two_enrichedActionProfile u ht,(hasDerivAt_enrichedActionProfile u ht).deriv]
  unfold enrichedActionProfile normalizedActionInverseReserve actionProfileInverseReserve
    actionProfileLogRate actionProfileLogRateJet enrichedInverseIncrementReserve
    curvatureShapeAction curvatureShapeAlpha curvatureShapeGamma curvatureShapeBeta curvatureShapeDelta
    descentDenominator completedLocalDenominator descentDenominatorJet completedFirstDenominator
    shapeCurvatureSlope shapeCurvatureSecond
  field_simp [ht.ne',hE.ne',hQ.ne']
  ring

/-- The added source strictly exceeds multiplication of the original source by the profile factor. -/
theorem enrichedActionInverseSource_gt_original {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    intrinsicActionInverseSource u t*(1+(Q u t)^2/15) < enrichedActionInverseSource u t := by
  rw [enrichedActionInverseSource_eq_normalized u ht,intrinsicActionInverseSource_eq_normalized u ht]
  have hi := enrichedInverseIncrementReserve_pos ht htu
  have hF := intrinsicActionProfile_pos u ht
  have hQ := thetaCuspReflectedLogAction_pos (u := u) ht
  have hp : 0 < F u t*(Q u t)^2*enrichedInverseIncrementReserve u t/(60*t^4) := by positivity
  have he : F u t*(R u t*(1+(Q u t)^2/15)+(Q u t)^2*enrichedInverseIncrementReserve u t/15)/(4*t^4)-
      F u t*R u t/(4*t^4)*(1+(Q u t)^2/15)=
      F u t*(Q u t)^2*enrichedInverseIncrementReserve u t/(60*t^4) := by ring
  apply sub_pos.mp
  rw [he]
  exact hp

theorem enrichedActionInverseSource_pos {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < enrichedActionInverseSource u t := by
  have hh := mul_pos (intrinsicActionInverseSource_pos ht htu) (show 0<1+(Q u t)^2/15 by positivity)
  exact hh.trans (enrichedActionInverseSource_gt_original ht htu)

end
end RHTower.ThetaCuspDefect
