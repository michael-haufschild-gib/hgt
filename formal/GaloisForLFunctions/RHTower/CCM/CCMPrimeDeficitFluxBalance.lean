import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitCriticalEnergy
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exact flux balance for the critical prime deficit

The incoming amplitude is the actual square-root-normalized deficit. A
state constructed from its weighted primitive defines an outgoing amplitude.
Their squared flux difference is exactly the derivative of the stored state
energy. The initial state is the arithmetic constant gamma + 1; no bound on
either amplitude is postulated.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

def ccmPrimeDeficitIncoming (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * ccmLogChebyshevDeficitPrimitive t

def ccmPrimeDeficitFluxState (t : ℝ) : ℝ :=
  Real.exp (t / 2) * (Real.eulerMascheroniConstant + 1 -
    ∫ s in (0 : ℝ)..t, Real.exp (-s) * ccmLogChebyshevDeficitPrimitive s)

def ccmPrimeDeficitOutgoing (t : ℝ) : ℝ :=
  ccmPrimeDeficitFluxState t - ccmPrimeDeficitIncoming t

theorem continuous_ccmPrimeDeficitIncoming : Continuous ccmPrimeDeficitIncoming :=
  (Real.continuous_exp.comp (continuous_neg.div_const 2)).mul
    continuous_ccmLogChebyshevDeficitPrimitive

private theorem continuous_weighted_deficit :
    Continuous (fun t => Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) :=
  (Real.continuous_exp.comp continuous_neg).mul continuous_ccmLogChebyshevDeficitPrimitive

theorem continuous_ccmPrimeDeficitFluxState : Continuous ccmPrimeDeficitFluxState :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
    (continuous_const.sub (intervalIntegral.continuous_primitive
      continuous_weighted_deficit.intervalIntegrable 0))

theorem continuous_ccmPrimeDeficitOutgoing : Continuous ccmPrimeDeficitOutgoing :=
  continuous_ccmPrimeDeficitFluxState.sub continuous_ccmPrimeDeficitIncoming

theorem ccmPrimeDeficitIncoming_sq (t : ℝ) :
    ccmPrimeDeficitIncoming t ^ 2 = ccmPrimeDeficitCriticalEnergy t := by
  unfold ccmPrimeDeficitIncoming ccmPrimeDeficitCriticalEnergy
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

@[simp] theorem ccmPrimeDeficitFluxState_zero :
    ccmPrimeDeficitFluxState 0 = Real.eulerMascheroniConstant + 1 := by
  simp [ccmPrimeDeficitFluxState]

/-- The literal weighted primitive solves the state equation at every time,
including prime entries, because the deficit primitive is continuous. -/
theorem hasDerivAt_ccmPrimeDeficitFluxState (t : ℝ) :
    HasDerivAt ccmPrimeDeficitFluxState
      (ccmPrimeDeficitFluxState t / 2 - ccmPrimeDeficitIncoming t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (continuous_weighted_deficit.intervalIntegrable 0 t)
    continuous_weighted_deficit.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_weighted_deficit.continuousAt
  have hd := (((hasDerivAt_id t).div_const 2).exp).mul
    (hi.const_sub (Real.eulerMascheroniConstant + 1))
  have he : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  convert! hd using 1
  dsimp only [ccmPrimeDeficitFluxState, ccmPrimeDeficitIncoming, id_eq]
  rw [show Real.exp (t / 2) * (-(Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t)) =
    -(Real.exp (-t / 2) * ccmLogChebyshevDeficitPrimitive t) by rw [mul_neg, ← mul_assoc, he]]
  ring

/-- Incoming and outgoing squared fluxes differ only by stored energy. -/
theorem hasDerivAt_ccmPrimeDeficitFluxState_sq (t : ℝ) :
    HasDerivAt (fun s => ccmPrimeDeficitFluxState s ^ 2)
      (ccmPrimeDeficitOutgoing t ^ 2 - ccmPrimeDeficitCriticalEnergy t) t := by
  convert! (hasDerivAt_ccmPrimeDeficitFluxState t).pow 2 using 1
  rw [← ccmPrimeDeficitIncoming_sq]
  unfold ccmPrimeDeficitOutgoing
  ring

/-- Exact balance on every finite interval, with both boundary terms kept. -/
theorem ccmPrimeDeficitFlux_balance (a b : ℝ) :
    (∫ t in a..b, ccmPrimeDeficitOutgoing t ^ 2) -
        (∫ t in a..b, ccmPrimeDeficitCriticalEnergy t) =
      ccmPrimeDeficitFluxState b ^ 2 - ccmPrimeDeficitFluxState a ^ 2 := by
  have ho : IntervalIntegrable (fun t => ccmPrimeDeficitOutgoing t ^ 2) volume a b :=
    (continuous_ccmPrimeDeficitOutgoing.pow 2).intervalIntegrable a b
  have hi := continuous_ccmPrimeDeficitCriticalEnergy.intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_sub ho hi]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_ccmPrimeDeficitFluxState_sq t) (ho.sub hi)

theorem ccmPrimeDeficitCriticalEnergy_integral_le_outgoing (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) ≤
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitOutgoing t ^ 2) +
        (Real.eulerMascheroniConstant + 1) ^ 2 := by
  have h := ccmPrimeDeficitFlux_balance 0 T
  rw [ccmPrimeDeficitFluxState_zero] at h
  nlinarith only [h, sq_nonneg (ccmPrimeDeficitFluxState T)]

end RHTower
