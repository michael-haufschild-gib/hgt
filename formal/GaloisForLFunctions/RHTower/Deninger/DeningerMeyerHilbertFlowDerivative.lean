import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHilbertFlow
import Mathlib.Analysis.Complex.RealDeriv

/-! # The original generator differentiates every full-flow coordinate

The formula includes the Hasse predecessor term at every repeated zero. It
will permit integration by parts for actual flow averages without assuming
that arbitrary Hilbert vectors lie in the unbounded generator domain.
-/

noncomputable section
open Complex

namespace RHTower

theorem hasDerivAt_deningerHasseShiftEvolution (t : ℝ) :
    HasDerivAt deningerHasseShiftEvolution
      (deningerHasseHilbertShift.comp (deningerHasseShiftEvolution t)) t := by
  have h := (hasDerivAt_exp_smul_const' deningerHasseHilbertShift (t : ℂ)).scomp t
    Complex.ofRealCLM.hasDerivAt
  simpa only [deningerHasseShiftEvolution, Function.comp_def, Complex.ofRealCLM_apply,
    Complex.ofReal_one, one_smul] using! h

theorem deningerHasseDiagonalFlow_shift (t : ℝ) (x : DeningerArithmeticJetHilbert) :
    deningerHasseDiagonalFlow t (deningerHasseHilbertShift x) =
      deningerHasseHilbertShift (deningerHasseDiagonalFlow t x) := by
  apply lp.ext
  funext q
  rcases q with ⟨rho, j, hj⟩
  cases j with
  | zero => simp only [deningerHasseDiagonalFlow_apply, deningerHasseHilbertShift_zero, mul_zero]
  | succ j => simp only [deningerHasseDiagonalFlow_apply, deningerHasseHilbertShift_succ]

/-- Differentiation is coordinatewise valid for every Hilbert vector, with every Jordan term. -/
theorem hasDerivAt_deningerMeyerHilbertFlow_coordinate (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) (t : ℝ) :
    HasDerivAt (fun s => deningerMeyerHilbertFlow s x q)
      ((q.1 : ℂ)*deningerMeyerHilbertFlow t x q +
        deningerHasseHilbertShift (deningerMeyerHilbertFlow t x) q) t := by
  let ev := ((lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q).comp
    ((ContinuousLinearMap.apply ℂ DeningerArithmeticJetHilbert) x)).restrictScalars ℝ
  have he := ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_deningerHasseShiftEvolution t)
  change HasDerivAt (fun s => deningerHasseShiftEvolution s x q)
    (deningerHasseHilbertShift (deningerHasseShiftEvolution t x) q) t at he
  have hd : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ)*(q.1 : ℂ)))
      ((q.1 : ℂ)*Complex.exp ((t : ℂ)*(q.1 : ℂ))) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_comm, mul_one, one_mul] using
      (((hasDerivAt_id t).ofReal_comp.mul_const (q.1 : ℂ)).cexp)
  have hcomm := congrArg (fun y : DeningerArithmeticJetHilbert => y q)
    (deningerHasseDiagonalFlow_shift t (deningerHasseShiftEvolution t x))
  change Complex.exp ((t : ℂ)*(q.1 : ℂ))*
      deningerHasseHilbertShift (deningerHasseShiftEvolution t x) q =
    deningerHasseHilbertShift (deningerMeyerHilbertFlow t x) q at hcomm
  have hprod := hd.mul he
  change HasDerivAt (fun s => deningerMeyerHilbertFlow s x q) _ t at hprod
  convert hprod using 1
  rw [← hcomm]
  change (q.1 : ℂ)*(Complex.exp ((t : ℂ)*(q.1 : ℂ))*deningerHasseShiftEvolution t x q) + _ = _
  ring

theorem continuous_deningerMeyerHilbertFlow_coordinate_deriv (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    Continuous (fun t => (q.1 : ℂ)*deningerMeyerHilbertFlow t x q +
      deningerHasseHilbertShift (deningerMeyerHilbertFlow t x) q) := by
  let ev := lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q
  exact (continuous_const.mul (ev.continuous.comp (continuous_deningerMeyerHilbertFlow_orbit x))).add
    (ev.continuous.comp (deningerHasseHilbertShift.continuous.comp
      (continuous_deningerMeyerHilbertFlow_orbit x)))

end RHTower
