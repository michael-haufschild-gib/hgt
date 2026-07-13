import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProuhetPacket
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailHaarSeamCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedPotential

/-!
# The invariant residual of a two-endpoint Prouhet seam packet

Subtracting one half of the elementary decaying character from the canonical density removes its
entire reflection defect.  The resulting signed density is exactly even.  This is the full-line
coordinate in which the finite Prouhet packet annihilates every polynomial translation moment.

There is nevertheless a depth-independent residual.  If the packet has total mass one and its
second endpoint cancels the growing elementary square, the surviving value/derivative
polarization is the mixed current of `E - 2 U` with `E`.  Algebraically it is exactly

`current (U - E) - current U`.

Thus increasing the Prouhet depth cannot remove this residual: it is an invariant of the two
endpoint constraints, not a truncation error.  This module records that no-go identity so the
Prouhet packet is used only for the translation polynomial it genuinely cancels.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-- The canonical density with its decaying half-exponential reflection character removed. -/
def thetaCuspTailSecondEvenRemainder (x : ℝ) : ℝ :=
  thetaCuspTailSecondDensity x - (1 / 2 : ℝ) * Real.exp (-x / 2)

/-- The remainder is exactly even; this uses the precise theta reflection value relation. -/
theorem thetaCuspTailSecondEvenRemainder_neg (x : ℝ) :
    thetaCuspTailSecondEvenRemainder (-x) = thetaCuspTailSecondEvenRemainder x := by
  rw [thetaCuspTailSecondEvenRemainder, thetaCuspTailSecondEvenRemainder,
    thetaCuspTailSecondDensity_neg]
  unfold thetaCuspReflectionMode
  have hneg : -(-x) / 2 = x / 2 := by ring
  rw [hneg]
  ring

/-- The even remainder is the derivative of the odd completed-survival profile. -/
theorem hasDerivAt_thetaCuspCompletedSurvivalRemainder
    (x : ℝ) :
    HasDerivAt thetaCuspCompletedSurvivalRemainder
      (thetaCuspTailSecondEvenRemainder x) x := by
  unfold thetaCuspCompletedSurvivalRemainder thetaCuspTailSecondEvenRemainder
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t / 2))
      (-(1 / 2 : ℝ) * Real.exp (-x / 2)) x := by
    convert (Real.hasDerivAt_exp (-x / 2)).comp x
      ((hasDerivAt_neg x).div_const 2) using 1
    ring
  convert hexp.sub (hasDerivAt_thetaCuspTailSurvival x) using 1
  ring

private theorem integrableOn_exp_neg_half_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) (Set.Ioi 0) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
    fun x : ℝ => (Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ 0 -
      (z ^ 2 + 1 / 4) * ((Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondSection d z x) by
      funext x
      unfold thetaCuspTailSecondCoreAtom
      simp only [pow_zero, mul_one]
      ring]
  refine (integrableOn_exp_neg_half_mul_complexPower 0).sub ?_
  rw [show (fun x : ℝ => (z ^ 2 + 1 / 4) *
      ((Real.exp (-x / 2) : ℂ) * thetaCuspTailSecondSection d z x)) =
    fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
      ((z ^ 2 + 1 / 4) * thetaCuspTailSecondSectionSourceCoefficient z r) *
        ((Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ (2 * r + 2)) by
      funext x
      rw [thetaCuspTailSecondSection_eq_sourcePowerPacket,
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
  exact MeasureTheory.integrable_finsetSum _ fun r _hr =>
    (integrableOn_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _

private theorem integrableOn_exp_neg_half_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) (Set.Ioi 0) := by
  rw [show (fun x : ℝ => (Real.exp (-x / 2) : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
    fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
      thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
        ((Real.exp (-x / 2) : ℂ) * (x : ℂ) ^ (2 * r + 2)) by
      funext x
      rw [thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
  exact MeasureTheory.integrable_finsetSum _ fun r _hr =>
    (integrableOn_exp_neg_half_mul_complexPower (2 * r + 2)).const_mul _

/-- The positive-half transform of the even remainder is exactly the finite core minus its
leading completed-survival monomial.  This identifies the Prouhet invariant at value level. -/
theorem integral_thetaCuspTailSecondEvenRemainder_mul_coreAtom
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Set.Ioi 0, (thetaCuspTailSecondEvenRemainder x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
      2 * (xiCTaylorThetaTailCorePolynomial d).eval z -
        thetaCuspCompletedSurvivalMonomial d z := by
  rw [show (fun x : ℝ => (thetaCuspTailSecondEvenRemainder x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x) =
    fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x -
      (1 / 2 : ℂ) * ((Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) by
      funext x
      unfold thetaCuspTailSecondEvenRemainder
      push_cast
      ring]
  rw [MeasureTheory.integral_sub
      (integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z)
      ((integrableOn_exp_neg_half_mul_coreAtom d z).const_mul (1 / 2 : ℂ)),
    MeasureTheory.integral_const_mul,
    integral_exp_neg_half_mul_coreAtom]
  have h := xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral d z
  unfold thetaCuspCompletedSurvivalMonomial
  rw [h]
  ring

/-- Derivative-level companion of the exact even-remainder transform. -/
theorem integral_thetaCuspTailSecondEvenRemainder_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Set.Ioi 0, (thetaCuspTailSecondEvenRemainder x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
      2 * (xiCTaylorThetaTailCorePolynomial d).derivative.eval z -
        thetaCuspCompletedSurvivalMonomialDerivative d z := by
  rw [show (fun x : ℝ => (thetaCuspTailSecondEvenRemainder x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x) =
    fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x -
      (1 / 2 : ℂ) * ((Real.exp (-x / 2) : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) by
      funext x
      unfold thetaCuspTailSecondEvenRemainder
      push_cast
      ring]
  rw [MeasureTheory.integral_sub
      (integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z)
      ((integrableOn_exp_neg_half_mul_coreAtomDerivative d z).const_mul (1 / 2 : ℂ)),
    MeasureTheory.integral_const_mul,
    integral_exp_neg_half_mul_coreAtomDerivative]
  have h := xiCTaylorThetaTailCorePolynomial_derivative_eval_eq_second_integral d z
  unfold thetaCuspCompletedSurvivalMonomialDerivative
  rw [h]
  ring

/-- The residual current forced by the two endpoint constraints.  Here `2 U` is the unnormalized
canonical-density transform and `E` is the elementary half-exponential transform.  The left side
is one half of their symmetric mixed value/derivative current. -/
theorem twoEndpointProuhet_residual_current_invariant
    (U E : Polynomial ℂ) (z : ℂ) :
    (1 / 2 : ℝ) *
        (((E.derivative.eval z - 2 * U.derivative.eval z) *
            (starRingEnd ℂ) (E.eval z)).im +
          (E.derivative.eval z *
            (starRingEnd ℂ) (E.eval z - 2 * U.eval z)).im) =
      orientedPolynomialCurrent (U - E) z - orientedPolynomialCurrent U z := by
  rw [orientedPolynomialCurrent_sub_exact]
  simp [orientedPolynomialCurrent, Complex.sub_im]
  ring

end

end RHTower
