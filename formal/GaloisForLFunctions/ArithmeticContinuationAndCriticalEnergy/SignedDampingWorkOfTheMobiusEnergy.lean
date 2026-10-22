import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy
import GaloisForLFunctions.BezoutValuationIncidence.DampingWorkAsArithmeticMarkovBoundaryFlux

/-!
# The complete signed damping work of the Möbius energy

Continuation in the damping asks for one number per damping and horizon: the **complete signed
work** of the centred source against its own damping tangent,

`W_T(ε) = Σ_{n ≤ T} A_ε(n) · E_ε(n) / (n(n+1))`,

where `A_ε` is the centred damped divisor prefix and `E_ε = ∂_ε A_ε` the centred damped Chebyshev
function.  The energy's damping derivative is exactly `2 W_T(ε)`; this is the quantity whose
negative part has to be paid, and it is *not* a norm, not a sum of absolute cross terms, and not
an energy with the pole correction deleted.

Three facts are recorded.

* The derivative identity `∂_ε E_T = 2 W_T`, from the owned tangent law.
* The bridge to the Markov form of the same derivative: `2 W_T` equals boundary flux minus jump
  energy minus density forcing.  So the signed work has two exact faces and may be attacked from
  either: a Cauchy–Schwarz face against the tangent norm, and a flux/dissipation face.
* Cauchy–Schwarz: the tangent-norm receiver controls the signed work, with `√E ≤ (1+E)/2`
  absorbing the energy factor.  This is the inclusion that makes the signed-work demand *weaker*
  than the tangent-norm demand it replaces.
-/

open Finset Set RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The signed work and the derivative identity -/

/-- **The complete signed damping work.**  The pronic pairing of the centred damped divisor prefix
with its own damping tangent, read to horizon `T`.  Signs are kept: this is one number, not a sum
of separately bounded pieces. -/
def signedDampingWork (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n * dampedChebyshevError ε n /
    ((n : ℝ) * ((n : ℝ) + 1))

/-- **The damping derivative of the critical energy is twice the signed work.** -/
theorem hasDerivAt_dampedMobiusEnergy {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => dampedMobiusEnergy x T) (2 * signedDampingWork ε T) ε := by
  have h := HasDerivAt.fun_sum (u := Icc 1 T)
    (A := fun n x => pmPowerDampedCenteredDivisorPrefix x n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
    (A' := fun n => 2 * pmPowerDampedCenteredDivisorPrefix ε n * dampedChebyshevError ε n /
      ((n : ℝ) * ((n : ℝ) + 1)))
    (fun n _ => by
      have hp := ((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε n).pow 2).div_const
        ((n : ℝ) * ((n : ℝ) + 1))
      refine hp.congr_deriv ?_
      push_cast
      ring)
  refine h.congr_deriv ?_
  rw [signedDampingWork, mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- **Two faces of one derivative.**  The signed work equals the Markov balance of the same
arithmetic chain: counting-measure boundary flux, less the nonnegative jump energy, less the
density forcing.  Both faces are exact; neither supplies a horizon-uniform bound by itself. -/
theorem two_mul_signedDampingWork_eq_markov {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    2 * signedDampingWork ε T =
      arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T -
        arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T -
        2 * dampedReadout ε *
          ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean ε n :=
  (hasDerivAt_dampedMobiusEnergy hε T).unique
    (hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov hε T)

/-! ## §2. Cauchy–Schwarz against the tangent norm -/

theorem pronicNorm_neg (T : ℕ) (v : ℕ → ℝ) : pronicNorm T (fun n => -v n) = pronicNorm T v := by
  unfold pronicNorm
  exact congrArg Real.sqrt (sum_congr rfl fun n _ => by rw [neg_pow_two])

theorem pronicNorm_centeredPrefix (ε : ℝ) (T : ℕ) :
    pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) = Real.sqrt (dampedMobiusEnergy ε T) := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_pronicNorm_sq,
    Real.sqrt_sq (pronicNorm_nonneg T _)]

/-- The negative part of the signed work is at most the product of the energy's square root with
the tangent norm. -/
theorem neg_signedDampingWork_le (ε : ℝ) (T : ℕ) :
    -signedDampingWork ε T ≤
      Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T (dampedChebyshevError ε) := by
  have h := sum_mul_div_le_pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε)
    (fun n => -dampedChebyshevError ε n)
  rw [pronicNorm_neg, pronicNorm_centeredPrefix] at h
  refine le_trans (le_of_eq ?_) h
  rw [signedDampingWork, ← sum_neg_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- `2√E ≤ 1 + E`: the elementary step that converts a linear-in-norm bound into the linear
continuation shape `β'(ε)(1 + E)`. -/
theorem two_mul_sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : 2 * Real.sqrt x ≤ 1 + x := by
  have h := sq_nonneg (Real.sqrt x - 1)
  rw [sub_sq, Real.sq_sqrt hx] at h
  linarith

/-- **The tangent norm pays the continuation budget.**  A horizon-uniform bound `g` on the pronic
norm of the damped Chebyshev tangent gives the complete signed inequality in continuation shape,
with budget derivative `g` — no horizon enters. -/
theorem neg_two_mul_signedDampingWork_le_of_tangentNorm_le {ε g : ℝ} (T : ℕ)
    (hg : pronicNorm T (dampedChebyshevError ε) ≤ g) :
    -(2 * signedDampingWork ε T) ≤ g * (1 + dampedMobiusEnergy ε T) := by
  have hg0 : 0 ≤ g := le_trans (pronicNorm_nonneg _ _) hg
  have hE := dampedMobiusEnergy_nonneg ε T
  have h1 := neg_signedDampingWork_le ε T
  have h2 : Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T (dampedChebyshevError ε) ≤
      Real.sqrt (dampedMobiusEnergy ε T) * g :=
    mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)
  have h3 : 2 * Real.sqrt (dampedMobiusEnergy ε T) ≤ 1 + dampedMobiusEnergy ε T :=
    two_mul_sqrt_le_one_add hE
  nlinarith [Real.sqrt_nonneg (dampedMobiusEnergy ε T)]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
