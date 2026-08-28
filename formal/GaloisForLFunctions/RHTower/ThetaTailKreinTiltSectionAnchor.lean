import GaloisForLFunctions.RHTower.ThetaTailKreinXiCentTiltCollapse

/-!
# Sesquilinear section anchor for the tilt channels

The sesquilinear specialization of the all-plane tilt identity: every Bezoutian section entry is
the tilt Gram difference at that node pair, so finite Bezoutian sections are congruent to
differences of two tilt Grams, uniformly in the tilt parameter.  The tilt parameter enters both
sides only through the common positive factor: the Gram differences at two parameters are exact
positive rescalings of one another, so every inertia-type datum of a section is
parameter-independent.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- **Sesquilinear tilt form of the Bezoutian section entry.** -/
theorem two_mul_mul_xiCentBezoutian_conj_eq_tiltGram (c : ℝ) (w v : ℂ) :
    2 * (c : ℂ) * (w + conj v) * xiCentBezoutian w (conj v) =
      xiCentTiltPlus c w * conj (xiCentTiltPlus c v) -
        xiCentTiltMinus c w * conj (xiCentTiltMinus c v) := by
  rw [two_mul_add_mul_xiCentBezoutian_eq_tilt c w (conj v),
    ← xiCentTiltPlus_conj, ← xiCentTiltMinus_conj]

/-- **Parameter uniformity of the tilt Gram difference.**  The Gram differences at two tilt
parameters are exact mutual rescalings: section inertia carries no dependence on the tilt. -/
theorem tiltGram_param_uniform (c c' : ℝ) (w v : ℂ) :
    (c' : ℂ) * (xiCentTiltPlus c w * conj (xiCentTiltPlus c v) -
        xiCentTiltMinus c w * conj (xiCentTiltMinus c v)) =
      (c : ℂ) * (xiCentTiltPlus c' w * conj (xiCentTiltPlus c' v) -
        xiCentTiltMinus c' w * conj (xiCentTiltMinus c' v)) := by
  rw [← two_mul_mul_xiCentBezoutian_conj_eq_tiltGram c w v,
    ← two_mul_mul_xiCentBezoutian_conj_eq_tiltGram c' w v]
  ring

end

end RHTower
