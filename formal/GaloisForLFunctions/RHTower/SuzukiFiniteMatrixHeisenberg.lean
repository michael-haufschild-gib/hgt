import GaloisForLFunctions.RHTower.SuzukiPositionCommutatorGroup
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# A finite matrix realization of the Suzuki position flow

The two-level nilpotent shift and position projector satisfy `[A,X]=A`. Since `A` commutes with
itself, the Suzuki Heisenberg evolution terminates after the first commutator and becomes the exact
affine law `exp(tA) X exp(-tA) = X + tA`. The word transport theorem then applies with no premises.
-/

open NormedSpace Matrix
open scoped Matrix.Norms.Operator

noncomputable section

namespace RHTower

/-- Two-level nilpotent raising shift. -/
def nilpotentShift2 : Matrix Bool Bool ℝ :=
  fun i j => if i = false ∧ j = true then 1 else 0

/-- Projection onto the upper position level. -/
def positionProjection2 : Matrix Bool Bool ℝ :=
  Matrix.diagonal fun i => if i = true then 1 else 0

/-- Exact finite matrix commutator `[A,X]=A`. -/
theorem nilpotentShift2_positionProjection2_commutator :
    nilpotentShift2 * positionProjection2 - positionProjection2 * nilpotentShift2 =
      nilpotentShift2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentShift2, positionProjection2, Matrix.mul_apply, Fintype.sum_bool]

/-- Exact affine Heisenberg flow of the two-level position projector. -/
theorem nilpotentShift2_position_heisenbergFlow (t : ℝ) :
    exp (t • nilpotentShift2) * positionProjection2 * exp ((-t) • nilpotentShift2) =
      positionProjection2 + t • nilpotentShift2 :=
  conj_position_eq nilpotentShift2 positionProjection2 nilpotentShift2
    nilpotentShift2_positionProjection2_commutator (Commute.refl nilpotentShift2) t

/-- Position passes through the finite evolution with the exact affine correction. -/
theorem nilpotentShift2_position_mul_evolution (t : ℝ) :
    positionProjection2 * exp ((-t) • nilpotentShift2) =
      exp ((-t) • nilpotentShift2) * (positionProjection2 + t • nilpotentShift2) :=
  position_mul_exp nilpotentShift2 positionProjection2 nilpotentShift2
    nilpotentShift2_positionProjection2_commutator (Commute.refl nilpotentShift2) t

/-- Every word in the position projector transports through evolution by the same affine shift. -/
theorem nilpotentShift2_positionWord_mul_evolution (t : ℝ) (l : List Unit) :
    (l.map fun _ => positionProjection2).prod * exp ((-t) • nilpotentShift2) =
      exp ((-t) • nilpotentShift2) *
        (l.map fun _ => positionProjection2 + t • nilpotentShift2).prod :=
  listProd_mul_exp nilpotentShift2 (fun _ => positionProjection2)
    (fun _ => nilpotentShift2)
    (fun _ => nilpotentShift2_positionProjection2_commutator)
    (fun _ => Commute.refl nilpotentShift2) t l

end RHTower
