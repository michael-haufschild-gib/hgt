import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaXiLanding
import GaloisForLFunctions.HTGeometry.FiniteBuresTargetMinimaxCore

/-!
# Orientation-preserving pure density behind the Euler--Wick Xi landing

The scalar EWQ replica diagonal recovers every Euler-log coefficient, but scalarization erases
the joint quadratic character.  This file proves that loss is not intrinsic.  At every prime and
valuation depth the two channels form the rank-one density

`(1 / k) [[1, chi^k], [chi^k, 1]]`.

After trace normalization this is a positive semidefinite rank-one projection.  A fixed Pauli-X
observable reads `chi^k` exactly, while either diagonal channel remains the coefficient-faithful
Euler-log source whose completed carrier is Xi.  Thus completed-Xi landing and arithmetic
orientation coexist in one unconditional matrix source; only a later scalar or invariant reader
throws the orientation away.
-/

namespace GaloisForLFunctions.RHTower

open Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Every prime-depth EWQ character remains an involution. -/
theorem eulerWickQuadraticDepthCharacter_sq (x : PrimePowerClockIndex) :
    eulerWickQuadraticDepthCharacter x ^ 2 = 1 := by
  unfold eulerWickQuadraticDepthCharacter
  rw [← pow_mul, Nat.mul_comm (x.2 + 1) 2, pow_mul,
    quadraticResidueProductPrimeCoefficient_sq, one_pow]

/-- The prime-depth character is a literal binary orientation. -/
theorem eulerWickQuadraticDepthCharacter_eq_one_or_neg_one
    (x : PrimePowerClockIndex) :
    eulerWickQuadraticDepthCharacter x = 1 ∨
      eulerWickQuadraticDepthCharacter x = -1 := by
  exact (sq_eq_one_iff).mp (eulerWickQuadraticDepthCharacter_sq x)

@[simp] theorem star_eulerWickQuadraticDepthCharacter (x : PrimePowerClockIndex) :
    star (eulerWickQuadraticDepthCharacter x) =
      eulerWickQuadraticDepthCharacter x := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    simp [h]

/-- Two-channel pure vector retaining vacuum and joint-character coordinates. -/
def eulerWickReplicaVector (x : PrimePowerClockIndex) : Fin 2 → ℂ :=
  ![1, eulerWickQuadraticDepthCharacter x]

/-- Trace-one pure state determined by one EWQ prime-depth character. -/
def eulerWickReplicaPureProjector
    (x : PrimePowerClockIndex) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • finiteBuresTargetRay (eulerWickReplicaVector x)

theorem eulerWickReplicaPureProjector_apply
    (x : PrimePowerClockIndex) (i j : Fin 2) :
    eulerWickReplicaPureProjector x i j =
      (1 / 2 : ℂ) *
        (if i = 0 then 1 else eulerWickQuadraticDepthCharacter x) *
        (if j = 0 then 1 else eulerWickQuadraticDepthCharacter x) := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickReplicaPureProjector, eulerWickReplicaVector,
        finiteBuresTargetRay, Matrix.vecMulVec, h]

/-- The normalized EWQ lift is positive semidefinite. -/
theorem eulerWickReplicaPureProjector_posSemidef
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaPureProjector x).PosSemidef := by
  exact (finiteBuresTargetRay_posSemidef (eulerWickReplicaVector x)).smul (by norm_num)

/-- The normalized EWQ lift is a projection, hence a pure density operator. -/
theorem eulerWickReplicaPureProjector_sq
    (x : PrimePowerClockIndex) :
    eulerWickReplicaPureProjector x * eulerWickReplicaPureProjector x =
      eulerWickReplicaPureProjector x := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, eulerWickReplicaPureProjector_apply, h] <;>
      norm_num

/-- The pure projector has unit trace. -/
theorem eulerWickReplicaPureProjector_trace
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaPureProjector x).trace = 1 := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h
  · norm_num [Matrix.trace, eulerWickReplicaPureProjector_apply, h]
  · norm_num [Matrix.trace, eulerWickReplicaPureProjector_apply, h]

/-- Fixed Pauli-X reporter on the two replica channels. -/
def eulerWickReplicaPauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else 1

/-- The pure EWQ state is a Pauli-X eigenstate with its literal depth character as eigenvalue. -/
theorem eulerWickReplicaPauliX_mul_projector
    (x : PrimePowerClockIndex) :
    eulerWickReplicaPauliX * eulerWickReplicaPureProjector x =
      eulerWickQuadraticDepthCharacter x • eulerWickReplicaPureProjector x := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [eulerWickReplicaPauliX, Matrix.mul_apply,
        eulerWickReplicaPureProjector_apply, h]

/-- The fixed Pauli-X observable reads the literal arithmetic character from the pure lift. -/
theorem trace_eulerWickReplicaPauliX_mul_projector
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaPauliX * eulerWickReplicaPureProjector x).trace =
      eulerWickQuadraticDepthCharacter x := by
  rw [eulerWickReplicaPauliX_mul_projector]
  simp [Matrix.trace_smul, eulerWickReplicaPureProjector_trace]

/-- Euler-log-weighted pure density at one prime-depth coordinate. -/
def eulerWickReplicaDensity
    (x : PrimePowerClockIndex) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((x.2 + 1 : ℕ) : ℝ))⁻¹ •
    finiteBuresTargetRay (eulerWickReplicaVector x)

theorem eulerWickReplicaDensity_posSemidef
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaDensity x).PosSemidef := by
  exact (finiteBuresTargetRay_posSemidef (eulerWickReplicaVector x)).smul (by positivity)

/-- First diagonal coordinate is the canonical Euler-log coefficient. -/
theorem eulerWickReplicaDensity_apply_zero_zero
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x 0 0 = eulerLogValuationProfile x.2 := by
  simp [eulerWickReplicaDensity, eulerWickReplicaVector,
    finiteBuresTargetRay, Matrix.vecMulVec, eulerLogValuationProfile]

/-- Forward off-diagonal coordinate retains the unsquared character replica. -/
theorem eulerWickReplicaDensity_apply_zero_one
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x 0 1 = eulerWickQuadraticEulerLogReplica x := by
  simp only [eulerWickReplicaDensity, eulerWickReplicaVector,
    finiteBuresTargetRay, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply,
    star_eulerWickQuadraticDepthCharacter, Complex.real_smul,
    eulerWickQuadraticEulerLogReplica]
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Reverse off-diagonal coordinate retains the same real quadratic character. -/
theorem eulerWickReplicaDensity_apply_one_zero
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x 1 0 = eulerWickQuadraticEulerLogReplica x := by
  simp only [eulerWickReplicaDensity, eulerWickReplicaVector,
    finiteBuresTargetRay, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply, star_one,
    Complex.real_smul, eulerWickQuadraticEulerLogReplica, mul_one]
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Second diagonal coordinate is the same canonical Euler-log coefficient. -/
theorem eulerWickReplicaDensity_apply_one_one
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x 1 1 = eulerLogValuationProfile x.2 := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    simp [eulerWickReplicaDensity, eulerWickReplicaVector,
      finiteBuresTargetRay, Matrix.vecMulVec, eulerLogValuationProfile, h]

/-- Arithmetic source in one matrix channel of the EWQ pure density. -/
def eulerWickReplicaDensitySource (i j : Fin 2) : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile (fun x => eulerWickReplicaDensity x i j)

/-- The unsquared off-diagonal channel retains the joint quadratic character at every depth. -/
def eulerWickQuadraticEulerLogCharacterSource : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile eulerWickQuadraticEulerLogReplica

/-- Either diagonal channel is the complete Euler-log source that lands on completed Xi. -/
theorem eulerWickReplicaDensitySource_zero_zero_eq_diagonalSource :
    eulerWickReplicaDensitySource 0 0 =
      eulerWickQuadraticReplicaDiagonalSource := by
  rw [eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogProfile]
  change arithmeticFunctionOfPrimePowerProfile
      (fun x => eulerWickReplicaDensity x 0 0) =
    arithmeticFunctionOfPrimePowerProfile (fun x => eulerLogValuationProfile x.2)
  congr 1
  funext x
  exact eulerWickReplicaDensity_apply_zero_zero x

/-- Off-diagonal observation recovers the character-valued Euler-log replica without loss. -/
theorem eulerWickReplicaDensitySource_zero_one_eq_characterSource :
    eulerWickReplicaDensitySource 0 1 =
      eulerWickQuadraticEulerLogCharacterSource := by
  unfold eulerWickReplicaDensitySource eulerWickQuadraticEulerLogCharacterSource
  congr 1
  funext x
  exact eulerWickReplicaDensity_apply_zero_one x

/-- The diagonal of the orientation-preserving matrix lift still lands coefficientwise on zeta. -/
theorem eulerWickReplicaDensitySource_zero_zero_eq_eulerLogDirichletCoeff :
    (eulerWickReplicaDensitySource 0 0 : ℕ → ℂ) =
      _root_.RHTower.eulerLogDirichletCoeff := by
  rw [eulerWickReplicaDensitySource_zero_zero_eq_diagonalSource]
  exact eulerWickQuadraticReplicaDiagonalSource_eq_eulerLogDirichletCoeff

end

end GaloisForLFunctions.RHTower
