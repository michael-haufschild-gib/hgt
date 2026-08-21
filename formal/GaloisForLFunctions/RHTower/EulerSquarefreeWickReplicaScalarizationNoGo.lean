import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaDensityOrientation

/-!
# Scalar Xi landing cannot recover the Euler--Wick orientation

The orientation-preserving EWQ density has a second, gauge-flipped pure lift.  The two lifts are
positive semidefinite, have identical diagonal Euler-log coefficients at every prime and depth,
and hence have the same coefficient-faithful zeta/Xi scalar landing.  Their off-diagonal Pauli
channels are opposite and nonzero.

Thus the scalar landing is intrinsically two-to-one.  No deterministic reader of its arithmetic
diagonal can recover the EWQ orientation for both gauge lifts.  The positive survivor is precise:
any viable EWQ completion must retain a noncommutative matrix channel through completion; no
post-processing of the scalar Xi carrier can reconstruct the lost sign.
-/

namespace GaloisForLFunctions.RHTower

open Complex
open ArithmeticFunction
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder MatrixOrder LSeries.notation

noncomputable section

/-- The opposite logical orientation in the same two-replica carrier. -/
def eulerWickReplicaFlippedVector (x : PrimePowerClockIndex) : Fin 2 → ℂ :=
  ![1, -eulerWickQuadraticDepthCharacter x]

/-- Euler-log-weighted pure density with the opposite EWQ orientation. -/
def eulerWickReplicaFlippedDensity
    (x : PrimePowerClockIndex) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((x.2 + 1 : ℕ) : ℝ))⁻¹ •
    finiteBuresTargetRay (eulerWickReplicaFlippedVector x)

/-- The gauge-flipped lift remains positive semidefinite. -/
theorem eulerWickReplicaFlippedDensity_posSemidef
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaFlippedDensity x).PosSemidef := by
  exact (finiteBuresTargetRay_posSemidef
    (eulerWickReplicaFlippedVector x)).smul (by positivity)

/-- Gauge flip is invisible in the first diagonal Euler-log channel. -/
theorem eulerWickReplicaFlippedDensity_apply_zero_zero
    (x : PrimePowerClockIndex) :
    eulerWickReplicaFlippedDensity x 0 0 = eulerLogValuationProfile x.2 := by
  simp [eulerWickReplicaFlippedDensity, eulerWickReplicaFlippedVector,
    finiteBuresTargetRay, Matrix.vecMulVec, eulerLogValuationProfile]

/-- Gauge flip reverses the forward character channel. -/
theorem eulerWickReplicaFlippedDensity_apply_zero_one
    (x : PrimePowerClockIndex) :
    eulerWickReplicaFlippedDensity x 0 1 =
      -eulerWickQuadraticEulerLogReplica x := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    simp [eulerWickReplicaFlippedDensity, eulerWickReplicaFlippedVector,
      finiteBuresTargetRay, Matrix.vecMulVec,
      eulerWickQuadraticEulerLogReplica, h] <;> ring

/-- Gauge flip reverses the reverse character channel. -/
theorem eulerWickReplicaFlippedDensity_apply_one_zero
    (x : PrimePowerClockIndex) :
    eulerWickReplicaFlippedDensity x 1 0 =
      -eulerWickQuadraticEulerLogReplica x := by
  simp only [eulerWickReplicaFlippedDensity, eulerWickReplicaFlippedVector,
    finiteBuresTargetRay, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.star_apply, star_one,
    Complex.real_smul, eulerWickQuadraticEulerLogReplica]
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Gauge flip is invisible in the second diagonal Euler-log channel. -/
theorem eulerWickReplicaFlippedDensity_apply_one_one
    (x : PrimePowerClockIndex) :
    eulerWickReplicaFlippedDensity x 1 1 = eulerLogValuationProfile x.2 := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    simp [eulerWickReplicaFlippedDensity, eulerWickReplicaFlippedVector,
      finiteBuresTargetRay, Matrix.vecMulVec, eulerLogValuationProfile, h]

/-- Every unsquared EWQ Euler-log character coefficient is nonzero. -/
theorem eulerWickQuadraticEulerLogReplica_ne_zero
    (x : PrimePowerClockIndex) :
    eulerWickQuadraticEulerLogReplica x ≠ 0 := by
  unfold eulerWickQuadraticEulerLogReplica
  apply div_ne_zero
  · intro hzero
    have hsquare := eulerWickQuadraticDepthCharacter_sq x
    rw [hzero, zero_pow (by omega)] at hsquare
    norm_num at hsquare
  · exact_mod_cast Nat.succ_ne_zero x.2

/-- The two positive lifts are genuinely different at every prime-depth coordinate. -/
theorem eulerWickReplicaDensity_ne_flippedDensity
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x ≠ eulerWickReplicaFlippedDensity x := by
  intro heq
  have hentry := congrFun (congrFun heq 0) 1
  rw [eulerWickReplicaDensity_apply_zero_one,
    eulerWickReplicaFlippedDensity_apply_zero_one] at hentry
  have htwo : (2 : ℂ) * eulerWickQuadraticEulerLogReplica x = 0 := by
    linear_combination hentry
  exact (eulerWickQuadraticEulerLogReplica_ne_zero x)
    ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

/-- **Positive survivor.**  Keeping both opposite gauge lifts produces a strictly positive scalar
matrix, not a cancellation: the logical sign disappears but its two-dimensional carrier becomes
full rank. -/
theorem eulerWickReplicaDensity_add_flippedDensity_eq_smul_one
    (x : PrimePowerClockIndex) :
    eulerWickReplicaDensity x + eulerWickReplicaFlippedDensity x =
      (2 * (((x.2 + 1 : ℕ) : ℝ))⁻¹) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [eulerWickReplicaDensity, eulerWickReplicaVector,
        eulerWickReplicaFlippedDensity, eulerWickReplicaFlippedVector,
        finiteBuresTargetRay, Matrix.vecMulVec, h] <;> ring

/-- Gauge-orbit completion converts the pair of rank-one states into a positive-definite
two-channel carrier at every prime depth. -/
theorem eulerWickReplicaDensity_add_flippedDensity_posDef
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaDensity x + eulerWickReplicaFlippedDensity x).PosDef := by
  rw [eulerWickReplicaDensity_add_flippedDensity_eq_smul_one]
  exact Matrix.PosDef.one.smul (by positivity)

/-- Exact nonzero determinant of the gauge-completed local carrier. -/
theorem det_eulerWickReplicaDensity_add_flippedDensity
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaDensity x + eulerWickReplicaFlippedDensity x).det =
      (((2 * (((x.2 + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) ^ 2) := by
  rw [eulerWickReplicaDensity_add_flippedDensity_eq_smul_one,
    Matrix.det_fin_two]
  simp
  ring

/-- Arithmetic matrix source of the gauge-flipped lift. -/
def eulerWickReplicaFlippedDensitySource (i j : Fin 2) : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile
    (fun x => eulerWickReplicaFlippedDensity x i j)

/-- The two gauge lifts have literally the same scalar diagonal source. -/
theorem eulerWickReplicaFlippedDensitySource_zero_zero_eq_densitySource :
    eulerWickReplicaFlippedDensitySource 0 0 =
      eulerWickReplicaDensitySource 0 0 := by
  unfold eulerWickReplicaFlippedDensitySource eulerWickReplicaDensitySource
  exact congrArg arithmeticFunctionOfPrimePowerProfile (funext fun x => by
    rw [eulerWickReplicaFlippedDensity_apply_zero_zero,
      eulerWickReplicaDensity_apply_zero_zero])

/-- The flipped off-diagonal source is exactly the negative character carrier. -/
theorem eulerWickReplicaFlippedDensitySource_zero_one_eq_neg_characterSource :
    eulerWickReplicaFlippedDensitySource 0 1 =
      -eulerWickQuadraticEulerLogCharacterSource := by
  unfold eulerWickReplicaFlippedDensitySource
    eulerWickQuadraticEulerLogCharacterSource
  calc
    arithmeticFunctionOfPrimePowerProfile
          (fun x => eulerWickReplicaFlippedDensity x 0 1) =
        arithmeticFunctionOfPrimePowerProfile
          (-eulerWickQuadraticEulerLogReplica) := by
            congr 1
            funext x
            exact eulerWickReplicaFlippedDensity_apply_zero_one x
    _ = -arithmeticFunctionOfPrimePowerProfile
          eulerWickQuadraticEulerLogReplica :=
      map_neg arithmeticFunctionOfPrimePowerProfile _

/-- The gauge-flipped diagonal has the same coefficient-faithful Euler-log stream. -/
theorem eulerWickReplicaFlippedDensitySource_zero_zero_eq_eulerLogDirichletCoeff :
    (eulerWickReplicaFlippedDensitySource 0 0 : ℕ → ℂ) =
      _root_.RHTower.eulerLogDirichletCoeff := by
  rw [eulerWickReplicaFlippedDensitySource_zero_zero_eq_densitySource]
  exact eulerWickReplicaDensitySource_zero_zero_eq_eulerLogDirichletCoeff

/-- Consequently the flipped lift has exactly the same zeta landing on the Euler half-plane. -/
theorem exp_LSeries_eulerWickReplicaFlippedDiagonal_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (eulerWickReplicaFlippedDensitySource 0 0) s) =
      riemannZeta s := by
  rw [eulerWickReplicaFlippedDensitySource_zero_zero_eq_densitySource,
    eulerWickReplicaDensitySource_zero_zero_eq_diagonalSource]
  exact exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs

/-- The archimedean completion of the flipped scalar channel is again actual Xi. -/
theorem archFactor_mul_exp_LSeries_eulerWickReplicaFlippedDiagonal_eq_xi
    {s : ℂ} (hs : 1 < s.re) :
    _root_.RHTower.archFactor s *
        Complex.exp (LSeries (eulerWickReplicaFlippedDensitySource 0 0) s) =
      _root_.RHTower.xi s := by
  rw [exp_LSeries_eulerWickReplicaFlippedDiagonal_eq_riemannZeta hs]
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  exact (_root_.RHTower.xi_eq_archFactor_mul_zeta h0 h1 hG).symm

/-- **Scalarization no-go.**  No deterministic function of the diagonal arithmetic source can
recover the off-diagonal orientation on both positive gauge lifts. -/
theorem no_eulerWickDiagonalOrientationRecovery
    (x : PrimePowerClockIndex) :
    ¬ ∃ recover : ArithmeticFunction ℂ → PrimePowerClockIndex → ℂ,
        recover (eulerWickReplicaDensitySource 0 0) x =
            eulerWickReplicaDensity x 0 1 ∧
          recover (eulerWickReplicaFlippedDensitySource 0 0) x =
            eulerWickReplicaFlippedDensity x 0 1 := by
  rintro ⟨recover, hforward, hflipped⟩
  rw [eulerWickReplicaFlippedDensitySource_zero_zero_eq_densitySource] at hflipped
  have hopposite : eulerWickReplicaDensity x 0 1 =
      eulerWickReplicaFlippedDensity x 0 1 := hforward.symm.trans hflipped
  rw [eulerWickReplicaDensity_apply_zero_one,
    eulerWickReplicaFlippedDensity_apply_zero_one] at hopposite
  have htwo : (2 : ℂ) * eulerWickQuadraticEulerLogReplica x = 0 := by
    linear_combination hopposite
  exact (eulerWickQuadraticEulerLogReplica_ne_zero x)
    ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

end

end GaloisForLFunctions.RHTower
