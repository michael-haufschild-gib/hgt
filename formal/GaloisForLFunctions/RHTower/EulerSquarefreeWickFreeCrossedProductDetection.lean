import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaKreinExtension
import GaloisForLFunctions.RHTower.RealCoronaFreeCrossedProductMatrix

/-!
# Free crossed-product recipient for the EWQ replica

The free two-point reflection crossed product is the full two-by-two matrix algebra.  Reindexing the
EWQ replica density by its two reflection parities therefore gives a literal crossed-product
element, not an auxiliary regular-orbit tensor factor.  Its commutator with the free-orbit grading
kills both diagonal Euler-log marginals and reads the two oriented off-diagonal entries as
`-2 chi(p)^k/k` and `2 chi(p)^k/k`.

This closes a source-side part of the EWQ-V open core: there is a free, dimension-preserving,
proper-marginal-detecting recipient, and its detector is nonzero at every prime depth.  It does not
by itself continue that free action to the original completed Xi divisor module.  Combining it
with the completed Weyl-kernel obstruction shows why that continuation cannot be the ordinary
semisimple character shift: it must preserve the crossed-product off-diagonal extension while
controlling the auxiliary completed L-divisors.
-/

open Complex Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Identify the two reflection parities with the two replica coordinates. -/
def reflectionParityToFinTwo : ReflectionParity → Fin 2
  | .even => 0
  | .odd => 1

/-- EWQ replica density on the free reflection orbit. -/
def eulerWickReplicaFreeOrbitMatrix
    (x : PrimePowerClockIndex) : Matrix ReflectionParity ReflectionParity ℂ :=
  fun p q => eulerWickReplicaDensity x (reflectionParityToFinTwo p) (reflectionParityToFinTwo q)

/-- Literal preimage of the EWQ density in the free reflection crossed product. -/
def eulerWickReplicaFreeCrossedElement
    (x : PrimePowerClockIndex) :
    SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity :=
  letI := freeCoordinateFunctionAction
  freeReflectionMatrixRingEquiv.symm (eulerWickReplicaFreeOrbitMatrix x)

/-- The regular crossed-product representation recovers the EWQ density exactly. -/
theorem freeReflectionMatrixRingEquiv_eulerWickReplicaFreeCrossedElement
    (x : PrimePowerClockIndex) :
    letI := freeCoordinateFunctionAction
    freeReflectionMatrixRingEquiv (eulerWickReplicaFreeCrossedElement x) =
      eulerWickReplicaFreeOrbitMatrix x := by
  letI := freeCoordinateFunctionAction
  exact freeReflectionMatrixRingEquiv.apply_symm_apply _

/-- The even-to-odd grading commutator reads the forward EWQ character with exact factor `-2`. -/
theorem eulerWickReplicaFreeOrbit_orientationCommutator_even_odd
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaFreeOrbitMatrix x * freeOrbitOrientationMatrix -
        freeOrbitOrientationMatrix * eulerWickReplicaFreeOrbitMatrix x)
        ReflectionParity.even ReflectionParity.odd =
      -2 * eulerWickQuadraticEulerLogReplica x := by
  rw [freeOrbitOrientationMatrix_commutator_entry]
  change ((-1 : ℂ) - 1) * eulerWickReplicaDensity x 0 1 = _
  rw [eulerWickReplicaDensity_apply_zero_one]
  ring

/-- The odd-to-even grading commutator reads the reverse EWQ character with exact factor `2`. -/
theorem eulerWickReplicaFreeOrbit_orientationCommutator_odd_even
    (x : PrimePowerClockIndex) :
    (eulerWickReplicaFreeOrbitMatrix x * freeOrbitOrientationMatrix -
        freeOrbitOrientationMatrix * eulerWickReplicaFreeOrbitMatrix x)
        ReflectionParity.odd ReflectionParity.even =
      2 * eulerWickQuadraticEulerLogReplica x := by
  rw [freeOrbitOrientationMatrix_commutator_entry]
  change ((1 : ℂ) - (-1)) * eulerWickReplicaDensity x 1 0 = _
  rw [eulerWickReplicaDensity_apply_one_zero]
  ring

/-- The unsquared Euler-log interaction coefficient never vanishes at a prime depth. -/
theorem eulerWickQuadraticEulerLogReplica_ne_zero (x : PrimePowerClockIndex) :
    eulerWickQuadraticEulerLogReplica x ≠ 0 := by
  have hdepth : (((x.2 + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero x.2)
  have hchar : eulerWickQuadraticDepthCharacter x ≠ 0 := by
    intro h
    have hsquare := eulerWickQuadraticDepthCharacter_sq x
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsquare
    norm_num at hsquare
  exact div_ne_zero hchar hdepth

/-- The free crossed-product grading detects every literal EWQ prime-depth interaction. -/
theorem eulerWickReplicaFreeOrbit_orientationCommutator_ne_zero
    (x : PrimePowerClockIndex) :
    eulerWickReplicaFreeOrbitMatrix x * freeOrbitOrientationMatrix -
        freeOrbitOrientationMatrix * eulerWickReplicaFreeOrbitMatrix x ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ReflectionParity.even) ReflectionParity.odd
  rw [eulerWickReplicaFreeOrbit_orientationCommutator_even_odd] at hentry
  change -2 * eulerWickQuadraticEulerLogReplica x = 0 at hentry
  exact eulerWickQuadraticEulerLogReplica_ne_zero x
    (mul_eq_zero.mp hentry |>.resolve_left (by norm_num))

end

end GaloisForLFunctions.RHTower
