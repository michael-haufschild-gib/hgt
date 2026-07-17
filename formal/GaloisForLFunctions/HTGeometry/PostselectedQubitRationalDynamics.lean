import GaloisForLFunctions.HTGeometry.AsymmetricBinaryTreeRG
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# Exact rational dynamics of two postselected-qubit protocols

Two identical pure qubits, an XOR/entangling gate, a successful projective measurement, and a
one-qubit rotation induce exact rational maps on the projective amplitude coordinate.  This module
formalizes the unconditional algebra of two such maps:

* the balanced XOR--rotation map `(z^2+1)/(1-z^2)`;
* the experimentally realized orthogonalizer `2z/(1+z^2)`.

The first map's projective critical orbit data differ from the second map's exact projective
conjugacy to squaring.  An explicit pair of successive pure-state projector numerators also proves
that the balanced protocol is not confined to a commuting state orbit.

Physical realizability, complex hyperbolicity, and the external Ritt--Becker--Bergweiler
hypertranscendence classification are not encoded as assumptions.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- XOR plus successful zero-outcome postselection squares the projective amplitudes. -/
def xorPostselectedQubitAmplitude (z : ℚ) : ℚ × ℚ :=
  (z ^ 2, 1)

/-- Balanced one-qubit rotation, with the common square-root normalization removed. -/
def balancedQubitRotationAmplitude (q : ℚ × ℚ) : ℚ × ℚ :=
  (q.1 + q.2, q.2 - q.1)

/-- Homogeneous projective lift of the balanced conditional-qubit rational map. -/
def postselectedQubitProjectiveMap (q : ℚ × ℚ) : ℚ × ℚ :=
  (q.1 ^ 2 + q.2 ^ 2, q.2 ^ 2 - q.1 ^ 2)

/-- The physical XOR/postselection step followed by balanced rotation is the projective map. -/
theorem balancedRotation_after_xorPostselection (z : ℚ) :
    balancedQubitRotationAmplitude (xorPostselectedQubitAmplitude z) =
      postselectedQubitProjectiveMap (z, 1) := by
  simp [balancedQubitRotationAmplitude, xorPostselectedQubitAmplitude,
    postselectedQubitProjectiveMap]

/-- Primitive numerator of the balanced conditional-qubit map. -/
def postselectedQubitNumerator : ℚ[X] :=
  X ^ 2 + 1

/-- Primitive denominator of the balanced conditional-qubit map. -/
def postselectedQubitDenominator : ℚ[X] :=
  1 - X ^ 2

/-- Exact rational map on the affine amplitude chart. -/
def postselectedQubitRationalMap : RatFunc ℚ :=
  ((RatFunc.X : RatFunc ℚ) ^ 2 + 1) / (1 - (RatFunc.X : RatFunc ℚ) ^ 2)

/-- Exact affine formula away from the projective pole. -/
def postselectedQubitAffineStep (z : ℚ) : ℚ :=
  (z ^ 2 + 1) / (1 - z ^ 2)

/-- The balanced map's primitive projective pair has no common complex zero. -/
theorem postselectedQubit_noCommonZero
    (z : ℂ) (hN : z ^ 2 + 1 = 0) (hD : 1 - z ^ 2 = 0) : False := by
  have htwo : (2 : ℂ) = 0 := by
    linear_combination hN + hD
  norm_num at htwo

/-- Exact finite derivative cross-numerator; hence zero is the only finite critical point. -/
theorem postselectedQubit_derivativeCrossNumerator :
    derivative postselectedQubitNumerator * postselectedQubitDenominator -
        postselectedQubitNumerator * derivative postselectedQubitDenominator =
      4 * X := by
  simp [postselectedQubitNumerator, postselectedQubitDenominator, derivative_pow,
    Polynomial.C_ofNat]
  ring

/-- Zero maps projectively to one. -/
@[simp] theorem postselectedQubitProjectiveMap_zero :
    postselectedQubitProjectiveMap (0, 1) = (1, 1) := by
  norm_num [postselectedQubitProjectiveMap]

/-- One maps projectively to infinity. -/
@[simp] theorem postselectedQubitProjectiveMap_one :
    postselectedQubitProjectiveMap (1, 1) = (2, 0) := by
  norm_num [postselectedQubitProjectiveMap]

/-- Infinity maps projectively to minus one. -/
@[simp] theorem postselectedQubitProjectiveMap_infinity :
    postselectedQubitProjectiveMap (1, 0) = (1, -1) := by
  norm_num [postselectedQubitProjectiveMap]

/-- Minus one returns projectively to infinity. -/
@[simp] theorem postselectedQubitProjectiveMap_minusOne :
    postselectedQubitProjectiveMap (-1, 1) = (2, 0) := by
  norm_num [postselectedQubitProjectiveMap]

/-- In the reciprocal coordinate at infinity, displacement from minus one has quadratic numerator. -/
theorem postselectedQubit_infinityLocalDisplacementNumerator (w : ℚ) :
    (1 + w ^ 2) + (w ^ 2 - 1) = 2 * w ^ 2 := by
  ring

/-- The quadratic local displacement at infinity has nonzero second derivative. -/
theorem postselectedQubit_infinityLocal_secondDerivative :
    (derivative (derivative ((2 : ℚ[X]) * X ^ 2))).eval 0 = 4 := by
  norm_num [derivative_pow]

/-- Homogeneous projective lift of the experimentally realized qubit orthogonalizer. -/
def experimentalQubitProjectiveMap (q : ℚ × ℚ) : ℚ × ℚ :=
  (2 * q.1 * q.2, q.1 ^ 2 + q.2 ^ 2)

/-- Exact experimentally realized affine rational map. -/
def experimentalQubitOrthogonalizer : RatFunc ℚ :=
  (2 * RatFunc.X) / (1 + (RatFunc.X : RatFunc ℚ) ^ 2)

/-- Projective Moebius coordinate used to expose the power-map conjugacy. -/
def qubitPowerProjectiveCoordinate (q : ℚ × ℚ) : ℚ × ℚ :=
  (q.1 + q.2, q.2 - q.1)

/-- Homogeneous lift of the squaring map. -/
def qubitProjectiveSquare (q : ℚ × ℚ) : ℚ × ℚ :=
  (q.1 ^ 2, q.2 ^ 2)

/-- The experimental orthogonalizer is exactly projectively conjugate to squaring. -/
theorem qubitPowerCoordinate_after_experimental (q : ℚ × ℚ) :
    qubitPowerProjectiveCoordinate (experimentalQubitProjectiveMap q) =
      qubitProjectiveSquare (qubitPowerProjectiveCoordinate q) := by
  ext <;>
    simp [qubitPowerProjectiveCoordinate, experimentalQubitProjectiveMap,
      qubitProjectiveSquare] <;>
    ring

/-- The positive orthogonal state is a projective fixed point of the experimental map. -/
@[simp] theorem experimentalQubitProjectiveMap_positiveFixed :
    experimentalQubitProjectiveMap (1, 1) = (2, 2) := by
  norm_num [experimentalQubitProjectiveMap]

/-- The negative orthogonal state is the other projective fixed point. -/
@[simp] theorem experimentalQubitProjectiveMap_negativeFixed :
    experimentalQubitProjectiveMap (-1, 1) = (-2, 2) := by
  norm_num [experimentalQubitProjectiveMap]

/-- Exact critical polynomial of the experimental map, exposing its two fixed critical points. -/
theorem experimentalQubit_derivativeCrossNumerator :
    derivative ((2 : ℚ[X]) * X) * (1 + X ^ 2) -
        ((2 : ℚ[X]) * X) * derivative (1 + X ^ 2) =
      2 * (1 - X ^ 2) := by
  simp [derivative_pow, Polynomial.C_ofNat]
  ring

/-- Unnormalized rank-one projector of the real pure ray `z|0>+|1>`. -/
def qubitRayProjectorNumerator (z : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![z ^ 2, z; z, 1]

/-- Exact commutator entry for two real pure-state projector numerators. -/
theorem qubitRayProjector_commutator_zero_one (z w : ℚ) :
    (qubitRayProjectorNumerator z * qubitRayProjectorNumerator w -
        qubitRayProjectorNumerator w * qubitRayProjectorNumerator z) 0 1 =
      (z - w) * (z * w + 1) := by
  simp [qubitRayProjectorNumerator]
  ring

/-- One exact balanced-protocol step sends the real ray `2` to `-5/3`. -/
theorem postselectedQubitAffineStep_two :
    postselectedQubitAffineStep 2 = -5 / 3 := by
  norm_num [postselectedQubitAffineStep]

/-- Successive projectors on the explicit orbit `2 -> -5/3` do not commute. -/
theorem postselectedQubit_adjacentProjectors_noncommuting :
    qubitRayProjectorNumerator 2 * qubitRayProjectorNumerator (-5 / 3) ≠
      qubitRayProjectorNumerator (-5 / 3) * qubitRayProjectorNumerator 2 := by
  intro h
  have hcomm :
      qubitRayProjectorNumerator 2 * qubitRayProjectorNumerator (-5 / 3) -
          qubitRayProjectorNumerator (-5 / 3) * qubitRayProjectorNumerator 2 = 0 :=
    sub_eq_zero.mpr h
  have hentry := congrFun (congrFun hcomm (0 : Fin 2)) (1 : Fin 2)
  rw [qubitRayProjector_commutator_zero_one] at hentry
  norm_num at hentry

end

end GaloisForLFunctions.HTGeometry
