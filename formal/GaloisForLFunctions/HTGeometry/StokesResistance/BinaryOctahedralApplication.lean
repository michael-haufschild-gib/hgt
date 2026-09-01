import GaloisForLFunctions.HTGeometry.StokesResistance.FiniteGroupCharacter
import GaloisForLFunctions.HTGeometry.StokesResistance.SymmetricTensorCharacter
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign

/-!
# Binary-octahedral application of Stokes symmetry counting

The strict single-qubit Clifford group in the corpus is the `48`-element binary-octahedral group.
This module applies the finite-group and symmetric-tensor machinery extracted from Moreau,
*The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*,
arXiv:2608.23907v1.

The existing qubit swap is exactly the general factor swap. The fundamental two-dimensional
Clifford carrier has no nonzero invariant vector because the central lift `-1` acts as `-I`;
therefore its Reynolds average and averaged character vanish, and its stacked symmetry-defect map
is injective. At quadratic order, the symmetric-tensor projector has trace three. This is a concrete
octahedral instance of the paper's principle that higher response levels reveal symmetry sectors
invisible to vector probes.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open QuantumAlg.QubitTwoDesign

/-- The qubit-design swap is the dimension-two instance of the general tensor swap. -/
theorem qubitSwap_eq_tensorSwap :
    qubitSwap = tensorSwap (ι := Fin 2) := rfl

/-- Existing qubit-swap trace is recovered without finite enumeration. -/
theorem qubitSwap_trace_from_symmetricTensor :
    Matrix.trace qubitSwap = 2 := by
  rw [qubitSwap_eq_tensorSwap, trace_tensorSwap]
  norm_num

/-- The symmetric square of the two-dimensional qubit carrier has dimension three. -/
theorem qubit_symmetricTensorProjection_trace :
    Matrix.trace (symmetricTensorProjection (ι := Fin 2)) = 3 := by
  rw [trace_symmetricTensorProjection]
  norm_num

/-- Existing qubit-swap commutation is a direct instance of factor-swap naturality. -/
theorem kronecker_self_commute_qubitSwap_from_tensorSwap
    (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (U ⊗ₖ U) * qubitSwap = qubitSwap * (U ⊗ₖ U) := by
  rw [qubitSwap_eq_tensorSwap]
  exact (tensorSwap_commutes_kronecker_self U).symm

/-- Identity element of the exact binary-octahedral matrix lift. -/
theorem qubitClifford_one : qubitClifford 1 = 1 := by
  rw [qubitClifford, binaryOctahedralQuaternion_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realQuaternion, quaternionMatrix, sqrtTwoEval_apply,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The nontrivial central lift acts as negative identity on the qubit carrier. -/
theorem qubitClifford_negOne :
    qubitClifford binaryOctahedralNegOne = -1 := by
  rw [qubitClifford, binaryOctahedralQuaternion_negOne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realQuaternion, quaternionMatrix, sqrtTwoEval_apply,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one,
      Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Exact binary-octahedral representation on the two-dimensional complex qubit carrier. -/
def qubitCliffordRepresentation :
    Representation ℂ BinaryOctahedral (Fin 2 → ℂ) where
  toFun g := (qubitClifford g).toLin'
  map_one' := by
    ext v
    simp [qubitClifford_one]
  map_mul' a b := by
    ext v
    simp [qubitClifford_mul, Module.End.mul_apply]

/-- Fundamental binary-octahedral Clifford carrier has no nonzero fixed vector. -/
theorem qubitCliffordRepresentation_invariants_eq_bot :
    qubitCliffordRepresentation.invariants = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hneg := hv binaryOctahedralNegOne
  change (qubitClifford binaryOctahedralNegOne).mulVec v = v at hneg
  rw [qubitClifford_negOne] at hneg
  ext i
  have hi := congrFun hneg i
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply] at hi
  change v i = 0
  linear_combination (-1 / 2 : ℂ) * hi

/-- Moreau's character average vanishes on the fundamental binary-octahedral carrier. -/
theorem qubitClifford_character_average_eq_zero :
    (Fintype.card BinaryOctahedral : ℂ)⁻¹ *
      ∑ g : BinaryOctahedral,
        LinearMap.trace ℂ (Fin 2 → ℂ) (qubitCliffordRepresentation g) = 0 := by
  rw [← finrank_invariants_eq_character_average qubitCliffordRepresentation,
    qubitCliffordRepresentation_invariants_eq_bot]
  simp

/-- Reynolds averaging annihilates every vector in the fundamental binary-octahedral carrier. -/
theorem finiteGroupAverage_qubitCliffordRepresentation_eq_zero :
    finiteGroupAverage qubitCliffordRepresentation = 0 := by
  apply LinearMap.ext
  intro v
  have hv := finiteGroupAverage_mem_invariants qubitCliffordRepresentation v
  rw [qubitCliffordRepresentation_invariants_eq_bot, Submodule.mem_bot] at hv
  simpa using hv

/-- Moreau's stacked invariance equations have full column rank on the fundamental carrier. -/
theorem ker_qubitClifford_invarianceDefect_eq_bot :
    LinearMap.ker (invarianceDefect qubitCliffordRepresentation) = ⊥ := by
  rw [ker_invarianceDefect, qubitCliffordRepresentation_invariants_eq_bot]

/-- Moreau's symmetric-square character formula specialized to every exact Clifford element. -/
theorem qubitClifford_symmetricTensor_character (g : BinaryOctahedral) :
    Matrix.trace
        (symmetricTensorProjection * (qubitClifford g ⊗ₖ qubitClifford g)) =
      (Matrix.trace (qubitClifford g) ^ 2 +
        Matrix.trace (qubitClifford g * qubitClifford g)) / 2 :=
  trace_symmetricTensorProjection_mul_kronecker_self (qubitClifford g)

end GaloisForLFunctions.HTGeometry.StokesResistance
