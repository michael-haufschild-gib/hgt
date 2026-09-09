import GaloisForLFunctions.HTGeometry.ConservativeDissipativeQuantum
import GaloisForLFunctions.HTGeometry.StaticGaussianCrossingMemoryLaw

set_option autoImplicit false

/-!
# Conservative–dissipative gaussian laws

Applications of Schaffer–Exl, arXiv:2609.04530, to constructed operators
and the existing mathematical objects used below.
-/

open scoped Matrix
open Matrix QuantumAlg
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq N]

/-- Total response of a Hermitian matrix pencil to its own dephasing channels. -/
def gaussianPencilPower (A : K → Matrix N N ℂ) : ℝ :=
  ∑ i, ∑ j, (hsInner (hermitianPart (A j))
    (quantumField 0 (A i) (hermitianPart (A j)))).re

/-- Static commutator energy is exactly the opposite of total dephasing power. -/
theorem gaussianPencilPower_eq_neg_commutatorEnergy (A : K → Matrix N N ℂ) :
    gaussianPencilPower A = - (matrixFamilyCommutatorEnergy (fun i => hermitianPart (A i))).re := by
  simp only [gaussianPencilPower, quantumField_power, matrixFamilyCommutatorEnergy,
    Complex.re_sum, Finset.sum_neg_distrib]
  rfl

theorem gaussianPencilPower_nonpos (A : K → Matrix N N ℂ) : gaussianPencilPower A ≤ 0 :=
  Finset.sum_nonpos (fun _ _ => Finset.sum_nonpos (fun _ _ => quantumField_power_nonpos _ _ _))

/-- The classical/free fourth-order crossing deficit has an exact dissipative realization. -/
theorem crossingMemory_eq_squareEnergy_add_half_power (A : K → Matrix N N ℂ) :
    (matrixFamilyCrossingMemory (fun i => hermitianPart (A i))).re =
      (matrixFamilySquareFourthEnergy (fun i => hermitianPart (A i))).re +
        (1 / 2 : ℝ) * gaussianPencilPower A := by
  classical
  rw [matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy _
    (fun i => hermitianPart_star (A i)), gaussianPencilPower_eq_neg_commutatorEnergy]
  simp only [Complex.sub_re, Complex.mul_re]
  norm_num
  ring

/-- Dephasing gives the sign of the Wick crossing correction with no commutativity premise. -/
theorem crossingMemory_re_le_squareEnergy (A : K → Matrix N N ℂ) :
    (matrixFamilyCrossingMemory (fun i => hermitianPart (A i))).re ≤
      (matrixFamilySquareFourthEnergy (fun i => hermitianPart (A i))).re := by
  rw [crossingMemory_eq_squareEnergy_add_half_power]
  linarith [gaussianPencilPower_nonpos A]

/-- Vanishing aggregate dephasing is equivalent to pairwise commutativity of the whole pencil. -/
theorem gaussianPencilPower_eq_zero_iff (A : K → Matrix N N ℂ) :
    gaussianPencilPower A = 0 ↔ ∀ i j, ringCommutator (hermitianPart (A i))
      (hermitianPart (A j)) = 0 := by
  unfold gaussianPencilPower
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun i _ =>
    Finset.sum_nonpos (fun j _ => quantumField_power_nonpos _ _ _))]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro i
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun j _ => quantumField_power_nonpos _ _ _)]
  simp only [Finset.mem_univ, forall_true_left, quantumField_lossless_iff]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
