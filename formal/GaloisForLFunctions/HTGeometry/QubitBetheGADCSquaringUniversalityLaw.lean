import GaloisForLFunctions.HTGeometry.GADCTreePopulationRG
import GaloisForLFunctions.HTGeometry.PostselectedQubitRationalDynamics

/-!
# Qubit--Bethe--GADC squaring universality

The experimentally realized postselected-qubit orthogonalizer and the noiseless two-branch
generalized-amplitude-damping population recursion are the same rational map.  The former is
presented as `2X / (1 + X²)` and the latter as a Bethe-lattice sum/difference quotient; expanding
the depth-two quotient identifies them exactly.  The homogeneous qubit lift is simultaneously
conjugate to coordinatewise squaring.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The experimental qubit orthogonalizer is exactly the depth-two noiseless Bethe RG map. -/
theorem experimentalQubitOrthogonalizer_eq_betheHolographicIsingRG :
    experimentalQubitOrthogonalizer = betheHolographicIsingRG 2 1 := by
  unfold experimentalQubitOrthogonalizer betheHolographicIsingRG
  ring_nf
  field_simp
  norm_num

/-- Every zero-damping two-branch GADC population recursion is the experimental qubit
orthogonalizer, independently of bath population. -/
theorem gadcTreePopulationRG_two_zero_eq_experimentalQubitOrthogonalizer
    (N : ℚ) :
    gadcTreePopulationRG 2 0 N = experimentalQubitOrthogonalizer := by
  rw [gadcTreePopulationRG_zeroDamping,
    experimentalQubitOrthogonalizer_eq_betheHolographicIsingRG]

/-- **Qubit--Bethe--GADC squaring universality law.**  One rational map has three exact
presentations: the experimental qubit orthogonalizer, every zero-damping depth-two GADC
population recursion, and the depth-two unit-transmissivity Bethe recursion.  Its homogeneous
qubit lift is conjugate to coordinatewise squaring, its two orthogonal rays are projective fixed
points, its critical cross-numerator is `2(1-X²)`, and its zero-message multiplier is exactly two
for every bath population. -/
theorem qubitBetheGADCSquaringUniversality :
    (∀ N : ℚ,
      gadcTreePopulationRG 2 0 N = experimentalQubitOrthogonalizer) ∧
      experimentalQubitOrthogonalizer = betheHolographicIsingRG 2 1 ∧
      (∀ q : ℚ × ℚ,
        qubitPowerProjectiveCoordinate (experimentalQubitProjectiveMap q) =
          qubitProjectiveSquare (qubitPowerProjectiveCoordinate q)) ∧
      experimentalQubitProjectiveMap (1, 1) = (2, 2) ∧
      experimentalQubitProjectiveMap (-1, 1) = (-2, 2) ∧
      derivative ((2 : ℚ[X]) * X) * (1 + X ^ 2) -
          ((2 : ℚ[X]) * X) * derivative (1 + X ^ 2) =
        2 * (1 - X ^ 2) ∧
      ∀ N : ℚ,
        (derivative
            (asymmetricBinaryTreeNumerator 2
              (gadcPositiveSignal 0 N) (gadcNegativeSignal 0 N))).eval 0 /
          (asymmetricBinaryTreeDenominator 2
            (gadcPositiveSignal 0 N) (gadcNegativeSignal 0 N)).eval 0 =
          2 := by
  refine ⟨gadcTreePopulationRG_two_zero_eq_experimentalQubitOrthogonalizer,
    experimentalQubitOrthogonalizer_eq_betheHolographicIsingRG,
    qubitPowerCoordinate_after_experimental,
    experimentalQubitProjectiveMap_positiveFixed,
    experimentalQubitProjectiveMap_negativeFixed,
    experimentalQubit_derivativeCrossNumerator, ?_⟩
  intro N
  simpa using gadcTreePopulation_linearMultiplier 2 0 N

end

end GaloisForLFunctions.HTGeometry
