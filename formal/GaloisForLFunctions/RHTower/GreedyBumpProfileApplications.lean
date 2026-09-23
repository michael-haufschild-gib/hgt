import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFisherTangent
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift
import GaloisForLFunctions.RHTower.SquarefreeEulerModularCoronaCurvatureColligation

/-!
# Greedy-bump local-profile applications

Concrete applications of the exact local geometry in arXiv:2609.03581 to
centered arithmetic tangents already present in the corpus.  All analytic
admissibility conditions are discharged at the fixed point `sigma = 2`.
-/

open Complex MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Fixed positive signal used by the closed corpus applications. -/
def greedyBumpSignalTwo : PositiveSignal := ⟨2, by norm_num⟩

/-- Euler centered tangent is a valid profile direction and has exact gain. -/
theorem greedyBump_eulerCenteredTangent_profile_bridge :
    (inner ℂ (eulerPointedState (by norm_num : (1 : ℝ) < 2))
      (eulerCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)) : ℂ) = 0 ∧
    greedyBumpProfile greedyBumpSignalTwo
      (eulerCenteredTangent 1 (by norm_num : (1 : ℝ) < 2))
      (greedyBumpDisplacement greedyBumpSignalTwo
        (eulerCenteredTangent 1 (by norm_num : (1 : ℝ) < 2))) =
      ‖eulerCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)‖ ^ (2 : ℕ) / 4 := by
  constructor
  · exact inner_eulerPointedState_eulerCenteredTangent 1 (by norm_num)
  · rw [greedyBumpProfile_at_displacement]
    norm_num [greedyBumpSignalTwo]

/-- Squarefree centered tangent is a second valid arithmetic profile direction. -/
theorem greedyBump_squarefreeCenteredTangent_profile_bridge :
    (inner ℂ (squarefreePointedState (by norm_num : (1 : ℝ) < 2))
      (squarefreeCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)) : ℂ) = 0 ∧
    greedyBumpProfile greedyBumpSignalTwo
      (squarefreeCenteredTangent 1 (by norm_num : (1 : ℝ) < 2))
      (greedyBumpDisplacement greedyBumpSignalTwo
        (squarefreeCenteredTangent 1 (by norm_num : (1 : ℝ) < 2))) =
      ‖squarefreeCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)‖ ^ (2 : ℕ) / 4 := by
  constructor
  · exact inner_squarefreePointedState_squarefreeCenteredTangent 1 (by norm_num)
  · rw [greedyBumpProfile_at_displacement]
    norm_num [greedyBumpSignalTwo]

/-- Critical Mobius tangent supplies a third exact profile direction. -/
theorem greedyBump_mobiusCriticalTangent_profile_bridge :
    inner ℂ
      (infiniteMobiusSignedWeightLp 2 (by norm_num : (1 : ℝ) < 2))
      (infiniteMobiusCriticalFisherTangentLp 2 (by norm_num : (1 : ℝ) < 2)) = 0 ∧
    greedyBumpProfile greedyBumpSignalTwo
      (infiniteMobiusCriticalFisherTangentLp 2 (by norm_num : (1 : ℝ) < 2))
      (greedyBumpDisplacement greedyBumpSignalTwo
        (infiniteMobiusCriticalFisherTangentLp 2 (by norm_num : (1 : ℝ) < 2))) =
      ‖infiniteMobiusCriticalFisherTangentLp 2
        (by norm_num : (1 : ℝ) < 2)‖ ^ (2 : ℕ) / 4 := by
  constructor
  · exact inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero (by norm_num)
  · rw [greedyBumpProfile_at_displacement]
    norm_num [greedyBumpSignalTwo]

/-- Euler state/tangent packaged for the matched-filter residual bridge. -/
def greedyBumpEulerTemplateTangent : OrthogonalComplexTemplateTangent EulerPositiveL2 where
  template := eulerPointedState (by norm_num : (1 : ℝ) < 2)
  tangent := eulerCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)
  orthogonal := inner_eulerPointedState_eulerCenteredTangent 1 (by norm_num)

/-- Euler score derivative is unchanged after subtracting any matched amplitude. -/
theorem greedyBump_euler_matchedFilter_derivative_bridge
    (Q : ℝ) (data : EulerPositiveL2) :
    @inner ℂ EulerPositiveL2 _ data greedyBumpEulerTemplateTangent.tangent =
      @inner ℂ EulerPositiveL2 _
        (greedyBumpComplexResidual Q data greedyBumpEulerTemplateTangent.template)
        greedyBumpEulerTemplateTangent.tangent :=
  greedyBump_complexMatchedFilter_derivative_bridge greedyBumpEulerTemplateTangent Q data

/-- Squarefree state/tangent packaged for the residual bridge. -/
def greedyBumpSquarefreeTemplateTangent :
    OrthogonalComplexTemplateTangent (lp (fun _ : SquarefreePNat => ℂ) 2) where
  template := squarefreePointedState (by norm_num : (1 : ℝ) < 2)
  tangent := squarefreeCenteredTangent 1 (by norm_num : (1 : ℝ) < 2)
  orthogonal := inner_squarefreePointedState_squarefreeCenteredTangent 1 (by norm_num)

/-- Squarefree score derivative also couples only to residual data. -/
theorem greedyBump_squarefree_matchedFilter_derivative_bridge
    (Q : ℝ) (data : lp (fun _ : SquarefreePNat => ℂ) 2) :
    @inner ℂ _ _ data greedyBumpSquarefreeTemplateTangent.tangent =
      @inner ℂ _ _
        (greedyBumpComplexResidual Q data greedyBumpSquarefreeTemplateTangent.template)
        greedyBumpSquarefreeTemplateTangent.tangent :=
  greedyBump_complexMatchedFilter_derivative_bridge greedyBumpSquarefreeTemplateTangent Q data

/-- Mobius state/tangent packaged for the residual bridge. -/
def greedyBumpMobiusTemplateTangent :
    OrthogonalComplexTemplateTangent (lp (fun _ : ℕ => ℂ) 2) where
  template := infiniteMobiusSignedWeightLp 2 (by norm_num : (1 : ℝ) < 2)
  tangent := infiniteMobiusCriticalFisherTangentLp 2 (by norm_num : (1 : ℝ) < 2)
  orthogonal := inner_infiniteMobiusSignedWeightLp_fisherTangent_eq_zero (by norm_num)

/-- Mobius score derivative also couples only to residual data. -/
theorem greedyBump_mobius_matchedFilter_derivative_bridge
    (Q : ℝ) (data : lp (fun _ : ℕ => ℂ) 2) :
    @inner ℂ _ _ data greedyBumpMobiusTemplateTangent.tangent =
      @inner ℂ _ _
        (greedyBumpComplexResidual Q data greedyBumpMobiusTemplateTangent.template)
        greedyBumpMobiusTemplateTangent.tangent :=
  greedyBump_complexMatchedFilter_derivative_bridge greedyBumpMobiusTemplateTangent Q data

/-- Canonical prime used in the closed finite-squarefree application. -/
def greedyBumpPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Orthogonal prime insertion makes optimized profile gains exactly additive. -/
theorem greedyBump_finiteSquarefree_insert_profile_gain_adds :
    greedyBumpProfile greedyBumpSignalTwo
      (finiteSquarefreeTangent (insert greedyBumpPrimeTwo ∅) 2)
      (greedyBumpDisplacement greedyBumpSignalTwo
        (finiteSquarefreeTangent (insert greedyBumpPrimeTwo ∅) 2)) =
      greedyBumpProfile greedyBumpSignalTwo
        (finiteSquarefreeTangent ∅ 2)
        (greedyBumpDisplacement greedyBumpSignalTwo
          (finiteSquarefreeTangent ∅ 2)) +
      greedyBumpProfile greedyBumpSignalTwo
        (squarefreePrimeTangent 2 greedyBumpPrimeTwo)
        (greedyBumpDisplacement greedyBumpSignalTwo
          (squarefreePrimeTangent 2 greedyBumpPrimeTwo)) := by
  simp_rw [greedyBumpProfile_at_displacement]
  rw [norm_finiteSquarefreeTangent_insert_sq
    (S := ∅) (p := greedyBumpPrimeTwo) (by simp) 2]
  simp [greedyBumpSignalTwo]
  ring

/-- The same insertion exhibits the paper's required tangent orthogonality. -/
theorem greedyBump_finiteSquarefree_insert_branches_orthogonal :
    inner ℂ
      (finiteSquarefreeLowerTangentBranch
        (S := ∅) (p := greedyBumpPrimeTwo) (by simp) 2)
      (finiteSquarefreePrimeTangentBranch
        (S := ∅) (p := greedyBumpPrimeTwo) (by simp) 2) = 0 := by
  exact inner_finiteSquarefreeTangentBranches_eq_zero
    (S := ∅) (p := greedyBumpPrimeTwo) (by simp) 2

end RHTower

end
