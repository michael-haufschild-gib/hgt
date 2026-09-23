import GaloisForLFunctions.HTGeometry.TriangleFactOrientationTransmutation
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor

/-!
# No-outside quadratic witness descent

A scalar reporter invariant under every relabeling of the unlabeled triangle restricts to an even
function on its orientation line. If that restriction is entire, it therefore descends through
the orientation square.

This is classical one-variable invariant theory connected to the explicit source-symmetry
theorem. It does not identify the squared coordinate with probability, metric, causality, or any
physical observable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A scalar reporter is blind to presentation changes of the unlabeled triangle. -/
def TriangleRelabelInvariantReporter
    (F : Matrix (Fin 3) (Fin 3) ℂ → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (c : Matrix (Fin 3) (Fin 3) ℂ),
    F (triangleRelabel σ c) = F c

/-- Restriction of a matrix reporter to the complexified orientation residual. -/
def triangleResidualReport
    (F : Matrix (Fin 3) (Fin 3) ℂ → ℂ) (a : ℂ) : ℂ :=
  F (triangleOrientationResidual a)

/-- The source-invariant scalar coordinate of the sign residual. -/
def triangleOrientationQuadraticWitness (a : ℂ) : ℂ :=
  a ^ (2 : ℕ)

/-- Orientation reversal leaves the quadratic witness unchanged. -/
theorem triangleOrientationQuadraticWitness_neg (a : ℂ) :
    triangleOrientationQuadraticWitness (-a) =
      triangleOrientationQuadraticWitness a := by
  simp [triangleOrientationQuadraticWitness]

/-- Every presentation-invariant reporter restricts to an even function of orientation. -/
theorem triangleResidualReport_even
    (F : Matrix (Fin 3) (Fin 3) ℂ → ℂ)
    (hF : TriangleRelabelInvariantReporter F) :
    Function.Even (triangleResidualReport F) := by
  intro a
  change F (triangleOrientationResidual (-a)) =
    F (triangleOrientationResidual a)
  rw [← triangleRelabel_swap01_orientationResidual]
  exact hF triangleSwap01 (triangleOrientationResidual a)

/--
**No-outside quadratic witness descent.** Every entire scalar reporter invariant under source
relabeling factors on the orientation residual through its squared coordinate.
-/
theorem triangleResidualReport_exists_entire_squareFactor
    (F : Matrix (Fin 3) (Fin 3) ℂ → ℂ)
    (hF : TriangleRelabelInvariantReporter F)
    (hEntire : Differentiable ℂ (triangleResidualReport F)) :
    ∃ Q : ℂ → ℂ,
      Differentiable ℂ Q ∧
        ∀ a : ℂ, Q (triangleOrientationQuadraticWitness a) =
          triangleResidualReport F a := by
  refine ⟨evenEntireSquareFactor (triangleResidualReport F),
    differentiable_evenEntireSquareFactor hEntire, ?_⟩
  intro a
  exact evenEntireSquareFactor_sq hEntire
    (triangleResidualReport_even F hF) a

end

end GaloisForLFunctions.HTGeometry
