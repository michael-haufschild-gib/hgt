import Mathlib

/-!
# Algebraic elimination of normalized torsion

An auxiliary torsion variable enters quadratically and linearly.  Completing the square eliminates
it exactly and leaves a nonnegative contact Lagrangian.  The corresponding derivative-free
Hamiltonian contribution is nonpositive.  The positive coupling is encoded by its logarithm, so
every result is unconditional.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Normalized quadratic-plus-linear auxiliary torsion Lagrangian. -/
def auxiliaryTorsionLagrangian (logKappa source auxiliary : ℝ) : ℝ :=
  -(auxiliary ^ (2 : ℕ)) / 2 + Real.exp (logKappa / 2) * auxiliary * source

/-- Contact term obtained after eliminating normalized torsion. -/
def eliminatedContactLagrangian (logKappa source : ℝ) : ℝ :=
  (Real.exp (logKappa / 2) * source) ^ (2 : ℕ) / 2

/-- Exact completed-square decomposition of the auxiliary interaction. -/
theorem auxiliaryTorsionLagrangian_completeSquare
    (logKappa source auxiliary : ℝ) :
    auxiliaryTorsionLagrangian logKappa source auxiliary =
      eliminatedContactLagrangian logKappa source -
        (auxiliary - Real.exp (logKappa / 2) * source) ^ (2 : ℕ) / 2 := by
  unfold auxiliaryTorsionLagrangian eliminatedContactLagrangian
  ring

/-- Substituting the algebraic torsion equation leaves exactly the contact term. -/
theorem auxiliaryTorsionLagrangian_eliminate (logKappa source : ℝ) :
    auxiliaryTorsionLagrangian logKappa source (Real.exp (logKappa / 2) * source) =
      eliminatedContactLagrangian logKappa source := by
  rw [auxiliaryTorsionLagrangian_completeSquare]
  ring

/-- Eliminated contact Lagrangian is nonnegative. -/
theorem eliminatedContactLagrangian_nonneg (logKappa source : ℝ) :
    0 ≤ eliminatedContactLagrangian logKappa source := by
  unfold eliminatedContactLagrangian
  positivity

/-- Normalized elimination reproduces `kappa * source^(2 : ℕ) / 2`. -/
theorem eliminatedContactLagrangian_eq (logKappa source : ℝ) :
    eliminatedContactLagrangian logKappa source = Real.exp logKappa * source ^ (2 : ℕ) / 2 := by
  unfold eliminatedContactLagrangian
  rw [mul_pow, show Real.exp (logKappa / 2) ^ (2 : ℕ) = Real.exp logKappa by
    rw [← Real.exp_nat_mul]
    congr 1
    ring]

/-- The derivative-free interaction Hamiltonian is the negative contact Lagrangian. -/
theorem eliminatedContactHamiltonian_nonpos (logKappa source : ℝ) :
    -eliminatedContactLagrangian logKappa source ≤ 0 := by
  exact neg_nonpos.mpr (eliminatedContactLagrangian_nonneg logKappa source)

/-- Quartic invariant corresponding to a contracted torsion current square. -/
def spinTorsionQuarticInvariant (currentSquare : ℝ) : ℝ := -16 * currentSquare

/-- Exact paper normalization of the quartic contact Lagrangian. -/
def spinTorsionContactLagrangian (kappa quartic : ℝ) : ℝ := -kappa * quartic / 32

/-- Derivative-free interaction Hamiltonian obtained by reversing the contact-Lagrangian sign. -/
def spinTorsionInteractionHamiltonian (kappa quartic : ℝ) : ℝ := kappa * quartic / 32

/-- The current-square and quartic normalizations give the exact coefficient `-κ/32`. -/
theorem spinTorsionContactLagrangian_eq_currentSquare (kappa currentSquare : ℝ) :
    kappa / 2 * currentSquare =
      spinTorsionContactLagrangian kappa (spinTorsionQuarticInvariant currentSquare) := by
  unfold spinTorsionContactLagrangian spinTorsionQuarticInvariant
  ring

/-- Exact Lorentzian sign flip between contact Lagrangian and interaction Hamiltonian. -/
theorem spinTorsionInteractionHamiltonian_eq_neg_contact (kappa quartic : ℝ) :
    spinTorsionInteractionHamiltonian kappa quartic =
      -spinTorsionContactLagrangian kappa quartic := by
  unfold spinTorsionInteractionHamiltonian spinTorsionContactLagrangian
  ring

end GaloisForLFunctions.HTGeometry
