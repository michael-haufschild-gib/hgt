import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy

/-!
# Diagonal observables cannot produce thermodynamic transition response

KMS entropy production is an off-diagonal, energy-gap phenomenon. An amplitude supported only on
the state-space diagonal has zero transition intensity on every ordered pair and therefore zero
finite passive response at every spectral parameter.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A diagonally supported amplitude has identically zero KMS entropy-production intensity. -/
theorem finiteKMSEntropyProductionTransitionIntensity_eq_zero_of_diagonal
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hdiag : ∀ a b, a ≠ b → amplitude a b = 0)
    (a b : α) :
    finiteKMSEntropyProductionTransitionIntensity β energy amplitude a b = 0 := by
  by_cases hab : a = b
  · subst b
    rw [finiteKMSEntropyProductionTransitionIntensity,
      thermodynamicAffinity_finiteGibbsStateWeight]
    ring
  · have hab' : b ≠ a := Ne.symm hab
    rw [finiteKMSEntropyProductionTransitionIntensity,
      _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity,
      _root_.HTGeometry.finiteGibbsTransitionIntensity,
      _root_.HTGeometry.finiteGibbsTransitionIntensity,
      hdiag a b hab, hdiag b a hab']
    simp

/-- The finite entropy-production passive response of a diagonally supported amplitude vanishes
at every spectral parameter. -/
theorem finiteKMSEntropyProductionTransitionResponse_eq_zero_of_diagonal
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hdiag : ∀ a b, a ≠ b → amplitude a b = 0)
    (z : ℂ) :
    _root_.HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
        energy z = 0 := by
  rw [_root_.HTGeometry.finiteTransitionPassiveResponse]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  rw [finiteKMSEntropyProductionTransitionIntensity_eq_zero_of_diagonal
    β energy amplitude hdiag a b]
  simp

end


end GaloisForLFunctions.HTGeometry
