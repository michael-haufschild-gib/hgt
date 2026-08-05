import GaloisForLFunctions.HTGeometry.ClockProbeCovectorSlicing

/-!
# Profiles differentiable at a covector phase exist

The slicing and Riccati laws are conditioned on a profile having a derivative at the covector phase
of a probe point.  The condition is about the profile alone, and every differentiable profile
satisfies it at every phase — in particular the identity, the constants and the exponential.
-/

namespace GaloisForLFunctions.HTGeometry

variable {d : ℕ}

/-- **A differentiable profile has a derivative at every covector phase.** -/
theorem hasDerivAt_covectorPhase_of_differentiable {w : ℝ → ℝ} (hw : Differentiable ℝ w)
    (n x : Fin (d + 1) → ℝ) :
    HasDerivAt w (deriv w (covectorPhase n x)) (covectorPhase n x) :=
  (hw _).hasDerivAt

/-- The identity profile has derivative one at every covector phase. -/
theorem hasDerivAt_id_covectorPhase (n x : Fin (d + 1) → ℝ) :
    HasDerivAt (fun s : ℝ => s) 1 (covectorPhase n x) := hasDerivAt_id _

/-- A constant profile has derivative zero at every covector phase. -/
theorem hasDerivAt_const_covectorPhase (c : ℝ) (n x : Fin (d + 1) → ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 (covectorPhase n x) := hasDerivAt_const _ c

/-- The exponential profile is its own derivative at every covector phase. -/
theorem hasDerivAt_exp_covectorPhase (n x : Fin (d + 1) → ℝ) :
    HasDerivAt Real.exp (Real.exp (covectorPhase n x)) (covectorPhase n x) :=
  Real.hasDerivAt_exp _

/-- So the differentiability hypothesis of the slicing layer is satisfiable at every phase. -/
theorem exists_hasDerivAt_covectorPhase (n x : Fin (d + 1) → ℝ) :
    ∃ (w : ℝ → ℝ) (c : ℝ), HasDerivAt w c (covectorPhase n x) :=
  ⟨fun s => s, 1, hasDerivAt_id_covectorPhase n x⟩

end GaloisForLFunctions.HTGeometry
