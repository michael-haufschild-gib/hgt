import GaloisForLFunctions.HTGeometry.ReciprocalScaleNoether

/-!
# Reciprocal Noether action with a varying coefficient

The canonical bilinear Hamiltonian may have a prescribed time-dependent
coefficient. Reciprocal scaling still preserves the action: its symmetry
acts on the fields, while leaving that coefficient fixed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Canonical action with a prescribed coefficient along the trajectory. -/
def reciprocalScaleDrivenAction (a : ℝ → ℂ) (z : ℝ → ℂ × ℂ) (l r : ℝ) : ℂ :=
  ∫ t in l..r, reciprocalScaleLagrangian (a t) (z t)
    (deriv (fun u => (z u).1) t, deriv (fun u => (z u).2) t)

theorem reciprocalScaleDrivenAction_const (a : ℂ) (z : ℝ → ℂ × ℂ) (l r : ℝ) :
    reciprocalScaleDrivenAction (fun _ => a) z l r = reciprocalScaleAction a z l r := rfl

/-- A varying external coefficient preserves the reciprocal variational symmetry. -/
theorem reciprocalScaleDrivenAction_symmetry
    (a : ℝ → ℂ) (s : ℝ) (z : ℝ → ℂ × ℂ) (l r : ℝ) :
    reciprocalScaleDrivenAction a (fun t => reciprocalScale s (z t)) l r =
      reciprocalScaleDrivenAction a z l r := by
  unfold reciprocalScaleDrivenAction
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [reciprocalScale, deriv_const_mul_field] using
    reciprocalScaleLagrangian_symmetry (a t) s (z t)
      (deriv (fun u => (z u).1) t, deriv (fun u => (z u).2) t)

end GaloisForLFunctions.HTGeometry
