import GaloisForLFunctions.HTGeometry.ClockTube

/-!
# Functions differentiable on a clock tube exist

The tube layer assumes holomorphy on the tube and only recorded that the tube is open.  Every
globally differentiable function is differentiable there, so constants and coordinate projections
qualify, and differentiability on the tube is closed under the ring operations.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- Global differentiability restricts to the tube. -/
theorem differentiableOn_tube_of_differentiable {f : (Fin k → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (ρ : ℝ) : DifferentiableOn ℂ f (tube k ρ) :=
  hf.differentiableOn

/-- Constants are differentiable on every tube. -/
theorem differentiableOn_tube_const (c : ℂ) (ρ : ℝ) :
    DifferentiableOn ℂ (fun _ : Fin k → ℂ => c) (tube k ρ) :=
  differentiableOn_tube_of_differentiable (differentiable_const c) ρ

/-- Each coordinate is differentiable on every tube. -/
theorem differentiableOn_tube_apply (i : Fin k) (ρ : ℝ) :
    DifferentiableOn ℂ (fun z : Fin k → ℂ => z i) (tube k ρ) :=
  differentiableOn_tube_of_differentiable ((differentiable_apply i)) ρ

/-- Differentiability on a tube is closed under products. -/
theorem DifferentiableOn.tube_mul {f g : (Fin k → ℂ) → ℂ} {ρ : ℝ}
    (hf : DifferentiableOn ℂ f (tube k ρ)) (hg : DifferentiableOn ℂ g (tube k ρ)) :
    DifferentiableOn ℂ (fun z => f z * g z) (tube k ρ) := hf.mul hg

end GaloisForLFunctions.HTGeometry
