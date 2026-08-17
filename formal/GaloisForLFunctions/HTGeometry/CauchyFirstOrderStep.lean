import Mathlib.Analysis.Complex.Liouville

/-!
# One Cauchy step for the first derivative

The derivative at the centre of a disc is controlled by the boundary sup norm alone:
`‖f′(z)‖ ≤ M/R`.  This is the estimate that converts a window bound for a holomorphic profile into a
window bound for its height derivative, at the cost of one power of the radius.
-/

open Complex Metric

namespace HTGeometry

/-- **Cauchy's estimate for the first derivative.** -/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {f : ℂ → ℂ} {z : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball z R))
    (hM : ∀ ζ ∈ sphere z R, ‖f ζ‖ ≤ M) :
    ‖deriv f z‖ ≤ M / R := by
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hM
  rw [iteratedDeriv_one] at h1
  simp only [Nat.factorial] at h1
  refine le_trans h1 (le_of_eq ?_)
  push_cast
  ring

end HTGeometry
