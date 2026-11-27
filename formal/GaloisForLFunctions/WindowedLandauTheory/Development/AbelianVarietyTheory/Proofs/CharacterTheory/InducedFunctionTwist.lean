import GaloisForLFunctions.RHTower.Artin.ArtinMonomialSpan

/-! Twisting by an ambient linear character commutes with induction. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

variable {G : Type*} [Group G] [Fintype G]

/-- An ambient class function factors out of the inducing average. -/
theorem inducedFunction_mul_class (H : Subgroup G) (f : H → ℂ) (η : G → ℂ)
    (hη : ∀ x y, η (y * x * y⁻¹) = η x) (x : G) :
    inducedFunction H (fun u => η u.val * f u) x = η x * inducedFunction H f x := by
  simpa only [mul_comm] using
    congrFun (inducedFunction_mul_restrict H f η (fun y z => hη z y)) x

/-- A twist by an ambient linear character factors out of the inducing average. -/
theorem inducedFunction_twist (H : Subgroup G) (f : H → ℂ) (η : G →* ℂˣ) (x : G) :
    inducedFunction H (fun u => (η u.val : ℂ) * f u) x =
      (η x : ℂ) * inducedFunction H f x := by
  refine inducedFunction_mul_class H f (fun y => (η y : ℂ)) ?_ x
  intro z y
  have h : η (y * z * y⁻¹) = η z := by
    simp only [map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
  exact congrArg (fun t : ℂˣ => (t : ℂ)) h

end GaloisForLFunctions
