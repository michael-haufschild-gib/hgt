import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex finrank under conjugate-semilinear equivalence

A conjugate-semilinear equivalence is real-linear. Realification and
`finrank_real_of_complex` therefore show that it preserves complex finrank.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

def conjugateLinearEquivToReal
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℂ E] [Module ℂ F]
    (e : E ≃ₗ⋆[ℂ] F) : E ≃ₗ[ℝ] F where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' r x := by
    change e ((r : ℂ) • x) = (r : ℂ) • e x
    simpa using e.map_smulₛₗ (r : ℂ) x

theorem finrank_eq_of_conjugateLinearEquiv
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℂ E] [Module ℂ F]
    (e : E ≃ₗ⋆[ℂ] F) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  have hreal := (conjugateLinearEquivToReal e).finrank_eq
  rw [finrank_real_of_complex,
    finrank_real_of_complex] at hreal
  omega

end RHTower
end GaloisForLFunctions
