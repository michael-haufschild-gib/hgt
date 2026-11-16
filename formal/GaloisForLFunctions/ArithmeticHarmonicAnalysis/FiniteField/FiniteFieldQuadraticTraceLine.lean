import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The trace-zero line of a quadratic finite field

The nonzero trace functional has a one-dimensional kernel. Consequently
every nonzero trace-zero element is a basis of that kernel over the base
field, including in characteristic two.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] [Algebra K L]
variable (hdegree : Module.finrank K L = 2)
include hdegree

/-- The trace-zero subspace of a quadratic finite-field extension has dimension one. -/
theorem finiteField_quadratic_trace_kernel_finrank :
    Module.finrank K (LinearMap.ker (Algebra.trace K L)) = 1 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (Algebra.trace_ne_zero K L)
  rw [hdegree] at h
  omega

/-- Every nonzero trace-zero element spans precisely all trace-zero elements over the base field. -/
theorem finiteField_quadratic_trace_zero_iff (θ : L) (hθ0 : θ ≠ 0)
    (hθ : Algebra.trace K L θ = 0) (x : L) :
    Algebra.trace K L x = 0 ↔ ∃ a : K, x = θ * algebraMap K L a := by
  constructor
  · intro hx
    let t : LinearMap.ker (Algebra.trace K L) := ⟨θ, hθ⟩
    have ht : t ≠ 0 := fun h => hθ0 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' t ht).mp
      (finiteField_quadratic_trace_kernel_finrank hdegree) ⟨x, hx⟩
    refine ⟨a, ?_⟩
    have he : a • θ = x := congrArg Subtype.val ha
    rw [Algebra.smul_def, mul_comm] at he
    exact he.symm
  · rintro ⟨a, rfl⟩
    rw [mul_comm θ (algebraMap K L a), ← Algebra.smul_def, map_smul, hθ, smul_zero]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
