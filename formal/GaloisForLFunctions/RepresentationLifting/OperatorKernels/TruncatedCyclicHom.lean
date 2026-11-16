import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicOperatorHom
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.TruncatedShiftDefects

/-!
# Exact Hom dimensions for truncated cyclic modules

The cyclic relation Xᵐ=0 restricts a generator image in an n-coefficient
jet to the terminal min(m,n) coefficients. Consequently the Hom space
has exactly that dimension, including either zero-length module. This
realizes the generator-kernel reduction on the actual truncated shift.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

open Polynomial OperatorKernels

variable {K : Type*} [Field K]

/-- The nullity of any truncated shift is the smaller of shift and horizon. -/
theorem finrank_truncatedShift_kernel_min (N k : ℕ) :
    Module.finrank K (LinearMap.ker (truncatedShift (R := K) (M := K) N k)) = min N k := by
  by_cases hk : k ≤ N
  · have h := finrank_truncatedShift_kernel (K := K) (M := K) (N - k) k
    rw [Nat.sub_add_cancel hk] at h
    simpa only [Module.finrank_self, mul_one, min_eq_right hk] using h
  · have hz : truncatedShift (R := K) (M := K) N k = 0 := by
      apply LinearMap.ext
      intro v
      funext i
      exact dif_neg (by have := i.isLt; omega)
    rw [hz, LinearMap.ker_zero]
    simp [min_eq_left (by omega : N ≤ k)]

/-- Homomorphisms from the length-m cyclic presentation to the actual length-n jet. -/
abbrev TruncatedCyclicHom (m n : ℕ) :=
  CyclicOperatorHom (truncatedShift (R := K) (M := K) n 1) (X ^ m)

/-- Exact Hom dimension; no characteristic or nonzero-length restriction is needed. -/
theorem finrank_truncatedCyclicHom (m n : ℕ) :
    Module.finrank K (TruncatedCyclicHom (K := K) m n) = min m n := by
  change Module.finrank K
    (CyclicOperatorHom (truncatedShift (R := K) (M := K) n 1) (X ^ m)) = min m n
  rw [finrank_cyclicOperatorHom, map_pow, aeval_X,
    truncatedShift_pow, finrank_truncatedShift_kernel_min, min_comm]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.finrank_truncatedShift_kernel_min
#print axioms GaloisForLFunctions.RepresentationLifting.finrank_truncatedCyclicHom

