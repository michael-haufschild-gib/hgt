import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel
import GaloisForLFunctions.RepresentationLifting.TruncatedResolution

/-!
# Exact operator defects of truncated jets

For a jet of length `a + b`, multiplication by `xᵇ` kills exactly its last
`b` coefficients. Restriction identifies the quotient of observation maps
by maps factoring through this shift with observations on those coefficients.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels

variable {K M W : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup W] [Module K W]

/-- The kernel of a truncated shift is its terminal block of coefficients. -/
def truncatedShiftKernelEquiv (a b : ℕ) :
    (LinearMap.ker (truncatedShift (R := K) (M := M) (a + b) b)) ≃ₗ[K] (Fin b → M) where
  toFun v j := v.val ⟨a + j.val, by omega⟩
  invFun w := ⟨fun i => if h : a ≤ i.val then w ⟨i.val - a, by omega⟩ else 0, by
    rw [LinearMap.mem_ker, truncatedShift_eq_zero_iff]
    intro i hi
    exact dif_neg (by omega)⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    change (if h : a ≤ i.val then v.val ⟨a + (i.val - a), by omega⟩ else 0) = v.val i
    split
    · apply congrArg v.val
      exact Fin.ext (Nat.add_sub_of_le ‹a ≤ i.val›)
    · symm
      exact (truncatedShift_eq_zero_iff _ _ v.val).mp v.property i (by omega)
  right_inv w := by
    funext j
    change (if h : a ≤ a + j.val then w ⟨a + j.val - a, by omega⟩ else 0) = w j
    rw [dif_pos (by omega)]
    apply congrArg w
    exact Fin.ext (Nat.add_sub_cancel_left a j.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each killed coefficient contributes one full coefficient-module dimension. -/
theorem finrank_truncatedShift_kernel [FiniteDimensional K M] (a b : ℕ) :
    Module.finrank K (LinearMap.ker (truncatedShift (R := K) (M := M) (a + b) b)) =
      b * Module.finrank K M := by
  rw [(truncatedShiftKernelEquiv (K := K) (M := M) a b).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The remaining coefficients give the exact image dimension. -/
theorem finrank_truncatedShift_range [FiniteDimensional K M] (a b : ℕ) :
    Module.finrank K (LinearMap.range (truncatedShift (R := K) (M := M) (a + b) a)) =
      b * Module.finrank K M := by
  rw [truncatedShift_range_eq_ker, finrank_truncatedShift_kernel]

/-- The quotient obstruction for arbitrary vector-valued observations of a truncated jet. -/
theorem truncatedShift_observation_defect [FiniteDimensional K M] [FiniteDimensional K W]
    (a b : ℕ) :
    Module.finrank K (((Fin (a + b) → M) →ₗ[K] W) ⧸
      (precompose (W := W) (truncatedShift (R := K) (M := M) (a + b) b)).range) =
      Module.finrank K W * (b * Module.finrank K M) := by
  rw [finrank_compositionCokernel, finrank_truncatedShift_kernel]

/-- Endomorphism defects grow by jet length times the number of killed coefficients. -/
theorem truncatedShift_endomorphism_defect (a b : ℕ) :
    Module.finrank K (Module.End K (Fin (a + b) → K) ⧸
      (precompose (W := Fin (a + b) → K)
        (truncatedShift (R := K) (M := K) (a + b) b)).range) = (a + b) * b := by
  rw [finrank_endomorphism_quotient, finrank_truncatedShift_kernel]
  simp

/-- The socle contributes exactly one ambient jet length to the operator quotient. -/
theorem truncatedShift_socle_defect (a : ℕ) :
    Module.finrank K (Module.End K (Fin (a + 1) → K) ⧸
      (precompose (W := Fin (a + 1) → K)
        (truncatedShift (R := K) (M := K) (a + 1) 1)).range) = a + 1 := by
  rw [truncatedShift_endomorphism_defect, Nat.mul_one]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.truncatedShiftKernelEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedShift_observation_defect
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedShift_endomorphism_defect
