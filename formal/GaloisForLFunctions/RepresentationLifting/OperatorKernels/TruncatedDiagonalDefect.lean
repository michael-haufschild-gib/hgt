import GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual diagonal defect of a truncated local algebra

Multiplication from the local tensor square onto the truncated algebra is
surjective. Its kernel realizes the reduced intersection charge `m(m-1)`.
Thus injectivity holds exactly in dimensions zero and one.

This is a finite algebraic test of the unit-rigidity mechanism in
Scheimbauer--Van Dyke, arXiv:2611.18555, Section 2.5. It concerns ordinary
multiplication, not derived diagonal descent.
-/

noncomputable section
open scoped TensorProduct
namespace GaloisForLFunctions.RepresentationLifting
open RHTower.ShiftPairLocalIntersectionAlgebra

local instance truncatedRootFinite (m : ℕ) : Module.Finite ℂ (TruncatedRootAlgebra m) :=
  (truncatedRootPowerBasis m).finite

/-- Restriction to the diagonal in the literal local intersection algebra. -/
def localDiagonal (m : ℕ) : LocalIntersectionAlgebra m m →ₐ[ℂ] TruncatedRootAlgebra m :=
  Algebra.TensorProduct.lmul' ℂ

/-- Every truncated function extends to the tensor square by ignoring one coordinate. -/
theorem localDiagonal_surjective (m : ℕ) : Function.Surjective (localDiagonal m) := by
  intro x
  refine ⟨x ⊗ₜ[ℂ] 1, ?_⟩
  exact (Algebra.TensorProduct.lmul'_apply_tmul x 1).trans (mul_one x)

/-- The reduced intersection charge is the dimension of an actual kernel. -/
theorem localDiagonal_kernel_finrank (m : ℕ) :
    Module.finrank ℂ (LinearMap.ker (localDiagonal m).toLinearMap) = m * (m - 1) := by
  have hr : LinearMap.range (localDiagonal m).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (localDiagonal_surjective m)
  have h := (localDiagonal m).toLinearMap.finrank_range_add_finrank_ker
  rw [hr, finrank_top, finrank_truncatedRootAlgebra, finrank_localIntersectionAlgebra] at h
  have hcharge := diagonalReducedMultiplicity_eq m
  rw [localIntersectionMultiplicity_eq_mul] at hcharge
  omega

/-- Ordinary diagonal multiplication is injective precisely at the zero or scalar algebra. -/
theorem localDiagonal_injective_iff (m : ℕ) :
    Function.Injective (localDiagonal m) ↔ m ≤ 1 := by
  change Function.Injective (localDiagonal m).toLinearMap ↔ m ≤ 1
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero, localDiagonal_kernel_finrank,
    Nat.mul_eq_zero]
  omega

/-- Every higher-order thickening has a nonzero diagonal kernel with its exact dimension. -/
theorem localDiagonal_thickening_defect (n : ℕ) :
    ¬Function.Injective (localDiagonal (n + 2)) ∧
      Module.finrank ℂ (LinearMap.ker (localDiagonal (n + 2)).toLinearMap) =
        (n + 2) * (n + 1) := by
  constructor
  · rw [localDiagonal_injective_iff]
    omega
  · have hsub : n + 2 - 1 = n + 1 := by omega
    simpa only [hsub] using localDiagonal_kernel_finrank (n + 2)

#print axioms localDiagonal_surjective
#print axioms localDiagonal_kernel_finrank
#print axioms localDiagonal_injective_iff
#print axioms localDiagonal_thickening_defect

end GaloisForLFunctions.RepresentationLifting
