import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace
import Mathlib.LinearAlgebra.Vandermonde

open Complex Matrix
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Model space of an arbitrary bounded analytic disk multiplier. -/
def hardyMultiplierModelSpace (F : DiskMultiplier) : Submodule ℂ HardyDisk :=
  (LinearMap.range ((hardyMul F : HardyDisk →L[ℂ] HardyDisk) :
    HardyDisk →ₗ[ℂ] HardyDisk))ᗮ

noncomputable instance (F : DiskMultiplier) : CompleteSpace (hardyMultiplierModelSpace F) :=
  (Submodule.isClosed_orthogonal
    (LinearMap.range ((hardyMul F : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk))).completeSpace_coe

noncomputable instance (F : DiskMultiplier) :
    (hardyMultiplierModelSpace F).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

private theorem adjoint_hardyMul_hardyKernel_zeroModel
    (F : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) :
    (hardyMul F).adjoint (hardyKernel ha) =
      (starRingEnd ℂ) (F.fn a) • hardyKernel ha := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_hardyKernel,
    hardyFun_hardyMul F x ha, inner_smul_left, inner_hardyKernel]
  simp

/-- Every disk zero of a multiplier contributes its Szegő kernel to the model space. -/
theorem hardyKernel_mem_hardyMultiplierModelSpace
    (F : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hFa : F.fn a = 0) :
    hardyKernel ha ∈ hardyMultiplierModelSpace F := by
  rw [hardyMultiplierModelSpace,
    (hardyMul F).orthogonal_range]
  change (hardyMul F).adjoint (hardyKernel ha) = 0
  rw [adjoint_hardyMul_hardyKernel_zeroModel F ha, hFa, map_zero, zero_smul]

private theorem det_vandermonde_ne_zero_of_injective
    {k : ℕ} (a : Fin k → ℂ) (ha : Function.Injective a) :
    (Matrix.vandermonde a).det ≠ 0 := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (ha.ne (Finset.mem_Ioi.mp hj).ne')

private theorem mulVec_injective_of_det_ne_zero'
    {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.det ≠ 0) :
    Function.Injective M.mulVec :=
  Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM))

/-- Szegő kernels at pairwise distinct disk points are linearly independent. -/
theorem linearIndependent_hardyKernel_of_injective
    {k : ℕ} (a : Fin k → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (ha : Function.Injective a) :
    LinearIndependent ℂ (fun i => hardyKernel (haDisk i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let nodes : Fin k → ℂ := fun j => (starRingEnd ℂ) (a j)
  let V : Matrix (Fin k) (Fin k) ℂ := (Matrix.vandermonde nodes).transpose
  have hnodes : Function.Injective nodes := by
    intro x y hxy
    apply ha
    simpa [nodes] using congrArg (starRingEnd ℂ) hxy
  have hdet : V.det ≠ 0 := by
    dsimp only [V]
    rw [Matrix.det_transpose]
    exact det_vandermonde_ne_zero_of_injective nodes hnodes
  have hVinj : Function.Injective V.mulVec := mulVec_injective_of_det_ne_zero' hdet
  have hVg : V.mulVec g = 0 := by
    funext j
    let evalCoeff : HardyDisk →ₗ[ℂ] ℂ :=
      { toFun := fun x => x (j : ℕ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hj := congrArg evalCoeff hg
    simp only [map_sum, map_smul, map_zero] at hj
    change (∑ x, g x * (starRingEnd ℂ) (a x) ^ (j : ℕ)) = 0 at hj
    simpa [V, nodes, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      mul_comm] using hj
  have hg0 : g = 0 := hVinj (hVg.trans (Matrix.mulVec_zero V).symm)
  exact congrFun hg0 i

/-- Any finite packet of distinct zeros supplies that many independent model-space directions. -/
theorem linearIndependent_hardyMultiplierModelSpace_zeroKernels
    (F : DiskMultiplier) {k : ℕ} (a : Fin k → ℂ)
    (haDisk : ∀ i, ‖a i‖ < 1) (ha : Function.Injective a)
    (hzero : ∀ i, F.fn (a i) = 0) :
    LinearIndependent ℂ (fun i =>
      (⟨hardyKernel (haDisk i),
        hardyKernel_mem_hardyMultiplierModelSpace F (haDisk i) (hzero i)⟩ :
          hardyMultiplierModelSpace F)) := by
  apply LinearIndependent.of_comp (hardyMultiplierModelSpace F).subtype
  change LinearIndependent ℂ (fun i => hardyKernel (haDisk i))
  exact linearIndependent_hardyKernel_of_injective a haDisk ha

/-- A multiplier with distinct zero packets of every finite size has an infinite-dimensional model
space. -/
theorem not_finiteDimensional_hardyMultiplierModelSpace_of_unbounded_zeros
    (F : DiskMultiplier)
    (hzeros : ∀ k : ℕ, ∃ a : Fin k → ℂ,
      (∀ i, ‖a i‖ < 1) ∧ Function.Injective a ∧ (∀ i, F.fn (a i) = 0)) :
    ¬ FiniteDimensional ℂ (hardyMultiplierModelSpace F) := by
  intro hfinite
  letI : FiniteDimensional ℂ (hardyMultiplierModelSpace F) := hfinite
  let k := Module.finrank ℂ (hardyMultiplierModelSpace F) + 1
  obtain ⟨a, haDisk, ha, hzero⟩ := hzeros k
  have hLI := linearIndependent_hardyMultiplierModelSpace_zeroKernels
    F a haDisk ha hzero
  have hcard := hLI.fintype_card_le_finrank
  simp [k] at hcard

end

end GaloisForLFunctions.HTGeometry
