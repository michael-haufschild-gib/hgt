import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Kernel vectors are nonzero at the deleted column

A square matrix with a nonsingular submatrix of codimension one has all its kernel vectors
nonvanishing at the deleted column: otherwise the restricted vector would be in the kernel of an
invertible matrix.

For the horizon Jacobian the deleted column is the last raw one, whose conormal coordinate is the
constant term of the tangent `U` — so this is exactly what supplies `U(0) ≠ 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- **A kernel vector is nonzero at the deleted column.**  If a square matrix has a nonsingular
submatrix obtained by deleting one column `i₀` (and one row), then every nonzero kernel vector has
a nonzero `i₀`-coordinate. -/
theorem ker_coord_ne_zero_of_det_submatrix_ne_zero
    {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι F) {r c : κ → ι} (hc : Function.Injective c) {i₀ : ι}
    (hsurj : ∀ i, i ≠ i₀ → ∃ j, c j = i)
    (hB : (M.submatrix r c).det ≠ 0)
    {v : ι → F} (hv : M.mulVec v = 0) (hvne : v ≠ 0) :
    v i₀ ≠ 0 := by
  classical
  intro hzero
  have hsum : ∀ i : κ, ((M.submatrix r c).mulVec (fun j => v (c j))) i = 0 := by
    intro i
    have himg : ∑ s ∈ Finset.image c Finset.univ, M (r i) s * v s
        = ∑ j : κ, M (r i) (c j) * v (c j) :=
      Finset.sum_image (fun a _ b _ h => hc h)
    have hall : ∑ s ∈ Finset.image c Finset.univ, M (r i) s * v s
        = ∑ s : ι, M (r i) s * v s := by
      refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => ?_
      have hsi : s = i₀ := by
        by_contra hne
        obtain ⟨j, rfl⟩ := hsurj s hne
        exact hs (Finset.mem_image_of_mem c (Finset.mem_univ j))
      rw [hsi, hzero, mul_zero]
    show ∑ j : κ, M (r i) (c j) * v (c j) = 0
    rw [← himg, hall]
    have := congrFun hv (r i)
    simpa [Matrix.mulVec, dotProduct] using this
  have hker : (fun j => v (c j)) = 0 := by
    have hunit : IsUnit (M.submatrix r c).det := isUnit_iff_ne_zero.mpr hB
    have h0 : (M.submatrix r c).mulVec (fun j => v (c j)) = 0 := funext hsum
    have hcon := congrArg (fun w => (M.submatrix r c)⁻¹.mulVec w) h0
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hcon
    exact hcon
  refine hvne (funext fun s => ?_)
  by_cases hs : s = i₀
  · rw [hs, hzero]; rfl
  · obtain ⟨j, rfl⟩ := hsurj s hs
    have := congrFun hker j
    simpa using this

end GaloisForLFunctions.HTGeometry
