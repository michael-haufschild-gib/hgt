import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingRank
import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingSchur
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank and nullity of alternating matrices

The quadratic matrix condition identifies both radicals of the associated bilinear
form. Even rank therefore holds over every field; nullity has the parity of the size.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The corpus's quadratic definition of an alternating matrix agrees with the
alternating condition on its associated bilinear form. -/
theorem IsAlternatingMatrix.toBilin' {M : Matrix ι ι K} (hM : IsAlternatingMatrix M) :
    M.toBilin'.IsAlt := by
  intro v
  rw [Matrix.toBilin'_apply']
  exact hM v

/-- For an alternating matrix, the left and right radicals coincide. -/
theorem IsAlternatingMatrix.ker_toBilin' {M : Matrix ι ι K} (hM : IsAlternatingMatrix M) :
    M.toBilin'.ker = M.mulVecLin.ker := by
  ext v
  constructor
  · intro hv
    change M *ᵥ v = 0
    ext i
    have hvi : M.toBilin' v (Pi.single i 1) = 0 :=
      congrArg (fun f : (ι → K) →ₗ[K] K => f (Pi.single i 1)) hv
    have hiv := hM.toBilin'.isRefl _ _ hvi
    simpa [Matrix.toBilin'_apply', dotProduct, Pi.single_apply] using hiv
  · intro hv
    ext w
    apply hM.toBilin'.isRefl
    rw [Matrix.toBilin'_apply', show M *ᵥ v = 0 from hv, dotProduct_zero]

/-- Alternating matrices have even rank over every field, including characteristic two. -/
theorem IsAlternatingMatrix.even_rank {M : Matrix ι ι K} (hM : IsAlternatingMatrix M) :
    Even M.rank := by
  have hB := LinearMap.finrank_range_add_finrank_ker M.toBilin'
  have hrank := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hM.ker_toBilin'] at hB
  have heq : finrank K M.toBilin'.range = M.rank := by
    change finrank K M.toBilin'.range = finrank K M.mulVecLin.range
    omega
  rw [← heq]
  exact even_finrank_range_of_isAlt hM.toBilin'

/-- The nullity of an alternating matrix has the same parity as its size. -/
theorem IsAlternatingMatrix.nullity_mod_two {M : Matrix ι ι K}
    (hM : IsAlternatingMatrix M) :
    finrank K M.mulVecLin.ker % 2 = Fintype.card ι % 2 := by
  obtain ⟨r, hr⟩ := hM.even_rank
  have hd : M.rank + finrank K M.mulVecLin.ker = Fintype.card ι := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  omega

omit [DecidableEq ι] in
/-- Skew-symmetrization is alternating in every characteristic. -/
theorem isAlternatingMatrix_sub_transpose (M : Matrix ι ι K) :
    IsAlternatingMatrix (M - Mᵀ) := by
  intro v
  have ht : v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  rw [sub_mulVec, dotProduct_sub, ht, sub_self]

/-- Every skew-symmetrization has even rank. -/
theorem even_rank_sub_transpose (M : Matrix ι ι K) : Even (M - Mᵀ).rank :=
  (isAlternatingMatrix_sub_transpose M).even_rank

#print axioms IsAlternatingMatrix.even_rank
#print axioms IsAlternatingMatrix.nullity_mod_two
#print axioms even_rank_sub_transpose
end GaloisForLFunctions.HTGeometry.LinearAlgebra
