import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Corank one, and its stability under extension of the coefficient field

A square matrix over a field whose determinant vanishes while some submatrix of codimension one
stays nonsingular has a kernel of dimension exactly one: the nonsingular submatrix forces the rank
to be at least `N`, the vanishing determinant forces a nonzero kernel vector, and rank-nullity
closes the gap.

Both hypotheses are determinantal, hence transported by any homomorphism of fields, so corank one
survives every extension of the coefficient field:

```text
finrank_ker_mulVecLin_eq_one_of_det_eq_zero
finrank_ker_mulVecLin_map_eq_one
    ** det M = 0, one cofactor nonzero  ⟹  the kernel of M over ANY extension field is a line **
```

This is the form in which generic corank one on the function field of a divisor becomes corank one
at the residue field of a place above it, where the tangent to a collision actually lives.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- **Corank one from a vanishing determinant and a surviving cofactor.**  A square matrix over a
field whose determinant vanishes but which has a nonsingular submatrix of codimension one has a
one-dimensional kernel. -/
theorem finrank_ker_mulVecLin_eq_one_of_det_eq_zero
    {F : Type*} [Field F] {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (hdet : M.det = 0) {r c : Fin N → Fin (N + 1)}
    (hB : (M.submatrix r c).det ≠ 0) :
    Module.finrank F (LinearMap.ker M.mulVecLin) = 1 := by
  classical
  obtain ⟨v, hvne, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hkerne : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, by simpa [Matrix.mulVecLin_apply] using hv, hvne⟩
  have hkerge : 1 ≤ Module.finrank F (LinearMap.ker M.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hkerne
  have hrankB : (M.submatrix r c).rank = N := by
    have h := Matrix.rank_mul_eq_right_of_isUnit_det (M.submatrix r c)
      (1 : Matrix (Fin N) (Fin N) F) (isUnit_iff_ne_zero.mpr hB)
    simpa using h
  have hrankge : N ≤ M.rank := hrankB.symm.trans_le (Matrix.rank_submatrix_le M r c)
  change N ≤ Module.finrank F (LinearMap.range M.mulVecLin) at hrankge
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  omega

/-- **Corank one survives every field extension.**  The determinant and the cofactor are polynomial
in the entries, so they transport along any homomorphism of fields. -/
theorem finrank_ker_mulVecLin_map_eq_one
    {F E : Type*} [Field F] [Field E] (φ : F →+* E) {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) F) (hdet : M.det = 0)
    {r c : Fin N → Fin (N + 1)} (hB : (M.submatrix r c).det ≠ 0) :
    Module.finrank E (LinearMap.ker (M.map φ).mulVecLin) = 1 := by
  refine finrank_ker_mulVecLin_eq_one_of_det_eq_zero (r := r) (c := c) _ ?_ ?_
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
  · rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hB (φ.injective (by rw [h, map_zero]))

/-- **Corank one, stated as a rank equality.**  This is the form the cokernel-annihilator theorem
consumes. -/
theorem rank_add_one_eq_of_det_eq_zero
    {F : Type*} [Field F] {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) F)
    (hdet : M.det = 0) {r c : Fin N → Fin (N + 1)}
    (hB : (M.submatrix r c).det ≠ 0) :
    M.rank + 1 = N + 1 := by
  classical
  have hker := finrank_ker_mulVecLin_eq_one_of_det_eq_zero M hdet hB
  have hsum := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hker] at hsum
  exact hsum

/-- The same after any extension of the coefficient field. -/
theorem rank_map_add_one_eq_of_det_eq_zero
    {F E : Type*} [Field F] [Field E] (φ : F →+* E) {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) F) (hdet : M.det = 0)
    {r c : Fin N → Fin (N + 1)} (hB : (M.submatrix r c).det ≠ 0) :
    (M.map φ).rank + 1 = N + 1 := by
  refine rank_add_one_eq_of_det_eq_zero (r := r) (c := c) _ ?_ ?_
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero]
  · rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hB (φ.injective (by rw [h, map_zero]))

end GaloisForLFunctions.HTGeometry
