import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Inertia under rectangular isometric congruence

If `C` is a rectangular matrix with `Cᴴ C = 1`, then the Hermitian form of `C X Cᴴ` is the form of
`X` pulled back along the surjection `Cᴴ`.  Its positive and negative indices therefore agree with
those of `X`; only the null index grows, by the codimension of the range of `C`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- Rectangular congruence of the Hermitian quadratic form. -/
theorem hermQuad_rect_conjugate (H : Matrix m m ℂ) (S : Matrix m n ℂ) (x : n → ℂ) :
    hermQuad (Sᴴ * H * S) x = hermQuad H (S *ᵥ x) := by
  simp only [hermQuad]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

omit [DecidableEq n] in
theorem mulVecLin_injective_of_isometry {C : Matrix n m ℂ} (hC : Cᴴ * C = 1) :
    Function.Injective C.mulVecLin := by
  intro x y hxy
  have hx : C *ᵥ x = C *ᵥ y := by simpa [Matrix.mulVecLin_apply] using hxy
  have h : (Cᴴ * C) *ᵥ x = (Cᴴ * C) *ᵥ y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx]
  rwa [hC, Matrix.one_mulVec, Matrix.one_mulVec] at h

omit [DecidableEq n] [DecidableEq m] in
theorem hermQuad_isometric {C : Matrix n m ℂ} (X : Matrix m m ℂ) (y : n → ℂ) :
    hermQuad (C * X * Cᴴ) y = hermQuad X (Cᴴ *ᵥ y) := by
  have hCX : C * X * Cᴴ = (Cᴴ)ᴴ * X * Cᴴ := by rw [Matrix.conjTranspose_conjTranspose]
  rw [hCX, hermQuad_rect_conjugate]

omit [DecidableEq n] in
/-- **Rectangular isometric congruence preserves the positive index.** -/
theorem posIndex_isometric_congr {C : Matrix n m ℂ} (hC : Cᴴ * C = 1) (X : Matrix m m ℂ) :
    hermPosIndex (C * X * Cᴴ) = hermPosIndex X := by
  refine le_antisymm ?_ ?_
  · obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (C * X * Cᴴ)
    have hinj : Function.Injective ((Cᴴ).mulVecLin.domRestrict W) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker] at hy
      by_contra hy0
      have hyv : (y : n → ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
      have hpos := hW _ y.2 hyv
      have hzero : Cᴴ *ᵥ (y : n → ℂ) = 0 := by
        simpa [Matrix.mulVecLin_apply] using hy
      rw [hermQuad_isometric, hzero] at hpos
      simp [hermQuad] at hpos
    have hmap : IsPosDefOn X (W.map (Cᴴ).mulVecLin) := by
      rintro w ⟨y, hy, rfl⟩ hw0
      have hy0 : (y : n → ℂ) ≠ 0 := fun h => hw0 (by simp [h])
      have hpos := hW y hy hy0
      rw [hermQuad_isometric] at hpos
      exact hpos
    have hrangeeq : LinearMap.range ((Cᴴ).mulVecLin.domRestrict W)
        = W.map (Cᴴ).mulVecLin := LinearMap.range_domRestrict _ _
    have heq : Module.finrank ℂ W = Module.finrank ℂ (W.map (Cᴴ).mulVecLin) := by
      rw [← hrangeeq]
      exact (LinearEquiv.ofInjective _ hinj).finrank_eq
    rw [← hrank, heq]
    exact finrank_le_posIndex hmap
  · obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex X
    have hinjC : Function.Injective C.mulVecLin := mulVecLin_injective_of_isometry hC
    have hmap : IsPosDefOn (C * X * Cᴴ) (W.map C.mulVecLin) := by
      rintro y ⟨w, hw, rfl⟩ hy0
      have hw0 : w ≠ 0 := fun h => hy0 (by simp [h])
      have hpull : Cᴴ *ᵥ (C.mulVecLin w) = w := by
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hC, Matrix.one_mulVec]
      rw [hermQuad_isometric, hpull]
      exact hW w hw hw0
    have heq : Module.finrank ℂ (W.map C.mulVecLin) = Module.finrank ℂ W :=
      ((Submodule.equivMapOfInjective C.mulVecLin hinjC W).symm).finrank_eq
    rw [← hrank, ← heq]
    exact finrank_le_posIndex hmap

omit [DecidableEq n] in
/-- **Rectangular isometric congruence preserves the negative index.** -/
theorem negIndex_isometric_congr {C : Matrix n m ℂ} (hC : Cᴴ * C = 1) (X : Matrix m m ℂ) :
    hermNegIndex (C * X * Cᴴ) = hermNegIndex X := by
  have hneg : -(C * X * Cᴴ) = C * (-X) * Cᴴ := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [hermNegIndex, hneg, posIndex_isometric_congr hC, hermNegIndex]

end GaloisForLFunctions.HTGeometry
