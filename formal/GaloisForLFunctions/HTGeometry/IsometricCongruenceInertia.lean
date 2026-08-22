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

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem hermQuad_add (X Y : Matrix m m ℂ) (x : m → ℂ) :
    hermQuad (X + Y) x = hermQuad X x + hermQuad Y x := by
  simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

omit [Fintype n] [DecidableEq n] in
theorem hermQuad_one (x : m → ℂ) :
    hermQuad (1 : Matrix m m ℂ) x = ∑ i, ‖x i‖ ^ 2 := by
  simp only [hermQuad, Matrix.one_mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

omit [Fintype n] [DecidableEq n] in
theorem hermQuad_one_pos {x : m → ℂ} (hx : x ≠ 0) : 0 < hermQuad (1 : Matrix m m ℂ) x := by
  rw [hermQuad_one]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
  have : 0 < ‖x i‖ := norm_pos_iff.mpr hi
  positivity

omit [Fintype n] [DecidableEq n] in
theorem hermQuad_conjTranspose_mul_self_nonneg (A : Matrix m m ℂ) (x : m → ℂ) :
    0 ≤ hermQuad (Aᴴ * A) x := by
  have h : Aᴴ * A = Aᴴ * (1 : Matrix m m ℂ) * A := by rw [Matrix.mul_one]
  rw [h, hermQuad_rect_conjugate, hermQuad_one]
  positivity

/-- A positive multiple of the identity plus a Gram square is positive definite. -/
theorem isPosDefOn_top_smul_one_add_gram {c : ℝ} (hc : 0 < c) (A : Matrix m m ℂ) :
    IsPosDefOn ((c : ℂ) • (1 : Matrix m m ℂ) + Aᴴ * A) ⊤ := by
  intro x _ hx
  rw [hermQuad_add]
  have h1 : 0 < hermQuad ((c : ℂ) • (1 : Matrix m m ℂ)) x := by
    have hq : hermQuad ((c : ℂ) • (1 : Matrix m m ℂ)) x = c * hermQuad (1 : Matrix m m ℂ) x := by
      simp only [hermQuad, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hq]
    exact mul_pos hc (hermQuad_one_pos hx)
  have h2 := hermQuad_conjTranspose_mul_self_nonneg A x
  linarith

end GaloisForLFunctions.HTGeometry
