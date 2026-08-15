import GaloisForLFunctions.HTGeometry.BlockHermitianInertia

/-!
# Finite-rank boundary Schur index

For a Hermitian finite-rank update `B + V C Vᴴ`, this module proves the exact Schur-complement
inertia identity, component by component.  It also proves the semidefinite and positive-definite
boundary gates in the convention `S = -C⁻¹ - Vᴴ B⁻¹ V`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder

noncomputable section

variable {E r : Type*} [Fintype E] [DecidableEq E] [Fintype r] [DecidableEq r]

/-- The Hermitian block form joining the bulk and finite boundary channels. -/
noncomputable def finiteRankBoundaryBlock (B : Matrix E E ℂ) (V : Matrix E r ℂ)
    (C : Matrix r r ℂ) : Matrix (E ⊕ r) (E ⊕ r) ℂ :=
  Matrix.fromBlocks B V Vᴴ (-C⁻¹)

/-- The boundary Schur matrix in the boundary-removal sign convention. -/
noncomputable def finiteRankBoundarySchur (B : Matrix E E ℂ) (V : Matrix E r ℂ)
    (C : Matrix r r ℂ) : Matrix r r ℂ :=
  -C⁻¹ - Vᴴ * B⁻¹ * V

/-- The finite-rank repaired bulk form. -/
noncomputable def finiteRankRepaired (B : Matrix E E ℂ) (V : Matrix E r ℂ)
    (C : Matrix r r ℂ) : Matrix E E ℂ :=
  B + V * C * Vᴴ

/-- The opposite-sign Schur matrix. -/
noncomputable def finiteRankBoundarySchurPlus (B : Matrix E E ℂ) (V : Matrix E r ℂ)
    (C : Matrix r r ℂ) : Matrix r r ℂ :=
  C⁻¹ + Vᴴ * B⁻¹ * V

/-- The upper triangular change of coordinates for the first Schur complement. -/
noncomputable def finiteRankBoundaryUpper (B : Matrix E E ℂ) (V : Matrix E r ℂ) :
    Matrix (E ⊕ r) (E ⊕ r) ℂ :=
  Matrix.fromBlocks 1 (B⁻¹ * V) 0 1

/-- The lower triangular change of coordinates for the second Schur complement. -/
noncomputable def finiteRankBoundaryLower (V : Matrix E r ℂ) (C : Matrix r r ℂ) :
    Matrix (E ⊕ r) (E ⊕ r) ℂ :=
  Matrix.fromBlocks 1 0 (-C * Vᴴ) 1

omit [Fintype E] [DecidableEq E] in
/-- The boundary block is Hermitian whenever its bulk and boundary forms are Hermitian. -/
theorem finiteRankBoundaryBlock_isHermitian {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (finiteRankBoundaryBlock B V C).IsHermitian :=
  Matrix.IsHermitian.fromBlocks hB rfl hC.inv.neg

/-- The boundary Schur matrix is Hermitian. -/
theorem finiteRankBoundarySchur_isHermitian {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (finiteRankBoundarySchur B V C).IsHermitian := by
  exact (Matrix.IsHermitian.fromBlocks₁₁ V (-C⁻¹) hB).mp
    (finiteRankBoundaryBlock_isHermitian hB hC)

omit [Fintype E] [DecidableEq E] [DecidableEq r] in
/-- The repaired bulk form is Hermitian. -/
theorem finiteRankRepaired_isHermitian {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (finiteRankRepaired B V C).IsHermitian :=
  hB.add (Matrix.isHermitian_mul_mul_conjTranspose V hC)

/-- The first Schur coordinate change is invertible. -/
theorem finiteRankBoundaryUpper_isUnit (B : Matrix E E ℂ) (V : Matrix E r ℂ) :
    IsUnit (finiteRankBoundaryUpper B V) := by
  unfold finiteRankBoundaryUpper
  exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩

/-- The second Schur coordinate change is invertible. -/
theorem finiteRankBoundaryLower_isUnit (V : Matrix E r ℂ) (C : Matrix r r ℂ) :
    IsUnit (finiteRankBoundaryLower V C) := by
  unfold finiteRankBoundaryLower
  exact Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩

omit [Fintype r] in
/-- Adjoint of the first triangular Schur coordinate change. -/
theorem finiteRankBoundaryUpper_conjTranspose {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    (hB : B.IsHermitian) :
    (finiteRankBoundaryUpper B V)ᴴ = Matrix.fromBlocks 1 0 (Vᴴ * B⁻¹) 1 := by
  simp only [finiteRankBoundaryUpper, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, hB.eq]

omit [Fintype E] in
/-- Adjoint of the second triangular Schur coordinate change. -/
theorem finiteRankBoundaryLower_conjTranspose {V : Matrix E r ℂ} {C : Matrix r r ℂ}
    (hC : C.IsHermitian) :
    (finiteRankBoundaryLower V C)ᴴ = Matrix.fromBlocks 1 (-V * C) 0 1 := by
  simp only [finiteRankBoundaryLower, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC.eq, Matrix.mul_neg]
  rw [Matrix.neg_mul]

/-- First exact Schur congruence: the boundary block is congruent to `B ⊕ S`. -/
theorem finiteRankBoundaryBlock_eq_upper_congr {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hBunit : IsUnit B) :
    finiteRankBoundaryBlock B V C =
      (finiteRankBoundaryUpper B V)ᴴ *
        Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C) *
          finiteRankBoundaryUpper B V := by
  letI : Invertible B := hBunit.invertible
  rw [finiteRankBoundaryUpper_conjTranspose hB]
  simpa only [finiteRankBoundaryBlock, finiteRankBoundarySchur, finiteRankBoundaryUpper,
    Matrix.invOf_eq_nonsing_inv] using
    (Matrix.fromBlocks_eq_of_invertible₁₁ B V Vᴴ (-C⁻¹))

/-- Second exact Schur congruence: the boundary block is congruent to `H ⊕ (-C⁻¹)`. -/
theorem finiteRankBoundaryBlock_eq_lower_congr {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hC : C.IsHermitian) (hCunit : IsUnit C) :
    finiteRankBoundaryBlock B V C =
      (finiteRankBoundaryLower V C)ᴴ *
        Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹) *
          finiteRankBoundaryLower V C := by
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have hDunit : IsUnit (-C⁻¹) := (Matrix.isUnit_nonsing_inv_iff.mpr hCunit).neg
  letI : Invertible (-C⁻¹) := hDunit.invertible
  have hDinv : ⅟(-C⁻¹) = -C := by
    rw [Matrix.invOf_eq_nonsing_inv]
    apply Matrix.inv_eq_left_inv
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      Matrix.mul_nonsing_inv C hCdet
  rw [finiteRankBoundaryLower_conjTranspose hC]
  simpa only [finiteRankBoundaryBlock, finiteRankRepaired, finiteRankBoundaryLower, hDinv,
    Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add] using
    (Matrix.fromBlocks_eq_of_invertible₂₂ B V Vᴴ (-C⁻¹))

/-- Balanced componentwise inertia identity behind the finite-rank boundary Schur formula. -/
theorem finiteRankBoundary_inertia_balanced {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hBunit : IsUnit B) (hCunit : IsUnit C) :
    hermPosIndex B + hermPosIndex (finiteRankBoundarySchur B V C) =
        hermPosIndex (finiteRankRepaired B V C) + hermPosIndex (-C⁻¹) ∧
      hermNegIndex B + hermNegIndex (finiteRankBoundarySchur B V C) =
        hermNegIndex (finiteRankRepaired B V C) + hermNegIndex (-C⁻¹) ∧
      hermNullIndex B + hermNullIndex (finiteRankBoundarySchur B V C) =
        hermNullIndex (finiteRankRepaired B V C) + hermNullIndex (-C⁻¹) := by
  have hS := finiteRankBoundarySchur_isHermitian (V := V) hB hC
  have hH := finiteRankRepaired_isHermitian (V := V) hB hC
  have hUpper := finiteRankBoundaryUpper_isUnit B V
  have hLower := finiteRankBoundaryLower_isUnit V C
  have hLeft := finiteRankBoundaryBlock_eq_upper_congr hB hBunit (V := V) (C := C)
  have hRight := finiteRankBoundaryBlock_eq_lower_congr (B := B) (V := V) hC hCunit
  have hPosLeft : hermPosIndex (finiteRankBoundaryBlock B V C) =
      hermPosIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := by
    rw [hLeft, posIndex_conjugate _ hUpper]
  have hNegLeft : hermNegIndex (finiteRankBoundaryBlock B V C) =
      hermNegIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := by
    rw [hLeft, negIndex_conjugate _ hUpper]
  have hNullLeft : hermNullIndex (finiteRankBoundaryBlock B V C) =
      hermNullIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := by
    rw [hLeft, nullIndex_conjugate _ hUpper]
  have hPosRight : hermPosIndex (finiteRankBoundaryBlock B V C) =
      hermPosIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := by
    rw [hRight, posIndex_conjugate _ hLower]
  have hNegRight : hermNegIndex (finiteRankBoundaryBlock B V C) =
      hermNegIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := by
    rw [hRight, negIndex_conjugate _ hLower]
  have hNullRight : hermNullIndex (finiteRankBoundaryBlock B V C) =
      hermNullIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := by
    rw [hRight, nullIndex_conjugate _ hLower]
  obtain ⟨hPosBS, hNegBS, hNullBS⟩ := inertia_fromBlocks_zero hB hS
  obtain ⟨hPosHD, hNegHD, hNullHD⟩ := inertia_fromBlocks_zero hH hC.inv.neg
  refine ⟨?_, ?_, ?_⟩
  · calc
      hermPosIndex B + hermPosIndex (finiteRankBoundarySchur B V C) =
          hermPosIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := hPosBS.symm
      _ = hermPosIndex (finiteRankBoundaryBlock B V C) := hPosLeft.symm
      _ = hermPosIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := hPosRight
      _ = hermPosIndex (finiteRankRepaired B V C) + hermPosIndex (-C⁻¹) := hPosHD
  · calc
      hermNegIndex B + hermNegIndex (finiteRankBoundarySchur B V C) =
          hermNegIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := hNegBS.symm
      _ = hermNegIndex (finiteRankBoundaryBlock B V C) := hNegLeft.symm
      _ = hermNegIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := hNegRight
      _ = hermNegIndex (finiteRankRepaired B V C) + hermNegIndex (-C⁻¹) := hNegHD
  · calc
      hermNullIndex B + hermNullIndex (finiteRankBoundarySchur B V C) =
          hermNullIndex (Matrix.fromBlocks B 0 0 (finiteRankBoundarySchur B V C)) := hNullBS.symm
      _ = hermNullIndex (finiteRankBoundaryBlock B V C) := hNullLeft.symm
      _ = hermNullIndex (Matrix.fromBlocks (finiteRankRepaired B V C) 0 0 (-C⁻¹)) := hNullRight
      _ = hermNullIndex (finiteRankRepaired B V C) + hermNullIndex (-C⁻¹) := hNullHD

/-- Exact componentwise finite-rank boundary Schur inertia formula. -/
theorem finiteRankBoundary_inertia {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hBunit : IsUnit B) (hCunit : IsUnit C) :
    hermPosIndex (finiteRankRepaired B V C) =
        hermPosIndex B + hermPosIndex (finiteRankBoundarySchur B V C) - hermPosIndex (-C⁻¹) ∧
      hermNegIndex (finiteRankRepaired B V C) =
        hermNegIndex B + hermNegIndex (finiteRankBoundarySchur B V C) - hermNegIndex (-C⁻¹) ∧
      hermNullIndex (finiteRankRepaired B V C) =
        hermNullIndex B + hermNullIndex (finiteRankBoundarySchur B V C) - hermNullIndex (-C⁻¹) := by
  obtain ⟨hPos, hNeg, hNull⟩ := finiteRankBoundary_inertia_balanced hB hC hBunit hCunit
  exact ⟨Nat.eq_sub_of_add_eq hPos.symm, Nat.eq_sub_of_add_eq hNeg.symm,
    Nat.eq_sub_of_add_eq hNull.symm⟩

/-- Negative definiteness of `C` makes `-C⁻¹` positive definite. -/
theorem finiteRankBoundary_neg_nonsing_inv_posDef {C : Matrix r r ℂ} (hCneg : (-C).PosDef) :
    (-C⁻¹).PosDef := by
  have hCunit : IsUnit C := by simpa using hCneg.isUnit.neg
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have hnegInv : (-C)⁻¹ = -C⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      Matrix.nonsing_inv_mul C hCdet
  rw [← hnegInv]
  exact hCneg.inv

/-- With positive bulk and negative boundary form, repaired and Schur forms have the same
positive-semidefinite gate. -/
theorem finiteRankBoundary_posSemidef_iff_boundarySchur_posSemidef {B : Matrix E E ℂ}
    {V : Matrix E r ℂ} {C : Matrix r r ℂ} (hBpos : B.PosDef) (hCneg : (-C).PosDef) :
    (finiteRankRepaired B V C).PosSemidef ↔ (finiteRankBoundarySchur B V C).PosSemidef := by
  have hDpos := finiteRankBoundary_neg_nonsing_inv_posDef hCneg
  letI : Invertible B := hBpos.isUnit.invertible
  letI : Invertible (-C⁻¹) := hDpos.isUnit.invertible
  have hCunit : IsUnit C := by simpa using hCneg.isUnit.neg
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have hDinv : (-C⁻¹)⁻¹ = -C := by
    apply Matrix.inv_eq_left_inv
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      Matrix.mul_nonsing_inv C hCdet
  have hMS : (finiteRankBoundaryBlock B V C).PosSemidef ↔
      (finiteRankBoundarySchur B V C).PosSemidef := by
    simpa only [finiteRankBoundaryBlock, finiteRankBoundarySchur, Matrix.invOf_eq_nonsing_inv] using
      (Matrix.PosDef.fromBlocks₁₁ V (-C⁻¹) hBpos)
  have hMH : (finiteRankBoundaryBlock B V C).PosSemidef ↔
      (finiteRankRepaired B V C).PosSemidef := by
    simpa only [finiteRankBoundaryBlock, finiteRankRepaired, hDinv, Matrix.mul_neg,
      Matrix.neg_mul, sub_neg_eq_add] using
      (Matrix.PosDef.fromBlocks₂₂ B V hDpos)
  exact hMH.symm.trans hMS

/-- With positive bulk and negative boundary form, repaired and Schur forms have the same
positive-definite gate. -/
theorem finiteRankBoundary_posDef_iff_boundarySchur_posDef {B : Matrix E E ℂ}
    {V : Matrix E r ℂ} {C : Matrix r r ℂ} (hBpos : B.PosDef) (hCneg : (-C).PosDef) :
    (finiteRankRepaired B V C).PosDef ↔ (finiteRankBoundarySchur B V C).PosDef := by
  have hPSD := finiteRankBoundary_posSemidef_iff_boundarySchur_posSemidef (V := V) hBpos hCneg
  have hDpos := finiteRankBoundary_neg_nonsing_inv_posDef hCneg
  letI : Invertible B := hBpos.isUnit.invertible
  letI : Invertible (-C⁻¹) := hDpos.isUnit.invertible
  have hCunit : IsUnit C := by simpa using hCneg.isUnit.neg
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have hDinv : ⅟(-C⁻¹) = -C := by
    rw [Matrix.invOf_eq_nonsing_inv]
    apply Matrix.inv_eq_left_inv
    simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      Matrix.mul_nonsing_inv C hCdet
  have hUnitS : IsUnit (finiteRankBoundaryBlock B V C) ↔
      IsUnit (finiteRankBoundarySchur B V C) := by
    simpa only [finiteRankBoundaryBlock, finiteRankBoundarySchur, Matrix.invOf_eq_nonsing_inv] using
      (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
        (A := B) (B := V) (C := Vᴴ) (D := -C⁻¹))
  have hUnitH : IsUnit (finiteRankBoundaryBlock B V C) ↔
      IsUnit (finiteRankRepaired B V C) := by
    simpa only [finiteRankBoundaryBlock, finiteRankRepaired, hDinv, Matrix.mul_neg,
      Matrix.neg_mul, sub_neg_eq_add] using
      (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂
        (A := B) (B := V) (C := Vᴴ) (D := -C⁻¹))
  constructor
  · intro hH
    have hSPSD := hPSD.mp hH.posSemidef
    have hSunit := hUnitS.mp (hUnitH.mpr hH.isUnit)
    exact hSPSD.posDef_iff_isUnit.mpr hSunit
  · intro hS
    have hHPSD := hPSD.mpr hS.posSemidef
    have hHunit := hUnitH.mp (hUnitS.mpr hS.isUnit)
    exact hHPSD.posDef_iff_isUnit.mpr hHunit

/-- The opposite-sign Schur convention is the negative of the boundary-removal convention. -/
theorem finiteRankBoundarySchurPlus_eq_neg {B : Matrix E E ℂ} {V : Matrix E r ℂ}
    {C : Matrix r r ℂ} :
    finiteRankBoundarySchurPlus B V C = -finiteRankBoundarySchur B V C := by
  unfold finiteRankBoundarySchurPlus finiteRankBoundarySchur
  rw [neg_sub, sub_neg_eq_add, add_comm]

/-- In the opposite convention the positive-definite boundary gate is strict negativity. -/
theorem finiteRankBoundary_posDef_iff_boundarySchurPlus_negDef {B : Matrix E E ℂ}
    {V : Matrix E r ℂ} {C : Matrix r r ℂ} (hBpos : B.PosDef) (hCneg : (-C).PosDef) :
    (finiteRankRepaired B V C).PosDef ↔ (-finiteRankBoundarySchurPlus B V C).PosDef := by
  rw [finiteRankBoundarySchurPlus_eq_neg]
  simpa using finiteRankBoundary_posDef_iff_boundarySchur_posDef hBpos hCneg

end

end GaloisForLFunctions.HTGeometry
