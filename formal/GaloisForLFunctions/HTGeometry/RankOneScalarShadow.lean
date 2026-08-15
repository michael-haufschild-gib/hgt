import GaloisForLFunctions.HTGeometry.FiniteRankOneSelector

/-!
# Rank-one scalar shadow in split coordinates

This module formalizes the exact Schur scalar statement after a boundary
functional has been split as `ker β ⊕ ℂ q`.  A positive definite kernel block
reduces the full block form to one scalar.  It also proves the principal-block
gate and a literal split-coordinate counterexample showing that a positive
scalar alone can miss a negative kernel direction.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The Schur scalar for a rank-one boundary update in supplied split coordinates. -/
def rankOneScalarShadow (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ) : ℝ :=
  a + t - rankOneEnergy B ell

/-- The repaired block form on `E ⊕ Fin 1` in supplied split coordinates. -/
def rankOneScalarShadowBlock (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ) :
    Matrix (E ⊕ Fin 1) (E ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks B (rankOneChannel ell) (rankOneChannel ell)ᴴ (rankOneBoundary (a + t))

/-- The one-channel Gram term is the diagonal scalar `ell* B⁻¹ ell`. -/
theorem rankOneChannel_gram_eq_energy (B : Matrix E E ℂ) (ell : E → ℂ)
    (hB : B.IsHermitian) :
    (rankOneChannel ell)ᴴ * B⁻¹ * rankOneChannel ell = rankOneBoundary (rankOneEnergy B ell) := by
  have hquad :
      ∑ x, (∑ y, star (ell y) * B⁻¹ y x) * ell x = star ell ⬝ᵥ B⁻¹ *ᵥ ell := by
    calc
      ∑ x, (∑ y, star (ell y) * B⁻¹ y x) * ell x =
          ∑ x, ∑ y, (star (ell y) * B⁻¹ y x) * ell x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
      _ = ∑ y, ∑ x, (star (ell y) * B⁻¹ y x) * ell x := by
        rw [Finset.sum_comm]
      _ = ∑ y, star (ell y) * ∑ x, B⁻¹ y x * ell x := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = star ell ⬝ᵥ B⁻¹ *ᵥ ell := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  ext i j
  fin_cases i
  fin_cases j
  simp only [rankOneChannel, rankOneBoundary, Matrix.replicateCol_apply,
    Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hquad, ← rankOneEnergy_coe B ell hB]

/-- The supplied block's Schur complement is its scalar shadow. -/
theorem rankOneScalarShadow_blockSchur (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ)
    (hB : B.IsHermitian) :
    rankOneBoundary (a + t) - (rankOneChannel ell)ᴴ * B⁻¹ * rankOneChannel ell =
      rankOneBoundary (rankOneScalarShadow B ell a t) := by
  rw [rankOneChannel_gram_eq_energy B ell hB]
  ext i j
  fin_cases i
  fin_cases j
  simp [rankOneBoundary, rankOneScalarShadow]

theorem rankOneBoundary_posSemidef_iff {s : ℝ} :
    (rankOneBoundary s).PosSemidef ↔ 0 ≤ s := by
  rw [rankOneBoundary, Matrix.posSemidef_diagonal_iff]
  simp

theorem rankOneBoundary_isUnit_iff {s : ℝ} : IsUnit (rankOneBoundary s) ↔ s ≠ 0 := by
  constructor
  · intro h
    rw [Matrix.isUnit_iff_isUnit_det] at h
    simpa [rankOneBoundary] using (isUnit_iff_ne_zero.mp h)
  · intro h
    exact rankOneBoundary_isUnit h

/-- With a positive definite kernel block, semidefiniteness is exactly the nonnegative
scalar shadow condition. -/
theorem rankOneScalarShadowBlock_posSemidef_iff (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ)
    (hB : B.PosDef) :
    (rankOneScalarShadowBlock B ell a t).PosSemidef ↔ 0 ≤ rankOneScalarShadow B ell a t := by
  letI : Invertible B := hB.isUnit.invertible
  unfold rankOneScalarShadowBlock
  rw [Matrix.PosDef.fromBlocks₁₁ (rankOneChannel ell) (rankOneBoundary (a + t)) hB]
  rw [rankOneScalarShadow_blockSchur B ell a t hB.isHermitian]
  exact rankOneBoundary_posSemidef_iff

theorem rankOneScalarShadowBlock_isUnit_iff (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ)
    (hB : B.PosDef) :
    IsUnit (rankOneScalarShadowBlock B ell a t) ↔
      IsUnit (rankOneBoundary (rankOneScalarShadow B ell a t)) := by
  letI : Invertible B := hB.isUnit.invertible
  unfold rankOneScalarShadowBlock
  have hunit : IsUnit (Matrix.fromBlocks B (rankOneChannel ell) (rankOneChannel ell)ᴴ
      (rankOneBoundary (a + t))) ↔
      IsUnit (rankOneBoundary (a + t) - (rankOneChannel ell)ᴴ * B⁻¹ * rankOneChannel ell) := by
    simpa using (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
      (A := B) (B := rankOneChannel ell) (C := (rankOneChannel ell)ᴴ)
        (D := rankOneBoundary (a + t)))
  rw [rankOneScalarShadow_blockSchur B ell a t hB.isHermitian] at hunit
  exact hunit

/-- With a positive definite kernel block, positive definiteness is exactly strict positivity
of the scalar shadow. -/
theorem rankOneScalarShadowBlock_posDef_iff (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ)
    (hB : B.PosDef) :
    (rankOneScalarShadowBlock B ell a t).PosDef ↔ 0 < rankOneScalarShadow B ell a t := by
  constructor
  · intro h
    have hnonneg : 0 ≤ rankOneScalarShadow B ell a t :=
      (rankOneScalarShadowBlock_posSemidef_iff B ell a t hB).mp h.posSemidef
    have hunit : IsUnit (rankOneBoundary (rankOneScalarShadow B ell a t)) :=
      (rankOneScalarShadowBlock_isUnit_iff B ell a t hB).mp h.isUnit
    have hne : rankOneScalarShadow B ell a t ≠ 0 :=
      rankOneBoundary_isUnit_iff.mp hunit
    exact lt_of_le_of_ne hnonneg hne.symm
  · intro h
    have hPSD : (rankOneScalarShadowBlock B ell a t).PosSemidef :=
      (rankOneScalarShadowBlock_posSemidef_iff B ell a t hB).mpr h.le
    have hunit : IsUnit (rankOneScalarShadowBlock B ell a t) :=
      (rankOneScalarShadowBlock_isUnit_iff B ell a t hB).mpr
        (rankOneBoundary_isUnit_iff.mpr h.ne')
    exact hPSD.posDef_iff_isUnit.mpr hunit

/-- Complete Schur gate in supplied split coordinates. -/
theorem rankOneScalarShadow_splitCertificate (B : Matrix E E ℂ) (ell : E → ℂ) (a t : ℝ)
    (hB : B.PosDef) :
    ((rankOneScalarShadowBlock B ell a t).PosSemidef ↔
      0 ≤ rankOneScalarShadow B ell a t) ∧
      ((rankOneScalarShadowBlock B ell a t).PosDef ↔
        0 < rankOneScalarShadow B ell a t) :=
  ⟨rankOneScalarShadowBlock_posSemidef_iff B ell a t hB,
    rankOneScalarShadowBlock_posDef_iff B ell a t hB⟩

omit [Fintype E] [DecidableEq E] in
/-- A positive-semidefinite block form has a positive-semidefinite kernel principal block. -/
theorem rankOneScalarShadowBlock_principal_posSemidef {B : Matrix E E ℂ} {ell : E → ℂ}
    {a t : ℝ} (hH : (rankOneScalarShadowBlock B ell a t).PosSemidef) : B.PosSemidef := by
  have hsub := hH.submatrix Sum.inl
  have hEq : (rankOneScalarShadowBlock B ell a t).submatrix Sum.inl Sum.inl = B := by
    ext i j
    simp [rankOneScalarShadowBlock, Matrix.fromBlocks_apply₁₁]
  rw [hEq] at hsub
  exact hsub

omit [Fintype E] [DecidableEq E] in
/-- A positive-definite block form has a positive-definite kernel principal block. -/
theorem rankOneScalarShadowBlock_principal_posDef {B : Matrix E E ℂ} {ell : E → ℂ}
    {a t : ℝ} (hH : (rankOneScalarShadowBlock B ell a t).PosDef) : B.PosDef := by
  have hsub := hH.submatrix Sum.inl_injective
  have hEq : (rankOneScalarShadowBlock B ell a t).submatrix Sum.inl Sum.inl = B := by
    ext i j
    simp [rankOneScalarShadowBlock, Matrix.fromBlocks_apply₁₁]
  rw [hEq] at hsub
  exact hsub

/-- In split order `ker β ⊕ ℂq`, the scalar can be positive while the kernel block is negative. -/
def rankOneScalarShadowCounterexampleBlock :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  rankOneScalarShadowBlock (rankOneBoundary (-1)) (fun _ => 0) (-1) 2

theorem rankOneScalarShadowCounterexample_scalar :
    rankOneScalarShadow (rankOneBoundary (-1)) (fun _ => 0) (-1) 2 = 1 := by
  norm_num [rankOneScalarShadow, rankOneEnergy, Matrix.mulVec, dotProduct]

theorem rankOneScalarShadowCounterexample_not_posSemidef :
    ¬ rankOneScalarShadowCounterexampleBlock.PosSemidef := by
  intro h
  have hB : (rankOneBoundary (-1)).PosSemidef := by
    simpa [rankOneScalarShadowCounterexampleBlock] using
      rankOneScalarShadowBlock_principal_posSemidef h
  have : (0 : ℝ) ≤ -1 := rankOneBoundary_posSemidef_iff.mp hB
  norm_num at this

end

end GaloisForLFunctions.HTGeometry
