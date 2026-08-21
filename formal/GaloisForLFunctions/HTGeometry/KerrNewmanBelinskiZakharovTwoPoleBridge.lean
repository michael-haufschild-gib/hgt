import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Aligned two-pole Belinski--Zakharov dressing

Two one-pole BZ dressings with residues in the same canonical nilpotent
direction commute. Their product is one unipotent shear whose coefficient is
the sum of the two rational pole coefficients. Consequently this aligned
two-pole sector preserves the Kerr--Newman Killing-block determinant but has no
nonabelian soliton interaction.

This is a finite algebraic model, not a construction of a general multipole BZ
inverse-scattering solution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix

/-- Product of two canonical one-pole BZ dressings at possibly different poles. -/
def belinskiZakharovTwoPoleDressing
    (spectral pole₁ residue₁ pole₂ residue₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovOnePoleDressing spectral pole₁ residue₁ *
    belinskiZakharovOnePoleDressing spectral pole₂ residue₂

/-- Aligned two-pole dressings collapse to one unipotent shear with the summed rational
coefficient. -/
theorem belinskiZakharovTwoPoleDressing_eq_unipotent
    (spectral pole₁ residue₁ pole₂ residue₂ : ℝ) :
    belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂ =
      belinskiZakharovUnipotentDressing
        (residue₁ / (spectral - pole₁) + residue₂ / (spectral - pole₂)) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [belinskiZakharovTwoPoleDressing, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [belinskiZakharovTwoPoleDressing, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [belinskiZakharovTwoPoleDressing, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [belinskiZakharovTwoPoleDressing, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, Matrix.mul_apply, Fin.sum_univ_two]

/-- Canonical one-pole BZ dressings commute even when their poles differ. -/
theorem belinskiZakharovOnePoleDressing_commute
    (spectral pole₁ residue₁ pole₂ residue₂ : ℝ) :
    belinskiZakharovOnePoleDressing spectral pole₁ residue₁ *
        belinskiZakharovOnePoleDressing spectral pole₂ residue₂ =
      belinskiZakharovOnePoleDressing spectral pole₂ residue₂ *
        belinskiZakharovOnePoleDressing spectral pole₁ residue₁ := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [belinskiZakharovOnePoleDressing, belinskiZakharovUnipotentDressing,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The aligned two-pole dressing remains unimodular. -/
theorem belinskiZakharovTwoPoleDressing_det
    (spectral pole₁ residue₁ pole₂ residue₂ : ℝ) :
    (belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂).det = 1 := by
  rw [belinskiZakharovTwoPoleDressing, Matrix.det_mul,
    belinskiZakharovOnePoleDressing_det, belinskiZakharovOnePoleDressing_det]
  norm_num

/-- Congruence by an aligned two-pole BZ dressing preserves the Kerr--Newman Killing-block
determinant exactly. -/
theorem belinskiZakharovTwoPoleDressedKerrNewmanKillingBlock_det
    (spectral pole₁ residue₁ pole₂ residue₂ mass spin charge radius polar : ℝ) :
    (belinskiZakharovDressing
      (belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂)
      (kerrNewmanKillingBlock mass spin charge radius polar)).det =
      (kerrNewmanKillingBlock mass spin charge radius polar).det := by
  rw [belinskiZakharovDressing_det, belinskiZakharovTwoPoleDressing_det]
  ring

/-- The aligned two-pole dressed Kerr--Newman Killing block remains symmetric. -/
theorem belinskiZakharovTwoPoleDressedKerrNewmanKillingBlock_transpose
    (spectral pole₁ residue₁ pole₂ residue₂ mass spin charge radius polar : ℝ) :
    Matrix.transpose (belinskiZakharovDressing
      (belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂)
      (kerrNewmanKillingBlock mass spin charge radius polar)) =
      belinskiZakharovDressing
        (belinskiZakharovTwoPoleDressing spectral pole₁ residue₁ pole₂ residue₂)
        (kerrNewmanKillingBlock mass spin charge radius polar) := by
  simp only [belinskiZakharovDressing, Matrix.transpose_mul,
    Matrix.transpose_transpose, kerrNewmanKillingBlock_transpose]
  rw [Matrix.mul_assoc]

end

end GaloisForLFunctions.HTGeometry
