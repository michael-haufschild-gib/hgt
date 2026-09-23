import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurQuarticQuadraticTraceEnergyDefect

/-!
# Finite Schur quartic skew-adjoint defect

The quadratic trace-energy defect has the coefficient-only normal form

`matHSNormSq M - Re (trace (M^(2 : ℕ))) = (1/2) * matHSNormSq (M - Mᴴ)`.

Thus positive Schur quartic charge is controlled by squared Hilbert--Schmidt distance to the
Hermitian locus:

`charge ≤ 575 * matHSNormSq M * matHSNormSq (M - Mᴴ)`.

This identifies the exact overstrength in the raw quadratic producer.  It asks a general matrix to
become Hermitian, while real spectrum alone permits nonnormal Jordan blocks.
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared Hilbert--Schmidt energy of the skew-adjoint part of a finite matrix. -/
def finiteMatrixSkewAdjointEnergy
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  matHSNormSq (M - Mᴴ)

private theorem norm_sub_conj_sq (a b : ℂ) :
    ‖a - (starRingEnd ℂ) b‖ ^ (2 : ℕ) =
      ‖a‖ ^ (2 : ℕ) + ‖b‖ ^ (2 : ℕ) - 2 * (a * b).re := by
  simp only [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.mul_re]
  ring

/-- Exact coefficient-only normal form of the quadratic trace-energy defect. -/
theorem finiteMatrixQuadraticTraceEnergyDefect_eq_half_skewAdjointEnergy
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    finiteMatrixQuadraticTraceEnergyDefect M =
      (1 / 2 : ℝ) * finiteMatrixSkewAdjointEnergy M := by
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, ‖M j i‖ ^ (2 : ℕ)) =
        ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ (2 : ℕ) := by
    rw [Finset.sum_comm]
  have hmul :
      (∑ i : Fin n, ∑ j : Fin n, 2 * (M i j * M j i).re) =
        2 * (∑ i : Fin n, ∑ j : Fin n, (M i j * M j i).re) := by
    simp only [Finset.mul_sum]
  unfold finiteMatrixQuadraticTraceEnergyDefect finiteMatrixSkewAdjointEnergy matHSNormSq
  rw [pow_two M]
  rw [Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum,
    Matrix.sub_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  simp_rw [norm_sub_conj_sq]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap, hmul]
  ring

theorem finiteMatrixSkewAdjointEnergy_nonneg
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ finiteMatrixSkewAdjointEnergy M := by
  exact matHSNormSq_nonneg _

/-- Root-free quartic majorant by ordinary skew-adjoint Hilbert--Schmidt energy. -/
theorem finiteMatrixSchurPositiveQuarticCharge_le_skewAdjointEnergy
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    finiteMatrixSchurPositiveQuarticCharge S ≤
      575 * matHSNormSq M * finiteMatrixSkewAdjointEnergy M := by
  calc
    finiteMatrixSchurPositiveQuarticCharge S ≤
        1150 * matHSNormSq M * finiteMatrixQuadraticTraceEnergyDefect M :=
      finiteMatrixSchurPositiveQuarticCharge_le_quadraticTraceEnergyDefect S
    _ = 575 * matHSNormSq M * finiteMatrixSkewAdjointEnergy M := by
      rw [finiteMatrixQuadraticTraceEnergyDefect_eq_half_skewAdjointEnergy]
      ring

theorem quadraticTraceEnergyDefectJordanBlock_skewAdjointEnergy_eq_two :
    finiteMatrixSkewAdjointEnergy quadraticTraceEnergyDefectJordanBlock = 2 := by
  have h := finiteMatrixQuadraticTraceEnergyDefect_eq_half_skewAdjointEnergy
    quadraticTraceEnergyDefectJordanBlock
  rw [quadraticTraceEnergyDefectJordanBlock_defect_eq_one] at h
  linarith

/-- The skew-adjoint majorant is sufficient but not necessary for zero quartic charge. -/
theorem skewAdjointEnergy_not_necessary_for_zero_schurQuarticCharge :
    finiteMatrixSchurPositiveQuarticCharge
        quadraticTraceEnergyDefectJordanSchurPacket = 0 ∧
      0 < finiteMatrixSkewAdjointEnergy quadraticTraceEnergyDefectJordanBlock := by
  rw [quadraticTraceEnergyDefectJordanBlock_charge_zero,
    quadraticTraceEnergyDefectJordanBlock_skewAdjointEnergy_eq_two]
  norm_num

end

end GaloisForLFunctions.HTGeometry
