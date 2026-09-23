import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticSpectralSplit

/-!
# Finite Schur quartic quadratic trace-energy defect

The root-free quadratic defect

`matHSNormSq M - Re (trace (M^(2 : ℕ)))`

splits exactly, in Schur coordinates, into nonnormal off-diagonal energy plus twice the squared
imaginary mass of the spectrum.  The second term quantitatively controls positive quartic charge,
giving the dimension-free estimate

`charge ≤ 1150 * matHSNormSq M * quadraticTraceEnergyDefect M`.

The full quadratic defect is sufficient but not necessary for real spectrum: a nilpotent Jordan
block has zero Schur quartic charge and quadratic defect one.  Thus a quadratic source producer must
separate transverse spectral energy from nonnormal Schur energy.
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Root-free quadratic trace-energy defect of a finite complex matrix. -/
def finiteMatrixQuadraticTraceEnergyDefect
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  matHSNormSq M - ((M ^ (2 : ℕ)).trace).re

/-- Schur off-diagonal energy: total matrix energy minus spectral diagonal energy. -/
def finiteMatrixSchurNonnormalEnergy
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) : ℝ :=
  matHSNormSq M - ∑ i, Complex.normSq (S.T i i)

/-- Twice the squared imaginary mass of a Schur spectral packet. -/
def finiteMatrixSchurTransverseQuadraticEnergy
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) : ℝ :=
  2 * ∑ i, (S.T i i).im ^ (2 : ℕ)

theorem trace_sq_re_eq_sum_schur_normSq_sub_two_im_sq
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    ((M ^ (2 : ℕ)).trace).re =
      ∑ i, (Complex.normSq (S.T i i) - 2 * (S.T i i).im ^ (2 : ℕ)) := by
  rw [trace_pow_eq_sum_diag S.unitary_left S.unitary_right S.triangular
    S.conjugates_matrix 2]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  simp [pow_two, Complex.mul_re]
  ring

/-- Exact decomposition of the quadratic trace-energy defect into nonnormal and transverse
spectral energy. -/
theorem finiteMatrixQuadraticTraceEnergyDefect_eq_schur_decomposition
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    finiteMatrixQuadraticTraceEnergyDefect M =
      finiteMatrixSchurNonnormalEnergy S +
        finiteMatrixSchurTransverseQuadraticEnergy S := by
  rw [finiteMatrixQuadraticTraceEnergyDefect, finiteMatrixSchurNonnormalEnergy,
    finiteMatrixSchurTransverseQuadraticEnergy,
    trace_sq_re_eq_sum_schur_normSq_sub_two_im_sq S,
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem finiteMatrixSchurNonnormalEnergy_nonneg
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    0 ≤ finiteMatrixSchurNonnormalEnergy S := by
  unfold finiteMatrixSchurNonnormalEnergy
  rw [sub_nonneg]
  simpa only [Complex.normSq_eq_norm_sq] using
    sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_matrix

theorem finiteMatrixSchurTransverseQuadraticEnergy_nonneg
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    0 ≤ finiteMatrixSchurTransverseQuadraticEnergy S := by
  unfold finiteMatrixSchurTransverseQuadraticEnergy
  positivity

theorem finiteMatrixQuadraticTraceEnergyDefect_nonneg
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    0 ≤ finiteMatrixQuadraticTraceEnergyDefect M := by
  rw [finiteMatrixQuadraticTraceEnergyDefect_eq_schur_decomposition S]
  exact add_nonneg (finiteMatrixSchurNonnormalEnergy_nonneg S)
    (finiteMatrixSchurTransverseQuadraticEnergy_nonneg S)

/-- Positive quartic charge is controlled sharply by transverse quadratic spectral energy and
total Hilbert--Schmidt energy. -/
theorem finiteMatrixSchurPositiveQuarticCharge_le_transverseQuadraticEnergy
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    finiteMatrixSchurPositiveQuarticCharge S ≤
      1150 * matHSNormSq M * finiteMatrixSchurTransverseQuadraticEnergy S := by
  have hdiagSum :
      (∑ i, Complex.normSq (S.T i i)) ≤ matHSNormSq M := by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_matrix
  have hpoint : ∀ i,
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        2300 * matHSNormSq M * (S.T i i).im ^ (2 : ℕ) := by
    intro i
    have hsingle :
        Complex.normSq (S.T i i) ≤ ∑ j, Complex.normSq (S.T j j) :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (S.T j j))
        (Finset.mem_univ i)
    have hiM := hsingle.trans hdiagSum
    have himsq : 0 ≤ (S.T i i).im ^ (2 : ℕ) := sq_nonneg _
    calc
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
          2300 * Complex.normSq (S.T i i) * (S.T i i).im ^ (2 : ℕ) :=
        sourcePairPositiveQuarticCharge_le_normSq_mul_im_sq _
      _ ≤ 2300 * matHSNormSq M * (S.T i i).im ^ (2 : ℕ) := by
        nlinarith
  unfold finiteMatrixSchurPositiveQuarticCharge finitePacketPositiveQuarticCharge
  rw [finiteMatrixSchurTransverseQuadraticEnergy]
  calc
    (∑ i, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤
        ∑ i, 2300 * matHSNormSq M * (S.T i i).im ^ (2 : ℕ) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = 1150 * matHSNormSq M * (2 * ∑ i, (S.T i i).im ^ (2 : ℕ)) := by
      rw [← Finset.mul_sum]
      ring

/-- Root-free corollary: full quadratic trace-energy defect controls positive quartic charge. -/
theorem finiteMatrixSchurPositiveQuarticCharge_le_quadraticTraceEnergyDefect
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    finiteMatrixSchurPositiveQuarticCharge S ≤
      1150 * matHSNormSq M * finiteMatrixQuadraticTraceEnergyDefect M := by
  have htrans :
      finiteMatrixSchurTransverseQuadraticEnergy S ≤
        finiteMatrixQuadraticTraceEnergyDefect M := by
    rw [finiteMatrixQuadraticTraceEnergyDefect_eq_schur_decomposition S]
    linarith [finiteMatrixSchurNonnormalEnergy_nonneg S]
  exact (finiteMatrixSchurPositiveQuarticCharge_le_transverseQuadraticEnergy S).trans
    (mul_le_mul_of_nonneg_left htrans
      (mul_nonneg (by norm_num) (matHSNormSq_nonneg M)))

/-- Minimal nonnormal real-spectrum witness for failure of necessity. -/
def quadraticTraceEnergyDefectJordanBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- Identity Schur packet of the upper-triangular Jordan witness. -/
def quadraticTraceEnergyDefectJordanSchurPacket :
    FiniteMatrixSchurPacket quadraticTraceEnergyDefectJordanBlock where
  U := 1
  T := quadraticTraceEnergyDefectJordanBlock
  unitary_left := by simp
  unitary_right := by simp
  triangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [quadraticTraceEnergyDefectJordanBlock] at hij ⊢
  conjugates_matrix := by simp

theorem quadraticTraceEnergyDefectJordanBlock_charge_zero :
    finiteMatrixSchurPositiveQuarticCharge
      quadraticTraceEnergyDefectJordanSchurPacket = 0 := by
  simp [finiteMatrixSchurPositiveQuarticCharge, finitePacketPositiveQuarticCharge,
    quadraticTraceEnergyDefectJordanSchurPacket, quadraticTraceEnergyDefectJordanBlock,
    sourcePairPositiveQuarticCharge]

theorem quadraticTraceEnergyDefectJordanBlock_defect_eq_one :
    finiteMatrixQuadraticTraceEnergyDefect quadraticTraceEnergyDefectJordanBlock = 1 := by
  simp [finiteMatrixQuadraticTraceEnergyDefect, matHSNormSq,
    quadraticTraceEnergyDefectJordanBlock, Matrix.trace, pow_two, Fin.sum_univ_two]

/-- Closed no-go: vanishing full quadratic trace-energy defect is sufficient but not necessary for
zero Schur quartic charge or real spectrum. -/
theorem quadraticTraceEnergyDefect_not_necessary_for_zero_schurQuarticCharge :
    finiteMatrixSchurPositiveQuarticCharge
        quadraticTraceEnergyDefectJordanSchurPacket = 0 ∧
      0 < finiteMatrixQuadraticTraceEnergyDefect quadraticTraceEnergyDefectJordanBlock := by
  rw [quadraticTraceEnergyDefectJordanBlock_charge_zero,
    quadraticTraceEnergyDefectJordanBlock_defect_eq_one]
  norm_num

end

end GaloisForLFunctions.HTGeometry
