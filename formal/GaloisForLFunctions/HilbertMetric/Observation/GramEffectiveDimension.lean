import GaloisForLFunctions.HTGeometry.FiniteMatrixShiftedResolvent
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gram effective dimension and its regularization geometry

The trace of the existing Gram resolvent cutoff is a sum of scalar spectral cutoffs.
Its logarithmic regularization derivative is negative. The slope is at most one quarter
of the state dimension, with an exact square defect and a rigid equality case.
-/

open scoped BigOperators Matrix ComplexOrder
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HilbertMetric.Observation
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

def gramEffectiveDimension (A : Matrix m n ℂ) (t : ℝ) : ℝ :=
  (finiteMatrixResolventCutoff (Aᴴ * A) (Real.exp t)).trace.re

def gramSpectrum (A : Matrix m n ℂ) : n → ℝ :=
  (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues

private theorem spectrum_nonneg (A : Matrix m n ℂ) (i : n) : 0 ≤ gramSpectrum A i :=
  (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i

theorem gramEffectiveDimension_spectral (A : Matrix m n ℂ) (t : ℝ) :
    gramEffectiveDimension A t = ∑ i, gramSpectrum A i / (gramSpectrum A i + Real.exp t) := by
  rw [gramEffectiveDimension, finiteMatrixResolventCutoff_trace_re
    (Matrix.posSemidef_conjTranspose_mul_self A) (Real.exp_pos t)]
  simp only [gramSpectrum, div_eq_mul_inv]

theorem gramEffectiveDimension_bounds (A : Matrix m n ℂ) (t : ℝ) :
    0 ≤ gramEffectiveDimension A t ∧ gramEffectiveDimension A t ≤ Fintype.card n := by
  rw [gramEffectiveDimension_spectral]
  constructor
  · exact Finset.sum_nonneg fun i _ => div_nonneg (spectrum_nonneg A i)
      (add_nonneg (spectrum_nonneg A i) (Real.exp_pos t).le)
  · calc
      _ ≤ ∑ _ : n, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (div_le_one (add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t))).mpr
          (le_add_of_nonneg_right (Real.exp_pos t).le)
      _ = _ := by simp

theorem gramEffectiveDimension_antitone (A : Matrix m n ℂ) : Antitone (gramEffectiveDimension A) := by
  intro t u htu
  rw [gramEffectiveDimension_spectral, gramEffectiveDimension_spectral]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (spectrum_nonneg A i)
    (add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t))
    (add_le_add_right (Real.exp_le_exp.mpr htu) _)

def gramDimensionSlope (A : Matrix m n ℂ) (t : ℝ) : ℝ :=
  ∑ i, gramSpectrum A i * Real.exp t / (gramSpectrum A i + Real.exp t) ^ 2

theorem gramEffectiveDimension_hasDerivAt (A : Matrix m n ℂ) (t : ℝ) :
    HasDerivAt (gramEffectiveDimension A) (-gramDimensionSlope A t) t := by
  have hd (i : n) : HasDerivAt (fun u : ℝ => gramSpectrum A i / (gramSpectrum A i + Real.exp u))
      (-(gramSpectrum A i * Real.exp t / (gramSpectrum A i + Real.exp t) ^ 2)) t := by
    have h := (hasDerivAt_const t (gramSpectrum A i)).fun_div
      ((Real.hasDerivAt_exp t).const_add (gramSpectrum A i))
      (add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t)).ne'
    convert! h using 1 <;> ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)
  simpa only [← gramEffectiveDimension_spectral, Finset.sum_neg_distrib, gramDimensionSlope] using hsum

theorem gramDimensionSlope_bounds (A : Matrix m n ℂ) (t : ℝ) :
    0 ≤ gramDimensionSlope A t ∧ gramDimensionSlope A t ≤ gramEffectiveDimension A t := by
  rw [gramEffectiveDimension_spectral]
  constructor
  · exact Finset.sum_nonneg fun i _ => div_nonneg
      (mul_nonneg (spectrum_nonneg A i) (Real.exp_pos t).le) (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro i _
    have hd : 0 < gramSpectrum A i + Real.exp t :=
      add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t)
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd).mpr
    nlinarith only [mul_nonneg (sq_nonneg (gramSpectrum A i)) hd.le]


theorem gramDimensionSlope_sharp_defect (A : Matrix m n ℂ) (t : ℝ) :
    (Fintype.card n : ℝ) / 4 - gramDimensionSlope A t =
      ∑ i, (gramSpectrum A i - Real.exp t) ^ 2 /
        (4 * (gramSpectrum A i + Real.exp t) ^ 2) := by
  have hc : (Fintype.card n : ℝ) / 4 = ∑ _ : n, (1 / 4 : ℝ) := by simp [div_eq_mul_inv]
  rw [hc, gramDimensionSlope, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd : gramSpectrum A i + Real.exp t ≠ 0 :=
    (add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t)).ne'
  field_simp
  ring

theorem gramDimensionSlope_le_card_quarter (A : Matrix m n ℂ) (t : ℝ) :
    gramDimensionSlope A t ≤ (Fintype.card n : ℝ) / 4 := by
  apply sub_nonneg.mp
  rw [gramDimensionSlope_sharp_defect]
  exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (by positivity)

theorem gramDimensionSlope_sharp_iff (A : Matrix m n ℂ) (t : ℝ) :
    gramDimensionSlope A t = (Fintype.card n : ℝ) / 4 ↔
      ∀ i, gramSpectrum A i = Real.exp t := by
  rw [eq_comm, ← sub_eq_zero, gramDimensionSlope_sharp_defect]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (by positivity))]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro i
  have hd : 4 * (gramSpectrum A i + Real.exp t) ^ 2 ≠ 0 := by
    positivity [spectrum_nonneg A i]
  rw [div_eq_zero_iff, or_iff_left hd, sq_eq_zero_iff, sub_eq_zero]


/-- Curvature changes sign as the regularization scale crosses each Gram eigenvalue. -/
theorem gramDimensionSlope_hasDerivAt (A : Matrix m n ℂ) (t : ℝ) :
    HasDerivAt (gramDimensionSlope A)
      (∑ i, gramSpectrum A i * Real.exp t * (gramSpectrum A i - Real.exp t) /
        (gramSpectrum A i + Real.exp t) ^ 3) t := by
  have hd (i : n) : HasDerivAt
      (fun u : ℝ => gramSpectrum A i * Real.exp u / (gramSpectrum A i + Real.exp u) ^ 2)
      (gramSpectrum A i * Real.exp t * (gramSpectrum A i - Real.exp t) /
        (gramSpectrum A i + Real.exp t) ^ 3) t := by
    have hn : gramSpectrum A i + Real.exp t ≠ 0 :=
      (add_pos_of_nonneg_of_pos (spectrum_nonneg A i) (Real.exp_pos t)).ne'
    have h := ((Real.hasDerivAt_exp t).const_mul (gramSpectrum A i)).fun_div
      (((Real.hasDerivAt_exp t).const_add (gramSpectrum A i)).pow 2) (pow_ne_zero _ hn)
    convert! h using 1
    field_simp
    ring
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)

#print axioms gramEffectiveDimension_bounds
#print axioms gramEffectiveDimension_antitone
#print axioms gramEffectiveDimension_hasDerivAt
#print axioms gramDimensionSlope_sharp_iff
#print axioms gramDimensionSlope_hasDerivAt

end
end GaloisForLFunctions.HilbertMetric.Observation
