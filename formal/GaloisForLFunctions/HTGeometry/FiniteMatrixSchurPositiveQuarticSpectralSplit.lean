import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticDivisorCharge
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant

/-!
# Finite-matrix Schur positive quartic spectral split

The positive quartic charge of a Schur diagonal has a dimension-free spectral-tail estimate.
Small eigenvalues are controlled by their squared norm and large eigenvalues by their squared
imaginary part.  Splitting at thresholds `δ` and `η` bounds total charge by

`2300 * (δ + η) * matHSNormSq M`.

No normality, eigenvalue multiplicity bound, or dimension bound is required.
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Local quartic charge is controlled by the square of the node's squared norm. -/
theorem sourcePairPositiveQuarticCharge_le_normSq_sq (z : ℂ) :
    sourcePairPositiveQuarticCharge z.re z.im ≤
      2300 * Complex.normSq z ^ (2 : ℕ) := by
  have hdiff :
      2300 * Complex.normSq z ^ (2 : ℕ) -
          sourcePairPositiveQuarticCharge z.re z.im =
        2300 * (z.re ^ (2 : ℕ)) ^ (2 : ℕ) + 4000 * z.re ^ (2 : ℕ) * z.im ^ (2 : ℕ) := by
    rw [sourcePairPositiveQuarticCharge, Complex.normSq_apply]
    ring
  rw [← sub_nonneg]
  rw [hdiff]
  positivity

/-- Local quartic charge is controlled by squared norm times squared imaginary part. -/
theorem sourcePairPositiveQuarticCharge_le_normSq_mul_im_sq (z : ℂ) :
    sourcePairPositiveQuarticCharge z.re z.im ≤
      2300 * Complex.normSq z * z.im ^ (2 : ℕ) := by
  have hdiff :
      2300 * Complex.normSq z * z.im ^ (2 : ℕ) -
          sourcePairPositiveQuarticCharge z.re z.im =
        1700 * z.re ^ (2 : ℕ) * z.im ^ (2 : ℕ) := by
    rw [sourcePairPositiveQuarticCharge, Complex.normSq_apply]
    ring
  rw [← sub_nonneg]
  rw [hdiff]
  positivity

/-- Portion of Schur quartic charge carried by diagonal eigenvalues whose squared norm is at most
`δ`. -/
def finiteMatrixSchurPositiveQuarticSmallSpectrumCharge
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (δ : ℝ) (S : FiniteMatrixSchurPacket M) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => Complex.normSq (S.T i i) ≤ δ),
    sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im

/-- Small Schur eigenvalues carry at most `2300 * δ` times matrix Hilbert--Schmidt energy.
The estimate is independent of matrix dimension. -/
theorem finiteMatrixSchurPositiveQuarticSmallSpectrumCharge_le
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (δ : ℝ) (hδ : 0 ≤ δ) (S : FiniteMatrixSchurPacket M) :
    finiteMatrixSchurPositiveQuarticSmallSpectrumCharge δ S ≤
      2300 * δ * matHSNormSq M := by
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i => Complex.normSq (S.T i i) ≤ δ)
  have hpoint : ∀ i ∈ s,
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        2300 * δ * Complex.normSq (S.T i i) := by
    intro i hi
    have hiδ : Complex.normSq (S.T i i) ≤ δ := (Finset.mem_filter.mp hi).2
    calc
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
          2300 * Complex.normSq (S.T i i) ^ (2 : ℕ) :=
        sourcePairPositiveQuarticCharge_le_normSq_sq _
      _ ≤ 2300 * δ * Complex.normSq (S.T i i) := by
        have hn := Complex.normSq_nonneg (S.T i i)
        nlinarith
  have hsum :
      (∑ i ∈ s, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤
        ∑ i ∈ s, 2300 * δ * Complex.normSq (S.T i i) := by
    exact Finset.sum_le_sum fun i hi => hpoint i hi
  have hfilter :
      (∑ i ∈ s, Complex.normSq (S.T i i)) ≤
        ∑ i, Complex.normSq (S.T i i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Complex.normSq_nonneg (S.T i i))
  have hschur :
      (∑ i, Complex.normSq (S.T i i)) ≤ matHSNormSq M := by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_matrix
  unfold finiteMatrixSchurPositiveQuarticSmallSpectrumCharge
  change (∑ i ∈ s, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤ _
  calc
    (∑ i ∈ s, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤
        ∑ i ∈ s, 2300 * δ * Complex.normSq (S.T i i) := hsum
    _ = 2300 * δ * ∑ i ∈ s, Complex.normSq (S.T i i) := by
      rw [Finset.mul_sum]
    _ ≤ 2300 * δ * ∑ i, Complex.normSq (S.T i i) := by
      exact mul_le_mul_of_nonneg_left hfilter (mul_nonneg (by norm_num) hδ)
    _ ≤ 2300 * δ * matHSNormSq M := by
      exact mul_le_mul_of_nonneg_left hschur (mul_nonneg (by norm_num) hδ)

/-- Dimension-free spectral split.  If every Schur eigenvalue above squared-norm threshold `δ`
has squared imaginary part at most `η`, total positive quartic charge is bounded by
`2300 * (δ + η)` times matrix Hilbert--Schmidt energy. -/
theorem finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (S : FiniteMatrixSchurPacket M)
    (hlarge : ∀ i, δ < Complex.normSq (S.T i i) → (S.T i i).im ^ (2 : ℕ) ≤ η) :
    finiteMatrixSchurPositiveQuarticCharge S ≤
      2300 * (δ + η) * matHSNormSq M := by
  have hpoint : ∀ i,
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        2300 * (δ + η) * Complex.normSq (S.T i i) := by
    intro i
    have hn : 0 ≤ Complex.normSq (S.T i i) := Complex.normSq_nonneg _
    by_cases hsmall : Complex.normSq (S.T i i) ≤ δ
    · calc
        sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
            2300 * Complex.normSq (S.T i i) ^ (2 : ℕ) :=
          sourcePairPositiveQuarticCharge_le_normSq_sq _
        _ ≤ 2300 * δ * Complex.normSq (S.T i i) := by nlinarith
        _ ≤ 2300 * (δ + η) * Complex.normSq (S.T i i) := by nlinarith
    · have him : (S.T i i).im ^ (2 : ℕ) ≤ η := hlarge i (lt_of_not_ge hsmall)
      calc
        sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
            2300 * Complex.normSq (S.T i i) * (S.T i i).im ^ (2 : ℕ) :=
          sourcePairPositiveQuarticCharge_le_normSq_mul_im_sq _
        _ ≤ 2300 * Complex.normSq (S.T i i) * η := by nlinarith
        _ ≤ 2300 * (δ + η) * Complex.normSq (S.T i i) := by nlinarith
  have hsum :
      (∑ i, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤
        ∑ i, 2300 * (δ + η) * Complex.normSq (S.T i i) :=
    Finset.sum_le_sum fun i _ => hpoint i
  have hschur :
      (∑ i, Complex.normSq (S.T i i)) ≤ matHSNormSq M := by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_diag_normSq_le_matHSNormSq S.unitary_right S.conjugates_matrix
  unfold finiteMatrixSchurPositiveQuarticCharge finitePacketPositiveQuarticCharge
  calc
    (∑ i, sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im) ≤
        ∑ i, 2300 * (δ + η) * Complex.normSq (S.T i i) := hsum
    _ = 2300 * (δ + η) * ∑ i, Complex.normSq (S.T i i) := by
      rw [Finset.mul_sum]
    _ ≤ 2300 * (δ + η) * matHSNormSq M := by
      exact mul_le_mul_of_nonneg_left hschur
        (mul_nonneg (by norm_num) (add_nonneg hδ hη))

end

end GaloisForLFunctions.HTGeometry
