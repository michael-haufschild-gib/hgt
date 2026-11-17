import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold

/-!
# Separating column means with one spectral penalty

Subtracting each column's mean is orthogonal projection away from the constant
row vector. The column Gram splits exactly into centered covariance and a
positive matrix of rank at most one. Clipped energy therefore charges only one
cutoff square for the complete vector of column means.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty ι]

def columnMean (A : Matrix ι κ ℂ) (j : κ) : ℂ := (∑ i, A i j) / (Fintype.card ι : ℂ)
def meanColumns (A : Matrix ι κ ℂ) : Matrix ι κ ℂ := fun _ j => columnMean A j
def centeredColumns (A : Matrix ι κ ℂ) : Matrix ι κ ℂ := A - meanColumns A

theorem sum_centeredColumns (A : Matrix ι κ ℂ) (j : κ) : ∑ i, centeredColumns A i j = 0 := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [centeredColumns, Matrix.sub_apply, meanColumns, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, columnMean]
  field_simp [hn]
  ring

theorem centeredColumns_gram_decomposition (A : Matrix ι κ ℂ) :
    Aᴴ * A = (centeredColumns A)ᴴ * centeredColumns A + (meanColumns A)ᴴ * meanColumns A := by
  have hcross : (meanColumns A)ᴴ * centeredColumns A = 0 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, meanColumns,
      ← Finset.mul_sum, sum_centeredColumns, mul_zero, Matrix.zero_apply]
  have hcross' : (centeredColumns A)ᴴ * meanColumns A = 0 := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have hA : A = centeredColumns A + meanColumns A := by rw [centeredColumns]; abel
  calc
    _ = (centeredColumns A + meanColumns A)ᴴ * (centeredColumns A + meanColumns A) := by
      conv_lhs => rw [hA]
    _ = _ := by
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        hcross, hcross']
      abel

theorem meanColumns_gram_rank_le_one (A : Matrix ι κ ℂ) :
    ((meanColumns A)ᴴ * meanColumns A).rank ≤ 1 := by
  have he : meanColumns A = Matrix.vecMulVec (fun _ : ι => (1 : ℂ)) (columnMean A) := by
    ext i j
    simp only [meanColumns, Matrix.vecMulVec, Matrix.of_apply, one_mul]
  calc
    _ ≤ (meanColumns A).rank := Matrix.rank_mul_le_right _ _
    _ ≤ 1 := by
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _

omit [DecidableEq κ] [Nonempty ι] in
theorem meanColumns_gram_trace (A : Matrix ι κ ℂ) :
    (trace ((meanColumns A)ᴴ * meanColumns A)).re =
      Fintype.card ι * (∑ j, Complex.normSq (columnMean A j)) := by
  simp only [trace, diag, Matrix.mul_apply, Matrix.conjTranspose_apply, meanColumns,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Finset.mul_sum]

/-- Centered covariance retains its clipped energy, while all column means together
pay at most one cutoff-square penalty. -/
theorem centeredColumns_clipped_threshold (A : Matrix ι κ ℂ) (c : ℝ) :
    energy c ((centeredColumns A)ᴴ * centeredColumns A) +
      2 * c * (Fintype.card ι * (∑ j, Complex.normSq (columnMean A j))) - c ^ 2 ≤
        (trace ((Aᴴ * A) * (Aᴴ * A))).re := by
  have hE := Matrix.posSemidef_conjTranspose_mul_self (centeredColumns A)
  have hM := Matrix.posSemidef_conjTranspose_mul_self (meanColumns A)
  have h := threshold hE hM.isHermitian c
  have hr : (posIndex hM.isHermitian : ℝ) ≤ 1 := by
    rw [posIndex_eq_rank_of_posSemidef hM]
    exact_mod_cast meanColumns_gram_rank_le_one A
  have hc := mul_le_mul_of_nonneg_left hr (sq_nonneg c)
  rw [← centeredColumns_gram_decomposition, meanColumns_gram_trace] at h
  linarith only [h, hc]

#print axioms centeredColumns_gram_decomposition
#print axioms meanColumns_gram_rank_le_one
#print axioms centeredColumns_clipped_threshold

end
end GaloisForLFunctions.HilbertMetric.Clipped
