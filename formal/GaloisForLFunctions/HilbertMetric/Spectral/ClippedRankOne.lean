import GaloisForLFunctions.HilbertMetric.Spectral.ClippedTrace

/-!
# Rank-one spectra and coherent first moments

The spectrum of `u u*` records only `∑ |uᵢ|²`. Clipping therefore forgets
relative phases. Pairing with the constant vector retains `|∑ uᵢ|²`, and the
pairwise squared differences give its exact deficit from maximal coherence.
-/

open Matrix
open scoped ComplexConjugate NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The covariance of a single complex column. -/
def columnCovariance (u : ι → ℂ) : Matrix ι ι ℂ := fun i j => u i * conj (u j)

/-- Every spectral sum of a rank-one covariance is determined by its total mass,
including the correction for zero eigenvalues in an empty ambient space. -/
theorem spectralSum_columnCovariance (f : ℝ → ℝ) (u : ι → ℂ) :
    spectralSum f (columnCovariance u) + f 0 =
      f (∑ i, Complex.normSq (u i)) + Fintype.card ι * f 0 := by
  let A : Matrix ι Unit ℂ := fun i _ => u i
  have hAA : A * Aᴴ = columnCovariance u := by
    ext i j
    simp [A, Matrix.mul_apply, columnCovariance]
  have hA : Aᴴ * A = diagonal (fun _ : Unit => ((∑ i, Complex.normSq (u i) : ℝ) : ℂ)) := by
    ext i j
    cases i
    cases j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, A, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, Matrix.diagonal_apply_eq]
  have h := spectralSum_rectangular f A Aᴴ
  rw [hAA, hA, spectralSum_diagonal] at h
  simpa using h

/-- Clipping a single coherent column costs exactly one scalar clipped mass. -/
theorem energy_columnCovariance (u : ι → ℂ) (c : ℝ≥0) :
    energy c (columnCovariance u) = quadratic c (∑ i, Complex.normSq (u i)) := by
  have hz : quadratic c 0 = 0 := by rw [quadratic_of_le c.coe_nonneg]; ring
  simpa only [energy, hz, mul_zero, add_zero] using
    spectralSum_columnCovariance (quadratic c) u

/-- Equal column masses give every spectral statistic the same value. -/
theorem spectralSum_columnCovariance_eq {u v : ι → ℂ}
    (h : (∑ i, Complex.normSq (u i)) = ∑ i, Complex.normSq (v i)) (f : ℝ → ℝ) :
    spectralSum f (columnCovariance u) = spectralSum f (columnCovariance v) := by
  have hu := spectralSum_columnCovariance f u
  have hv := spectralSum_columnCovariance f v
  rw [h] at hu
  linarith only [hu, hv]

/-- Replacing every entry by its modulus preserves all covariance spectral sums. -/
theorem spectralSum_columnCovariance_abs (u : ι → ℂ) (f : ℝ → ℝ) :
    spectralSum f (columnCovariance u) =
      spectralSum f (columnCovariance (fun i => (‖u i‖ : ℂ))) := by
  apply spectralSum_columnCovariance_eq
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq_eq_norm_sq]

/-- All unimodular phase choices have the same clipped covariance energy. -/
theorem energy_columnCovariance_of_normSq_one (u : ι → ℂ)
    (hu : ∀ i, Complex.normSq (u i) = 1) (c : ℝ≥0) :
    energy c (columnCovariance u) = quadratic c (Fintype.card ι) := by
  rw [energy_columnCovariance]
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

omit [DecidableEq ι] in
/-- Pairing the covariance with the constant vector recovers the squared first moment. -/
theorem sum_columnCovariance (u : ι → ℂ) :
    (∑ i, ∑ j, columnCovariance u i j) = (Complex.normSq (∑ i, u i) : ℂ) := by
  simp only [columnCovariance, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum,
    Complex.mul_conj]

omit [DecidableEq ι] in
/-- Exact loss of coherent first-moment mass, before taking any spectral invariant. -/
theorem coherence_deficit (u : ι → ℂ) :
    (∑ i, ∑ j, Complex.normSq (u i - u j)) =
      2 * Fintype.card ι * (∑ i, Complex.normSq (u i)) -
        2 * Complex.normSq (∑ i, u i) := by
  have hsub (i j : ι) : Complex.normSq (u i - u j) =
      Complex.normSq (u i) + Complex.normSq (u j) -
        2 * (columnCovariance u i j).re := Complex.normSq_sub _ _
  simp_rw [hsub]
  have hpair := congrArg Complex.re (sum_columnCovariance u)
  simp only [Complex.re_sum, Complex.ofReal_re] at hpair
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hpair]
  ring

omit [DecidableEq ι] in
/-- Maximal first-moment mass occurs exactly when every entry has the same amplitude and phase. -/
theorem maximal_coherence_iff (u : ι → ℂ) :
    Complex.normSq (∑ i, u i) = Fintype.card ι * (∑ i, Complex.normSq (u i)) ↔
      ∀ i j, u i = u j := by
  have h := coherence_deficit u
  constructor
  · intro heq
    have hz : (∑ i, ∑ j, Complex.normSq (u i - u j)) = 0 := by linarith only [h, heq]
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (u i - u j))).mp hz
    intro i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (u i - u j))).mp (hs i (Finset.mem_univ i))
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (hj j (Finset.mem_univ j)))
  · intro heq
    have hz : (∑ i, ∑ j, Complex.normSq (u i - u j)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [heq i j, sub_self, map_zero]
    linarith only [h, hz]

#print axioms spectralSum_columnCovariance
#print axioms energy_columnCovariance
#print axioms maximal_coherence_iff

end
end GaloisForLFunctions.HilbertMetric.Clipped
