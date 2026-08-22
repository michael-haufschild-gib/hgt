/-
# The sorted spectrum of a linear Hermitian family scales with its coefficients

Scaling the coefficient vector of a real-linear Hermitian family scales the matrix, hence every
power sum of its spectrum.  Monotone tuples with equal power sums coincide, so the increasing
rearrangement of the spectrum scales exactly -- unlike the canonical eigenvalue tuple, whose
labelling is a choice.  Consequently the anchored gap ratios, being quotients of two gaps, are
invariant under positive rescaling of the coefficients: the projective spectral data of a linear
family lives on the coefficient sphere.

Main results:
* `sortedTuple_eigenvalues_real_smul` — the increasing rearrangement of a Hermitian spectrum scales.
* `sortedEnsembleSpectrum_const_mul` — the same for a linear family in its coefficients.
* `anchoredGapRatioMap_sortedEnsembleSpectrum_const_mul` — **the anchored gap ratios are radial**.
-/
import GaloisForLFunctions.HTGeometry.ShellCoeffScaling
import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality
import GaloisForLFunctions.HTGeometry.AngularPhaseLaw

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D N : ℕ}

/-- **The increasing rearrangement of a Hermitian spectrum scales with the matrix.** -/
theorem sortedTuple_eigenvalues_real_smul {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian)
    {t : ℝ} (ht : 0 < t) (hHt : (((t : ℝ) : ℂ) • H).IsHermitian) :
    sortedTuple hHt.eigenvalues = fun j => t * sortedTuple hH.eigenvalues j := by
  refine eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) ?_ ?_
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (monotone_sortedTuple _ hij) ht.le
  · intro p
    rw [sum_pow_sortedTuple, sum_pow_eigenvalues_smul hH t hHt p]
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_pow_sortedTuple]

variable {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- The canonically labelled spectrum of a linear Hermitian family scales with the coefficients. -/
theorem sortedEnsembleSpectrum_const_mul (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : 0 < t)
    (θ : Fin N → ℝ) :
    sortedEnsembleSpectrum hP (fun a => t * θ a)
      = fun j => t * sortedEnsembleSpectrum hP θ j := by
  have hsm : (spectralEnsembleMatrix P fun a => t * θ a)
      = (((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ := spectralEnsembleMatrix_smul P t θ
  have hherm : ((((t : ℝ) : ℂ)) • spectralEnsembleMatrix P θ).IsHermitian := by
    rw [← hsm]
    exact isHermitian_spectralEnsembleMatrix hP _
  have hev : (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues
      = hherm.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)) hherm).2
      (congrArg Matrix.charpoly hsm)
  show sortedTuple (isHermitian_spectralEnsembleMatrix hP (fun a => t * θ a)).eigenvalues = _
  rw [hev]
  exact sortedTuple_eigenvalues_real_smul (isHermitian_spectralEnsembleMatrix hP θ) ht hherm

theorem spectralTuple_eq_sortedEnsembleSpectrum (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    spectralTuple hP θ = sortedEnsembleSpectrum hP θ := rfl

/-- **The anchored gap ratios are invariant under positive rescaling of the coefficients.** -/
theorem anchoredGapRatioMap_sortedEnsembleSpectrum_const_mul {n : ℕ}
    (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : 0 < t) (θ : Fin N → ℝ)
    (anchor clock : Fin D) (ι : Fin n → Fin D) :
    anchoredGapRatioMap (sortedEnsembleSpectrum hP (fun a => t * θ a)) anchor clock ι
      = anchoredGapRatioMap (sortedEnsembleSpectrum hP θ) anchor clock ι := by
  funext k
  rw [anchoredGapRatioMap, anchoredGapRatioMap, sortedEnsembleSpectrum_const_mul hP ht]
  rw [show t * sortedEnsembleSpectrum hP θ (ι k) - t * sortedEnsembleSpectrum hP θ anchor
      = t * (sortedEnsembleSpectrum hP θ (ι k) - sortedEnsembleSpectrum hP θ anchor) from by ring,
    show t * sortedEnsembleSpectrum hP θ clock - t * sortedEnsembleSpectrum hP θ anchor
      = t * (sortedEnsembleSpectrum hP θ clock - sortedEnsembleSpectrum hP θ anchor) from by ring,
    mul_div_mul_left _ _ ht.ne']


/-- Positive rescaling of the coefficients preserves simplicity of the spectrum. -/
theorem mem_simpleEnsembleLocus_const_mul_iff (hP : ∀ a, (P a).IsHermitian) {t : ℝ} (ht : 0 < t)
    (θ : Fin N → ℝ) :
    (fun a => t * θ a) ∈ simpleEnsembleLocus hP ↔ θ ∈ simpleEnsembleLocus hP := by
  have hiff : ∀ φ : Fin N → ℝ, φ ∈ simpleEnsembleLocus hP
      ↔ Function.Injective (sortedEnsembleSpectrum hP φ) := by
    intro φ
    exact injective_iff_injective_sortedTuple _
  rw [hiff, hiff, sortedEnsembleSpectrum_const_mul hP ht]
  constructor
  · intro h i j hij
    exact h (by simpa using congrArg (fun z : ℝ => t * z) hij)
  · intro h i j hij
    exact h (mul_left_cancel₀ ht.ne' hij)

end

end GaloisForLFunctions.HTGeometry
