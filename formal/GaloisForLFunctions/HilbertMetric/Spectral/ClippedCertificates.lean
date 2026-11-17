import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCongruence
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.RankTrace

/-!
# Scalar certificates and negative spectral energy

Diagonal dual certificates add without diagonalizing the matrix. At cutoff
zero the clipped energy is the squared negative spectrum: it vanishes exactly
on positive matrices and decreases under positive additions. A single scalar
negative direction is detected by some positive cutoff.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section

/-- The scalar clipped certificate detects exactly negative directions. -/
theorem scalar_negative_certificate_iff {p k : ℝ} (hp : 0 ≤ p) :
    (∃ c : ℝ, 0 < c ∧ (k - p) ^ 2 < quadratic c p - 2 * c * k) ↔ k < 0 := by
  constructor
  · rintro ⟨c, hc, h⟩
    by_contra hk
    have hk0 : 0 ≤ k := le_of_not_gt hk
    rcases le_total p c with hpc | hcp
    · rw [quadratic_of_le hpc] at h
      have hmul := mul_nonneg hk0 (sub_nonneg.mpr hpc)
      nlinarith only [h, hmul, sq_nonneg k]
    · rw [quadratic_of_ge hcp] at h
      nlinarith only [h, sq_nonneg (p - k - c)]
  · intro hk
    have hd : 0 < -2 * k := by linarith only [hk]
    let c := p + ((k - p) ^ 2 + 1) / (-2 * k)
    have hq : 0 < ((k - p) ^ 2 + 1) / (-2 * k) :=
      div_pos (by positivity) hd
    have hpc : p ≤ c := by dsimp [c]; linarith only [hq]
    have hid : c * (-2 * k) = p * (-2 * k) + (k - p) ^ 2 + 1 := by
      dsimp [c]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hd)]
      ring
    refine ⟨c, lt_of_le_of_lt hp (by dsimp [c]; linarith only [hq]), ?_⟩
    rw [quadratic_of_le hpc]
    have hmul := mul_nonneg hp hd.le
    nlinarith only [hid, hmul, sq_nonneg p]

theorem quadratic_zero (x : ℝ) : quadratic 0 x = (min x 0) ^ 2 := by
  rcases le_total x 0 with h | h
  · rw [quadratic_of_le h, min_eq_left h]
  · rw [quadratic_of_ge h, min_eq_right h]; ring

theorem quadratic_zero_eq_zero_iff (x : ℝ) : quadratic 0 x = 0 ↔ 0 ≤ x := by
  rw [quadratic_zero, sq_eq_zero_iff, min_eq_right_iff]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each diagonal entry supplies its own clipped dual certificate. -/
theorem diagonal_clipped_lower {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ) :
    (∑ i, quadratic c (A i i).re) ≤ energy c A := by
  let b : ι → ℝ := fun i => min (A i i).re c
  have hcap : ((c : ℂ) • (1 : Matrix ι ι ℂ) - realDiagonal b).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal]
    change (diagonal (fun _ : ι => (c : ℂ)) - diagonal (fun i => (b i : ℂ))).PosSemidef
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
    · change 0 ≤ c - min (A i i).re c
      exact sub_nonneg.mpr (min_le_right _ _)
    · simp only [Complex.sub_im, Complex.ofReal_im, sub_self]
  have h := dual_bound hA (realDiagonal_hermitian b) c hcap
  have hp : (trace (realDiagonal b * A)).re = ∑ i, b i * (A i i).re := by
    simp only [realDiagonal, trace, diag, diagonal_mul, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hs : (trace (realDiagonal b * realDiagonal b)).re = ∑ i, (b i) ^ 2 := by
    simp only [realDiagonal, Matrix.diagonal_mul_diagonal, trace_diagonal, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, pow_two]
  rw [hp, hs] at h
  simpa only [quadratic_eq_dual, b, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_assoc] using h

theorem energy_zero_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : 0 ≤ energy 0 A := by
  rw [energy, spectralSum_eq hA]
  exact Finset.sum_nonneg fun i _ => by rw [quadratic_zero]; positivity

/-- Zero clipped energy is precisely positive semidefiniteness. -/
theorem energy_zero_eq_zero_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    energy 0 A = 0 ↔ A.PosSemidef := by
  rw [energy, spectralSum_eq hA, hA.posSemidef_iff_eigenvalues_nonneg]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by rw [quadratic_zero]; positivity)]
  simp only [Finset.mem_univ, forall_const, quadratic_zero_eq_zero_iff, Pi.le_def, Pi.zero_apply]

/-- Adding a positive matrix can only reduce the squared negative spectrum. -/
theorem energy_zero_antitone {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hBA : (B - A).PosSemidef) : energy 0 B ≤ energy 0 A := by
  have hC : (-certificate hB 0).PosSemidef := by
    simpa only [Complex.ofReal_zero, zero_smul, zero_sub] using certificate_cap hB 0
  have ht := trace_mul_nonneg_of_posSemidef hC hBA
  change 0 ≤ (trace ((-certificate hB 0) * (B - A))).re at ht
  simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.trace_neg, Matrix.trace_sub,
    Complex.neg_re, Complex.sub_re] at ht
  have hd := dual_bound hA (certificate_hermitian hB 0) 0 (certificate_cap hB 0)
  have he := certificate_attains hB 0
  linarith only [ht, hd, he]

#print axioms scalar_negative_certificate_iff
#print axioms diagonal_clipped_lower
#print axioms energy_zero_eq_zero_iff
#print axioms energy_zero_antitone

end
end GaloisForLFunctions.HilbertMetric.Clipped
