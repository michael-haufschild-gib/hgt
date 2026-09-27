import GaloisForLFunctions.RHTower.XiCriticalGaussianEnergyFloor

/-!
# Coefficient-uniform moving-cutoff control of the actual Xi heat tail

The complete polynomial is retained in every tail summand. Cauchy--Schwarz
provides a finite, coefficient-independent anchor at heat time one; increasing
the spectral cutoff increases the tail's exponential decay rate.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

/-- Complete positive energy above a cutoff in the real part of the spectral square. -/
def xiGaussianTailEnergy (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) : ℝ :=
  ∑' q : {q : XiZeroCopy // R < (xiSpectralPoint q ^ 2).re},
    ‖xiPolynomialGaussianHeatTerm Q t q.1‖

/-- Finite-order anchor, using actual monomial energies at time one. -/
def xiGaussianCoefficientAnchor (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑' q : XiZeroCopy,
    ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) 1 q‖

theorem xiGaussianCoefficientAnchor_nonneg (N : ℕ) : 0 ≤ xiGaussianCoefficientAnchor N :=
  Finset.sum_nonneg fun _ _ => tsum_nonneg fun _ => norm_nonneg _

theorem xiGaussianTailEnergy_nonneg (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) :
    0 ≤ xiGaussianTailEnergy Q t R := tsum_nonneg fun _ => norm_nonneg _

/-- Complete polynomial point energy is bounded without discarding any mixed term. -/
theorem norm_xiPolynomialGaussianHeatTerm_rangeSum_le
    (N : ℕ) (a : ℕ → ℝ) (t : ℝ) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q‖ ≤
        (∑ j ∈ Finset.range N, a j ^ 2) *
          ∑ j ∈ Finset.range N, ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) t q‖ := by
  let z := xiSpectralPoint q ^ 2
  have hn : ‖∑ j ∈ Finset.range N, (a j : ℂ) * z ^ j‖ ≤
      ∑ j ∈ Finset.range N, |a j| * ‖z ^ j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le (Finset.range N) (fun j => (a j : ℂ) * z ^ j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun j => |a j|) (fun j => ‖z ^ j‖)
  simp only [sq_abs] at hcs
  have hp := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have h := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(t * z.re))).le
  simp only [norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_rangeSum,
    evalRealPolynomial_pow, evalRealPolynomial_X]
  change ‖∑ j ∈ Finset.range N, (a j : ℂ) * z ^ j‖ ^ 2 * Real.exp (-(t * z.re)) ≤ _
  simpa only [Finset.sum_mul, mul_assoc] using h

/-- One common finite anchor controls the full energy of every coefficient direction. -/
theorem tsum_norm_xiGaussian_rangeSum_one_le_anchor (N : ℕ) (a : ℕ → ℝ) :
    (∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) 1 q‖) ≤
        (∑ j ∈ Finset.range N, a j ^ 2) * xiGaussianCoefficientAnchor N := by
  have hs : Summable (fun q : XiZeroCopy =>
      ∑ j ∈ Finset.range N, ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) 1 q‖) :=
    summable_sum fun j _ => summable_norm_xiPolynomialGaussianHeatTerm one_pos _
  have h := Summable.tsum_le_tsum (norm_xiPolynomialGaussianHeatTerm_rangeSum_le N a 1)
    (summable_norm_xiPolynomialGaussianHeatTerm one_pos _) (hs.mul_left _)
  rw [tsum_mul_left, Summable.tsum_finsetSum
    (fun j _ => summable_norm_xiPolynomialGaussianHeatTerm one_pos (Polynomial.X ^ j))] at h
  exact h

/-- Heat past time one damps the complete actual tail at the chosen cutoff rate. -/
theorem xiGaussianTailEnergy_le_timeOne (Q : Polynomial ℝ)
    (t : {t : ℝ // 1 ≤ t}) (R : ℝ) :
    xiGaussianTailEnergy Q ⟨t, zero_lt_one.trans_le t.property⟩ R ≤
      Real.exp (-(((t : ℝ) - 1) * R)) *
        ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q 1 q‖ := by
  classical
  let S : Set XiZeroCopy := {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re}
  have hs := summable_norm_xiPolynomialGaussianHeatTerm
    (zero_lt_one.trans_le t.property) Q
  have hs1 := summable_norm_xiPolynomialGaussianHeatTerm one_pos Q
  have hp (q : S) : ‖xiPolynomialGaussianHeatTerm Q t q.1‖ ≤
      Real.exp (-(((t : ℝ) - 1) * R)) * ‖xiPolynomialGaussianHeatTerm Q 1 q.1‖ := by
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
    have he : Real.exp (-((t : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
        Real.exp (-(((t : ℝ) - 1) * R)) * Real.exp (-(1 * (xiSpectralPoint q.1 ^ 2).re)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hm := mul_le_mul_of_nonneg_left q.property.le (sub_nonneg.mpr t.property)
      nlinarith only [hm]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have h : (∑' q : S, ‖xiPolynomialGaussianHeatTerm Q t q.1‖) ≤
      ∑' q : S, Real.exp (-(((t : ℝ) - 1) * R)) *
        ‖xiPolynomialGaussianHeatTerm Q 1 q.1‖ :=
    Summable.tsum_le_tsum hp (hs.subtype S) ((hs1.subtype S).mul_left _)
  rw [tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Summable.tsum_subtype_le _ S (fun _ => norm_nonneg _) hs1) (Real.exp_pos _).le)

/-- The tail ceiling is uniform over every coefficient vector at a fixed finite order. -/
theorem xiGaussianTailEnergy_rangeSum_le_anchor (N : ℕ) (a : ℕ → ℝ)
    (t : {t : ℝ // 1 ≤ t}) (R : ℝ) :
    xiGaussianTailEnergy
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j)
      ⟨t, zero_lt_one.trans_le t.property⟩ R ≤
        Real.exp (-(((t : ℝ) - 1) * R)) * xiGaussianCoefficientAnchor N *
          (∑ j ∈ Finset.range N, a j ^ 2) := by
  exact ((xiGaussianTailEnergy_le_timeOne _ t R).trans
    (mul_le_mul_of_nonneg_left (tsum_norm_xiGaussian_rangeSum_one_le_anchor N a)
      (Real.exp_pos _).le)).trans_eq (by ring)

end RHTower
