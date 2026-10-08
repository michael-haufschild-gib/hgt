import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianBessel

/-!
# Explicit finite Gaussian comparison errors

The Gram error is bounded by the off-diagonal kernel bound times the
coefficient l1 norm squared. The source variational estimate keeps that
error separate from finite Fourier-moment recovery errors. These finite
analytic estimates introduce no extra source assumption; a uniform
growing-cutoff application must still pay both errors from the source.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
variable {lam : ℕ → ℝ}

/-- Finite off-diagonal Gaussian entries control the entire Gram error. -/
theorem norm_quantizationGaussianGram_sub_diagonal_le
    (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (T : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hkernel : ∀ n ∈ S, ∀ m ∈ S, m ≠ n →
      Real.exp (-((T * (ω m - ω n)) ^ 2 / 4)) ≤ q) :
    ‖quantizationGaussianGram S c ω T - ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (∑ n ∈ S, ‖c n‖) ^ 2 * q := by
  classical
  let f (n m : ℕ) : ℂ := c n * conj (c m) *
    (Real.exp (-((T * (ω m - ω n)) ^ 2 / 4)) : ℂ) -
      if m = n then c n * conj (c m) else 0
  have hdiag : (∑ n ∈ S, ∑ m ∈ S, if m = n then c n * conj (c m) else 0) =
      ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have heq : quantizationGaussianGram S c ω T - ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, f n m := by
    rw [← hdiag]
    simp only [f, quantizationGaussianGram, Finset.sum_sub_distrib]
  have hb (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S) :
      ‖f n m‖ ≤ ‖c n‖ * ‖c m‖ * q := by
    by_cases he : m = n
    · subst m
      simp only [f, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
        neg_zero, Real.exp_zero, ofReal_one, mul_one, if_true, norm_zero]
      positivity
    · simp only [f, if_neg he, sub_zero, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hkernel n hn m hm he) (by positivity)
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, ‖∑ m ∈ S, f n m‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖f n m‖ :=
      Finset.sum_le_sum fun n _ => norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖c n‖ * ‖c m‖ * q :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hb n hn m hm
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- Quantitative finite Bessel comparison, retaining both independent errors. -/
theorem quantizationCenteredGaussianEnergy_finset_error_lower
    (hW : WeilPositiveFull lam) (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ)
    {T : ℝ} (hT : 0 < T) {q δ : ℝ} (hq : 0 ≤ q)
    (hkernel : ∀ n ∈ S, ∀ m ∈ S, m ≠ n →
      Real.exp (-((T * (ω m - ω n)) ^ 2 / 4)) ≤ q)
    (hmoment : ∀ n ∈ S, ‖quantizationCenteredGaussianMoment hW T (ω n) - c n‖ ≤ δ) :
    (∑ n ∈ S, ‖c n‖ ^ 2) -
        (2 * (∑ n ∈ S, ‖c n‖) * δ + (∑ n ∈ S, ‖c n‖) ^ 2 * q) ≤
      2 * quantizationCenteredGaussianEnergy hW T / (T * Real.sqrt Real.pi) := by
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖c n‖ ^ 2 - ‖c n‖ * δ ≤
        (conj (c n) * quantizationCenteredGaussianMoment hW T (ω n)).re := by
    have hb := Complex.re_le_norm (-(conj (c n) *
      (quantizationCenteredGaussianMoment hW T (ω n) - c n)))
    simp only [Complex.neg_re, norm_neg] at hb
    have he : conj (c n) * (quantizationCenteredGaussianMoment hW T (ω n) - c n) =
        conj (c n) * quantizationCenteredGaussianMoment hW T (ω n) -
          ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_sub, mul_comm (conj (c n)) (c n), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_mul, Complex.norm_conj, he, Complex.sub_re, Complex.ofReal_re] at hb
    nlinarith [mul_le_mul_of_nonneg_left (hmoment n hn) (norm_nonneg (c n))]
  have hc := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Complex.re_sum] at hc
  have hg := Complex.re_le_norm
    (quantizationGaussianGram S c ω T - ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ))
  have hgn := norm_quantizationGaussianGram_sub_diagonal_le S c ω T hq hkernel
  rw [Complex.sub_re, Complex.ofReal_re] at hg
  have hv := quantizationCenteredGaussianEnergy_variational hW S c ω hT
  linarith

end RHTower.WeilSpectral
