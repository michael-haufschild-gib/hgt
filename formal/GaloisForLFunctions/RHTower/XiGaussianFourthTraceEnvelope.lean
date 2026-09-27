import GaloisForLFunctions.RHTower.XiCriticalResidualPhaseGap
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# An explicit coefficient envelope against reciprocal fourth-trace weight

The power-exponential inequality controls every polynomial coordinate after
multiplication by the fourth power of the spectral norm. Cauchy--Schwarz is
applied to the complete polynomial before summing; no mixed term is removed.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

def xiGaussianFourthTraceEnvelope (N : ℕ) (s : {s : ℝ // 0 < s}) : ℝ :=
  ∑ j ∈ Finset.range N, ((2 * j + 2).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 2)

theorem xiGaussianFourthTraceEnvelope_nonneg (N : ℕ) (s : {s : ℝ // 0 < s}) :
    0 ≤ xiGaussianFourthTraceEnvelope N s := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg (by positivity) s.property.le) _)

/-- All spectral copies satisfy a source-weighted monomial heat ceiling. -/
theorem xiGaussianMonomial_mul_norm_four_le_envelope (j : ℕ)
    (s : {s : ℝ // 0 < s}) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) s q‖ * ‖xiSpectralPoint q‖ ^ 4 ≤
      ((2 * j + 2).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 2) := by
  let A := (xiSpectralPoint q ^ 2).re
  have hA : 0 < A := xiSpectralSq_re_pos q
  have hsector : ‖xiSpectralPoint q‖ ^ 2 ≤ 2 * A := by
    have h : ‖xiSpectralPoint q‖ ^ 2 < 2 * A := by
      simpa only [Complex.sq_norm, A] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
    exact h.le
  have hid : ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) s q‖ *
      ‖xiSpectralPoint q‖ ^ 4 =
        (‖xiSpectralPoint q‖ ^ 2) ^ (2 * j + 2) * Real.exp (-((s : ℝ) * A)) := by
    rw [norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_pow, evalRealPolynomial_X]
    simp only [norm_pow, ← pow_mul]
    calc
      _ = ‖xiSpectralPoint q‖ ^ ((2 * j) * 2 + 4) * Real.exp (-((s : ℝ) * A)) := by
        rw [pow_add]
        ring
      _ = ‖xiSpectralPoint q‖ ^ (2 * (2 * j + 2)) * Real.exp (-((s : ℝ) * A)) := by
        congr 2
        omega
  rw [hid]
  have hp := pow_le_pow_left₀ (sq_nonneg ‖xiSpectralPoint q‖) hsector (2 * j + 2)
  have h := GaloisForLFunctions.HTGeometry.pow_mul_exp_neg_le
    (div_pos s.property (by positivity : (0 : ℝ) < 2)) (2 * j + 2)
    (show 0 ≤ 2 * A by positivity)
  rw [show (s : ℝ) / 2 * (2 * A) = (s : ℝ) * A by ring] at h
  calc
    _ ≤ (2 * A) ^ (2 * j + 2) * Real.exp (-((s : ℝ) * A)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ ≤ ((2 * j + 2).factorial : ℝ) / ((s : ℝ) / 2) ^ (2 * j + 2) := h
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow, inv_div]

/-- Coefficient-uniform weighted energy control of the entire polynomial. -/
theorem xiGaussianPolynomial_mul_norm_four_le_envelope (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) s q‖ *
        ‖xiSpectralPoint q‖ ^ 4 ≤
          xiGaussianFourthTraceEnvelope N s * (∑ j ∈ Finset.range N, a j ^ 2) := by
  have h := mul_le_mul_of_nonneg_right
    (norm_xiPolynomialGaussianHeatTerm_rangeSum_le N a s q)
    (pow_nonneg (norm_nonneg (xiSpectralPoint q)) 4)
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ Finset.range N) => xiGaussianMonomial_mul_norm_four_le_envelope j s q)
  rw [← Finset.sum_mul] at hsum
  have hcoeff := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ ∑ j ∈ Finset.range N, a j ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _)
  change _ ≤ (∑ j ∈ Finset.range N, a j ^ 2) * xiGaussianFourthTraceEnvelope N s at hcoeff
  nlinarith only [h, hcoeff]

/-- The residual spectral gap propagates the weighted ceiling to every later time. -/
theorem xiGaussianPolynomial_mul_norm_four_le_residual_envelope
    (F : Finset XiZeroCopy) (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)})
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    ‖xiPolynomialGaussianHeatTerm
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q.1‖ *
        ‖xiSpectralPoint q.1‖ ^ 4 ≤
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
            xiGaussianFourthTraceEnvelope N s * (∑ j ∈ Finset.range N, a j ^ 2) := by
  let Q := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  have he : ‖xiPolynomialGaussianHeatTerm Q t.1 q.1‖ ≤
      e * ‖xiPolynomialGaussianHeatTerm Q s q.1‖ := by
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
    have hExp : Real.exp (-((t.1 : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
        e * Real.exp (-((s : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h := mul_le_mul_of_nonneg_left (xiSpectralSq_re_gt_residualPhaseGap F q).le
        (sub_nonneg.mpr t.property)
      nlinarith only [h]
    exact (mul_le_mul_of_nonneg_left hExp (sq_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have h := mul_le_mul_of_nonneg_right he (pow_nonneg (norm_nonneg (xiSpectralPoint q.1)) 4)
  have hbound := mul_le_mul_of_nonneg_left
    (xiGaussianPolynomial_mul_norm_four_le_envelope N a s q.1)
    (show 0 ≤ e from (Real.exp_pos _).le)
  calc
    _ ≤ e * ‖xiPolynomialGaussianHeatTerm Q s q.1‖ * ‖xiSpectralPoint q.1‖ ^ 4 := h
    _ = e * (‖xiPolynomialGaussianHeatTerm Q s q.1‖ * ‖xiSpectralPoint q.1‖ ^ 4) := by ring
    _ ≤ _ := hbound
    _ = _ := by ring

end RHTower
