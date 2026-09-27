import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion

/-!
# Normalized finite annihilators of the actual Xi divisor

Each selected divisor copy contributes both conjugate roots. The resulting
real polynomial has constant coefficient one and vanishes at every selected
squared spectral point. Bounds apply to the complete product, without
discarding coefficient cross terms.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-- A real quadratic with constant coefficient one and reciprocal root data. -/
def realNormalizedConjFactor (a : ℂ) : Polynomial ℝ :=
  1 - C (2 * a.re) * X + C (Complex.normSq a) * X ^ 2

theorem eval_realNormalizedConjFactor (a z : ℂ) :
    evalRealPolynomial (realNormalizedConjFactor a) z =
      (1 - a * z) * (1 - (starRingEnd ℂ) a * z) := by
  apply Complex.ext <;>
    simp [realNormalizedConjFactor, evalRealPolynomial, Complex.normSq_apply,
      pow_two, mul_re, mul_im] <;> ring

theorem norm_eval_realNormalizedConjFactor_le (a z : ℂ) :
    ‖evalRealPolynomial (realNormalizedConjFactor a) z‖ ≤
      Real.exp (2 * ‖z‖ * ‖a‖) := by
  rw [eval_realNormalizedConjFactor, norm_mul]
  have h1 : ‖1 - a * z‖ ≤ Real.exp (‖a‖ * ‖z‖) := by
    calc
      ‖1 - a * z‖ ≤ 1 + ‖a‖ * ‖z‖ := by
        simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ) (a * z)
      _ ≤ Real.exp (‖a‖ * ‖z‖) := by
        simpa only [add_comm] using Real.add_one_le_exp (‖a‖ * ‖z‖)
  have h2 : ‖1 - (starRingEnd ℂ) a * z‖ ≤ Real.exp (‖a‖ * ‖z‖) := by
    calc
      ‖1 - (starRingEnd ℂ) a * z‖ ≤ 1 + ‖a‖ * ‖z‖ := by
        simpa only [norm_one, norm_mul, Complex.norm_conj] using
          norm_sub_le (1 : ℂ) ((starRingEnd ℂ) a * z)
      _ ≤ Real.exp (‖a‖ * ‖z‖) := by
        simpa only [add_comm] using Real.add_one_le_exp (‖a‖ * ‖z‖)
  calc
    _ ≤ Real.exp (‖a‖ * ‖z‖) * Real.exp (‖a‖ * ‖z‖) :=
      mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Every copy is retained as a factor; repeated roots retain multiplicity. -/
def xiGaussianAnnihilator (F : Finset XiZeroCopy) : Polynomial ℝ :=
  ∏ q ∈ F, realNormalizedConjFactor ((xiSpectralPoint q ^ 2)⁻¹)

theorem eval_xiGaussianAnnihilator (F : Finset XiZeroCopy) (z : ℂ) :
    evalRealPolynomial (xiGaussianAnnihilator F) z =
      ∏ q ∈ F, evalRealPolynomial
        (realNormalizedConjFactor ((xiSpectralPoint q ^ 2)⁻¹)) z := by
  simp only [xiGaussianAnnihilator, evalRealPolynomial,
    Polynomial.map_prod, Polynomial.eval_prod]

theorem xiGaussianAnnihilator_zero (F : Finset XiZeroCopy) :
    (xiGaussianAnnihilator F).eval 0 = 1 := by
  simp only [xiGaussianAnnihilator, Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro q _
  simp only [realNormalizedConjFactor, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero, zero_pow two_ne_zero, add_zero]

theorem xiGaussianAnnihilator_coeff_zero (F : Finset XiZeroCopy) :
    (xiGaussianAnnihilator F).coeff 0 = 1 := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using xiGaussianAnnihilator_zero F

theorem xiGaussianAnnihilator_vanishes (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∈ F}) :
    evalRealPolynomial (xiGaussianAnnihilator F) (xiSpectralPoint q.1 ^ 2) = 0 := by
  classical
  rw [eval_xiGaussianAnnihilator]
  apply Finset.prod_eq_zero q.property
  rw [eval_realNormalizedConjFactor,
    inv_mul_cancel₀ (pow_ne_zero 2 (xiSpectralPoint_ne_zero q.1)), sub_self, zero_mul]

theorem norm_eval_xiGaussianAnnihilator_le (F : Finset XiZeroCopy) (z : ℂ) :
    ‖evalRealPolynomial (xiGaussianAnnihilator F) z‖ ≤
      Real.exp (2 * ‖z‖ * (∑ q ∈ F, 1 / ‖xiSpectralPoint q‖ ^ 2)) := by
  rw [eval_xiGaussianAnnihilator, norm_prod]
  calc
    _ ≤ ∏ q ∈ F, Real.exp (2 * ‖z‖ * ‖(xiSpectralPoint q ^ 2)⁻¹‖) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun _ _ => norm_eval_realNormalizedConjFactor_le _ _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [norm_inv, norm_pow, one_div, Finset.mul_sum]

/-- The exact head/tail product identity permits a fixed summable majorant. -/
theorem xiGaussianAnnihilator_union (F H : Finset XiZeroCopy) :
    xiGaussianAnnihilator (F ∪ H) =
      xiGaussianAnnihilator H * xiGaussianAnnihilator (F \ H) := by
  classical
  unfold xiGaussianAnnihilator
  rw [← Finset.prod_union (Finset.sdiff_disjoint.symm : Disjoint H (F \ H)),
    Finset.union_sdiff_self_eq_union, Finset.union_comm]

end RHTower
