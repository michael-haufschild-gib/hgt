import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterCentralLimit

/-!
# Gaussian fluctuations of finite character test functions

Centering a finite Sato–Tate character expansion deletes its constant
coefficient. Its variance is exactly the sum of the remaining coefficient
squares. Independent samples converge to the Gaussian with this variance,
including the degenerate constant-test case.
-/

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal
open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

theorem continuous_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (characterPolynomial s a) :=
  continuous_finsetSum s fun m _ => continuous_const.mul (continuous_cosSum m)

/-- A coefficient-weighted uniform bound for every finite character test. -/
theorem abs_characterPolynomial_le (s : Finset ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    |characterPolynomial s a θ| ≤ ∑ m ∈ s, |a m| * ((m : ℝ) + 1) := by
  unfold characterPolynomial
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_cosSum_le θ m) (abs_nonneg _)

theorem memLp_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) (q : ℝ≥0∞) :
    MemLp (characterPolynomial s a) q satoTate := by
  refine MemLp.of_bound (continuous_characterPolynomial s a).aestronglyMeasurable
    (∑ m ∈ s, |a m| * ((m : ℝ) + 1)) (ae_of_all _ fun θ => ?_)
  simpa only [Real.norm_eq_abs] using abs_characterPolynomial_le s a θ

/-- The exact limiting variance is the nonconstant character energy. -/
theorem variance_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) :
    variance (characterPolynomial s a) satoTate = ∑ m ∈ s.erase 0, a m ^ 2 := by
  rw [variance_eq_sub (memLp_characterPolynomial s a 2)]
  change (∫ θ, characterPolynomial s a θ ^ 2 ∂satoTate) -
    (∫ θ, characterPolynomial s a θ ∂satoTate) ^ 2 = _
  rw [integral_characterPolynomial_sq, integral_characterPolynomial]
  by_cases h0 : 0 ∈ s
  · rw [if_pos h0, ← sum_erase_add s (fun m => a m ^ 2) h0]
    ring
  · rw [if_neg h0, erase_eq_of_notMem h0]
    ring

/-- Zero fluctuation is equivalent to vanishing of every nonconstant coefficient. -/
theorem variance_characterPolynomial_eq_zero_iff (s : Finset ℕ) (a : ℕ → ℝ) :
    variance (characterPolynomial s a) satoTate = 0 ↔
      ∀ m ∈ s.erase 0, a m = 0 := by
  rw [variance_characterPolynomial,
    sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (a m))]
  simp only [sq_eq_zero_iff]

/-- A finite character test observed at one coordinate of the Sato–Tate sequence. -/
def characterPolynomialCoordinate (s : Finset ℕ) (a : ℕ → ℝ) (i : ℕ)
    (ω : ℕ → ℝ) : ℝ := characterPolynomial s a (ω i)

theorem integral_characterPolynomialCoordinate_pow (s : Finset ℕ) (a : ℕ → ℝ)
    (i r : ℕ) :
    ∫ ω, characterPolynomialCoordinate s a i ω ^ r ∂satoTateSequenceMeasure =
      ∫ θ, characterPolynomial s a θ ^ r ∂satoTate :=
  (hasLaw_satoTate_eval i).integral_comp
    ((continuous_characterPolynomial s a).pow r).aestronglyMeasurable

theorem integral_characterPolynomialCoordinate (s : Finset ℕ) (a : ℕ → ℝ) (i : ℕ) :
    ∫ ω, characterPolynomialCoordinate s a i ω ∂satoTateSequenceMeasure =
      if 0 ∈ s then a 0 else 0 := by
  have h := integral_characterPolynomialCoordinate_pow s a i 1
  simpa only [pow_one, integral_characterPolynomial] using h

theorem memLp_characterPolynomialCoordinate (s : Finset ℕ) (a : ℕ → ℝ)
    (i : ℕ) (q : ℝ≥0∞) :
    MemLp (characterPolynomialCoordinate s a i) q satoTateSequenceMeasure := by
  refine MemLp.of_bound
    ((continuous_characterPolynomial s a).comp (continuous_apply i)).aestronglyMeasurable
    (∑ m ∈ s, |a m| * ((m : ℝ) + 1)) (ae_of_all _ fun ω => ?_)
  simpa only [characterPolynomialCoordinate, Real.norm_eq_abs] using
    abs_characterPolynomial_le s a (ω i)

theorem variance_characterPolynomialCoordinate (s : Finset ℕ) (a : ℕ → ℝ) (i : ℕ) :
    variance (characterPolynomialCoordinate s a i) satoTateSequenceMeasure =
      ∑ m ∈ s.erase 0, a m ^ 2 := by
  rw [variance_eq_sub (memLp_characterPolynomialCoordinate s a i 2)]
  change (∫ ω, characterPolynomialCoordinate s a i ω ^ 2 ∂satoTateSequenceMeasure) -
    (∫ ω, characterPolynomialCoordinate s a i ω ∂satoTateSequenceMeasure) ^ 2 = _
  rw [integral_characterPolynomialCoordinate_pow]
  have hmean := integral_characterPolynomialCoordinate_pow s a i 1
  simp only [pow_one] at hmean
  rw [hmean]
  exact (variance_eq_sub (memLp_characterPolynomial s a 2)).symm.trans
    (variance_characterPolynomial s a)

/-- Every finite character test has a Gaussian fluctuation law with its exact
coefficient variance. Constant tests converge to the point mass at zero. -/
theorem tendstoInDistribution_characterPolynomial (s : Finset ℕ) (a : ℕ → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => (Real.sqrt n)⁻¹ *
        ((∑ i ∈ range n, characterPolynomial s a (ω i)) -
          n * (if 0 ∈ s then a 0 else 0)))
      atTop (id : ℝ → ℝ) (fun _ => satoTateSequenceMeasure)
      (gaussianReal 0 (∑ m ∈ s.erase 0, a m ^ 2).toNNReal) := by
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := characterPolynomialCoordinate s a)
    (P := satoTateSequenceMeasure)
    (P' := gaussianReal 0 (∑ m ∈ s.erase 0, a m ^ 2).toNNReal) (Y := id)
    (by rw [variance_characterPolynomialCoordinate]; exact HasLaw.id)
    (memLp_characterPolynomialCoordinate s a 0 2)
    (iIndepFun_infinitePi (fun _ : ℕ => (continuous_characterPolynomial s a).measurable))
    (fun i => ((hasLaw_satoTate_eval i).identDistrib (hasLaw_satoTate_eval 0)).comp
      (continuous_characterPolynomial s a).measurable)
  rw [integral_characterPolynomialCoordinate] at h
  simpa only [characterPolynomialCoordinate] using h

#print axioms variance_characterPolynomial
#print axioms variance_characterPolynomial_eq_zero_iff
#print axioms tendstoInDistribution_characterPolynomial

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
