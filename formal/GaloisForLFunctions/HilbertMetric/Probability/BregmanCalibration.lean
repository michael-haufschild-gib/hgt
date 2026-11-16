import GaloisForLFunctions.HilbertMetric.Probability.PearsonRobustness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite Bregman estimation and calibration

The flat-chart risk identity in Navas, arXiv:2611.18141, §§2 and 8,
applies to every finite probability law. Centering removes the linear
term exactly. Quadratic, quartic and exponential generators then give
the same unique mean estimator, with different exact excess risks.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Tangent remainder, with observation first and forecast second. -/
def scalarBregman (φ : ℝ → ℝ) (x q : ℝ) : ℝ :=
  φ x - φ q - deriv φ q * (x - q)

/-- Expected tangent remainder under the actual finite source law. -/
def bregmanRisk (p : FiniteProbabilityLaw ι) (φ : ℝ → ℝ)
    (x : ι → ℝ) (q : ℝ) : ℝ :=
  ∑ i, p.prob i * scalarBregman φ (x i) q

@[simp] theorem scalarBregman_self (φ : ℝ → ℝ) (x : ℝ) :
    scalarBregman φ x x = 0 := by
  simp only [scalarBregman, sub_self, mul_zero]

/-- Taking expectations leaves only the source mean in the tangent term. -/
theorem bregmanRisk_eq (p : FiniteProbabilityLaw ι) (φ : ℝ → ℝ)
    (x : ι → ℝ) (q : ℝ) :
    bregmanRisk p φ x q = finiteWeightedMean p.prob (φ ∘ x) - φ q -
      deriv φ q * (finiteWeightedMean p.prob x - q) := by
  unfold bregmanRisk scalarBregman
  simp_rw [mul_sub, mul_left_comm (p.prob _) (deriv φ q)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_mul, p.sum_prob]
  simp only [one_mul, finiteWeightedMean, Function.comp_apply]

/-- Excess risk is the Bregman divergence from the true mean to the forecast. -/
theorem bregmanRisk_mean_split (p : FiniteProbabilityLaw ι) (φ : ℝ → ℝ)
    (x : ι → ℝ) (q : ℝ) :
    bregmanRisk p φ x q =
      bregmanRisk p φ x (finiteWeightedMean p.prob x) +
        scalarBregman φ (finiteWeightedMean p.prob x) q := by
  rw [bregmanRisk_eq, bregmanRisk_eq]
  unfold scalarBregman
  ring

/-- Quadratic loss is exactly squared prediction error. -/
theorem scalarBregman_square (x q : ℝ) :
    scalarBregman (fun t => t ^ (2 : ℕ)) x q = (x - q) ^ (2 : ℕ) := by
  have hd : deriv (fun t : ℝ => t ^ (2 : ℕ)) q = 2 * q := by
    simp
  rw [scalarBregman, hd]
  ring

/-- Bias--variance decomposition for every finite law, including zero weights. -/
theorem squareRisk_eq_variance_add_bias (p : FiniteProbabilityLaw ι)
    (x : ι → ℝ) (q : ℝ) :
    (∑ i, p.prob i * (x i - q) ^ (2 : ℕ)) =
      finiteWeightedVariance p.prob x +
        (finiteWeightedMean p.prob x - q) ^ (2 : ℕ) := by
  simpa only [bregmanRisk, scalarBregman_square, finiteWeightedVariance] using
    bregmanRisk_mean_split p (fun t => t ^ (2 : ℕ)) x q

/-- The mean is the unique least-squares forecast. -/
theorem squareRisk_minimizer_iff (p : FiniteProbabilityLaw ι)
    (x : ι → ℝ) (q : ℝ) :
    (∀ r, (∑ i, p.prob i * (x i - q) ^ (2 : ℕ)) ≤
      ∑ i, p.prob i * (x i - r) ^ (2 : ℕ)) ↔ q = finiteWeightedMean p.prob x := by
  simp_rw [squareRisk_eq_variance_add_bias, add_le_add_iff_left]
  constructor
  · intro h
    have hz := h (finiteWeightedMean p.prob x)
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hz (sq_nonneg _)))).symm
  · rintro rfl r
    simpa only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      sq_nonneg (finiteWeightedMean p.prob x - r)

/-- A strictly convex quartic generator with a global quadratic lower bound. -/
def quarticGenerator (x : ℝ) : ℝ := x ^ (4 : ℕ) + x ^ (2 : ℕ)

theorem deriv_quarticGenerator (q : ℝ) :
    deriv quarticGenerator q = 4 * q ^ (3 : ℕ) + 2 * q := by
  apply HasDerivAt.deriv
  convert ((hasDerivAt_id q).pow 4).add ((hasDerivAt_id q).pow 2) using 1 <;>
    first | rfl | norm_num [quarticGenerator, id_eq]

/-- Factoring the quartic remainder exhibits its strictly positive coefficient. -/
theorem scalarBregman_quartic (x q : ℝ) :
    scalarBregman quarticGenerator x q =
      (x - q) ^ (2 : ℕ) * ((x + q) ^ (2 : ℕ) + 2 * q ^ (2 : ℕ) + 1) := by
  rw [scalarBregman, deriv_quarticGenerator]
  unfold quarticGenerator
  ring

theorem scalarBregman_quartic_ge_square (x q : ℝ) :
    (x - q) ^ (2 : ℕ) ≤ scalarBregman quarticGenerator x q := by
  rw [scalarBregman_quartic]
  nlinarith only [sq_nonneg (x - q), sq_nonneg (x + q), sq_nonneg q,
    mul_nonneg (sq_nonneg (x - q)) (sq_nonneg (x + q)),
    mul_nonneg (sq_nonneg (x - q)) (sq_nonneg q)]

/-- Quartic estimation has the same unique mean target as least squares. -/
theorem quarticRisk_minimizer_iff (p : FiniteProbabilityLaw ι)
    (x : ι → ℝ) (q : ℝ) :
    (∀ r, bregmanRisk p quarticGenerator x q ≤ bregmanRisk p quarticGenerator x r) ↔
      q = finiteWeightedMean p.prob x := by
  constructor
  · intro h
    have hb := h (finiteWeightedMean p.prob x)
    rw [bregmanRisk_mean_split p quarticGenerator x q] at hb
    have hsq := scalarBregman_quartic_ge_square (finiteWeightedMean p.prob x) q
    have hz : (finiteWeightedMean p.prob x - q) ^ (2 : ℕ) = 0 :=
      le_antisymm (by linarith only [hb, hsq]) (sq_nonneg _)
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hz)).symm
  · rintro rfl r
    rw [bregmanRisk_mean_split p quarticGenerator x r]
    exact le_add_of_nonneg_right ((sq_nonneg _).trans (scalarBregman_quartic_ge_square _ _))

/-- Exponential tangent loss factors through the translation-invariant remainder. -/
theorem scalarBregman_exp (x q : ℝ) :
    scalarBregman Real.exp x q = Real.exp q * (Real.exp (x - q) - 1 - (x - q)) := by
  rw [scalarBregman, Real.deriv_exp]
  have he : Real.exp x = Real.exp q * Real.exp (x - q) := by
    rw [← Real.exp_add, add_sub_cancel]
  rw [he]
  ring

theorem scalarBregman_exp_nonneg (x q : ℝ) : 0 ≤ scalarBregman Real.exp x q := by
  rw [scalarBregman_exp]
  exact mul_nonneg (Real.exp_pos q).le (by linarith only [Real.add_one_le_exp (x - q)])

theorem scalarBregman_exp_eq_zero_iff (x q : ℝ) :
    scalarBregman Real.exp x q = 0 ↔ x = q := by
  constructor
  · intro h
    by_contra hn
    have hp : 0 < scalarBregman Real.exp x q := by
      rw [scalarBregman_exp]
      exact mul_pos (Real.exp_pos q)
        (by linarith only [Real.add_one_lt_exp (sub_ne_zero.mpr hn)])
    exact (ne_of_gt hp) h
  · rintro rfl
    exact scalarBregman_self _ _

/-- Exponential loss also selects exactly the mean, with no moment assumptions. -/
theorem exponentialRisk_minimizer_iff (p : FiniteProbabilityLaw ι)
    (x : ι → ℝ) (q : ℝ) :
    (∀ r, bregmanRisk p Real.exp x q ≤ bregmanRisk p Real.exp x r) ↔
      q = finiteWeightedMean p.prob x := by
  constructor
  · intro h
    have hb := h (finiteWeightedMean p.prob x)
    rw [bregmanRisk_mean_split p Real.exp x q] at hb
    have hz : scalarBregman Real.exp (finiteWeightedMean p.prob x) q = 0 :=
      le_antisymm (by linarith only [hb]) (scalarBregman_exp_nonneg _ _)
    exact ((scalarBregman_exp_eq_zero_iff _ _).mp hz).symm
  · rintro rfl r
    rw [bregmanRisk_mean_split p Real.exp x r]
    exact le_add_of_nonneg_right (scalarBregman_exp_nonneg _ _)

/-- Conditional recalibration separates irreducible loss from calibration loss. -/
theorem bregmanRisk_conditional_split (p : FiniteProbabilityLaw ι)
    (conditional : ι → FiniteProbabilityLaw κ) (φ : ℝ → ℝ)
    (x : ι → κ → ℝ) (forecast : ι → ℝ) :
    (∑ i, p.prob i * bregmanRisk (conditional i) φ (x i) (forecast i)) =
      (∑ i, p.prob i * bregmanRisk (conditional i) φ (x i)
        (finiteWeightedMean (conditional i).prob (x i))) +
      ∑ i, p.prob i * scalarBregman φ
        (finiteWeightedMean (conditional i).prob (x i)) (forecast i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [bregmanRisk_mean_split (conditional i) φ (x i) (forecast i), mul_add]

/-- Uncertainty minus discrimination plus miscalibration, for finite conditional laws. -/
theorem bregmanRisk_calibration_decomposition (p : FiniteProbabilityLaw ι)
    (conditional : ι → FiniteProbabilityLaw κ) (φ : ℝ → ℝ)
    (x : ι → κ → ℝ) (forecast : ι → ℝ) (baseline : ℝ) :
    (∑ i, p.prob i * bregmanRisk (conditional i) φ (x i) (forecast i)) =
      (∑ i, p.prob i * bregmanRisk (conditional i) φ (x i) baseline) -
      (∑ i, p.prob i * scalarBregman φ
        (finiteWeightedMean (conditional i).prob (x i)) baseline) +
      ∑ i, p.prob i * scalarBregman φ
        (finiteWeightedMean (conditional i).prob (x i)) (forecast i) := by
  rw [bregmanRisk_conditional_split p conditional φ x forecast,
    bregmanRisk_conditional_split p conditional φ x (fun _ => baseline)]
  ring

#print axioms bregmanRisk_mean_split
#print axioms squareRisk_minimizer_iff
#print axioms quarticRisk_minimizer_iff
#print axioms exponentialRisk_minimizer_iff
#print axioms bregmanRisk_calibration_decomposition

end
end GaloisForLFunctions.HilbertMetric.Probability
