import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity

/-!
# Coercive circle densities need not be reflection positive

The one-mode family `1 - ε Re(z^(2N))` is an exact reusable obstruction to deriving reflected
Hankel positivity from ordinary density coercivity.  For `0 < ε < 1` it is a strictly positive
analytic probability density arbitrarily close to Haar density, while the reflected square of the
monomial `z^N` is exactly `-ε/2`.
-/

open MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Even one-mode perturbation of normalized circle Haar density. -/
def circleReflectionCoercivePerturbationDensity
    (epsilon : ℝ) (N : ℕ) (z : Circle) : ℝ :=
  1 - epsilon * ((z : ℂ) ^ (2 * N)).re

/-- Exact uniform coercivity bounds for the one-mode perturbation. -/
theorem circleReflectionCoercivePerturbationDensity_bounds
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (N : ℕ) (z : Circle) :
    1 - epsilon ≤ circleReflectionCoercivePerturbationDensity epsilon N z ∧
      circleReflectionCoercivePerturbationDensity epsilon N z ≤ 1 + epsilon := by
  have habs := Complex.abs_re_le_norm ((z : ℂ) ^ (2 * N))
  rw [norm_pow, Circle.norm_coe, one_pow] at habs
  have hle := abs_le.mp habs
  constructor <;>
    simp only [circleReflectionCoercivePerturbationDensity] <;>
    nlinarith

/-- The perturbation is pointwise strictly positive whenever `0 ≤ ε < 1`. -/
theorem circleReflectionCoercivePerturbationDensity_pos
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (N : ℕ) (z : Circle) :
    0 < circleReflectionCoercivePerturbationDensity epsilon N z := by
  linarith [
    (circleReflectionCoercivePerturbationDensity_bounds hepsilon0 N z).1]

/-- The one-mode perturbation is integrable against normalized circle Haar measure. -/
theorem integrable_circleReflectionCoercivePerturbationDensity
    (epsilon : ℝ) (N : ℕ) :
    Integrable (circleReflectionCoercivePerturbationDensity epsilon N)
      circleLebesgue := by
  let f : C(Circle, ℝ) :=
    ⟨circleReflectionCoercivePerturbationDensity epsilon N, by
      unfold circleReflectionCoercivePerturbationDensity
      fun_prop⟩
  exact (BoundedContinuousFunction.mkOfCompact f).integrable _

/-- Every positive-frequency perturbation has normalized mass one. -/
theorem integral_circleReflectionCoercivePerturbationDensity
    (epsilon : ℝ) {N : ℕ} (hN : 0 < N) :
    ∫ z : Circle, circleReflectionCoercivePerturbationDensity epsilon N z
      ∂circleLebesgue = 1 := by
  have hterm : Integrable (fun z : Circle =>
      epsilon * ((z : ℂ) ^ (2 * N)).re) circleLebesgue := by
    let f : C(Circle, ℝ) :=
      ⟨fun z => epsilon * ((z : ℂ) ^ (2 * N)).re, by fun_prop⟩
    exact (BoundedContinuousFunction.mkOfCompact f).integrable _
  have hzero : ∫ z : Circle, ((z : ℂ) ^ (2 * N)).re ∂circleLebesgue = 0 := by
    have hpow := integral_circleLebesgue_re_coe_pow_succ_eq_zero (2 * N - 1)
    have hsucc : 2 * N - 1 + 1 = 2 * N := by omega
    simpa only [hsucc] using hpow
  rw [show circleReflectionCoercivePerturbationDensity epsilon N =
      fun z : Circle => 1 - epsilon * ((z : ℂ) ^ (2 * N)).re by rfl,
    integral_sub (integrable_const 1) hterm,
    integral_const, integral_const_mul, hzero]
  simp

/-- Probability measure defined by the one-mode perturbation. -/
def circleReflectionCoercivePerturbationMeasure
    (epsilon : ℝ) (N : ℕ) : Measure Circle :=
  circleLebesgue.withDensity fun z =>
    ENNReal.ofReal (circleReflectionCoercivePerturbationDensity epsilon N z)

/-- The strictly coercive perturbation defines a genuine circle probability measure. -/
theorem isProbabilityMeasure_circleReflectionCoercivePerturbationMeasure
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (circleReflectionCoercivePerturbationMeasure epsilon N) := by
  have hnonneg : ∀ z : Circle,
      0 ≤ circleReflectionCoercivePerturbationDensity epsilon N z := fun z =>
    (circleReflectionCoercivePerturbationDensity_pos hepsilon0 hepsilon1 N z).le
  rw [isProbabilityMeasure_iff, circleReflectionCoercivePerturbationMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hmass := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_circleReflectionCoercivePerturbationDensity epsilon N)
    (Filter.Eventually.of_forall hnonneg)
  rw [integral_circleReflectionCoercivePerturbationDensity epsilon hN] at hmass
  simpa using hmass.symm

/-- Exact negative reflected monomial square. -/
theorem integral_monomial_sq_circleReflectionCoercivePerturbationDensity
    (epsilon : ℝ) {N : ℕ} (hN : 0 < N) :
    (∫ z : Circle,
        (z : ℂ) ^ (2 * N) *
          (circleReflectionCoercivePerturbationDensity epsilon N z : ℂ)
        ∂circleLebesgue) = -(epsilon : ℂ) / 2 := by
  have hmode : 2 * N ≠ 0 := by omega
  have hpow : Integrable (fun z : Circle => (z : ℂ) ^ (2 * N))
      circleLebesgue := by
    simpa only [zpow_natCast] using
      (circleZMonomial_memLp circleLebesgue ((2 * N : ℕ) : ℤ)).integrable
        (by norm_num)
  have hprod : Integrable (fun z : Circle =>
      (((z : ℂ) ^ (2 * N)).re : ℂ) * (z : ℂ) ^ (2 * N))
      circleLebesgue := by
    let f : C(Circle, ℂ) :=
      ⟨fun z => (((z : ℂ) ^ (2 * N)).re : ℂ) * (z : ℂ) ^ (2 * N), by
        fun_prop⟩
    exact (BoundedContinuousFunction.mkOfCompact f).integrable _
  rw [show (fun z : Circle =>
      (z : ℂ) ^ (2 * N) *
        (circleReflectionCoercivePerturbationDensity epsilon N z : ℂ)) =
      fun z : Circle => (z : ℂ) ^ (2 * N) -
        (epsilon : ℂ) *
          ((((z : ℂ) ^ (2 * N)).re : ℂ) * (z : ℂ) ^ (2 * N)) by
    funext z
    simp only [circleReflectionCoercivePerturbationDensity]
    push_cast
    ring]
  rw [integral_sub hpow (hprod.const_mul (epsilon : ℂ)),
    integral_circleLebesgue_coe_pow_eq_zero (2 * N) hmode,
    integral_const_mul,
    integral_re_circle_pow_mul_circle_pow (2 * N) (2 * N) hmode]
  simp
  ring

/-- The reflected monomial square is strictly negative for every `ε > 0`. -/
theorem re_integral_monomial_sq_circleReflectionCoercivePerturbationDensity_neg
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {N : ℕ} (hN : 0 < N) :
    (∫ z : Circle,
        (z : ℂ) ^ (2 * N) *
          (circleReflectionCoercivePerturbationDensity epsilon N z : ℂ)
        ∂circleLebesgue).re < 0 := by
  rw [integral_monomial_sq_circleReflectionCoercivePerturbationDensity epsilon hN]
  norm_num
  linarith

end

end GaloisForLFunctions.HTGeometry
