import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.PolynomialAverages
import GaloisForLFunctions.HTGeometry.UniformGridStep

/-! Uniform grid steps are polynomial translation averages of a single interval pulse.
Their real Laplace transforms are positive exactly when the grid polynomial is
positive on the positive real axis. -/

open Polynomial MeasureTheory Set
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

/-- Polynomial of the left endpoint values on a finite uniform grid. -/
def gridPolynomial (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range M, C (f (a + j * h)) * X ^ j

/-- Indicator of the first grid cell. -/
def gridPulse (a h : ℝ) : ℝ → ℝ := (Ioc a (a + h)).indicator 1

theorem gridPulse_sub (a h x : ℝ) (j : ℕ) :
    gridPulse a h (x - j * h) = (gridCell a h j).indicator 1 x := by
  have he : x - j * h ∈ Ioc a (a + h) ↔ x ∈ gridCell a h j := by
    change (a < x - j * h ∧ x - j * h ≤ a + h) ↔
      (a + j * h < x ∧ x ≤ a + (j + 1) * h)
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith only [hl, hu]
  by_cases hx : x ∈ gridCell a h j
  · simp only [gridPulse, Set.indicator_of_mem hx, Set.indicator_of_mem (he.mpr hx), Pi.one_apply]
  · simp only [gridPulse, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt he.mp hx)]

theorem polynomialAverage_gridPolynomial (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    polynomialAverage (gridPolynomial f a h M) h (gridPulse a h) = gridStep f a h M := by
  funext x
  simp only [polynomialAverage, gridPolynomial, map_sum, map_mul, map_pow, aeval_C,
    aeval_X, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Pi.smul_apply, smul_eq_mul, translationEnd_pow_apply, gridPulse_sub, gridStep]

theorem integrable_translate_exp {f : ℝ → ℝ} {s : ℝ}
    (hf : Integrable fun x => f x * Real.exp (s * x)) (t : ℝ) :
    Integrable fun x => f (x - t) * Real.exp (s * x) := by
  refine ((hf.comp_sub_right t).const_mul (Real.exp (s * t))).congr ?_
  filter_upwards [] with x
  simp only [mul_comm (Real.exp (s * t)), mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Real Laplace transformation diagonalizes the polynomial translation action. -/
theorem integral_polynomialAverage_exp (p : ℝ[X]) (h s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable fun x => f x * Real.exp (s * x)) :
    (∫ x, polynomialAverage p h f x * Real.exp (s * x)) =
      p.eval (Real.exp (s * h)) * ∫ x, f x * Real.exp (s * x) := by
  simp only [polynomialAverage_apply, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun (i : ℕ) _ => (integrable_translate_exp hf ((i : ℝ) * h)).const_mul (p.coeff i))]
  simp_rw [integral_const_mul]
  rw [eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Real.exp (s * (i * h)) = Real.exp (s * h) ^ i := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ht : (∫ x, f (x - (i : ℝ) * h) * Real.exp (s * x)) =
      Real.exp (s * ((i : ℝ) * h)) * ∫ x, f x * Real.exp (s * x) := by
    rw [← integral_add_right_eq_self
      (fun x => f (x - (i : ℝ) * h) * Real.exp (s * x)) ((i : ℝ) * h)]
    simp_rw [add_sub_cancel_right, mul_add, Real.exp_add]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [ht, he]
  ring

theorem integrable_gridPulse_exp (a h s : ℝ) :
    Integrable fun x => gridPulse a h x * Real.exp (s * x) := by
  have he : (fun x => gridPulse a h x * Real.exp (s * x)) =
      (Ioc a (a + h)).indicator (fun x => Real.exp (s * x)) := by
    funext x
    by_cases hx : x ∈ Ioc a (a + h) <;> simp [gridPulse, hx]
  rw [he]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact (show Continuous (fun x : ℝ => Real.exp (s * x)) by fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem integral_gridPulse_exp_pos (a s : ℝ) {h : ℝ} (hh : 0 < h) :
    0 < ∫ x, gridPulse a h x * Real.exp (s * x) := by
  have hn : ∀ x, 0 ≤ gridPulse a h x * Real.exp (s * x) := by
    intro x
    apply mul_nonneg _ (Real.exp_pos _).le
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  rw [integral_pos_iff_support_of_nonneg hn (integrable_gridPulse_exp a h s)]
  have hs : Ioc a (a + h) ⊆ Function.support (fun x => gridPulse a h x * Real.exp (s * x)) := by
    intro x hx
    simp only [Function.mem_support, gridPulse, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    exact (Real.exp_pos _).ne'
  exact lt_of_lt_of_le (by simp [Real.volume_Ioc, ENNReal.ofReal_pos, hh]) (measure_mono hs)

/-- A positive first coefficient fills in the endpoint omitted by real exponential parameters. -/
theorem gridPolynomial_eval_pos_of_laplace_pos {f : ℝ → ℝ} {a h : ℝ} {M : ℕ}
    (hh : 0 < h) (hfirst : 0 < f a) (hM : 0 < M)
    (hlap : ∀ s : ℝ, 0 < ∫ x, gridStep f a h M x * Real.exp (s * x)) :
    ∀ x : ℝ, 0 ≤ x → 0 < (gridPolynomial f a h M).eval x := by
  intro x hx
  rcases hx.eq_or_lt with rfl | hx
  · simpa [gridPolynomial, eval_finsetSum, zero_pow_eq, hM] using hfirst
  · let s := Real.log x / h
    have he : Real.exp (s * h) = x := by
      rw [show s * h = Real.log x by dsimp [s]; field_simp [hh.ne'], Real.exp_log hx]
    have hl := hlap s
    rw [← polynomialAverage_gridPolynomial, integral_polynomialAverage_exp _ _ _
      (integrable_gridPulse_exp a h s), he] at hl
    exact (mul_pos_iff_of_pos_right (integral_gridPulse_exp_pos a s hh)).mp hl

#print axioms gridPolynomial_eval_pos_of_laplace_pos
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
