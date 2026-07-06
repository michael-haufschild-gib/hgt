/-
Assembling the reflected-block mode sum.

Three ingredients: the pointwise identity turning `x^{−s−2}·e(nx)` into the weighted-oscillatory form
`exp((−s.re−2)log x)·exp(i·(2πnx − s.im·log x))` the van der Corput test reads; a general bounded-family
summation lemma; and their combination — every Fourier mode of the Euler–Maclaurin `B₂` kernel against
`x^{−s−2}` is bounded uniformly (independent of the frequency `n`) by `10N/√(−s.im)`, so the mode sum is
at most that uniform bound times the finite coefficient sum `∑ 1/(4π²n²)`.
-/
import GaloisForLFunctions.RHTower.ReflectedModeBound

open Complex intervalIntegral MeasureTheory Real
open scoped Interval BigOperators

noncomputable section

namespace RHTower

theorem reflected_integrand_eq {x : ℝ} (hx : 0 < x) (s : ℂ) (n : ℤ) :
    (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I)
      = (Real.exp ((-s.re - 2) * Real.log x) : ℂ)
          * Complex.exp (((2 * π * (n : ℝ)) * x - s.im * Real.log x : ℝ) * I) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by rw [Complex.ofReal_log hx.le]
  rw [Complex.cpow_def_of_ne_zero hxne, hlog, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  have hs : (-s - 2) = ((-s.re - 2 : ℝ) : ℂ) - (s.im : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [hs]; push_cast; ring

/-- Summation of a bounded complex family over any index type: absolutely summable and the norm of the
sum is at most the sum of the bounds. -/
theorem summable_and_norm_tsum_le_of_mode_bound' {ι : Type*} {T : ι → ℂ} {b : ι → ℝ}
    (hb : Summable b) (hbound : ∀ m, ‖T m‖ ≤ b m) :
    Summable T ∧ ‖∑' m, T m‖ ≤ ∑' m, b m := by
  have hsummT : Summable (fun m => ‖T m‖) :=
    hb.of_nonneg_of_le (fun m => norm_nonneg _) hbound
  refine ⟨hsummT.of_norm, ?_⟩
  calc ‖∑' m, T m‖ ≤ ∑' m, ‖T m‖ := norm_tsum_le_tsum_norm hsummT
    _ ≤ ∑' m, b m := Summable.tsum_mono hsummT hb hbound

/-- **Reflected-block mode sum, bounded.**  The Fourier expansion of the Euler–Maclaurin `B₂` kernel
against `x^{−s−2}` (`s.re ≥ −2`, `s.im < 0`) has each mode's oscillatory integral bounded uniformly by
`10N/√(−s.im)` (second-derivative van der Corput), so the whole mode sum is bounded by that times the
finite Fourier-coefficient sum `∑ 1/(4π²n²)`. -/
theorem reflected_mode_sum_bound {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : -2 ≤ s.re) (hτ : s.im < 0) :
    ‖∑' n : ℤ, ((1 / (4 * π ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ)
        * ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I)‖
      ≤ (∑' n : ℤ, 1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * (10 * (N : ℝ) / Real.sqrt (-s.im)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- per-mode bound, uniform in n
  have hTbound : ∀ n : ℤ,
      ‖∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I)‖
        ≤ 10 * (N : ℝ) / Real.sqrt (-s.im) := by
    intro n
    have hcongr : (∫ x in (1 : ℝ)..(N : ℝ),
          (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I))
        = ∫ x in (1 : ℝ)..(N : ℝ), (Real.exp ((-s.re - 2) * Real.log x) : ℂ)
            * Complex.exp (((2 * π * (n : ℝ)) * x - s.im * Real.log x : ℝ) * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hN1] at hx
      exact reflected_integrand_eq (by linarith [hx.1]) s n
    rw [hcongr]
    exact reflected_per_mode_bound hN hσ hτ n
  -- coefficient summability and nonnegativity
  have hc : Summable (fun n : ℤ => 1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    have heq : (fun n : ℤ => 1 / (4 * π ^ 2 * (n : ℝ) ^ 2))
        = fun n : ℤ => (1 / (4 * π ^ 2)) * (1 / (n : ℝ) ^ 2) := by
      ext n; rw [mul_one_div, div_div]
    rw [heq]; exact h.mul_left _
  have hcnn : ∀ n : ℤ, 0 ≤ 1 / (4 * π ^ 2 * (n : ℝ) ^ 2) := fun n => by positivity
  set B : ℝ := 10 * (N : ℝ) / Real.sqrt (-s.im) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]; apply div_nonneg (by positivity); exact Real.sqrt_nonneg _
  -- bound each summand
  have hSbound : ∀ n : ℤ,
      ‖((1 / (4 * π ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ)
          * ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I)‖
        ≤ (1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * B := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcnn n)]
    exact mul_le_mul_of_nonneg_left (hTbound n) (hcnn n)
  have hbsum : Summable (fun n : ℤ => (1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * B) := hc.mul_right B
  obtain ⟨_, hle⟩ := summable_and_norm_tsum_le_of_mode_bound' hbsum hSbound
  calc ‖∑' n : ℤ, ((1 / (4 * π ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ)
          * ∫ x in (1 : ℝ)..(N : ℝ), (x : ℂ) ^ (-s - 2) * Complex.exp (((2 * π * (n : ℝ)) * x : ℝ) * I)‖
      ≤ ∑' n : ℤ, (1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * B := hle
    _ = (∑' n : ℤ, 1 / (4 * π ^ 2 * (n : ℝ) ^ 2)) * B := tsum_mul_right

end RHTower
