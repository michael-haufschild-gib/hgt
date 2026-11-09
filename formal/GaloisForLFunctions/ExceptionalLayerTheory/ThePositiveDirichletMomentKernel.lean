import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Positive Euler moments for a real Dirichlet character

For a quadratic character `χ`, the auxiliary product `ζ(s)L(s,χ)` has
nonnegative logarithmic Euler coefficients `(1+χ(n))Λ(n)`. Every odd
jet of `ζ'/ζ + L'/L` at `σ>1` and `σ+it` has nonnegative total real
part: its exact infinite series has kernel `1+cos(t log n)` and a
nonnegative logarithmic weight.

The jet identity and absolute convergence are proved for every order.
These inequalities supply the Euler side of exceptional-zero repulsion;
the complementary divisor identity must retain all Gamma terms.
-/

open Complex Filter Topology LSeries ArithmeticFunction
open scoped LSeries.notation

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

variable {q : ℕ} [NeZero q]

/-- The Euler coefficients of `−(ζ'/ζ + L'/L)`. -/
def exceptionalEulerCoefficient (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  (Λ n : ℂ) + χ n * (Λ n : ℂ)

/-- The logarithmic derivative of the auxiliary product `ζ(s)L(s,χ)`. -/
def exceptionalEulerLogDerivative (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  logDeriv riemannZeta s + logDeriv χ.LFunction s

omit [NeZero q] in
private theorem exceptionalEulerCoefficient_summable (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (exceptionalEulerCoefficient χ) s :=
  (LSeriesSummable_vonMangoldt hs).add
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)

omit [NeZero q] in
private theorem exceptionalEulerCoefficient_abscissa (χ : DirichletCharacter ℂ q) :
    abscissaOfAbsConv (exceptionalEulerCoefficient χ) ≤ 1 := by
  apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact exceptionalEulerCoefficient_summable χ (by simpa using hy)

private theorem exceptionalEulerLogDerivative_eq (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    exceptionalEulerLogDerivative χ s = -LSeries (exceptionalEulerCoefficient χ) s := by
  have hζ := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hχ := RHTower.neg_logDeriv_LFunction_eq_LSeries χ hs
  have ha := LSeries_add (LSeriesSummable_vonMangoldt hs)
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
  change LSeries (exceptionalEulerCoefficient χ) s = _ at ha
  rw [ha, exceptionalEulerLogDerivative, hζ]
  simp only [logDeriv_apply] at hχ ⊢
  linear_combination -hχ

/-- Every jet of the auxiliary logarithmic derivative is an absolutely
convergent Dirichlet series with logarithmic weights. -/
theorem exceptionalEulerLogDerivative_jet (χ : DirichletCharacter ℂ q)
    (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j (exceptionalEulerLogDerivative χ) s =
      (-1 : ℂ) ^ (j + 1) * LSeries (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) s := by
  have heq : exceptionalEulerLogDerivative χ =ᶠ[𝓝 s]
      fun w => -LSeries (exceptionalEulerCoefficient χ) w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact exceptionalEulerLogDerivative_eq χ hw
  have habs : abscissaOfAbsConv (exceptionalEulerCoefficient χ) < s.re :=
    lt_of_le_of_lt (exceptionalEulerCoefficient_abscissa χ) (by exact_mod_cast hs)
  rw [heq.iteratedDeriv_eq j]
  rw [show (fun w => -LSeries (exceptionalEulerCoefficient χ) w) =
    fun w => (-1 : ℂ) * LSeries (exceptionalEulerCoefficient χ) w by funext; ring]
  rw [iteratedDeriv_const_mul_field]
  change (-1 : ℂ) * iteratedDeriv j (LSeries (exceptionalEulerCoefficient χ)) s = _
  rw [LSeries_iteratedDeriv j habs]
  ring

private theorem logMul_iterate_apply (f : ℕ → ℂ) (j n : ℕ) :
    (LSeries.logMul^[j] f) n = (Complex.log n) ^ j * f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]
    ring

omit [NeZero q] in
private theorem exceptionalEulerCoefficient_real_nonneg {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (n : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ exceptionalEulerCoefficient χ n = (a : ℂ) := by
  rcases hχ (n : ZMod q) with hn | hn | hn
  · exact ⟨Λ n, vonMangoldt_nonneg, by simp [exceptionalEulerCoefficient, hn]⟩
  · refine ⟨2 * Λ n, mul_nonneg (by norm_num) vonMangoldt_nonneg, ?_⟩
    simp only [exceptionalEulerCoefficient, hn, one_mul, ofReal_mul, ofReal_ofNat]
    ring
  · exact ⟨0, le_rfl, by simp [exceptionalEulerCoefficient, hn]⟩

omit [NeZero q] in
private theorem exceptionalEulerLogCoefficient_real_nonneg {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (j n : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) n = (a : ℂ) := by
  obtain ⟨a, ha, heq⟩ := exceptionalEulerCoefficient_real_nonneg hχ n
  have hlog : 0 ≤ Real.log n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  refine ⟨Real.log n ^ j * a, mul_nonneg (pow_nonneg hlog j) ha, ?_⟩
  rw [logMul_iterate_apply, heq, ← Complex.natCast_log, ofReal_mul, ofReal_pow]

private theorem nonnegative_coefficient_two_point {f : ℕ → ℂ} (σ t : ℝ) (n : ℕ)
    (hf : ∃ a : ℝ, 0 ≤ a ∧ f n = (a : ℂ)) :
    0 ≤ (LSeries.term f (σ : ℂ) n).re +
      (LSeries.term f ((σ : ℂ) + t * I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨a, ha, hfa⟩ := hf
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', hfa]
  have hnσ : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl
  have habs := abs_re_le_norm ((a : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I))
  rw [norm_div, norm_real, Real.norm_of_nonneg ha, Complex.norm_natCast_cpow_of_pos hn] at habs
  have hneg := neg_abs_le ((a : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I)).re
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero] at habs
  rw [hnσ, div_ofReal_re, ofReal_re]
  linarith only [habs, hneg]

omit [NeZero q] in
/-- The kernel `1 + cos(t log n)` is nonnegative against every logarithmic
moment of the actual Euler coefficients `(1+χ(n))Λ(n)`. -/
theorem exceptionalEulerLogSeries_two_point_nonneg {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (j : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ (LSeries (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) (σ : ℂ)).re +
      (LSeries (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) ((σ : ℂ) + t * I)).re := by
  have hb : abscissaOfAbsConv (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) ≤ 1 := by
    simpa only [LSeries.absicssaOfAbsConv_logPowMul] using exceptionalEulerCoefficient_abscissa χ
  have hs : abscissaOfAbsConv (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) <
      ((σ : ℂ)).re := lt_of_le_of_lt hb (by exact_mod_cast hσ)
  have hst : abscissaOfAbsConv (LSeries.logMul^[j] (exceptionalEulerCoefficient χ)) <
      ((σ : ℂ) + t * I).re := by simpa using hs
  have h₁ := hasSum_re (LSeriesSummable_of_abscissaOfAbsConv_lt_re hs).LSeriesHasSum
  have h₂ := hasSum_re (LSeriesSummable_of_abscissaOfAbsConv_lt_re hst).LSeriesHasSum
  exact (h₁.add h₂).nonneg fun n =>
    nonnegative_coefficient_two_point σ t n (exceptionalEulerLogCoefficient_real_nonneg hχ j n)

/-- Every odd derivative of `ζ'/ζ + L'/L`, evaluated at a real point and
its vertical translate, has nonnegative total real part. -/
theorem exceptionalEuler_odd_jet_nonneg {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsQuadratic) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ (iteratedDeriv (2 * k + 1) (exceptionalEulerLogDerivative χ) (σ : ℂ)).re +
      (iteratedDeriv (2 * k + 1) (exceptionalEulerLogDerivative χ) ((σ : ℂ) + t * I)).re := by
  have hσc : 1 < (σ : ℂ).re := hσ
  have hσt : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  rw [exceptionalEulerLogDerivative_jet χ _ hσc, exceptionalEulerLogDerivative_jet χ _ hσt]
  have heven : (-1 : ℂ) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  rw [heven, one_mul, one_mul]
  exact exceptionalEulerLogSeries_two_point_nonneg hχ _ hσ t

end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.exceptionalEuler_odd_jet_nonneg
