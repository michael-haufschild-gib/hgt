import GaloisForLFunctions.RHTower.TwoGaussianSourceCounterexample
import GaloisForLFunctions.RHTower.HedenmalmQuantileNormalForm
import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Every literal derivative of the two-Gaussian source

Polynomial envelopes prove admission to the ORIGINAL reciprocal-density source
space at every order. The actual pinned primitive kills the source and lowers
each ordinary derivative. No finite kernel energy or bounded inverse is assumed.
-/

open MeasureTheory Filter Set GaloisForLFunctions.HTGeometry
open RHTower.HedenmalmQuantile
open scoped Topology ENNReal

noncomputable section

namespace RHTower.TwoGaussianComparison

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev μS := volume.withDensity (realDensity (sourceWeight source))

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The exact polynomial recurrence for ordinary Gaussian derivatives. -/
def derivativePolynomial (b : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (derivativePolynomial b n).derivative -
      Polynomial.C (2 * b) * Polynomial.X * derivativePolynomial b n

/-- An explicit polynomial envelope, identified below with the ordinary derivative. -/
def gaussianDerivative (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (derivativePolynomial b n).eval x * Real.exp (-(b * x ^ 2))

theorem continuous_gaussianDerivative (b : ℝ) (n : ℕ) :
    Continuous (gaussianDerivative b n) := by
  unfold gaussianDerivative
  fun_prop

theorem hasDerivAt_gaussianDerivative (b : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (gaussianDerivative b n) (gaussianDerivative b (n + 1) x) x := by
  have hp := (derivativePolynomial b n).hasDerivAt x
  have hg := (((hasDerivAt_id x).pow 2).const_mul b).neg.exp
  apply (hp.mul hg).congr_deriv
  simp only [gaussianDerivative, derivativePolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Pi.neg_apply, Pi.pow_apply, id_eq]
  ring

theorem iteratedDeriv_gaussian (b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (-(b * x ^ 2))) =
      gaussianDerivative b n := by
  induction n with
  | zero =>
      funext x
      simp [iteratedDeriv_zero, gaussianDerivative, derivativePolynomial]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_gaussianDerivative b n x).deriv

theorem iteratedDeriv_density (n : ℕ) :
    iteratedDeriv n density =
      fun x => gaussianDerivative 1 n x + gaussianDerivative 2 n x := by
  induction n with
  | zero =>
      funext x
      simp [iteratedDeriv_zero, gaussianDerivative, derivativePolynomial, density]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact ((hasDerivAt_gaussianDerivative 1 n x).add
        (hasDerivAt_gaussianDerivative 2 n x)).deriv

/-- The actual ordinary derivative of the literal source, in complex coordinates. -/
def derivativeFunction (n : ℕ) (x : ℝ) : ℂ :=
  (iteratedDeriv n density x : ℝ)

theorem derivativeFunction_eq (n : ℕ) (x : ℝ) :
    derivativeFunction n x =
      ((gaussianDerivative 1 n x + gaussianDerivative 2 n x : ℝ) : ℂ) := by
  rw [derivativeFunction, iteratedDeriv_density]

private theorem derivativeFunction_eq_fun (n : ℕ) :
    derivativeFunction n = fun x : ℝ =>
      ((gaussianDerivative 1 n x + gaussianDerivative 2 n x : ℝ) : ℂ) :=
  funext (derivativeFunction_eq n)

theorem derivativeFunction_zero (x : ℝ) :
    derivativeFunction 0 x = (source.k x : ℂ) := by
  simp [derivativeFunction, iteratedDeriv_zero, source]

theorem continuous_derivativeFunction (n : ℕ) :
    Continuous (derivativeFunction n) := by
  have h := Complex.continuous_ofReal.comp
    ((continuous_gaussianDerivative 1 n).add (continuous_gaussianDerivative 2 n))
  rw [derivativeFunction_eq_fun]
  exact h

theorem hasDerivAt_derivativeFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (derivativeFunction n) (derivativeFunction (n + 1) x) x := by
  have h := ((hasDerivAt_gaussianDerivative 1 n x).add
    (hasDerivAt_gaussianDerivative 2 n x)).ofReal_comp
  rw [derivativeFunction_eq_fun, derivativeFunction_eq]
  exact h

private theorem integrable_gaussianDerivative {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (gaussianDerivative b n) :=
  integrable_polyEval_mul_gauss (derivativePolynomial b n) hb

theorem integrable_derivativeFunction (n : ℕ) :
    Integrable (derivativeFunction n) := by
  have h : Integrable (fun x : ℝ =>
      ((gaussianDerivative 1 n x + gaussianDerivative 2 n x : ℝ) : ℂ)) :=
    ((integrable_gaussianDerivative (by norm_num : (0 : ℝ) < 1) n).add
      (integrable_gaussianDerivative (by norm_num : (0 : ℝ) < 2) n)).ofReal
  rw [derivativeFunction_eq_fun]
  exact h

theorem derivativeFunction_tendsto_atBot (n : ℕ) :
    Tendsto (derivativeFunction n) atBot (𝓝 0) := by
  have h₁ := tendsto_polyEval_mul_gauss_atBot (derivativePolynomial 1 n)
    (by norm_num : (0 : ℝ) < 1)
  have h₂ := tendsto_polyEval_mul_gauss_atBot (derivativePolynomial 2 n)
    (by norm_num : (0 : ℝ) < 2)
  have hr : Tendsto (fun x => gaussianDerivative 1 n x + gaussianDerivative 2 n x)
      atBot (𝓝 0) := by
    simpa only [gaussianDerivative, add_zero] using h₁.add h₂
  have h := (Complex.continuous_ofReal.tendsto 0).comp hr
  rw [derivativeFunction_eq_fun]
  convert h using 1 <;> rfl

theorem derivativeFunction_tendsto_atTop (n : ℕ) :
    Tendsto (derivativeFunction n) atTop (𝓝 0) := by
  have h₁ := tendsto_polyEval_mul_gauss_atTop (derivativePolynomial 1 n)
    (by norm_num : (0 : ℝ) < 1)
  have h₂ := tendsto_polyEval_mul_gauss_atTop (derivativePolynomial 2 n)
    (by norm_num : (0 : ℝ) < 2)
  have hr : Tendsto (fun x => gaussianDerivative 1 n x + gaussianDerivative 2 n x)
      atTop (𝓝 0) := by
    simpa only [gaussianDerivative, add_zero] using h₁.add h₂
  have h := (Complex.continuous_ofReal.tendsto 0).comp hr
  rw [derivativeFunction_eq_fun]
  convert h using 1 <;> rfl

theorem integral_derivativeFunction_succ (n : ℕ) :
    (∫ x, derivativeFunction (n + 1) x) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_derivativeFunction n)
    (integrable_derivativeFunction (n + 1)) (integrable_derivativeFunction n)

theorem integral_Iic_derivativeFunction_succ (n : ℕ) (x : ℝ) :
    (∫ y in Iic x, derivativeFunction (n + 1) y) = derivativeFunction n x := by
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun y _ => hasDerivAt_derivativeFunction n y)
    (integrable_derivativeFunction (n + 1)).integrableOn
    (derivativeFunction_tendsto_atBot n)

theorem sourceInverse_derivativeFunction_zero (x : ℝ) :
    sourceInverse source (derivativeFunction 0) x = 0 := by
  rw [sourceInverse]
  simp_rw [derivativeFunction_zero]
  rw [integral_complex_ofReal]
  change Complex.I * (∫ y in Iic x,
    ((source.k y : ℂ) - ((source.mass : ℂ) / (source.mass : ℂ)) * (source.k y : ℂ))) = 0
  have hM : (source.mass : ℂ) ≠ 0 := by exact_mod_cast source.mass_ne_zero
  rw [div_self hM]
  simp

theorem sourceInverse_derivativeFunction_succ (n : ℕ) (x : ℝ) :
    sourceInverse source (derivativeFunction (n + 1)) x =
      Complex.I * derivativeFunction n x := by
  rw [sourceInverse, integral_derivativeFunction_succ]
  simp only [zero_div, zero_mul, sub_zero]
  rw [integral_Iic_derivativeFunction_succ]

private theorem polynomial_gaussian_memLp (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b)
    (hdom : ∀ x : ℝ, Real.exp (-(b * x ^ 2)) ≤ source.k x) :
    MemLp (fun x : ℝ => ((p.eval x * Real.exp (-(b * x ^ 2)) : ℝ) : ℂ)) 2 μS := by
  have hc : Continuous (fun x : ℝ =>
      ((p.eval x * Real.exp (-(b * x ^ 2)) : ℝ) : ℂ)) := by fun_prop
  have hm := (measurable_sqrtWeight (measurable_sourceWeight source)).aestronglyMeasurable.mul
    (hc.aestronglyMeasurable (μ := volume))
  apply (memLp_two_withDensity_iff (measurable_sourceWeight source)
    (sourceWeight_pos source)).mpr
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine (integrable_polyEval_mul_gauss (p ^ 2) hb).mono' (hm.norm.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs : ‖sqrtWeight (sourceWeight source) x *
      ((p.eval x * Real.exp (-(b * x ^ 2)) : ℝ) : ℂ)‖ ^ 2 =
      (source.k x)⁻¹ * (p.eval x * Real.exp (-(b * x ^ 2))) ^ 2 := by
    rw [norm_mul, mul_pow, sqrtWeight, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt (sourceWeight_pos source x).le]
    rfl
  change ‖sqrtWeight (sourceWeight source) x *
    ((p.eval x * Real.exp (-(b * x ^ 2)) : ℝ) : ℂ)‖ ^ 2 ≤
    (p ^ 2).eval x * Real.exp (-(b * x ^ 2))
  rw [hs, Polynomial.eval_pow]
  have h := mul_le_mul_of_nonneg_left (hdom x)
    (mul_nonneg (sq_nonneg (p.eval x)) (Real.exp_pos (-(b * x ^ 2))).le)
  have hdiv : (p.eval x * Real.exp (-(b * x ^ 2))) ^ 2 / source.k x ≤
      p.eval x ^ 2 * Real.exp (-(b * x ^ 2)) := by
    apply (div_le_iff₀ (source.pos_k x)).mpr
    convert h using 1
    ring
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- EVERY actual derivative belongs to ORIGINAL reciprocal-density L². -/
theorem derivativeFunction_memLp (n : ℕ) : MemLp (derivativeFunction n) 2 μS := by
  have h₁ := polynomial_gaussian_memLp (derivativePolynomial 1 n)
    (by norm_num : (0 : ℝ) < 1) (fun x => by
      change Real.exp (-(1 * x ^ 2)) ≤ density x
      dsimp [density]
      have hp := Real.exp_pos (-2 * x ^ 2)
      simp only [one_mul]
      linarith)
  have h₂ := polynomial_gaussian_memLp (derivativePolynomial 2 n)
    (by norm_num : (0 : ℝ) < 2) (fun x => by
      change Real.exp (-(2 * x ^ 2)) ≤ density x
      dsimp [density]
      have hp := Real.exp_pos (-x ^ 2)
      have he : -(2 * x ^ 2) = -2 * x ^ 2 := by ring
      rw [he]
      linarith)
  refine MemLp.ae_eq ?_ (h₁.add h₂)
  filter_upwards with x
  simp only [Pi.add_apply, derivativeFunction_eq, gaussianDerivative, Complex.ofReal_add]

/-- Genuine source vectors of the admitted ordinary derivatives. -/
def sourceDerivativeVector (n : ℕ) : SourceSpace source :=
  (derivativeFunction_memLp n).toLp (derivativeFunction n)

theorem sourceDerivativeVector_coe (n : ℕ) :
    sourceDerivativeVector n =ᵐ[μS] derivativeFunction n :=
  MemLp.coeFn_toLp _

end RHTower.TwoGaussianComparison
