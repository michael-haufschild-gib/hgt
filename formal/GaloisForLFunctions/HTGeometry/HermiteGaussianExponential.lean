import GaloisForLFunctions.HTGeometry.HermitePolynomialSpan

/-!
# Vanishing moments kill every exponential integral

If all Gaussian moments of a Schwartz function vanish then so does its integral against the
Gaussian times any complex exponential.  Expanding the exponential into its power series and
integrating term by term is legitimate because the Gaussian weight dominates every exponential:
`e^{a|x|-πx²} ≤ e^{a²/π} e^{-3πx²/4}`.

Specializing the exponent to `-2πitx` gives the vanishing of the Fourier transform of the Gaussian
multiple, the second step of the completeness of the Hermite system.

* `integrable_gauss_mul_exp_abs` : the dominating function is integrable.
* `integral_gaussMul_exp_eq_zero` : **every exponential integral vanishes.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The exponential series -/

theorem complex_hasSum_exp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem real_hasSum_exp (r : ℝ) :
    HasSum (fun n : ℕ => r ^ n / (Nat.factorial n : ℝ)) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-! ## The dominating function -/

theorem gauss_mul_exp_abs_le (a x : ℝ) :
    gaussReal x * Real.exp (|a| * |x|)
      ≤ Real.exp (a ^ (2 : ℕ) / π) * Real.exp (-(3 * π / 4) * x ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hkey : |a| * |x| ≤ a ^ (2 : ℕ) / π + π / 4 * x ^ (2 : ℕ) := by
    have hmain : 4 * π * (|a| * |x|) ≤ 4 * a ^ (2 : ℕ) + π ^ (2 : ℕ) * x ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (2 * |a| - π * |x|), sq_abs a, sq_abs x]
    have hdiff : a ^ (2 : ℕ) / π + π / 4 * x ^ (2 : ℕ) - |a| * |x|
        = (4 * a ^ (2 : ℕ) + π ^ (2 : ℕ) * x ^ (2 : ℕ) - 4 * π * (|a| * |x|)) / (4 * π) := by
      field_simp
    have hnn : 0 ≤ (4 * a ^ (2 : ℕ) + π ^ (2 : ℕ) * x ^ (2 : ℕ) - 4 * π * (|a| * |x|)) / (4 * π) :=
      div_nonneg (by linarith) (by positivity)
    rw [← hdiff] at hnn
    linarith
  rw [gaussReal, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hkey]

theorem integrable_gauss_mul_exp_abs (a : ℝ) :
    Integrable (fun x : ℝ => gaussReal x * Real.exp (|a| * |x|)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcont : Continuous fun x : ℝ => gaussReal x * Real.exp (|a| * |x|) := by
    refine Continuous.mul ?_ ?_
    · exact Real.continuous_exp.comp (by fun_prop)
    · exact Real.continuous_exp.comp (by fun_prop)
  have hdom : Integrable fun x : ℝ =>
      Real.exp (a ^ (2 : ℕ) / π) * Real.exp (-(3 * π / 4) * x ^ (2 : ℕ)) := by
    refine Integrable.const_mul ?_ _
    exact integrable_exp_neg_mul_sq (by positivity)
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (gaussReal_pos x).le (Real.exp_pos _).le)]
  exact gauss_mul_exp_abs_le a x

/-! ## Vanishing of the exponential integrals -/

/-- **A Schwartz function orthogonal to every Hermite function integrates to zero against the
Gaussian times any complex exponential.**  The exponential series is integrated term by term; the
Gaussian weight dominates every exponential, so dominated convergence applies, and each term is a
Gaussian moment, which vanishes. -/
theorem integral_gaussMul_exp_eq_zero {f : 𝓢(ℝ, ℂ)}
    (hf : ∀ n : ℕ, schwartzPair f (hermiteSchwartz n) = 0) (c : ℂ) :
    ∫ x : ℝ, f x * ((gaussReal x : ℝ) : ℂ) * Complex.exp (c * x) = 0 := by
  classical
  set M : ℝ := (SchwartzMap.seminorm ℂ 0 0) f with hM
  have hMnn : 0 ≤ M := apply_nonneg _ _
  have hfbound : ∀ x : ℝ, ‖f x‖ ≤ M := fun x => SchwartzMap.norm_le_seminorm ℂ f x
  -- the Gaussian moments vanish
  have hmom : ∀ n : ℕ, ∫ x : ℝ, f x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n = 0 := by
    intro n
    have h := schwartzPair_polyGauss_eq_zero hf (Polynomial.X ^ n)
    rw [schwartzPair_eq_integral] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n
      = f x * ((((Polynomial.X ^ n : Polynomial ℝ).eval x * gaussReal x : ℝ)) : ℂ)
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    ring
  -- the summands and the dominating family
  set F : ℕ → ℝ → ℂ := fun n x =>
    f x * ((gaussReal x : ℝ) : ℂ) * ((c * x) ^ n / (Nat.factorial n : ℂ)) with hF
  set bound : ℕ → ℝ → ℝ := fun n x =>
    M * (gaussReal x * ((‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ))) with hbound
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    refine Continuous.mul (Continuous.mul f.continuous ?_) (by fun_prop)
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume : Measure ℝ) := fun n =>
    (hFcont n).aestronglyMeasurable
  have hFbound : ∀ n, ∀ᵐ x : ℝ, ‖F n x‖ ≤ bound n x := by
    intro n
    filter_upwards with x
    have hgauss : ‖((gaussReal x : ℝ) : ℂ)‖ = gaussReal x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussReal_pos x)]
    have hpow : ‖((c * x) ^ n / (Nat.factorial n : ℂ))‖
        = (‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hF, norm_mul, norm_mul, hgauss, hpow]
    have h1 : ‖f x‖ * gaussReal x * ((‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ))
        = ‖f x‖ * (gaussReal x * ((‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ))) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hfbound x)
      (mul_nonneg (gaussReal_pos x).le (by positivity))
  have hsummable : ∀ᵐ x : ℝ, Summable fun n => bound n x := by
    filter_upwards with x
    exact ((real_hasSum_exp (‖c‖ * |x|)).summable.mul_left (gaussReal x)).mul_left M
  have htsum : ∀ x : ℝ, ∑' n, bound n x = M * (gaussReal x * Real.exp (‖c‖ * |x|)) := by
    intro x
    rw [hbound]
    rw [tsum_mul_left, tsum_mul_left, (real_hasSum_exp (‖c‖ * |x|)).tsum_eq]
  have hboundint : Integrable (fun x : ℝ => ∑' n, bound n x) (volume : Measure ℝ) := by
    have hrw : (fun x : ℝ => ∑' n, bound n x)
        = fun x : ℝ => M * (gaussReal x * Real.exp (‖c‖ * |x|)) := funext htsum
    rw [hrw]
    refine Integrable.const_mul ?_ _
    have habs : ‖c‖ = |‖c‖| := (abs_of_nonneg (norm_nonneg c)).symm
    rw [habs]
    exact integrable_gauss_mul_exp_abs ‖c‖
  have hlim : ∀ᵐ x : ℝ, HasSum (fun n => F n x) (f x * ((gaussReal x : ℝ) : ℂ)
      * Complex.exp (c * x)) := by
    filter_upwards with x
    exact (complex_hasSum_exp ((c : ℂ) * x)).mul_left _
  have hsum := MeasureTheory.hasSum_integral_of_dominated_convergence bound hFmeas hFbound
    hsummable hboundint hlim
  have hzero : ∀ n : ℕ, ∫ x : ℝ, F n x = 0 := by
    intro n
    have hrw : (fun x : ℝ => F n x)
        = fun x : ℝ => (c ^ n / (Nat.factorial n : ℂ))
          * (f x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n) := by
      funext x
      rw [hF]
      field_simp
      ring
    rw [hrw, MeasureTheory.integral_const_mul, hmom n, mul_zero]
  rw [funext hzero] at hsum
  exact (hasSum_zero.unique hsum).symm

end GaloisForLFunctions

end
