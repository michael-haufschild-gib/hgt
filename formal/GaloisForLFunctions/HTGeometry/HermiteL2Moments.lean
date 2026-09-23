import GaloisForLFunctions.HTGeometry.HermiteCompleteness
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Vanishing Gaussian moments of a square integrable function

An `L²` function orthogonal to every Hermite function is orthogonal to every polynomial multiple
of the Gaussian, because the Hermite polynomials span the polynomial ring.  Expanding a complex
exponential into its power series and integrating term by term then shows that the function
integrates to zero against the Gaussian times any complex exponential: the Gaussian weight
dominates every exponential, and Cauchy–Schwarz makes the dominating function integrable against
the square integrable factor.

This is the `L²` counterpart of the Schwartz-space computation, with the uniform bound on a
Schwartz function replaced by Hölder's inequality.

* `inner_polyGaussSchwartz_toLp_eq_zero` : orthogonality to every polynomial Gaussian.
* `integral_gaussMul_exp_l2_eq_zero` : **every exponential integral vanishes.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

theorem gaussReal_le_one (x : ℝ) : gaussReal x ≤ 1 := by
  rw [gaussReal]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

/-! ## Orthogonality to the polynomial Gaussians -/

variable {u : Lp ℂ 2 (volume : Measure ℝ)}

/-- **An `L²` function orthogonal to every Hermite function is orthogonal to every polynomial
multiple of the Gaussian**, since the Hermite polynomials span the polynomial ring. -/
theorem inner_polyGaussSchwartz_toLp_eq_zero
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0)
    (p : Polynomial ℝ) :
    inner ℂ ((polyGaussSchwartz p).toLp 2 (volume : Measure ℝ)) u = 0 := by
  have hmem : p ∈ Submodule.span ℝ (Set.range hermitePoly) := by
    rw [hermitePoly_span_eq_top]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    exact hu n
  | zero =>
    have hzero : polyGaussSchwartz (0 : Polynomial ℝ) = 0 := by
      apply SchwartzMap.ext
      intro x
      show (((0 : Polynomial ℝ).eval x * gaussReal x : ℝ) : ℂ) = 0
      simp
    have hLp : (polyGaussSchwartz (0 : Polynomial ℝ)).toLp 2 (volume : Measure ℝ) = 0 := by
      rw [hzero]
      have h := map_zero (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
      rwa [SchwartzMap.toLpCLM_apply] at h
    rw [hLp, inner_zero_left]
  | add q r _ _ hq hr =>
    have hLp : (polyGaussSchwartz (q + r)).toLp 2 (volume : Measure ℝ)
        = (polyGaussSchwartz q).toLp 2 (volume : Measure ℝ)
          + (polyGaussSchwartz r).toLp 2 (volume : Measure ℝ) := by
      rw [polyGaussSchwartz_add]
      have h := map_add (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
        (polyGaussSchwartz q) (polyGaussSchwartz r)
      rwa [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply,
        SchwartzMap.toLpCLM_apply] at h
    rw [hLp, inner_add_left, hq, hr, add_zero]
  | smul c q _ hq =>
    have hsm : (c • polyGaussSchwartz q) = ((c : ℂ)) • polyGaussSchwartz q := by
      apply SchwartzMap.ext
      intro x
      show c • (polyGaussSchwartz q x) = (c : ℂ) * polyGaussSchwartz q x
      rw [Complex.real_smul]
    have hLp : (polyGaussSchwartz (c • q)).toLp 2 (volume : Measure ℝ)
        = (c : ℂ) • (polyGaussSchwartz q).toLp 2 (volume : Measure ℝ) := by
      rw [polyGaussSchwartz_smul, hsm]
      have h := map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) (c : ℂ)
        (polyGaussSchwartz q)
      rwa [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply] at h
    rw [hLp, inner_smul_left, hq, mul_zero]

/-- The Gaussian moments of an `L²` function orthogonal to every Hermite function vanish. -/
theorem integral_polyGauss_mul_l2_eq_zero
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0)
    (p : Polynomial ℝ) :
    ∫ x : ℝ, (u : ℝ → ℂ) x * ((p.eval x * gaussReal x : ℝ) : ℂ) = 0 := by
  have h := inner_polyGaussSchwartz_toLp_eq_zero hu p
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (polyGaussSchwartz p) 2 (volume : Measure ℝ)] with x hx
  rw [hx, RCLike.inner_apply, polyGaussSchwartz_apply, Complex.conj_ofReal, mul_comm]

/-! ## The dominating function is integrable against an `L²` factor -/

theorem memLp_gauss_mul_exp_abs (a : ℝ) :
    MemLp (fun x : ℝ => gaussReal x * Real.exp (|a| * |x|)) 2 (volume : Measure ℝ) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcont : Continuous fun x : ℝ => gaussReal x * Real.exp (|a| * |x|) := by
    refine Continuous.mul ?_ ?_
    · exact Real.continuous_exp.comp (by fun_prop)
    · exact Real.continuous_exp.comp (by fun_prop)
  have hdom : MemLp (fun x : ℝ => Real.exp (a ^ (2 : ℕ) / π) * Real.exp (-(3 * π / 4) * x ^ (2 : ℕ))) 2
      (volume : Measure ℝ) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).mpr ?_
    have hint : Integrable (fun x : ℝ =>
        Real.exp (a ^ (2 : ℕ) / π) ^ (2 : ℕ) * Real.exp (-(3 * π / 2) * x ^ (2 : ℕ))) (volume : Measure ℝ) :=
      (integrable_exp_neg_mul_sq (by positivity)).const_mul _
    refine hint.congr ?_
    filter_upwards with x
    rw [mul_pow, sq (Real.exp (-(3 * π / 4) * x ^ (2 : ℕ))), ← Real.exp_add]
    ring_nf
  refine hdom.of_le hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hdomnn : (0 : ℝ) ≤ Real.exp (a ^ (2 : ℕ) / π) * Real.exp (-(3 * π / 4) * x ^ (2 : ℕ)) := by
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (gaussReal_pos x).le (Real.exp_pos _).le),
    abs_of_nonneg hdomnn]
  exact gauss_mul_exp_abs_le a x

theorem integrable_norm_l2_gauss_mul_exp_abs (a : ℝ) :
    Integrable (fun x : ℝ => ‖(u : ℝ → ℂ) x‖ * (gaussReal x * Real.exp (|a| * |x|)))
      (volume : Measure ℝ) := by
  have h1 : MemLp (fun x : ℝ => ‖(u : ℝ → ℂ) x‖) 2 (volume : Measure ℝ) := (Lp.memLp u).norm
  have h2 := memLp_gauss_mul_exp_abs a
  have hmul : MemLp ((fun x : ℝ => ‖(u : ℝ → ℂ) x‖) *
      fun x : ℝ => gaussReal x * Real.exp (|a| * |x|)) 1 (volume : Measure ℝ) := h2.mul h1
  have hint := memLp_one_iff_integrable.mp hmul
  have hfun : ((fun x : ℝ => ‖(u : ℝ → ℂ) x‖) *
      fun x : ℝ => gaussReal x * Real.exp (|a| * |x|))
      = fun x : ℝ => ‖(u : ℝ → ℂ) x‖ * (gaussReal x * Real.exp (|a| * |x|)) := rfl
  rwa [hfun] at hint

/-! ## Vanishing of the exponential integrals -/

/-- **An `L²` function orthogonal to every Hermite function integrates to zero against the
Gaussian times any complex exponential.**  The exponential series is integrated term by term; the
Gaussian weight dominates every exponential and Cauchy–Schwarz makes the dominating function
integrable, so dominated convergence applies, and each term is a Gaussian moment. -/
theorem integral_gaussMul_exp_l2_eq_zero
    (hu : ∀ n : ℕ, inner ℂ ((hermiteSchwartz n).toLp 2 (volume : Measure ℝ)) u = 0) (c : ℂ) :
    ∫ x : ℝ, (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * Complex.exp (c * x) = 0 := by
  classical
  have humeas : AEStronglyMeasurable (u : ℝ → ℂ) (volume : Measure ℝ) :=
    (Lp.memLp u).aestronglyMeasurable
  have hmom : ∀ n : ℕ,
      ∫ x : ℝ, (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n = 0 := by
    intro n
    have h := integral_polyGauss_mul_l2_eq_zero hu (Polynomial.X ^ n)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n
      = (u : ℝ → ℂ) x * ((((Polynomial.X ^ n : Polynomial ℝ)).eval x * gaussReal x : ℝ) : ℂ)
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    ring
  set F : ℕ → ℝ → ℂ := fun n x =>
    (u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * ((c * x) ^ n / (Nat.factorial n : ℂ)) with hF
  set bound : ℕ → ℝ → ℝ := fun n x =>
    ‖(u : ℝ → ℂ) x‖ * (gaussReal x * ((‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ))) with hbound
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume : Measure ℝ) := by
    intro n
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul humeas ?_) ?_
    · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop)))
        |>.aestronglyMeasurable
    · exact (by fun_prop : Continuous fun x : ℝ =>
        ((c * x) ^ n / (Nat.factorial n : ℂ))).aestronglyMeasurable
  have hFbound : ∀ n, ∀ᵐ x : ℝ, ‖F n x‖ ≤ bound n x := by
    intro n
    filter_upwards with x
    have hgauss : ‖((gaussReal x : ℝ) : ℂ)‖ = gaussReal x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussReal_pos x)]
    have hpow : ‖((c * x) ^ n / (Nat.factorial n : ℂ))‖
        = (‖c‖ * |x|) ^ n / (Nat.factorial n : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hF, hbound, norm_mul, norm_mul, hgauss, hpow]
    ring_nf
    exact le_refl _
  have hsummable : ∀ᵐ x : ℝ, Summable fun n => bound n x := by
    filter_upwards with x
    exact ((real_hasSum_exp (‖c‖ * |x|)).summable.mul_left (gaussReal x)).mul_left _
  have htsum : ∀ x : ℝ, ∑' n, bound n x
      = ‖(u : ℝ → ℂ) x‖ * (gaussReal x * Real.exp (‖c‖ * |x|)) := by
    intro x
    rw [hbound, tsum_mul_left, tsum_mul_left, (real_hasSum_exp (‖c‖ * |x|)).tsum_eq]
  have hboundint : Integrable (fun x : ℝ => ∑' n, bound n x) (volume : Measure ℝ) := by
    have hrw : (fun x : ℝ => ∑' n, bound n x)
        = fun x : ℝ => ‖(u : ℝ → ℂ) x‖ * (gaussReal x * Real.exp (‖c‖ * |x|)) := funext htsum
    rw [hrw]
    have habs : ‖c‖ = |‖c‖| := (abs_of_nonneg (norm_nonneg c)).symm
    rw [habs]
    exact integrable_norm_l2_gauss_mul_exp_abs (u := u) ‖c‖
  have hlim : ∀ᵐ x : ℝ, HasSum (fun n => F n x)
      ((u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * Complex.exp (c * x)) := by
    filter_upwards with x
    exact (complex_hasSum_exp ((c : ℂ) * x)).mul_left _
  have hsum := MeasureTheory.hasSum_integral_of_dominated_convergence bound hFmeas hFbound
    hsummable hboundint hlim
  have hzero : ∀ n : ℕ, ∫ x : ℝ, F n x = 0 := by
    intro n
    have hrw : (fun x : ℝ => F n x)
        = fun x : ℝ => (c ^ n / (Nat.factorial n : ℂ))
          * ((u : ℝ → ℂ) x * ((gaussReal x : ℝ) : ℂ) * (x : ℂ) ^ n) := by
      funext x
      rw [hF]
      field_simp
      ring
    rw [hrw, MeasureTheory.integral_const_mul, hmom n, mul_zero]
  rw [funext hzero] at hsum
  exact (hasSum_zero.unique hsum).symm

end GaloisForLFunctions

end
