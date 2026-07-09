import Mathlib

/-!
# The genus-one Weierstrass elementary factor and its quadratic estimate

The *genus-one Weierstrass elementary factor* is the entire function

`E₁(z) = (1 - z) · exp z`.

It equals `1` at the origin and vanishes to first order exactly at `z = 1`; these are the two
defining features of the factor Weierstrass uses to assemble canonical products of genus one from
a prescribed zero multiset `{aₙ}` as `∏ₙ E₁(z / aₙ)`.

The load-bearing analytic input for the convergence of such a product is the quadratic estimate

`‖E₁(z) - 1‖ ≤ ‖z‖²` on the closed unit disc `‖z‖ ≤ 1`.

It is what turns the summability `∑ₙ ‖aₙ‖⁻² < ∞` into normal (hence uniform-on-compacts)
convergence of `∏ₙ E₁(z / aₙ)`, so that the product is entire with divisor exactly `{aₙ}`.

The constant `1` is sharp and is obtained from the exact primitive representation

`E₁(z) - 1 = -∫₀¹ (d/dt)[(1 - t z)·exp(t z)] dt / (…)`,

concretely `E₁(z) - 1 = -z² · ∫₀¹ t · exp(t z) dt`, coming from `(d/dw)[(1-w)exp w] = -w·exp w` and
the fundamental theorem of calculus along the segment `w = t z`.  Bounding the integrand by
`‖ -z²·t·exp(t z) ‖ = ‖z‖²·t·exp(t·Re z) ≤ ‖z‖²·t·exp t` (valid because `Re z ≤ ‖z‖ ≤ 1`) and using
`∫₀¹ t·exp t dt = 1` gives the estimate with constant `1`.  The precise constant is immaterial for
the convergence application — any majorant of the form `C · ‖z‖²` would suffice.
-/

namespace RHTower

open Complex MeasureTheory

/-- The genus-one Weierstrass elementary factor `E₁(z) = (1 - z) · exp z`, the building block of
canonical products of genus one. -/
noncomputable def weierstrassE1 (z : ℂ) : ℂ := (1 - z) * Complex.exp z

/-- The genus-one factor normalises to `1` at the origin: `E₁(0) = 1`. -/
@[simp] theorem weierstrassE1_zero : weierstrassE1 0 = 1 := by
  simp [weierstrassE1, Complex.exp_zero]

/-- The genus-one factor has a simple zero at `z = 1`: `E₁(1) = 0`.  Rescaled by a root `aₙ`, this
is the simple zero the factor `E₁(z / aₙ)` contributes at `z = aₙ`. -/
@[simp] theorem weierstrassE1_one : weierstrassE1 1 = 0 := by
  simp [weierstrassE1]

/-- Sharp quadratic estimate driving canonical-product convergence: on the closed unit disc the
genus-one factor `E₁(z) = (1 - z)·exp z` differs from `1` by at most `‖z‖²`.

The bound is proved from the primitive representation `E₁(z) - 1 = -z²·∫₀¹ t·exp(t z) dt`, obtained
by the fundamental theorem of calculus from `(d/dw)[(1-w)·exp w] = -w·exp w`, together with the
integrand estimate `‖-z²·t·exp(t z)‖ = ‖z‖²·t·exp(t·Re z) ≤ ‖z‖²·t·exp t` (since `Re z ≤ ‖z‖ ≤ 1`)
and the value `∫₀¹ t·exp t dt = 1`. -/
theorem weierstrassE1_sub_one_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassE1 z - 1‖ ≤ ‖z‖ ^ 2 := by
  set f' : ℝ → ℂ := fun t => -(z ^ 2) * (t : ℂ) * Complex.exp ((t : ℂ) * z) with hf'def
  -- The FTC derivative datum on the segment `[0,1]`: `(d/dt)[(1 - t z)·exp(t z)] = -z²·t·exp(t z)`.
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (1 - (s : ℂ) * z) * Complex.exp ((s : ℂ) * z)) (f' t) t := by
    intro t _
    have hline : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const z
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * z))
        (Complex.exp ((t : ℂ) * z) * z) t := hline.cexp
    have hpoly : HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * z) (-z) t := by
      simpa using hline.const_sub 1
    have heq : f' t
        = -z * Complex.exp ((t : ℂ) * z) + (1 - (t : ℂ) * z) * (Complex.exp ((t : ℂ) * z) * z) := by
      simp only [hf'def]; ring
    rw [heq]
    exact hpoly.mul hexp
  have hcont : Continuous f' := by simp only [hf'def]; fun_prop
  have hint : IntervalIntegrable f' volume 0 1 := hcont.intervalIntegrable 0 1
  -- Representation of `E₁(z) - 1` as `∫₀¹ f'`.
  have hrep : weierstrassE1 z - 1 = ∫ t in (0 : ℝ)..1, f' t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [weierstrassE1, Complex.ofReal_one, Complex.ofReal_zero, zero_mul, sub_zero,
      mul_one, one_mul, Complex.exp_zero]
  -- The scalar primitive integral `∫₀¹ t·eᵗ dt = 1` (antiderivative `(t-1)·eᵗ`).
  have hval : ∫ t in (0 : ℝ)..1, t * Real.exp t = 1 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (s - 1) * Real.exp s) (t * Real.exp t) t := by
      intro t _
      have h := ((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)
      have heq : t * Real.exp t = 1 * Real.exp t + (id t - 1) * Real.exp t := by
        simp only [id_eq]; ring
      rw [heq]; exact h
    have hcont2 : Continuous (fun t : ℝ => t * Real.exp t) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont2.intervalIntegrable 0 1)]
    norm_num [Real.exp_zero]
  -- Pointwise majorant of the integrand's norm: `‖f' t‖ ≤ ‖z‖²·t·eᵗ` on `[0,1]`.
  have hptwise : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f' t‖ ≤ ‖z‖ ^ 2 * (t * Real.exp t) := by
    intro t ht
    have htnn : (0 : ℝ) ≤ t := ht.1
    have hnorm : ‖f' t‖ = ‖z‖ ^ 2 * (t * Real.exp (t * z.re)) := by
      simp only [hf'def]
      rw [norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, Complex.re_ofReal_mul, abs_of_nonneg htnn]
      ring
    rw [hnorm]
    have hzre : z.re ≤ 1 := le_trans (Complex.re_le_norm z) hz
    have hexple : Real.exp (t * z.re) ≤ Real.exp t := by
      apply Real.exp_le_exp.mpr; nlinarith [htnn, hzre]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hexple htnn
  -- Assemble: `‖∫ f'‖ ≤ ∫ ‖f'‖ ≤ ∫ ‖z‖²·t·eᵗ = ‖z‖²·∫ t·eᵗ = ‖z‖²`.
  rw [hrep]
  calc ‖∫ t in (0 : ℝ)..1, f' t‖
      ≤ ∫ t in (0 : ℝ)..1, ‖f' t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, ‖z‖ ^ 2 * (t * Real.exp t) := by
        refine intervalIntegral.integral_mono_on (by norm_num) hint.norm ?_ hptwise
        exact Continuous.intervalIntegrable (by fun_prop) 0 1
    _ = ‖z‖ ^ 2 * ∫ t in (0 : ℝ)..1, t * Real.exp t :=
        intervalIntegral.integral_const_mul _ _
    _ = ‖z‖ ^ 2 := by rw [hval]; ring

end RHTower
