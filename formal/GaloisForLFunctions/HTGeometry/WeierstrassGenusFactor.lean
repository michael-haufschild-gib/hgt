import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Weierstrass elementary factor of arbitrary genus

The genus-`p` elementary factor is the entire function

```text
E_p(w) = (1 - w) exp(w + w²/2 + ⋯ + w^p/p),
```

whose derivative collapses by the geometric telescoping `(1 - w)(1 + w + ⋯ + w^{p-1}) = 1 - w^p` to

```text
E_p'(w) = -w^p exp(w + ⋯ + w^p/p).
```

Since `E_p(0) = 1`, integrating that derivative along a segment gives the defining estimate of the
factor: on the half-disc `‖w‖ ≤ 1/2` the deviation of `E_p` from one is of order `p + 1`, with an
explicit constant depending only on the genus.

This is the convergence input of every Weierstrass product of genus `p`: paired with summability
of the inverse `(p+1)`-st powers of the zero set, it makes the product converge locally uniformly.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-! ## The truncated logarithm -/

/-- The truncated logarithm `∑_{k=1}^{p} w^k / k`. -/
def weierstrassLog (p : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range p, w ^ (k + 1) / ((k + 1 : ℕ) : ℂ)

@[simp] theorem weierstrassLog_zero_arg (p : ℕ) : weierstrassLog p 0 = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [zero_pow (Nat.succ_ne_zero k), zero_div]

theorem hasDerivAt_weierstrassLog (p : ℕ) (w : ℂ) :
    HasDerivAt (weierstrassLog p) (∑ k ∈ Finset.range p, w ^ k) w := by
  have hsum : HasDerivAt
      (fun z : ℂ => ∑ k ∈ Finset.range p, z ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (∑ k ∈ Finset.range p, w ^ k) w := by
    refine HasDerivAt.fun_sum (A := fun k (z : ℂ) => z ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (A' := fun k => w ^ k) fun k _ => ?_
    have hne : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero k
    have hpow : HasDerivAt (fun z : ℂ => z ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * w ^ k) w := by
      simpa using hasDerivAt_pow (k + 1) w
    have hdiv := hpow.div_const (((k + 1 : ℕ) : ℂ))
    rwa [mul_comm, mul_div_assoc, div_self hne, mul_one] at hdiv
  exact hsum

/-! ## The elementary factor -/

/-- The genus-`p` Weierstrass elementary factor. -/
def weierstrassFactor (p : ℕ) (w : ℂ) : ℂ := (1 - w) * Complex.exp (weierstrassLog p w)

@[simp] theorem weierstrassFactor_zero_arg (p : ℕ) : weierstrassFactor p 0 = 1 := by
  rw [weierstrassFactor, weierstrassLog_zero_arg, Complex.exp_zero, sub_zero, mul_one]

/-- **The collapsed derivative.**  The geometric telescoping cancels everything but the top
power. -/
theorem hasDerivAt_weierstrassFactor (p : ℕ) (w : ℂ) :
    HasDerivAt (weierstrassFactor p) (-(w ^ p) * Complex.exp (weierstrassLog p w)) w := by
  have hS := hasDerivAt_weierstrassLog p w
  have hexp := hS.cexp
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hmul := hlin.mul hexp
  have hgeom : (1 - w) * (∑ k ∈ Finset.range p, w ^ k) = 1 - w ^ p := mul_neg_geom_sum w p
  have heq : (-1 : ℂ) * Complex.exp (weierstrassLog p w)
      + (1 - w) * (Complex.exp (weierstrassLog p w) * ∑ k ∈ Finset.range p, w ^ k)
      = -(w ^ p) * Complex.exp (weierstrassLog p w) := by
    linear_combination Complex.exp (weierstrassLog p w) * hgeom
  rw [← heq]
  exact hmul

theorem differentiable_weierstrassFactor (p : ℕ) : Differentiable ℂ (weierstrassFactor p) :=
  fun w => (hasDerivAt_weierstrassFactor p w).differentiableAt

theorem deriv_weierstrassFactor (p : ℕ) (w : ℂ) :
    deriv (weierstrassFactor p) w = -(w ^ p) * Complex.exp (weierstrassLog p w) :=
  (hasDerivAt_weierstrassFactor p w).deriv

/-! ## The half-disc estimate -/

/-- The explicit genus constant: the truncated logarithm evaluated at the half-disc radius. -/
def weierstrassLogBound (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range p, (1 / 2 : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

theorem norm_weierstrassLog_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖weierstrassLog p w‖ ≤ weierstrassLogBound p := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_div, norm_pow, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg w) hw _

theorem norm_exp_weierstrassLog_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.exp (weierstrassLog p w)‖ ≤ Real.exp (weierstrassLogBound p) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr
    ((Complex.re_le_norm _).trans (norm_weierstrassLog_le p hw))

/-- **The genus estimate.**  On the half-disc the elementary factor deviates from one by at most a
genus-dependent constant times the `(p+1)`-st power. -/
theorem norm_weierstrassFactor_sub_one_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖weierstrassFactor p w - 1‖ ≤ Real.exp (weierstrassLogBound p) * ‖w‖ ^ (p + 1) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) ‖w‖) := convex_closedBall _ _
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    simp [Metric.mem_closedBall, norm_nonneg]
  have hmem : w ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    simp [Metric.mem_closedBall]
  have hbound : ∀ ζ ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖deriv (weierstrassFactor p) ζ‖ ≤ Real.exp (weierstrassLogBound p) * ‖w‖ ^ p := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    have hζhalf : ‖ζ‖ ≤ 1 / 2 := le_trans hζ hw
    rw [deriv_weierstrassFactor, norm_mul, norm_neg, norm_pow]
    calc ‖ζ‖ ^ p * ‖Complex.exp (weierstrassLog p ζ)‖
        ≤ ‖w‖ ^ p * Real.exp (weierstrassLogBound p) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg ζ) hζ p)
            (norm_exp_weierstrassLog_le p hζhalf) (norm_nonneg _) (by positivity)
      _ = Real.exp (weierstrassLogBound p) * ‖w‖ ^ p := by ring
  have hmv := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun ζ _ => (differentiable_weierstrassFactor p) ζ) hbound hzero hmem
  rw [weierstrassFactor_zero_arg, sub_zero] at hmv
  calc ‖weierstrassFactor p w - 1‖
      ≤ Real.exp (weierstrassLogBound p) * ‖w‖ ^ p * ‖w‖ := hmv
    _ = Real.exp (weierstrassLogBound p) * ‖w‖ ^ (p + 1) := by ring

end

end GaloisForLFunctions
