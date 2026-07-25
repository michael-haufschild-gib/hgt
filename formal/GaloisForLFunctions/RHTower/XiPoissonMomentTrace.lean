import GaloisForLFunctions.RHTower.XiPoissonMomentSummable

/-!
# The moment traces of the Poisson divisor

`xiPoissonMomentTraceC n tau = sum_rho alpha^_rho ^ n * exp (-tau alpha^_rho)` is the `n`-th
alternating derivative of the Poisson trace.  Under RH every Poisson point is a nonnegative real, so
every summand is a nonnegative real and the whole family is nonnegative -- the trace is completely
monotone.  A single negative value therefore refutes RH, for any `n`.

The detection at `n >= 1` is geometric rather than arithmetic: at a fixed height an off-critical copy
lies strictly further from the origin than a critical one, and the `n`-th power separates them
(`HTGeometry.eq_zero_of_forall_mul_pow_le`).
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `n`-th moment trace of the Poisson divisor. -/
def xiPoissonMomentTraceC (n : ℕ) (τ : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiPoissonPoint q ^ n * xiPoissonTerm τ q

theorem summable_norm_xiPoissonMomentTerm {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    Summable (fun q : XiZeroCopy => ‖xiPoissonPoint q ^ n * xiPoissonTerm τ q‖) := by
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((summable_pow_mul_xiPoissonWeight hτ n).mul_left (Real.exp (|τ.im| / 2)))
  rw [norm_mul, norm_pow]
  have h := norm_xiPoissonTerm_le τ q
  calc ‖xiPoissonPoint q‖ ^ n * ‖xiPoissonTerm τ q‖
      ≤ ‖xiPoissonPoint q‖ ^ n * (Real.exp (|τ.im| / 2) * xiPoissonWeight τ.re q) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg _) n)
    _ = Real.exp (|τ.im| / 2) * (‖xiPoissonPoint q‖ ^ n * xiPoissonWeight τ.re q) := by ring

theorem summable_xiPoissonMomentTerm {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    Summable (fun q : XiZeroCopy => xiPoissonPoint q ^ n * xiPoissonTerm τ q) :=
  (summable_norm_xiPoissonMomentTerm hτ n).of_norm

/-- Under RH each moment summand is a nonnegative real. -/
theorem re_xiPoissonMomentTerm_nonneg_of_rh (hRH : RiemannHypothesis) (t : ℝ)
    (n : ℕ) (q : XiZeroCopy) :
    0 ≤ (xiPoissonPoint q ^ n * xiPoissonTerm ((t : ℝ) : ℂ) q).re := by
  have him : (xiPoissonPoint q).im = 0 := xiPoissonPoint_im_eq_zero_of_rh hRH q
  have hR : 0 ≤ (xiPoissonPoint q).re := xiPoissonPoint_re_nonneg q
  have hsplit : xiPoissonPoint q = (((xiPoissonPoint q).re : ℝ) : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im (xiPoissonPoint q)]
    rw [him]
    simp
  have hterm : xiPoissonTerm ((t : ℝ) : ℂ) q =
      ((Real.exp (-(t * (xiPoissonPoint q).re)) : ℝ) : ℂ) := by
    rw [xiPoissonTerm, hsplit, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    norm_cast
    congr 1
    ring
  rw [hterm, hsplit, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg hR n) (Real.exp_pos _).le

/-- **RH implies every moment trace is nonnegative** -- complete monotonicity of the Poisson
trace. -/
theorem re_xiPoissonMomentTraceC_nonneg_of_rh (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (n : ℕ) : 0 ≤ (xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re := by
  have hre : (0 : ℝ) < (((t : ℝ) : ℂ)).re := by simpa using ht
  have hsum := summable_xiPoissonMomentTerm hre n
  have hmap : (xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re =
      ∑' q : XiZeroCopy, (xiPoissonPoint q ^ n * xiPoissonTerm ((t : ℝ) : ℂ) q).re := by
    rw [xiPoissonMomentTraceC, ← Complex.reCLM_apply,
      ContinuousLinearMap.map_tsum Complex.reCLM hsum]
    rfl
  rw [hmap]
  exact tsum_nonneg fun q => re_xiPoissonMomentTerm_nonneg_of_rh hRH t n q

/-- **A moment RH-disproof endpoint.**  One negative moment trace at one positive real time refutes
RH, for any order `n`. -/
theorem not_riemannHypothesis_of_re_xiPoissonMomentTraceC_neg {t : ℝ} (ht : 0 < t) (n : ℕ)
    (h : (xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re < 0) :
    ¬ RiemannHypothesis := fun hRH =>
  absurd (re_xiPoissonMomentTraceC_nonneg_of_rh hRH ht n) (not_le.mpr h)

end

end RHTower
