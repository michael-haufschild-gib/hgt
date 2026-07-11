import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification
import GaloisForLFunctions.U0.PolyAsymptotics

/-!
# Exact order-one growth of polynomially weighted cosh envelopes

The product of a displaced cosh quartet envelope with a nonzero polynomial has exact entire order
one.  Rather than introduce a wrapper around the classical order definition, this module proves the
stronger estimates used by Hadamard arguments directly:

* a global polynomial-times-`exp (2 ‖z‖)` upper bound;
* an `exp (2x)` lower bound on the positive real ray.

Together they form an explicit two-sided exponential sandwich and close the exact-order interface
in finite quartet-passport realization.
-/

open Complex Polynomial Filter Topology Set

namespace RHTower

noncomputable section

/-- Complex `cosh` is bounded by the exponential of the argument norm. -/
theorem norm_cosh_le_exp_norm (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have htri := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at htri
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hnre : -z.re ≤ ‖z‖ := by
    simpa using Complex.re_le_norm (-z)
  have h1 := Real.exp_le_exp.mpr hre
  have h2 := Real.exp_le_exp.mpr hnre
  linarith

/-- Global exponential-type bound for the displaced cosh quartet envelope. -/
theorem norm_coshQuartetEnvelope_le (a : ℝ) (z : ℂ) :
    ‖coshQuartetEnvelope a z‖ ≤ Real.exp (2 * (‖z‖ + |a|)) := by
  rw [coshQuartetEnvelope, norm_mul]
  have hminus := norm_cosh_le_exp_norm (z - (a : ℂ))
  have hplus := norm_cosh_le_exp_norm (z + (a : ℂ))
  have hshiftMinus : ‖z - (a : ℂ)‖ ≤ ‖z‖ + |a| := by
    simpa using norm_sub_le z (a : ℂ)
  have hshiftPlus : ‖z + (a : ℂ)‖ ≤ ‖z‖ + |a| := by
    have := norm_add_le z (a : ℂ)
    simpa using this
  have heminus := Real.exp_le_exp.mpr hshiftMinus
  have heplus := Real.exp_le_exp.mpr hshiftPlus
  calc
    ‖Complex.cosh (z - (a : ℂ))‖ * ‖Complex.cosh (z + (a : ℂ))‖
        ≤ Real.exp ‖z - (a : ℂ)‖ * Real.exp ‖z + (a : ℂ)‖ :=
      mul_le_mul hminus hplus (norm_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (‖z‖ + |a|) * Real.exp (‖z‖ + |a|) :=
      mul_le_mul heminus heplus (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * (‖z‖ + |a|)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Sum of coefficient norms used in the global polynomial bound. -/
def polynomialCoeffNormSum (P : Polynomial ℂ) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖

/-- A polynomial is globally bounded by its coefficient-norm sum times `(1 + ‖z‖)^degree`. -/
theorem norm_polynomial_eval_le (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ≤ polynomialCoeffNormSum P * (1 + ‖z‖) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, polynomialCoeffNormSum, Finset.sum_mul]
  apply norm_sum_le_of_le
  intro i hi
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hirange : i < P.natDegree + 1 := Finset.mem_range.mp hi
  have hzle : ‖z‖ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  calc
    ‖z‖ ^ i ≤ (1 + ‖z‖) ^ i := by gcongr
    _ ≤ (1 + ‖z‖) ^ P.natDegree := by
      apply pow_le_pow_right₀ (by linarith [norm_nonneg z])
      omega

/-- Global polynomial-times-exponential upper bound for the weighted envelope. -/
theorem norm_coshQuartetEnvelope_mul_polynomial_le
    (a : ℝ) (P : Polynomial ℂ) (z : ℂ) :
    ‖coshQuartetEnvelope a z * P.eval z‖ ≤
      (polynomialCoeffNormSum P * Real.exp (2 * |a|)) *
        (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * ‖z‖) := by
  rw [norm_mul]
  have hA := norm_coshQuartetEnvelope_le a z
  have hP := norm_polynomial_eval_le P z
  calc
    ‖coshQuartetEnvelope a z‖ * ‖P.eval z‖ ≤
        Real.exp (2 * (‖z‖ + |a|)) *
          (polynomialCoeffNormSum P * (1 + ‖z‖) ^ P.natDegree) :=
      mul_le_mul hA hP (norm_nonneg _) (Real.exp_nonneg _)
    _ = (polynomialCoeffNormSum P * Real.exp (2 * |a|)) *
        (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * ‖z‖) := by
      rw [show 2 * (‖z‖ + |a|) = 2 * |a| + 2 * ‖z‖ by ring, Real.exp_add]
      ring

/-- The positive exponential half of real `cosh`. -/
theorem exp_div_two_le_real_cosh (x : ℝ) :
    Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

/-- The envelope alone carries an `exp (2x)` lower bound on the positive real ray. -/
theorem exp_two_mul_div_four_le_norm_coshQuartetEnvelope_ofReal (a x : ℝ) :
    Real.exp (2 * x) / 4 ≤ ‖coshQuartetEnvelope a (x : ℂ)‖ := by
  rw [coshQuartetEnvelope,
    ← Complex.ofReal_sub, ← Complex.ofReal_add,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cosh,
    norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), abs_of_pos (Real.cosh_pos _)]
  have hm := exp_div_two_le_real_cosh (x - a)
  have hp := exp_div_two_le_real_cosh (x + a)
  calc
    Real.exp (2 * x) / 4 = (Real.exp (x - a) / 2) * (Real.exp (x + a) / 2) := by
      rw [div_mul_div_comm, ← Real.exp_add]
      congr 1 <;> ring_nf
    _ ≤ Real.cosh (x - a) * Real.cosh (x + a) :=
      mul_le_mul hm hp (by positivity) (Real.cosh_pos _).le

/-- A nonzero polynomial cannot remove the envelope's exponential lower growth. -/
theorem eventually_le_norm_coshQuartetEnvelope_mul_polynomial_ofReal
    (a : ℝ) {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      (‖P.leadingCoeff‖ / 8) * Real.exp (2 * x) ≤
        ‖coshQuartetEnvelope a (x : ℂ) * P.eval (x : ℂ)‖ := by
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hlcnorm : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr hlc
  have hlim := PolyAsymptotics.tendsto_eval_div_pow_natDegree P
  have hnormlim : Tendsto
      (fun x : ℝ => ‖P.eval (x : ℂ) / (x : ℂ) ^ P.natDegree‖)
      atTop (𝓝 ‖P.leadingCoeff‖) :=
    (continuous_norm.tendsto _).comp hlim
  obtain ⟨R₀, hR₀⟩ := (Metric.tendsto_atTop.mp hnormlim)
    (‖P.leadingCoeff‖ / 2) (by positivity)
  refine ⟨max R₀ 1, fun x hx => ?_⟩
  have hxR : R₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hclose := hR₀ x hxR
  rw [Real.dist_eq] at hclose
  have hratio : ‖P.leadingCoeff‖ / 2 ≤
      ‖P.eval (x : ℂ) / (x : ℂ) ^ P.natDegree‖ := by
    have hlower := (abs_lt.mp hclose).1
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hxpow : 0 < x ^ P.natDegree := pow_pos hxpos _
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hxpos] at hratio
  have hPbound : (‖P.leadingCoeff‖ / 2) * x ^ P.natDegree ≤
      ‖P.eval (x : ℂ)‖ := (le_div_iff₀ hxpow).mp hratio
  have hxpowone : 1 ≤ x ^ P.natDegree := one_le_pow₀ hx1
  have hPconst : ‖P.leadingCoeff‖ / 2 ≤ ‖P.eval (x : ℂ)‖ := by
    calc
      ‖P.leadingCoeff‖ / 2 ≤ (‖P.leadingCoeff‖ / 2) * x ^ P.natDegree := by
        nlinarith [hlcnorm, hxpowone]
      _ ≤ ‖P.eval (x : ℂ)‖ := hPbound
  have hAlower := exp_two_mul_div_four_le_norm_coshQuartetEnvelope_ofReal a x
  rw [norm_mul]
  calc
    (‖P.leadingCoeff‖ / 8) * Real.exp (2 * x) =
        (Real.exp (2 * x) / 4) * (‖P.leadingCoeff‖ / 2) := by ring
    _ ≤ ‖coshQuartetEnvelope a (x : ℂ)‖ * ‖P.eval (x : ℂ)‖ :=
      mul_le_mul hAlower hPconst (by positivity) (norm_nonneg _)

/-- The coefficient-norm upper constant is strictly positive for a nonzero polynomial. -/
theorem polynomialCoeffNormSum_pos {P : Polynomial ℂ} (hP : P ≠ 0) :
    0 < polynomialCoeffNormSum P := by
  have hlc : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hmem : P.natDegree ∈ Finset.range (P.natDegree + 1) := by simp
  have hle : ‖P.coeff P.natDegree‖ ≤ polynomialCoeffNormSum P := by
    rw [polynomialCoeffNormSum]
    exact Finset.single_le_sum (fun i hi => norm_nonneg (P.coeff i)) hmem
  rw [P.coeff_natDegree] at hle
  exact lt_of_lt_of_le hlc hle

/-- **Exact order-one certificate.** A nonzero polynomially weighted cosh quartet envelope is
trapped between positive multiples of `exp (2x)` on a ray and
`(1 + ‖z‖)^degree * exp (2 ‖z‖)` globally. -/
theorem coshQuartetEnvelope_mul_polynomial_exact_order_one_bounds
    (a : ℝ) {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖coshQuartetEnvelope a z * P.eval z‖ ≤
        Kupper * (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤
        ‖coshQuartetEnvelope a (x : ℂ) * P.eval (x : ℂ)‖ := by
  obtain ⟨R, hR⟩ := eventually_le_norm_coshQuartetEnvelope_mul_polynomial_ofReal a hP
  refine ⟨polynomialCoeffNormSum P * Real.exp (2 * |a|),
    ‖P.leadingCoeff‖ / 8, R, ?_, ?_, ?_, hR⟩
  · exact mul_pos (polynomialCoeffNormSum_pos hP) (Real.exp_pos _)
  · exact div_pos (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)) (by norm_num)
  · exact norm_coshQuartetEnvelope_mul_polynomial_le a P

end

end RHTower
