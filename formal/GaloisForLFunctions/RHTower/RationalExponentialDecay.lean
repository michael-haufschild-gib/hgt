import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Rational functions cannot decay exponentially on a real ray

The ray-complete translation theorem first shows that a translated generalized Dirichlet carrier
decays exponentially on the positive real axis.  This file supplies the exact missing separation:
a quotient of two complex polynomials with nonzero numerator and denominator is asymptotic to a
nonzero integral power, and therefore cannot be `O(exp (-eta*x))` for `eta > 0`.
-/

open Filter Topology Asymptotics Polynomial Bornology

namespace GaloisForLFunctions.RHTower

/-- A quotient of nonzero complex polynomials is asymptotic on the positive real axis to the
quotient of leading coefficients times the corresponding integral power. -/
theorem complexPolynomial_div_isEquivalent_atTop
    {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    (fun x : ℝ => p.eval (x : ℂ) / q.eval (x : ℂ)) ~[atTop]
      (fun x : ℝ => (p.leadingCoeff / q.leadingCoeff) *
        (x : ℂ) ^ ((p.natDegree : ℤ) - q.natDegree)) := by
  have hpEq : (fun x : ℝ => p.eval (x : ℂ)) ~[atTop]
      (fun x : ℝ => p.leadingCoeff * (x : ℂ) ^ p.natDegree) := by
    simpa [Function.comp_def] using
      (Polynomial.isEquivalent_cobounded_leading_monomial (P := p)).comp_tendsto
        (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  have hqEq : (fun x : ℝ => q.eval (x : ℂ)) ~[atTop]
      (fun x : ℝ => q.leadingCoeff * (x : ℂ) ^ q.natDegree) := by
    simpa [Function.comp_def] using
      (Polynomial.isEquivalent_cobounded_leading_monomial (P := q)).comp_tendsto
        (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  refine (hpEq.div hqEq).trans (EventuallyEq.isEquivalent ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpLC : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hqLC : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  change (p.leadingCoeff * (x : ℂ) ^ p.natDegree) /
      (q.leadingCoeff * (x : ℂ) ^ q.natDegree) = _
  rw [zpow_sub₀ hxC]
  field_simp
  simp only [zpow_natCast]
  ring

/-- A negative exponential is little-o of every integral power along the positive real axis. -/
theorem complex_exp_neg_isLittleO_zpow_atTop {eta : ℝ} (heta : 0 < eta) (d : ℤ) :
    (fun x : ℝ => (Real.exp (-eta * x) : ℂ)) =o[atTop]
      (fun x : ℝ => (x : ℂ) ^ d) := by
  apply IsLittleO.of_norm_norm
  have h := isLittleO_exp_neg_mul_rpow_atTop heta (d : ℝ)
  apply h.congr'
  · filter_upwards with x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      ← Real.rpow_intCast]

/-- A nonzero rational polynomial quotient cannot be bounded by a strictly decaying exponential. -/
theorem complexPolynomial_div_not_isBigO_exp_neg
    {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    ¬ (fun x : ℝ => p.eval (x : ℂ) / q.eval (x : ℂ)) =O[atTop]
      (fun x : ℝ => (Real.exp (-eta * x) : ℂ)) := by
  intro hO
  let d : ℤ := (p.natDegree : ℤ) - q.natDegree
  let c : ℂ := p.leadingCoeff / q.leadingCoeff
  have hc : c ≠ 0 := div_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have heq : (fun x : ℝ => p.eval (x : ℂ) / q.eval (x : ℂ)) ~[atTop]
      (fun x : ℝ => c * (x : ℂ) ^ d) := by
    simpa [c, d] using complexPolynomial_div_isEquivalent_atTop hp hq
  have hexp : (fun x : ℝ => (Real.exp (-eta * x) : ℂ)) =o[atTop]
      (fun x : ℝ => c * (x : ℂ) ^ d) :=
    (complex_exp_neg_isLittleO_zpow_atTop heta d).const_mul_right hc
  have hself : (fun x : ℝ => c * (x : ℂ) ^ d) =o[atTop]
      (fun x : ℝ => c * (x : ℂ) ^ d) :=
    heq.symm.trans_isLittleO (hO.trans_isLittleO hexp)
  apply (isLittleO_irrefl ?_) hself
  exact Filter.Eventually.frequently <|
    (eventually_gt_atTop (0 : ℝ)).mono fun x hx =>
      mul_ne_zero hc (zpow_ne_zero _ (by exact_mod_cast hx.ne'))

/-- Pointwise exponential domination on a tail forces the numerator of a polynomial quotient to
vanish. -/
theorem complexPolynomial_eq_zero_of_div_exponential_bound
    {p q : Polynomial ℂ} (hq : q ≠ 0) {eta C : ℝ} (heta : 0 < eta) (hC : 0 ≤ C)
    (hbound : ∀ᶠ x : ℝ in atTop,
      ‖p.eval (x : ℂ) / q.eval (x : ℂ)‖ ≤ C * Real.exp (-eta * x)) :
    p = 0 := by
  by_contra hp
  apply complexPolynomial_div_not_isBigO_exp_neg hp hq heta
  apply IsBigO.of_bound C
  filter_upwards [hbound] with x hx
  simpa [Complex.norm_exp] using hx

end GaloisForLFunctions.RHTower
