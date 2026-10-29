import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Gindikin–Karpelevich zeta ratio of a curve datum

For a curve datum with reciprocal Frobenius eigenvalues `α_i`, put `P(X) = Π_i (1 − α_i X)`,
`T(s) = q^{−s}` and `Z(s) = P(T)/((1 − T)(1 − qT))`. The affine Gindikin–Karpelevich factor is
`Z(s)/Z(s + 1)`. Cancelling the common pole gives the entire numerator and denominator

`N(s) = (1 − T/q) P(T)`,   `Q(s) = (1 − qT) P(T/q)`.

Only the **strip condition** `1 < |α_i| < q` (every zero of `Z` in the open critical strip) is
used. It holds for every actual curve and for impure data such as the golden datum. Under it:

* the reduced ratio `N/Q` is analytic and bounded on `Re s ≥ 2` (`exists_reducedRatio_bound`);
* `N` and `Q` are bounded on `Re s ≥ −1` (`exists_ratioParts_bound`);
* a zero `s` of `P(T(s + 1))` has `−1 < Re s < 0`, `Q(s) = 0` with the exact root multiplicity,
  and `N(s) ≠ 0` (`ratioDenominator_order_at_root`, `ratioNumerator_ne_zero_at_root`);
* such a zero lies on `Re s = −1/2` iff its eigenvalue has `|β_i| = 1` (`re_root_eq_neg_half_iff`).
-/

open Polynomial Filter Topology Metric Set

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

open ArithmeticCastelnuovoSeveri

noncomputable section

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι)

/-! ### The numerator polynomial -/

/-- The numerator `P(X) = Π_i (1 − α_i X)` as a polynomial. -/
def numeratorPoly : ℂ[X] := ∏ i, (1 - C (D.alpha i) * X)

lemma numeratorPoly_eval (z : ℂ) : (numeratorPoly D).eval z = ∏ i, (1 - D.alpha i * z) := by
  simp [numeratorPoly, eval_prod]

lemma numeratorPoly_ne_zero : numeratorPoly D ≠ 0 := by
  intro h
  have h0 := congrArg (eval (0 : ℂ)) h
  rw [numeratorPoly_eval] at h0
  simp at h0

lemma numeratorPoly_eval_eq_zero_iff (z : ℂ) :
    (numeratorPoly D).eval z = 0 ↔ ∃ i, D.alpha i * z = 1 := by
  rw [numeratorPoly_eval, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, by linear_combination -hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ _, by linear_combination -hi⟩

lemma numeratorPoly_analytic (z : ℂ) :
    AnalyticAt ℂ (fun T => (numeratorPoly D).eval T) z := by
  simpa using (analyticAt_id : AnalyticAt ℂ (fun T : ℂ => T) z).aeval_polynomial (numeratorPoly D)

lemma numeratorPoly_meromorphicOrder (z : ℂ) :
    meromorphicOrderAt (fun T => (numeratorPoly D).eval T) z =
      (((numeratorPoly D).rootMultiplicity z : ℤ) : WithTop ℤ) := by
  rw [(numeratorPoly_analytic D z).meromorphicOrderAt_eq,
    HTGeometry.analyticOrderAt_eval_eq_rootMultiplicity (numeratorPoly_ne_zero D)]
  rfl

/-! ### The strip condition -/

lemma log_q_pos : 0 < Real.log D.q := Real.log_pos D.one_lt_q

lemma q_pos : 0 < D.q := lt_trans one_pos D.one_lt_q

/-- Every zero of the datum's zeta function lies in the open critical strip: `1 < |α_i| < q`. -/
def StripCondition : Prop := ∀ i, 1 < ‖D.alpha i‖ ∧ ‖D.alpha i‖ < D.q

lemma norm_alpha (i : ι) : ‖D.alpha i‖ = D.sqrtq * ‖D.β i‖ := by
  rw [CurveDatum.alpha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.sqrtq_pos]

/-! ### The zeta coordinate `T(s) = q^{−s}` -/

/-- The multiplicative coordinate `T(s) = q^{−s}`. -/
def zetaCoord (s : ℂ) : ℂ := Complex.exp (-(Real.log D.q : ℂ) * s)

lemma norm_zetaCoord (s : ℂ) : ‖zetaCoord D s‖ = Real.exp (-Real.log D.q * s.re) := by
  simp only [zetaCoord, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

lemma zetaCoord_ne_zero (s : ℂ) : zetaCoord D s ≠ 0 := Complex.exp_ne_zero _

lemma zetaCoord_analytic (s : ℂ) : AnalyticAt ℂ (zetaCoord D) s := by
  unfold zetaCoord
  fun_prop

lemma zetaCoord_deriv_ne_zero (s : ℂ) : deriv (zetaCoord D) s ≠ 0 := by
  have h : HasDerivAt (zetaCoord D) (zetaCoord D s * (-(Real.log D.q : ℂ))) s := by
    have h' := ((hasDerivAt_id s).const_mul (-(Real.log D.q : ℂ))).cexp
    simp only [id, mul_one] at h'
    exact h'
  rw [h.deriv]
  exact mul_ne_zero (zetaCoord_ne_zero D s)
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (log_q_pos D).ne'))

lemma zetaCoord_add_one (s : ℂ) : zetaCoord D (s + 1) = zetaCoord D s / D.q := by
  have he : Complex.exp (-(Real.log D.q : ℂ)) = (D.q : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (q_pos D)]
  simp only [zetaCoord, mul_add, mul_one, Complex.exp_add, he, div_eq_mul_inv]

lemma q_ne_zero : (D.q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (q_pos D).ne'

/-- `|T(s)| = q^{−Re s}` in exponential form, and its inverse. -/
lemma norm_zetaCoord_eq_rpow (s : ℂ) : ‖zetaCoord D s‖ = D.q ^ (-s.re) := by
  rw [norm_zetaCoord, Real.rpow_def_of_pos (q_pos D)]
  ring_nf

lemma norm_zetaCoord_le_of_le_re {s : ℂ} {a : ℝ} (h : a ≤ s.re) :
    ‖zetaCoord D s‖ ≤ D.q ^ (-a) := by
  rw [norm_zetaCoord_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le D.one_lt_q.le (by linarith)

lemma zetaCoord_ne_one (s : ℂ) (hs : s.re ≠ 0) : zetaCoord D s ≠ 1 := by
  intro h
  have he : Real.exp (-Real.log D.q * s.re) = Real.exp 0 := by
    rw [← norm_zetaCoord, h, norm_one, Real.exp_zero]
  have hz := Real.exp_injective he
  exact hs ((mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (log_q_pos D).ne'))

/-! ### The zeta function and its Gindikin–Karpelevich ratio -/

/-- The rational zeta function `Z(T) = P(T)/((1 − T)(1 − qT))` of the datum. -/
def zetaFunction (T : ℂ) : ℂ := (numeratorPoly D).eval T / ((1 - T) * (1 - D.q * T))

/-- The Gindikin–Karpelevich factor `Z(s)/Z(s + 1)` in the additive coordinate. -/
def zetaRatio (s : ℂ) : ℂ := zetaFunction D (zetaCoord D s) / zetaFunction D (zetaCoord D (s + 1))

/-- Entire numerator `(1 − T/q) P(T)` of the reduced ratio. -/
def ratioNumerator (s : ℂ) : ℂ :=
  (1 - zetaCoord D s / D.q) * (numeratorPoly D).eval (zetaCoord D s)

/-- Entire denominator `(1 − qT) P(T/q)` of the reduced ratio. -/
def ratioDenominator (s : ℂ) : ℂ :=
  (1 - D.q * zetaCoord D s) * (numeratorPoly D).eval (zetaCoord D s / D.q)

/-- The reduced meromorphic representative of `Z(s)/Z(s + 1)`. -/
def reducedRatio (s : ℂ) : ℂ := ratioNumerator D s / ratioDenominator D s

/-- Away from the common pole `T = 1` the ratio is its reduced form. -/
theorem zetaRatio_eq_reduced (s : ℂ) (hs : s.re ≠ 0) : zetaRatio D s = reducedRatio D s := by
  have h₁ : 1 - zetaCoord D s ≠ 0 := sub_ne_zero.mpr (zetaCoord_ne_one D s hs).symm
  have hq := q_ne_zero D
  unfold zetaRatio zetaFunction reducedRatio ratioNumerator ratioDenominator
  rw [zetaCoord_add_one, show (D.q : ℂ) * (zetaCoord D s / D.q) = zetaCoord D s by field_simp]
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div]
  rw [show (numeratorPoly D).eval (zetaCoord D s) * ((1 - zetaCoord D s / D.q) *
        (1 - zetaCoord D s)) = (1 - zetaCoord D s) * ((1 - zetaCoord D s / D.q) *
        (numeratorPoly D).eval (zetaCoord D s)) by ring,
    show (1 - zetaCoord D s) * (1 - D.q * zetaCoord D s) *
        (numeratorPoly D).eval (zetaCoord D s / D.q) = (1 - zetaCoord D s) *
        ((1 - D.q * zetaCoord D s) * (numeratorPoly D).eval (zetaCoord D s / D.q)) by ring]
  exact mul_div_mul_left _ _ h₁

lemma reducedRatio_eq_div (s : ℂ) :
    reducedRatio D s = ratioNumerator D s / ratioDenominator D s := rfl

lemma ratioNumerator_analytic (s : ℂ) : AnalyticAt ℂ (ratioNumerator D) s := by
  have hT := zetaCoord_analytic D s
  have hP := (numeratorPoly_analytic D (zetaCoord D s)).comp (f := zetaCoord D) hT
  exact (analyticAt_const.sub (hT.div_const (c := (D.q : ℂ)))).mul hP

lemma ratioDenominator_analytic (s : ℂ) : AnalyticAt ℂ (ratioDenominator D) s := by
  have hT := zetaCoord_analytic D s
  have hP := (numeratorPoly_analytic D (zetaCoord D s / D.q)).comp
    (f := fun z => zetaCoord D z / D.q) (hT.div_const (c := (D.q : ℂ)))
  exact (analyticAt_const.sub (analyticAt_const.mul hT)).mul hP

/-! ### Regularity on the right and boundedness on the strip -/

/-- The reduced ratio as a rational function of `T`. -/
def reducedQuotient (T : ℂ) : ℂ :=
  ((1 - T / D.q) * (numeratorPoly D).eval T) / ((1 - D.q * T) * (numeratorPoly D).eval (T / D.q))

lemma reducedQuotient_denominator_ne_zero (hD : StripCondition D) (T : ℂ)
    (hT : ‖T‖ ≤ D.q ^ (-2 : ℝ)) :
    (1 - D.q * T) * (numeratorPoly D).eval (T / D.q) ≠ 0 := by
  have hq := q_pos D
  have hq1 := D.one_lt_q
  have hsmall : D.q ^ (-2 : ℝ) < D.q⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by norm_num)
  apply mul_ne_zero
  · intro h
    have hqT : ‖(D.q : ℂ) * T‖ = 1 := by
      rw [show (D.q : ℂ) * T = 1 by linear_combination -h, norm_one]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at hqT
    have : D.q * ‖T‖ < D.q * D.q⁻¹ := mul_lt_mul_of_pos_left (hT.trans_lt hsmall) hq
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith
  · rw [Ne, numeratorPoly_eval_eq_zero_iff]
    rintro ⟨i, hi⟩
    have hn : ‖D.alpha i‖ * ‖T‖ = D.q := by
      have := congrArg norm hi
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_one] at this
      field_simp at this
      linarith
    have ha := (hD i).2
    have hTq : ‖T‖ < D.q⁻¹ := hT.trans_lt hsmall
    have : ‖D.alpha i‖ * ‖T‖ < D.q * D.q⁻¹ :=
      mul_lt_mul'' ha hTq (norm_nonneg _) (norm_nonneg _)
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith [D.one_lt_q]

lemma reducedQuotient_analytic (hD : StripCondition D) (T : ℂ) (hT : ‖T‖ ≤ D.q ^ (-2 : ℝ)) :
    AnalyticAt ℂ (reducedQuotient D) T := by
  have hP := numeratorPoly_analytic D T
  have hP' := (numeratorPoly_analytic D (T / D.q)).comp (f := fun z : ℂ => z / D.q)
    (analyticAt_id.div_const (c := (D.q : ℂ)))
  exact ((analyticAt_const.sub (analyticAt_id.div_const (c := (D.q : ℂ)))).mul hP).div
    ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).mul hP')
    (reducedQuotient_denominator_ne_zero D hD T hT)

lemma reducedRatio_eq_quotient (s : ℂ) : reducedRatio D s = reducedQuotient D (zetaCoord D s) :=
  rfl

lemma norm_zetaCoord_le_of_two_le (s : ℂ) (hs : 2 ≤ s.re) :
    ‖zetaCoord D s‖ ≤ D.q ^ (-2 : ℝ) :=
  norm_zetaCoord_le_of_le_re D hs

lemma reducedRatio_analytic_right (hD : StripCondition D) (s : ℂ) (hs : 2 ≤ s.re) :
    AnalyticAt ℂ (reducedRatio D) s :=
  (reducedQuotient_analytic D hD _ (norm_zetaCoord_le_of_two_le D s hs)).comp
    (f := zetaCoord D) (zetaCoord_analytic D s)

/-- One constant bounds every reduced root factor on `Re s ≥ 2`. -/
theorem exists_reducedRatio_bound (hD : StripCondition D) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, 2 ≤ s.re → ‖reducedRatio D s‖ ≤ B := by
  have hc : ContinuousOn (reducedQuotient D) (closedBall (0 : ℂ) (D.q ^ (-2 : ℝ))) := by
    intro T hT
    apply (reducedQuotient_analytic D hD T ?_).continuousAt.continuousWithinAt
    simpa only [mem_closedBall, dist_zero_right] using hT
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) _).exists_bound_of_continuousOn hc
  refine ⟨max B 1, le_max_right _ _, fun s hs => ?_⟩
  rw [reducedRatio_eq_quotient]
  exact (hB _ (by simpa only [mem_closedBall, dist_zero_right] using
    norm_zetaCoord_le_of_two_le D s hs)).trans (le_max_left _ _)

/-- One constant bounds the entire numerator and denominator on `Re s ≥ −1`. -/
theorem exists_ratioParts_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re →
      ‖ratioNumerator D s‖ ≤ B ∧ ‖ratioDenominator D s‖ ≤ B := by
  let fN : ℂ → ℂ := fun T => (1 - T / D.q) * (numeratorPoly D).eval T
  let fQ : ℂ → ℂ := fun T => (1 - D.q * T) * (numeratorPoly D).eval (T / D.q)
  have hN : ContinuousOn fN (closedBall (0 : ℂ) D.q) := by
    apply Continuous.continuousOn
    exact (continuous_const.sub (continuous_id.div_const _)).mul (Polynomial.continuous _)
  have hQ : ContinuousOn fQ (closedBall (0 : ℂ) D.q) := by
    apply Continuous.continuousOn
    exact (continuous_const.sub (continuous_const.mul continuous_id)).mul
      ((Polynomial.continuous _).comp (continuous_id.div_const _))
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) D.q).exists_bound_of_continuousOn hN
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) D.q).exists_bound_of_continuousOn hQ
  refine ⟨max 1 (max A B), le_max_left _ _, fun s hs => ?_⟩
  have hmem : zetaCoord D s ∈ closedBall (0 : ℂ) D.q := by
    rw [mem_closedBall, dist_zero_right]
    simpa only [neg_neg, Real.rpow_one] using norm_zetaCoord_le_of_le_re D hs
  exact ⟨(hA _ hmem).trans ((le_max_left A B).trans (le_max_right _ _)),
    (hB _ hmem).trans ((le_max_right A B).trans (le_max_right _ _))⟩

/-! ### The arithmetic poles -/

/-- At a root, `T(s + 1)` is the inverse of a Frobenius eigenvalue. -/
lemma exists_alpha_of_root (s : ℂ) (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    ∃ i, D.alpha i * zetaCoord D (s + 1) = 1 :=
  (numeratorPoly_eval_eq_zero_iff D _).mp hs

/-- The real part of a pole parameter is `log |α_i| / log q − 1`. -/
lemma re_root_eq (s : ℂ) (i : ι) (hi : D.alpha i * zetaCoord D (s + 1) = 1) :
    s.re = Real.log ‖D.alpha i‖ / Real.log D.q - 1 := by
  have hn : ‖D.alpha i‖ * Real.exp (-Real.log D.q * (s + 1).re) = 1 := by
    rw [← norm_zetaCoord, ← norm_mul, hi, norm_one]
  have ha : 0 < ‖D.alpha i‖ := by
    rcases eq_or_ne (D.alpha i) 0 with h | h
    · rw [h, zero_mul] at hi; exact absurd hi zero_ne_one
    · exact norm_pos_iff.mpr h
  have hl : Real.log ‖D.alpha i‖ + (-Real.log D.q * (s + 1).re) = 0 := by
    rw [← Real.log_exp (-Real.log D.q * (s + 1).re), ← Real.log_mul ha.ne' (Real.exp_pos _).ne',
      hn, Real.log_one]
  have hq := log_q_pos D
  simp only [Complex.add_re, Complex.one_re] at hl
  field_simp
  linarith

/-- Every pole parameter lies in `−1 < Re s < 0`. -/
lemma re_root_mem (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) : -1 < s.re ∧ s.re < 0 := by
  obtain ⟨i, hi⟩ := exists_alpha_of_root D s hs
  rw [re_root_eq D s i hi]
  have hq := log_q_pos D
  have h1 : 0 < Real.log ‖D.alpha i‖ := Real.log_pos (hD i).1
  have h2 : Real.log ‖D.alpha i‖ < Real.log D.q :=
    Real.log_lt_log (lt_trans one_pos (hD i).1) (hD i).2
  constructor
  · have : 0 < Real.log ‖D.alpha i‖ / Real.log D.q := div_pos h1 hq
    linarith
  · have : Real.log ‖D.alpha i‖ / Real.log D.q < 1 := (div_lt_one hq).mpr h2
    linarith

/-- A pole lies on the critical hyperplane `Re s = −1/2` iff its eigenvalue is unitary. -/
theorem re_root_eq_neg_half_iff (s : ℂ) (i : ι) (hi : D.alpha i * zetaCoord D (s + 1) = 1) :
    s.re = -(1 / 2 : ℝ) ↔ ‖D.β i‖ = 1 := by
  rw [re_root_eq D s i hi, norm_alpha]
  have hq := log_q_pos D
  have hsq := D.sqrtq_pos
  have hlog_sqrt : Real.log D.sqrtq = Real.log D.q / 2 := by
    rw [CurveDatum.sqrtq, Real.log_sqrt (q_pos D).le]
  constructor
  · intro h
    have hb : 0 < ‖D.β i‖ := by
      rcases eq_or_ne (D.β i) 0 with hb | hb
      · have : D.alpha i = 0 := by rw [CurveDatum.alpha, hb, mul_zero]
        rw [this, zero_mul] at hi; exact absurd hi zero_ne_one
      · exact norm_pos_iff.mpr hb
    have hl : Real.log (D.sqrtq * ‖D.β i‖) = Real.log D.q / 2 := by
      field_simp at h
      linarith
    rw [Real.log_mul hsq.ne' hb.ne', hlog_sqrt] at hl
    have h0 : Real.log ‖D.β i‖ = 0 := by linarith
    rcases Real.log_eq_zero.mp h0 with h' | h' | h'
    · linarith
    · exact h'
    · linarith
  · intro h
    rw [h, mul_one, hlog_sqrt]
    field_simp
    ring

lemma ratioDenominator_zero_at_root (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) : ratioDenominator D s = 0 := by
  unfold ratioDenominator
  rw [← zetaCoord_add_one, hs, mul_zero]

/-- Clearing a pole leaves a nonzero numerator: the strip condition separates the roots. -/
theorem ratioNumerator_ne_zero_at_root (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) : ratioNumerator D s ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_alpha_of_root D s hs
  have hq := q_ne_zero D
  have hqp := q_pos D
  have hai : D.alpha i ≠ 0 := by rintro h; rw [h, zero_mul] at hi; exact zero_ne_one hi
  have hT : zetaCoord D s = D.q / D.alpha i := by
    have h' : zetaCoord D s = D.q * zetaCoord D (s + 1) := by
      rw [zetaCoord_add_one]; field_simp
    rw [h', eq_div_iff hai]
    linear_combination (D.q : ℂ) * hi
  unfold ratioNumerator
  rw [hT]
  apply mul_ne_zero
  · rw [show D.q / D.alpha i / D.q = 1 / D.alpha i by field_simp]
    intro h
    have h1 : (1 : ℂ) / D.alpha i = 1 := by linear_combination -h
    have : D.alpha i = 1 := ((div_eq_one_iff_eq hai).mp h1).symm
    have hn := (hD i).1
    rw [this, norm_one] at hn
    exact lt_irrefl _ hn
  · rw [Ne, numeratorPoly_eval_eq_zero_iff]
    rintro ⟨j, hj⟩
    have hn : ‖D.alpha j‖ * D.q = ‖D.alpha i‖ := by
      have := congrArg norm hj
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqp,
        norm_one] at this
      have ha : 0 < ‖D.alpha i‖ := norm_pos_iff.mpr hai
      field_simp at this
      linarith
    have h1 := (hD j).1
    have h2 := (hD i).2
    nlinarith

/-- The common denominator has exactly the root multiplicity at a pole. -/
theorem ratioDenominator_order_at_root (hD : StripCondition D) (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    meromorphicOrderAt (ratioDenominator D) s =
      (((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) : WithTop ℤ) := by
  obtain ⟨i, hi⟩ := exists_alpha_of_root D s hs
  have hq := q_ne_zero D
  have hqp := q_pos D
  have hu : AnalyticAt ℂ (fun z : ℂ => 1 - D.q * zetaCoord D z) s :=
    analyticAt_const.sub (analyticAt_const.mul (zetaCoord_analytic D s))
  have hu0 : 1 - D.q * zetaCoord D s ≠ 0 := by
    have h' : zetaCoord D s = D.q * zetaCoord D (s + 1) := by
      rw [zetaCoord_add_one]; field_simp
    intro h
    have hai : D.alpha i ≠ 0 := by rintro h0; rw [h0, zero_mul] at hi; exact zero_ne_one hi
    have hsq : D.alpha i = D.q * D.q := by
      have h2 : (D.alpha i - D.q * D.q) * zetaCoord D (s + 1) = 0 := by
        rw [h'] at h
        linear_combination hi + h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (zetaCoord_ne_zero D _))
    have hn := (hD i).2
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqp] at hn
    nlinarith [D.one_lt_q]
  have huo : meromorphicOrderAt (fun z : ℂ => 1 - D.q * zetaCoord D z) s = 0 := by
    rw [hu.meromorphicOrderAt_eq, hu.analyticOrderAt_eq_zero.mpr hu0]
    rfl
  have hg : AnalyticAt ℂ (fun z : ℂ => zetaCoord D z / D.q) s :=
    (zetaCoord_analytic D s).div_const (c := (D.q : ℂ))
  have hgd : deriv (fun z : ℂ => zetaCoord D z / D.q) s ≠ 0 := by
    rw [((zetaCoord_analytic D s).differentiableAt.hasDerivAt.div_const (D.q : ℂ)).deriv]
    exact div_ne_zero (zetaCoord_deriv_ne_zero D s) hq
  have hp := (numeratorPoly_analytic D (zetaCoord D s / D.q)).comp
    (f := fun z : ℂ => zetaCoord D z / D.q) hg
  have horder : meromorphicOrderAt (fun z => (numeratorPoly D).eval (zetaCoord D z / D.q)) s =
      meromorphicOrderAt (fun z => (numeratorPoly D).eval z) (zetaCoord D s / D.q) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := fun z => (numeratorPoly D).eval z) (g := fun z : ℂ => zetaCoord D z / D.q) hg hgd
  have hmul : meromorphicOrderAt (ratioDenominator D) s =
      meromorphicOrderAt (fun z : ℂ => 1 - D.q * zetaCoord D z) s +
        meromorphicOrderAt (fun z => (numeratorPoly D).eval (zetaCoord D z / D.q)) s := by
    convert! meromorphicOrderAt_mul hu.meromorphicAt hp.meromorphicAt using 1
  rw [hmul, huo, zero_add, horder, numeratorPoly_meromorphicOrder, ← zetaCoord_add_one]

/-- In the Godement half-plane `Re s > 1` the common denominator does not vanish. -/
lemma ratioDenominator_ne_zero_chamber (hD : StripCondition D) (s : ℂ) (hs : 1 < s.re) :
    ratioDenominator D s ≠ 0 := by
  have hq := q_pos D
  have hT : ‖zetaCoord D s‖ < D.q⁻¹ := by
    rw [norm_zetaCoord_eq_rpow, ← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt D.one_lt_q (by linarith)
  apply mul_ne_zero
  · intro h
    have hqT : D.q * ‖zetaCoord D s‖ = 1 := by
      have := congrArg norm (show (D.q : ℂ) * zetaCoord D s = 1 by linear_combination -h)
      rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_one] at this
    have : D.q * ‖zetaCoord D s‖ < D.q * D.q⁻¹ := mul_lt_mul_of_pos_left hT hq
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith
  · rw [Ne, numeratorPoly_eval_eq_zero_iff]
    rintro ⟨i, hi⟩
    have hn : ‖D.alpha i‖ * ‖zetaCoord D s‖ = D.q := by
      have := congrArg norm hi
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_one]
        at this
      field_simp at this
      linarith
    have : ‖D.alpha i‖ * ‖zetaCoord D s‖ < D.q * D.q⁻¹ :=
      mul_lt_mul'' (hD i).2 hT (norm_nonneg _) (norm_nonneg _)
    rw [mul_inv_cancel₀ hq.ne'] at this
    linarith [D.one_lt_q]

end CurveDatum

end

end GaloisForLFunctions.RHTower.InfiniteSymmetry
