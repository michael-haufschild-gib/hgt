import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInnerFieldOfZeta
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheSzegoInfimum

/-!
# The inner mass is a mollifier infimum

The second expression of the inner mass. For `Re w > ½` let `φ_w(s) = (s − w)/(s + w̄ − 1)` be the
Blaschke coordinate of `w`, and for a polynomial `Q` with `Q(0) = 0` let

`M(s) = exp Q(φ_w(s))`,

a bounded holomorphic mollifier on `Re s ≥ ½` with `M(w) = 1`. Its **budget** is the Poisson second
moment `∫ |ζ(½ + iτ) M(½ + iτ)|² P_w(τ) dτ`. Then (`isGLB_budget`)

`inf_Q budget = exp (2 ∫ log |ζ| P_w)`.

At `w = 1` this reads (`isGLB_budget_one`, `exp_two_tsum_isGLB_budget_one`)

`Π_ρ (|ρ| / |1 − ρ|)^{2 m_ρ} = exp (2 I(1)) = inf_Q ∫ |ζM|² dP₁`.

The first expression of the inner mass is the zero sum, manifestly `≥ 0`. In this one each mollifier is a
manifest upper bound, and the infimum is exact: mollification loses nothing. Hence
`RH ⇔ inf_Q budget = 1` (`riemannHypothesis_iff_exists_budget_lt`), every budget is at least one, and at a
general nonzero centre the same holds with `|E(w)|²` in front (`isGLB_budget_innerField`).

The polynomial exponentials stand in for the outer function `1/O`; no boundary limit of `O` is used.
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The Poisson second moment of `ζ` against the mollifier `exp Q(φ_w)`. -/
def budget (w : ℂ) (Q : Polynomial ℂ) : ℝ :=
  ∫ τ : ℝ, ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 *
    ‖Complex.exp (Q.eval (blaschkeCoord w (1 / 2 + τ * I)))‖ ^ 2 * halfPlanePoissonKernel w τ

/-- The mollifier attached to `Q` and the centre `w`. -/
def polyMollifier (w : ℂ) (Q : Polynomial ℂ) (s : ℂ) : ℂ := Complex.exp (Q.eval (blaschkeCoord w s))

theorem polyMollifier_centre (w : ℂ) {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    polyMollifier w Q w = 1 := by
  have hc : blaschkeCoord w w = 0 := by simp [blaschkeCoord]
  rw [polyMollifier, hc, ← Polynomial.coeff_zero_eq_eval_zero, hQ, Complex.exp_zero]

/-- The mollifiers are bounded on the half-plane. -/
theorem exists_norm_polyMollifier_le {w : ℂ} (hw : 1 / 2 < w.re) (Q : Polynomial ℂ) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 < s.re → ‖polyMollifier w Q s‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun z => Complex.exp (Q.eval z)) (Complex.continuous_exp.comp Q.continuous).continuousOn
  refine ⟨C, fun s hs => hC _ ?_⟩
  simpa using (norm_blaschkeCoord_lt_one hw hs).le

theorem measurable_riemannZeta : Measurable riemannZeta := by
  refine measurable_of_continuousOn_compl_singleton 1 ?_
  intro z hz
  exact (differentiableAt_riemannZeta hz).continuousAt.continuousWithinAt

theorem measurable_discChart (w : ℂ) : Measurable (discChart w) := by
  have h2 : Continuous (halfPlaneShift w) := by unfold halfPlaneShift; fun_prop
  exact h2.measurable.comp ((measurable_const.sub measurable_id).inv)

theorem circleMap_criticalLineAngle_ne_one (t : ℝ) : circleMap 0 1 (criticalLineAngle t) ≠ 1 := by
  intro h
  have := halfPlaneOfDisc_circleMap_criticalLineAngle t
  rw [h, halfPlaneOfDisc, sub_self, inv_zero] at this
  have h2 := congrArg Complex.re this
  norm_num at h2

theorem discChart_circleMap (w : ℂ) (t : ℝ) :
    discChart w (circleMap 0 1 (criticalLineAngle t)) =
      1 / 2 + (((2 * w.re - 1) * t + w.im : ℝ) : ℂ) * I := by
  rw [discChart, halfPlaneOfDisc_circleMap_criticalLineAngle, halfPlaneShift_criticalLine]

theorem blaschkeCoord_line {w : ℂ} (hw : 1 / 2 < w.re) (t : ℝ) :
    blaschkeCoord w (1 / 2 + (((2 * w.re - 1) * t + w.im : ℝ) : ℂ) * I) =
      circleMap 0 1 (criticalLineAngle t) := by
  rw [← discChart_circleMap, blaschkeCoord_discChart hw (circleMap_criticalLineAngle_ne_one t)]

/-- The boundary second moment is integrable against every Poisson kernel. -/
theorem integrable_norm_sq_zeta_poisson {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel w τ) := by
  obtain ⟨C, hC0, hC⟩ := exists_poissonKernel_le_one hw
  have h1 := integrable_and_integral_norm_sq_zeta_criticalLine.1
  have h2 : Integrable (fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 / (1 / 4 + τ ^ 2) *
      (C * (2 * π)⁻¹)) := h1.mul_const _
  refine h2.mono' ?_ (Eventually.of_forall fun τ => ?_)
  · have hk : Measurable (fun τ : ℝ => halfPlanePoissonKernel w τ) := by
      unfold halfPlanePoissonKernel
      fun_prop
    have hz : Measurable fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ :=
      (measurable_riemannZeta.comp (by fun_prop)).norm
    exact ((hz.pow_const 2).mul hk).aestronglyMeasurable
  · have hP := hC τ
    have hP0 := (halfPlanePoissonKernel_pos hw τ).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hP0)]
    rw [halfPlanePoissonKernel_one] at hP
    have e : ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 / (1 / 4 + τ ^ 2) * (C * (2 * π)⁻¹) =
        ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * (C * ((2 * π)⁻¹ * (1 / (1 / 4 + τ ^ 2)))) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hP (sq_nonneg _)

/-- The zeros of `ζ` on the plane are countable. -/
theorem countable_zeta_zeros : {s : ℂ | riemannZeta s = 0}.Countable :=
  countable_setOf_zetaEntire_eq_zero.mono fun s hs => by
    rw [mem_setOf_eq, zetaEntire_eq_zero_iff]
    exact hs

local notation "𝕋" => AddCircle (2 * π)

/-- The boundary weight in the disc chart of `w`. -/
def chartWeight (w z : ℂ) : ℝ := ‖riemannZeta (discChart w z)‖ ^ 2

theorem measurable_chartWeight (w : ℂ) : Measurable (chartWeight w) :=
  (measurable_riemannZeta.comp (measurable_discChart w)).norm.pow_const 2

theorem ae_chartWeight_pos {w : ℂ} (hw : 1 / 2 < w.re) :
    ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, 0 < chartWeight w (circleZ x) := by
  have hA : ((blaschkeCoord w '' {s : ℂ | riemannZeta s = 0}) ∪ {1}).Countable :=
    (countable_zeta_zeros.image _).union (countable_singleton _)
  filter_upwards [ae_circleZ_notMem_of_countable hA] with x hx
  have hz1 : circleZ x ≠ 1 := fun h => hx (Or.inr h)
  have hne : riemannZeta (discChart w (circleZ x)) ≠ 0 := by
    intro h0
    apply hx
    left
    exact ⟨_, h0, blaschkeCoord_discChart hw hz1⟩
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-- **Szegő's infimum for `ζ` at the centre `w`.** -/
theorem isGLB_budget {w : ℂ} (hw : 1 / 2 < w.re) :
    IsGLB (budget w '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ)) := by
  have hinte := circleAverage_shift_eq_poisson hw
    (fun τ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2) (chartWeight w) (fun t => by
      simp only [chartWeight, discChart_circleMap])
  have hloge := circleAverage_shift_eq_poisson hw
    (fun τ => 2 * Real.log ‖riemannZeta (1 / 2 + τ * I)‖) (fun z => Real.log (chartWeight w z))
    (fun t => by simp only [chartWeight, discChart_circleMap, Real.log_pow]; norm_num)
  have hlogi : Integrable (fun τ : ℝ =>
      (2 * Real.log ‖riemannZeta (1 / 2 + τ * I)‖) * halfPlanePoissonKernel w τ) := by
    have := (integrable_log_zeta_poisson hw).const_mul 2
    refine this.congr (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  have h := isGLB_circleAverage (measurable_chartWeight w) (ae_chartWeight_pos hw)
    (hinte.1.mpr (integrable_norm_sq_zeta_poisson hw)) (hloge.1.mpr hlogi)
  have e1 : Real.circleAverage (fun z => Real.log (chartWeight w z)) 0 1 =
      2 * ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ := by
    rw [hloge.2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    ring
  have e2 : (fun Q : Polynomial ℂ =>
      Real.circleAverage (fun z => chartWeight w z * ‖Complex.exp (Q.eval z)‖ ^ 2) 0 1) = budget w := by
    funext Q
    have hQ := circleAverage_shift_eq_poisson hw
      (fun τ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 *
        ‖Complex.exp (Q.eval (blaschkeCoord w (1 / 2 + τ * I)))‖ ^ 2)
      (fun z => chartWeight w z * ‖Complex.exp (Q.eval z)‖ ^ 2)
      (fun t => by simp only [chartWeight, discChart_circleMap, blaschkeCoord_line hw])
    rw [hQ.2, budget]
  rw [e1, e2] at h
  exact h

/-- Every budget is at least the exponential of the logarithmic mean. -/
theorem exp_two_integral_log_le_budget {w : ℂ} (hw : 1 / 2 < w.re) {Q : Polynomial ℂ}
    (hQ : Q.coeff 0 = 0) :
    Real.exp (2 * ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) ≤
      budget w Q :=
  (isGLB_budget hw).1 ⟨Q, hQ, rfl⟩

/-- The value of the logarithmic mean in terms of the inner field. -/
theorem integral_log_zeta_poisson_eq {w : ℂ} :
    (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) =
      innerField w + (Real.log ‖zetaEntire w‖ - Real.log ‖w‖) := by
  rw [innerField]
  ring

/-- **Szegő's infimum at a nonzero centre.** With `E(s) = (s − 1)ζ(s)/s`,
`inf_Q budget = exp (2 I(w)) |E(w)|²`. -/
theorem isGLB_budget_innerField {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) :
    IsGLB (budget w '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * innerField w) * (‖zetaEntire w‖ / ‖w‖) ^ 2) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  have h := isGLB_budget hw
  rw [integral_log_zeta_poisson_eq] at h
  convert h using 1
  have hE : 0 < ‖zetaEntire w‖ := norm_pos_iff.mpr h0
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [mul_add, Real.exp_add, mul_sub, Real.exp_sub]
  congr 1
  rw [show (2 : ℝ) * Real.log ‖zetaEntire w‖ = Real.log (‖zetaEntire w‖ ^ 2) by
      rw [Real.log_pow]; norm_num,
    show (2 : ℝ) * Real.log ‖w‖ = Real.log (‖w‖ ^ 2) by rw [Real.log_pow]; norm_num,
    Real.exp_log (by positivity), Real.exp_log (by positivity), div_pow]

/-- **The second expression of the inner mass.** -/
theorem isGLB_budget_one :
    IsGLB (budget 1 '' {Q | Q.coeff 0 = 0}) (Real.exp (2 * innerField 1)) := by
  have h := isGLB_budget_innerField (w := 1) (by norm_num) zetaEntire_one_ne_zero
  simpa [zetaEntire_eval_one] using h

/-- Every mollifier budget at `1` bounds the inner mass from above. -/
theorem innerField_one_le_half_log_budget {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) :
    innerField 1 ≤ Real.log (budget 1 Q) / 2 := by
  have h := isGLB_budget_one.1 ⟨Q, hQ, rfl⟩
  have hpos := Real.exp_pos (2 * innerField 1)
  have hl := Real.log_le_log hpos h
  rw [Real.log_exp] at hl
  linarith

/-- Every mollifier budget is at least `1`. -/
theorem one_le_budget_one {Q : Polynomial ℂ} (hQ : Q.coeff 0 = 0) : 1 ≤ budget 1 Q := by
  have h := isGLB_budget_one.1 ⟨Q, hQ, rfl⟩
  have h1 : 1 ≤ Real.exp (2 * innerField 1) :=
    Real.one_le_exp (by
      have := innerField_nonneg (w := 1) (by norm_num) zetaEntire_one_ne_zero
      linarith)
  exact h1.trans h

/-- **The mollifier criterion, exact.** RH holds iff the budgets at `1` come arbitrarily close to one. -/
theorem riemannHypothesis_iff_exists_budget_lt :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ Q : Polynomial ℂ, Q.coeff 0 = 0 ∧ budget 1 Q < 1 + ε := by
  rw [riemannHypothesis_iff_innerField_eq_zero (w := 1) (by norm_num) zetaEntire_one_ne_zero]
  have hnn := innerField_nonneg (w := 1) (by norm_num) zetaEntire_one_ne_zero
  constructor
  · intro h0 ε hε
    have hglb := isGLB_budget_one
    rw [h0, mul_zero, Real.exp_zero] at hglb
    have hne : (budget 1 '' {Q | Q.coeff 0 = 0}).Nonempty := ⟨_, 0, by simp, rfl⟩
    obtain ⟨_, ⟨Q, hQ, rfl⟩, hlt⟩ := (isGLB_lt_iff hglb).mp (lt_add_of_pos_right 1 hε)
    exact ⟨Q, hQ, hlt⟩
  · intro h
    apply le_antisymm _ hnn
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨Q, hQ, hlt⟩ := h (Real.exp (2 * ε) - 1) (by
      have := Real.add_one_lt_exp (show (2 * ε : ℝ) ≠ 0 by positivity)
      linarith)
    have h1 := innerField_one_le_half_log_budget hQ
    have hb : 0 < budget 1 Q := lt_of_lt_of_le one_pos (one_le_budget_one hQ)
    have h2 : Real.log (budget 1 Q) ≤ 2 * ε := by
      rw [← Real.log_exp (2 * ε)]
      exact Real.log_le_log hb (by linarith)
    linarith

/-- The inner mass, in the zero sum: `Π_ρ (|ρ|/|1−ρ|)^{2m_ρ} = inf_Q budget`. -/
theorem exp_two_tsum_isGLB_budget_one :
    IsGLB (budget 1 '' {Q | Q.coeff 0 = 0})
      (Real.exp (2 * ∑' ρ : ZetaRightZero, zeroMult ρ * greenKernel 1 ρ)) := by
  rw [(hasSum_innerField (w := 1) (by norm_num) zetaEntire_one_ne_zero).tsum_eq]
  exact isGLB_budget_one

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
