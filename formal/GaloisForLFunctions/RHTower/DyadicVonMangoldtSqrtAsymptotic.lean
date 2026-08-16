import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtMass
import Mathlib.NumberTheory.AbelSummation

/-!
# The exact dyadic weighted prime constant

Abel summation against the inverse square root turns the dyadic weighted von Mangoldt mass into
two endpoint terms and one integral of Chebyshev's `ψ`.  The prime number theorem replaces `ψ(t)`
by `t` in each, and the elementary integral `∫_X^{2X} t^{-1/2} dt = 2(√(2X) − √X)` produces the
constant `2(√2 − 1)`.
-/

open Filter MeasureTheory Set ArithmeticFunction
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-! ## The inverse square root -/

/-- The weight of the dyadic aperture. -/
def invSqrt (t : ℝ) : ℝ := (Real.sqrt t)⁻¹

theorem hasDerivAt_invSqrt {t : ℝ} (ht : 0 < t) :
    HasDerivAt invSqrt (-(1 / (2 * t * Real.sqrt t))) t := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt (ne_of_gt ht)
  have hne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have h := hs.inv hne
  have hval : -(1 / (2 * Real.sqrt t)) / Real.sqrt t ^ 2 = -(1 / (2 * t * Real.sqrt t)) := by
    rw [Real.sq_sqrt ht.le]
    field_simp
  rw [← hval]
  exact h

theorem deriv_invSqrt {t : ℝ} (ht : 0 < t) :
    deriv invSqrt t = -(1 / (2 * t * Real.sqrt t)) := (hasDerivAt_invSqrt ht).deriv

theorem differentiableAt_invSqrt {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ invSqrt t :=
  (hasDerivAt_invSqrt ht).differentiableAt

theorem chebyshevPsiReal_eq_sum_Icc (y : ℝ) :
    chebyshevPsiReal y = ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, (vonMangoldt n : ℝ) := by
  rw [chebyshevPsiReal_eq_sum_range]
  congr 1
  ext n
  simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and]
  omega

/-! ## Abel summation on a dyadic block -/

/-- **Abel summation of the dyadic weighted prime mass.** -/
theorem dyadicSqrtVonMangoldtMass_abel {X : ℝ} (hX : 0 < X) :
    dyadicSqrtVonMangoldtMass X
      = chebyshevPsiReal (2 * X) * invSqrt (2 * X) - chebyshevPsiReal X * invSqrt X
        + ∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) := by
  have h2X : X ≤ 2 * X := by linarith
  have hsub : Icc X (2 * X) ⊆ Ioi (0 : ℝ) := by
    intro s hs
    exact lt_of_lt_of_le hX hs.1
  have hdiff : ∀ s ∈ Icc X (2 * X), DifferentiableAt ℝ invSqrt s := fun s hs =>
    differentiableAt_invSqrt (hsub hs)
  have hcont : ContinuousOn (deriv invSqrt) (Icc X (2 * X)) := by
    refine ContinuousOn.congr (f := fun s : ℝ => -(1 / (2 * s * Real.sqrt s))) ?_ ?_
    · refine ContinuousOn.neg (ContinuousOn.div continuousOn_const ?_ ?_)
      · exact (continuousOn_const.mul continuousOn_id).mul Real.continuous_sqrt.continuousOn
      · intro s hs
        have hs0 : 0 < s := hsub hs
        have : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
        positivity
    · intro s hs
      exact deriv_invSqrt (hsub hs)
  have hint : IntegrableOn (deriv invSqrt) (Icc X (2 * X)) volume :=
    hcont.integrableOn_compact isCompact_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) (fun n => (vonMangoldt n : ℝ))
    (f := invSqrt) hX.le h2X hdiff hint
  rw [dyadicSqrtVonMangoldtMass]
  have hlhs : ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, (vonMangoldt n : ℝ) / Real.sqrt n
      = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, invSqrt n * (vonMangoldt n : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [invSqrt, div_eq_mul_inv]
    ring
  rw [hlhs, habel, ← chebyshevPsiReal_eq_sum_Icc, ← chebyshevPsiReal_eq_sum_Icc]
  have hneg : (∫ t in Ioc X (2 * X), deriv invSqrt t * chebyshevPsiReal t)
      = -∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := lt_trans hX hs.1
    rw [deriv_invSqrt hs0]
    ring
  have hrw : ∀ t : ℝ, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt n : ℝ)) = chebyshevPsiReal t :=
    fun t => (chebyshevPsiReal_eq_sum_Icc t).symm
  simp only [hrw]
  rw [hneg]
  ring

/-! ## The dyadic weight integral -/

theorem continuousOn_sqrtWeight {X : ℝ} (hX : 0 < X) :
    ContinuousOn (fun t : ℝ => 1 / (2 * Real.sqrt t)) (Icc X (2 * X)) := by
  refine ContinuousOn.div continuousOn_const
    (continuousOn_const.mul Real.continuous_sqrt.continuousOn) fun s hs => ?_
  have hs0 : 0 < s := lt_of_lt_of_le hX hs.1
  have : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  positivity

theorem integrableOn_sqrtWeight {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun t : ℝ => 1 / (2 * Real.sqrt t)) (Ioc X (2 * X)) volume :=
  ((continuousOn_sqrtWeight hX).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem integral_sqrtWeight {X : ℝ} (hX : 0 < X) :
    (∫ t in Ioc X (2 * X), 1 / (2 * Real.sqrt t)) = Real.sqrt (2 * X) - Real.sqrt X := by
  have h2X : X ≤ 2 * X := by linarith
  have hderiv : ∀ s ∈ uIcc X (2 * X), HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := by
    intro s hs
    rw [uIcc_of_le h2X] at hs
    exact Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le hX hs.1))
  have hii : IntervalIntegrable (fun t : ℝ => 1 / (2 * Real.sqrt t)) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2X]
    exact integrableOn_sqrtWeight hX
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
  rw [intervalIntegral.integral_of_le h2X] at h
  exact h

theorem sqrt_two_mul_sub (X : ℝ) :
    Real.sqrt (2 * X) - Real.sqrt X = (Real.sqrt 2 - 1) * Real.sqrt X := by
  rw [Real.sqrt_mul (by norm_num)]
  ring

theorem integrableOn_psiWeight {X : ℝ} (hX : 0 < X) :
    IntegrableOn (fun t : ℝ => chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
      (Ioc X (2 * X)) volume := by
  have hmeas : Measurable fun t : ℝ => chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) := by
    refine (chebyshevPsiReal_mono.measurable).mul ?_
    exact measurable_const.div ((measurable_const.mul measurable_id).mul
      Real.continuous_sqrt.measurable)
  refine Measure.integrableOn_of_bounded (M := chebyshevPsiReal (2 * X) * (1 / (2 * X * Real.sqrt X)))
    ?_ hmeas.aestronglyMeasurable ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans hX ht.1
    have hpsi0 : 0 ≤ chebyshevPsiReal t := chebyshevPsiReal_nonneg t
    have hpsile : chebyshevPsiReal t ≤ chebyshevPsiReal (2 * X) :=
      chebyshevPsiReal_mono ht.2
    have hw : 0 < 2 * t * Real.sqrt t := by
      have : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
      positivity
    have hwle : 1 / (2 * t * Real.sqrt t) ≤ 1 / (2 * X * Real.sqrt X) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hsq : Real.sqrt X ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1.le
      nlinarith [ht.1.le, hsq, Real.sqrt_nonneg X, hX]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hpsile hwle (by positivity) (chebyshevPsiReal_nonneg _)

/-! ## The exact dyadic constant -/

theorem abs_integral_psiWeight_sub_le {X : ℝ} (hX : 0 < X) {δ : ℝ}
    (hpsi : ∀ t ∈ Ioc X (2 * X), |chebyshevPsiReal t - t| ≤ δ * t) :
    |(∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
        - (Real.sqrt (2 * X) - Real.sqrt X)|
      ≤ δ * (Real.sqrt (2 * X) - Real.sqrt X) := by
  have hdiffint : IntegrableOn
      (fun t : ℝ => chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t))
      (Ioc X (2 * X)) volume := (integrableOn_psiWeight hX).sub (integrableOn_sqrtWeight hX)
  have hsplit : (∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
      - (Real.sqrt (2 * X) - Real.sqrt X)
      = ∫ t in Ioc X (2 * X),
          (chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t)) := by
    rw [integral_sub (integrableOn_psiWeight hX) (integrableOn_sqrtWeight hX),
      integral_sqrtWeight hX]
  rw [hsplit]
  have hmono : ‖∫ t in Ioc X (2 * X),
      (chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t))‖
      ≤ ∫ t in Ioc X (2 * X), δ * (1 / (2 * Real.sqrt t)) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine setIntegral_mono_on hdiffint.norm
      ((integrableOn_sqrtWeight hX).const_mul δ) measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := lt_trans hX ht.1
    have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hval : chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)) - 1 / (2 * Real.sqrt t)
        = (chebyshevPsiReal t - t) * (1 / (2 * t * Real.sqrt t)) := by
      field_simp
    rw [Real.norm_eq_abs, hval, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * t * Real.sqrt t))]
    have hb := hpsi t ht
    have hstep : |chebyshevPsiReal t - t| * (1 / (2 * t * Real.sqrt t))
        ≤ (δ * t) * (1 / (2 * t * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  rw [← Real.norm_eq_abs]
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_sqrtWeight hX]

/-- **The exact dyadic weighted prime constant.** -/
theorem tendsto_dyadicSqrtVonMangoldtMass_div_sqrt :
    Tendsto (fun X : ℝ => dyadicSqrtVonMangoldtMass X / Real.sqrt X) atTop
      (nhds (2 * (Real.sqrt 2 - 1))) := by
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := by
      refine Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  have hc : (0 : ℝ) < Real.sqrt 2 - 1 := by linarith
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- the two endpoint terms
  have hA : Tendsto (fun X : ℝ => chebyshevPsiReal (2 * X) * invSqrt (2 * X) / Real.sqrt X)
      atTop (nhds (Real.sqrt 2)) := by
    have hbase := tendsto_chebyshevPsiReal_scaled (c := 2) (by norm_num)
    have hlim := hbase.const_mul (1 / Real.sqrt 2)
    have hval : (1 / Real.sqrt 2) * 2 = Real.sqrt 2 := by
      field_simp
      linarith [hs2sq]
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hXs : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
    have hXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
    have h2Xs : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
    rw [invSqrt, h2Xs]
    field_simp
    rw [Real.sq_sqrt hX.le]
    ring
  have hB : Tendsto (fun X : ℝ => chebyshevPsiReal X * invSqrt X / Real.sqrt X)
      atTop (nhds 1) := by
    refine tendsto_chebyshevPsiReal_div.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hXs : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
    have hXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX.le
    rw [invSqrt, div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv, hXsq]
  -- the integral term
  have hC : Tendsto (fun X : ℝ =>
      (∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t))) / Real.sqrt X)
      atTop (nhds (Real.sqrt 2 - 1)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Y, hY⟩ := (Metric.tendsto_atTop.mp tendsto_chebyshevPsiReal_div)
      (ε / (2 * (Real.sqrt 2 - 1))) (by positivity)
    refine ⟨max Y 1, fun X hX => ?_⟩
    have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right Y 1) hX
    have hXY : Y ≤ X := le_trans (le_max_left Y 1) hX
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1
    have hXs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hpsi : ∀ t ∈ Ioc X (2 * X),
        |chebyshevPsiReal t - t| ≤ (ε / (2 * (Real.sqrt 2 - 1))) * t := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans hX0 ht.1
      have htY : Y ≤ t := le_trans hXY ht.1.le
      have hd := hY t htY
      rw [Real.dist_eq] at hd
      have hval : chebyshevPsiReal t - t = (chebyshevPsiReal t / t - 1) * t := by
        field_simp
      rw [hval, abs_mul, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_right hd.le ht0.le
    have hbound := abs_integral_psiWeight_sub_le hX0 hpsi
    rw [sqrt_two_mul_sub] at hbound
    rw [Real.dist_eq]
    have hval : (∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
        / Real.sqrt X - (Real.sqrt 2 - 1)
        = ((∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
            - (Real.sqrt 2 - 1) * Real.sqrt X) / Real.sqrt X := by
      field_simp
    rw [hval, abs_div, abs_of_pos hXs, div_lt_iff₀ hXs]
    calc |(∫ t in Ioc X (2 * X), chebyshevPsiReal t * (1 / (2 * t * Real.sqrt t)))
            - (Real.sqrt 2 - 1) * Real.sqrt X|
        ≤ ε / (2 * (Real.sqrt 2 - 1)) * ((Real.sqrt 2 - 1) * Real.sqrt X) := hbound
      _ = (ε / 2) * Real.sqrt X := by
          field_simp
      _ < ε * Real.sqrt X := by nlinarith [hXs, hε]
  have hsum := (hA.sub hB).add hC
  have hlim : Real.sqrt 2 - 1 + (Real.sqrt 2 - 1) = 2 * (Real.sqrt 2 - 1) := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [dyadicSqrtVonMangoldtMass_abel hX]
  ring

end

end RHTower
