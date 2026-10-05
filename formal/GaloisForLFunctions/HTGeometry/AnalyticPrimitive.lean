import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import GaloisForLFunctions.HTGeometry.ClockIteratedIntegralBound

/-!
# Analytic primitives of real-analytic germs

If `f : ℝ → ℝ` is real analytic at `0`, its primitive `F(x) = ∫₀ˣ f` is real analytic at `0` and
satisfies `F' = f` near `0`.  On a ball where `f(t) = ∑ aₙ tⁿ`, integrating termwise (the
series converges uniformly on `[0, x]`) gives `F(x) = ∑ aₙ x^{n+1}/(n+1)`, a power series whose
radius is at least that of `f`.

Parity is transported: the primitive of an even germ is odd and the primitive of an odd germ is
even, by the substitution `t ↦ -t`; and the primitive of a germ positive on `(0, δ)` is positive
there.
-/

open Filter Topology Set intervalIntegral
open scoped NNReal ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The primitive `x ↦ ∫₀ˣ f`. -/
def primitiveAtZero (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t

/-- The coefficients of the termwise primitive: `c₀ = 0`, `c_{n+1} = aₙ/(n+1)`. -/
def primitiveCoeff (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a n / (n + 1)

/-- **Analytic primitive.**  The primitive of a real-analytic germ has a power series at `0` with
radius at least that of the germ, and differentiates back to it on that ball. -/
theorem hasFPowerSeriesOnBall_primitiveAtZero {f : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ}
    {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p 0 r) :
    HasFPowerSeriesOnBall (primitiveAtZero f)
      (FormalMultilinearSeries.ofScalars ℝ (primitiveCoeff p.coeff)) 0 r := by
  set a : ℕ → ℝ := p.coeff
  set q := FormalMultilinearSeries.ofScalars ℝ (primitiveCoeff a)
  have hsumm : ∀ s : ℝ≥0, (s : ℝ≥0∞) < r → Summable fun n => |a n| * (s : ℝ) ^ n := by
    intro s hs
    have h := p.summable_norm_mul_pow (hs.trans_le hp.r_le)
    refine h.congr fun n => ?_
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, Real.norm_eq_abs]
  have hrad : r ≤ q.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun s hs => ?_
    refine q.le_radius_of_summable_norm ?_
    have hshift : Summable fun n => ‖q (n + 1)‖ * (s : ℝ) ^ (n + 1) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        ((hsumm s hs).mul_right (s : ℝ))
      rw [FormalMultilinearSeries.ofScalars_norm, primitiveCoeff, Real.norm_eq_abs, abs_div,
        pow_succ]
      have hn : (1 : ℝ) ≤ |(n : ℝ) + 1| := by
        rw [abs_of_pos (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have hdiv : |a n| / |(n : ℝ) + 1| ≤ |a n| :=
        div_le_self (abs_nonneg _) hn
      calc |a n| / |(n : ℝ) + 1| * ((s : ℝ) ^ n * s) ≤ |a n| * ((s : ℝ) ^ n * s) :=
            mul_le_mul_of_nonneg_right hdiv (by positivity)
        _ = |a n| * (s : ℝ) ^ n * s := by ring
    exact (summable_nat_add_iff 1).mp hshift
  refine ⟨hrad, hp.r_pos, fun {y} hy => ?_⟩
  have hy' : (‖y‖₊ : ℝ≥0∞) < r := by
    rw [← enorm_eq_nnnorm]
    simpa [Metric.mem_eball, edist_zero_right] using hy
  have hfy : ∀ t ∈ uIcc 0 y, HasSum (fun n => a n * t ^ n) (f t) := by
    intro t ht
    have htball : t ∈ Metric.eball (0 : ℝ) r := by
      have : ‖t‖₊ ≤ ‖y‖₊ := by
        rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_le_abs_of_mem_uIcc_zero ht
      have h2 := (ENNReal.coe_le_coe.mpr this).trans_lt hy'
      rw [← enorm_eq_nnnorm] at h2
      simpa [Metric.mem_eball, edist_zero_right] using h2
    have h := hp.hasSum htball
    rw [zero_add] at h
    refine h.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  set g : ℕ → C(ℝ, ℝ) := fun n => ⟨fun t => a n * t ^ n, by fun_prop⟩
  have hg : Summable fun n =>
      ‖ContinuousMap.restrict (⟨uIcc 0 y, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)
        (g n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hsumm ‖y‖₊ hy')
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
    simp only [ContinuousMap.restrict_apply, g, ContinuousMap.coe_mk, Real.norm_eq_abs, abs_mul,
      abs_pow, coe_nnnorm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_le_abs_of_mem_uIcc_zero t.2) n) (abs_nonneg _)
  have hint := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hg
  have heq : ∫ t in (0 : ℝ)..y, ∑' n, g n t = primitiveAtZero f y := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    exact (hfy t ht).tsum_eq
  rw [heq] at hint
  have hterm : ∀ n, ∫ t in (0 : ℝ)..y, g n t = primitiveCoeff a (n + 1) * y ^ (n + 1) := by
    intro n
    simp only [g, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_const_mul, integral_pow, primitiveCoeff]
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, sub_zero]
    ring
  simp_rw [hterm] at hint
  rw [zero_add]
  refine (hasSum_nat_add_iff' 1).mp ?_
  have hq : ∀ m, q m (fun _ => y) = primitiveCoeff a m * y ^ m := fun m => by
    simp only [q, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  simp only [Finset.range_one, Finset.sum_singleton, hq, primitiveCoeff, zero_mul, sub_zero]
  exact hint

/-- **The primitive of a real-analytic germ is real analytic.** -/
theorem analyticAt_primitiveAtZero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    AnalyticAt ℝ (primitiveAtZero f) 0 := by
  obtain ⟨p, r, hp⟩ := hf
  exact ⟨_, _, hasFPowerSeriesOnBall_primitiveAtZero hp⟩

/-- **The primitive differentiates back to the germ** near `0`. -/
theorem eventually_hasDerivAt_primitiveAtZero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∀ᶠ x in 𝓝 0, HasDerivAt (primitiveAtZero f) (f x) x := by
  obtain ⟨p, r, hp⟩ := hf
  have hcont := hp.continuousOn
  have hopen : IsOpen (Metric.eball (0 : ℝ) r) := Metric.isOpen_eball
  filter_upwards [hopen.mem_nhds (Metric.mem_eball_self hp.r_pos)] with x hx
  have hsub : uIcc 0 x ⊆ Metric.eball (0 : ℝ) r := by
    intro t ht
    have h1 : ‖t‖₊ ≤ ‖x‖₊ := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
      exact abs_le_abs_of_mem_uIcc_zero ht
    have hx' : (‖x‖₊ : ℝ≥0∞) < r := by
      rw [← enorm_eq_nnnorm]
      simpa [Metric.mem_eball, edist_zero_right] using hx
    have h2 := (ENNReal.coe_le_coe.mpr h1).trans_lt hx'
    rw [← enorm_eq_nnnorm] at h2
    simpa [Metric.mem_eball, edist_zero_right] using h2
  exact intervalIntegral.integral_hasDerivAt_right ((hcont.mono hsub).intervalIntegrable)
    (hcont.stronglyMeasurableAtFilter hopen x hx) (hcont.continuousAt (hopen.mem_nhds hx))

theorem primitiveAtZero_zero (f : ℝ → ℝ) : primitiveAtZero f 0 = 0 := by
  simp [primitiveAtZero]

/-- `∫₀ˣ f(-t) dt = -∫₀^{-x} f`. -/
theorem integral_comp_neg_zero (f : ℝ → ℝ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, f (-t) = -primitiveAtZero f (-x) := by
  rw [intervalIntegral.integral_comp_neg, neg_zero, primitiveAtZero,
    intervalIntegral.integral_symm]

theorem eventually_forall_uIcc {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝 0, P t) :
    ∀ᶠ x in 𝓝 0, ∀ t ∈ uIcc 0 x, P t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hP
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with x hx t ht
  refine hball ?_
  rw [Real.dist_eq, sub_zero]
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact (abs_le_abs_of_mem_uIcc_zero ht).trans_lt hx

/-- **The primitive of an even germ is odd.** -/
theorem primitiveAtZero_neg_of_even {f : ℝ → ℝ} (heven : ∀ᶠ t in 𝓝 0, f (-t) = f t) :
    ∀ᶠ x in 𝓝 0, primitiveAtZero f (-x) = -primitiveAtZero f x := by
  filter_upwards [eventually_forall_uIcc heven] with x hx
  have h := integral_comp_neg_zero f x
  rw [intervalIntegral.integral_congr fun t ht => hx t ht] at h
  change primitiveAtZero f x = _ at h
  linarith

/-- **The primitive of an odd germ is even.** -/
theorem primitiveAtZero_neg_of_odd {f : ℝ → ℝ} (hodd : ∀ᶠ t in 𝓝 0, f (-t) = -f t) :
    ∀ᶠ x in 𝓝 0, primitiveAtZero f (-x) = primitiveAtZero f x := by
  filter_upwards [eventually_forall_uIcc hodd] with x hx
  have h := integral_comp_neg_zero f x
  rw [intervalIntegral.integral_congr fun t ht => hx t ht, intervalIntegral.integral_neg] at h
  change -primitiveAtZero f x = _ at h
  linarith

/-- **Positivity of the primitive.**  A continuous germ positive on `(0, δ)` has positive
primitive there. -/
theorem eventually_primitiveAtZero_pos {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hpos : ∀ᶠ t in 𝓝[>] 0, 0 < f t) : ∀ᶠ x in 𝓝[>] 0, 0 < primitiveAtZero f x := by
  have hcont : ∀ᶠ t in 𝓝 0, ContinuousAt f t := hf.eventually_analyticAt.mono fun t ht =>
    ht.continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hcont
  obtain ⟨ε, hε, hεpos⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  refine Metric.mem_nhdsWithin_iff.mpr ⟨min δ ε, lt_min hδ hε, fun x ⟨hx, hx0⟩ => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hx0' : (0 : ℝ) < x := hx0
  have hxδ : |x| < δ := hx.trans_le (min_le_left _ _)
  have hxε : |x| < ε := hx.trans_le (min_le_right _ _)
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => ?_) hx0'
  · refine ContinuousOn.intervalIntegrable fun t ht => (hball ?_).continuousWithinAt
    rw [Real.dist_eq, sub_zero]
    exact (abs_le_abs_of_mem_uIcc_zero ht).trans_lt hxδ
  · refine hεpos ⟨?_, ht.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2.trans ((le_abs_self x).trans_lt hxε)

end GaloisForLFunctions.HTGeometry
