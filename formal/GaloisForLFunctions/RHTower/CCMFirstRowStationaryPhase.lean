import GaloisForLFunctions.HTGeometry.LogLinearTailIntegral
import GaloisForLFunctions.RHTower.ScaleSigmaSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exact stationary point and the weighted first-row sum

Two parts of the low-radial first-row estimate are exact and need no asymptotic input at all.

**The stationary point.**  The stationary equation for the difference phase
`xi_s(x) - xi_s(k x)` reduces, in the variable `y = x²`, *exactly* to the quadratic
`k² y² - (k²+1) y + s = 0`; `stationary_equation_reduce` is that reduction as a ring identity, with the
factor `k² - 1` displayed, which is what makes `k = 1` the only excluded case.  Its root above one and
the two-sided estimate `y - 1 ≍ k^{-2}` are then explicit algebra:
`stationaryRoot_isRoot`, `stationaryRoot_sub_one`, `stationaryRoot_sub_one_bounds`.

**The weighted sum.**  Given the pointwise two-term first-row bound, the logarithmically weighted sum
over the exact aperture is `O(c^{-1/2}) + O(log²c / c) = o(1)`.  Both arithmetic inputs were already in
the tree: `HTGeometry.summable_logLin_div_sq` for `sum log k / k²` and `RHTower.sum_log_div_le` for
`sum_(k<=N) log k / k <= log²N/2 + 1`.  `weighted_firstRow_sum_le` is the explicit inequality and
`tendsto_firstRowBound_atTop` is the `o(1)`.

The parts that are *not* here are the ones that genuinely import external asymptotics: Dunster's
pole-uniform expansion, the Bessel symbol branches, and one-dimensional stationary phase.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-! ## The exact stationary point -/

/-- **Equation (7).**  The exact reduction of the stationary equation.  Cross-multiplying
`sqrt((y-s)/(y-1)) = k sqrt((k²y-s)/(k²y-1))` and subtracting produces the displayed factor `k² - 1`
times the quadratic; that factor is the only reason `k = 1` has to be excluded. -/
theorem stationary_equation_reduce (s k y : ℝ) :
    (y - s) * (k ^ 2 * y - 1) - k ^ 2 * ((k ^ 2 * y - s) * (y - 1))
      = (k ^ 2 - 1) * (-(k ^ 2 * y ^ 2) + (k ^ 2 + 1) * y - s) := by
  ring

/-- The discriminant of the stationary quadratic. -/
def stationaryDisc (s k : ℝ) : ℝ := (k ^ 2 + 1) ^ 2 - 4 * k ^ 2 * s

/-- **Equation (8).**  The root of the stationary quadratic lying above one. -/
def stationaryRoot (s k : ℝ) : ℝ :=
  ((k ^ 2 + 1) + Real.sqrt (stationaryDisc s k)) / (2 * k ^ 2)

theorem stationaryDisc_nonneg {s k : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    0 ≤ stationaryDisc s k := by
  rw [stationaryDisc]
  nlinarith [sq_nonneg (k ^ 2 - 1), sq_nonneg k, sq_nonneg (k ^ 2 + 1)]

/-- The discriminant is at least `k⁴`, which is the lower half of the `y - 1 ≍ k^{-2}` estimate. -/
theorem sq_le_sqrt_stationaryDisc {s k : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    k ^ 2 ≤ Real.sqrt (stationaryDisc s k) := by
  have hge : (k ^ 2) ^ 2 ≤ stationaryDisc s k := by
    rw [stationaryDisc]
    nlinarith [sq_nonneg k]
  have h := Real.sqrt_le_sqrt hge
  rwa [Real.sqrt_sq (by positivity)] at h

/-- The discriminant is at most `(k²+1)²`, the upper half of the estimate. -/
theorem sqrt_stationaryDisc_le {s k : ℝ} (_hs0 : 0 ≤ s) :
    Real.sqrt (stationaryDisc s k) ≤ k ^ 2 + 1 := by
  have hle : stationaryDisc s k ≤ (k ^ 2 + 1) ^ 2 := by
    rw [stationaryDisc]
    nlinarith [sq_nonneg k]
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by positivity)] at h

theorem sqrt_stationaryDisc_sq {s k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Real.sqrt (stationaryDisc s k) * Real.sqrt (stationaryDisc s k) = stationaryDisc s k :=
  Real.mul_self_sqrt (stationaryDisc_nonneg (k := k) hs0 hs1)

/-- **Equation (7), verified.**  `stationaryRoot` is a root of the stationary quadratic. -/
theorem stationaryRoot_isRoot {s k : ℝ} (hk : k ≠ 0) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    k ^ 2 * stationaryRoot s k ^ 2 - (k ^ 2 + 1) * stationaryRoot s k + s = 0 := by
  have hk2 : (0 : ℝ) < k ^ 2 := by positivity
  have hdsq : Real.sqrt (stationaryDisc s k) * Real.sqrt (stationaryDisc s k)
      = (k ^ 2 + 1) ^ 2 - 4 * k ^ 2 * s := by
    rw [sqrt_stationaryDisc_sq (k := k) hs0 hs1, stationaryDisc]
  rw [stationaryRoot]
  have hkey : k ^ 2 * (((k ^ 2 + 1) + Real.sqrt (stationaryDisc s k)) / (2 * k ^ 2)) ^ 2
      - (k ^ 2 + 1) * (((k ^ 2 + 1) + Real.sqrt (stationaryDisc s k)) / (2 * k ^ 2)) + s
      = (Real.sqrt (stationaryDisc s k) * Real.sqrt (stationaryDisc s k)
          - ((k ^ 2 + 1) ^ 2 - 4 * k ^ 2 * s)) / (4 * k ^ 2) := by
    field_simp
    ring
  rw [hkey, hdsq, sub_self, zero_div]

/-- **Equation (9).**  The exact rationalised form of `y_{s,k} - 1`. -/
theorem stationaryRoot_sub_one {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    stationaryRoot s k - 1
      = 2 * (1 - s) / (Real.sqrt (stationaryDisc s k) + k ^ 2 - 1) := by
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hk1 : (1 : ℝ) ≤ k ^ 2 := by nlinarith
  have hk2 : (0 : ℝ) < 2 * k ^ 2 := by positivity
  have hdsq : Real.sqrt (stationaryDisc s k) * Real.sqrt (stationaryDisc s k)
      = (k ^ 2 + 1) ^ 2 - 4 * k ^ 2 * s := by
    rw [sqrt_stationaryDisc_sq (k := k) hs0 hs1, stationaryDisc]
  have hlow := sq_le_sqrt_stationaryDisc (k := k) hs0 hs1
  have hden : (0 : ℝ) < Real.sqrt (stationaryDisc s k) + k ^ 2 - 1 := by nlinarith
  rw [stationaryRoot, div_sub_one (ne_of_gt hk2),
    div_eq_div_iff (ne_of_gt hk2) (ne_of_gt hden)]
  linear_combination hdsq

/-- **Equation (9), two-sided.**  `y_{s,k} - 1` is comparable to `k^{-2}` with absolute constants. -/
theorem stationaryRoot_sub_one_bounds {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    1 / (2 * k ^ 2) ≤ stationaryRoot s k - 1 ∧ stationaryRoot s k - 1 ≤ 2 / k ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k ^ 2 := by nlinarith
  have hlow := sq_le_sqrt_stationaryDisc (k := k) hs0 hs1
  have hhigh := sqrt_stationaryDisc_le (k := k) hs0
  have heq := stationaryRoot_sub_one hk hs0 hs1
  have hden1 : 0 < Real.sqrt (stationaryDisc s k) + k ^ 2 - 1 := by nlinarith
  have hden2 : Real.sqrt (stationaryDisc s k) + k ^ 2 - 1 ≤ 2 * k ^ 2 := by nlinarith
  have hden3 : k ^ 2 ≤ Real.sqrt (stationaryDisc s k) + k ^ 2 - 1 := by nlinarith
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  refine ⟨?_, ?_⟩
  · rw [heq]
    gcongr <;> linarith
  · rw [heq]
    gcongr
    linarith

/-! ## The weighted first-row sum -/

/-- The convergent weight `sum_k log k / k²`. -/
def logLinTailSum : ℝ := ∑' k : ℕ, Real.log k / (k : ℝ) ^ 2

theorem sum_logLin_div_sq_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, Real.log k / (k : ℝ) ^ 2 ≤ logLinTailSum := by
  have hnn : ∀ k : ℕ, 0 ≤ Real.log k / (k : ℝ) ^ 2 := by
    intro k
    rcases Nat.lt_or_ge k 1 with hk | hk
    · interval_cases k
      · norm_num
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have : 0 ≤ Real.log k := Real.log_nonneg hk1
      positivity
  exact _root_.GaloisForLFunctions.HTGeometry.summable_logLin_div_sq.sum_le_tsum _
    fun k _ => hnn k

/-- **Equation (18), explicit form.**  The logarithmically weighted first row obeys the two-term
bound with the convergent `log k / k²` weight and the `log²N/2 + 1` harmonic weight. -/
theorem weighted_firstRow_sum_le {N : ℕ} (hN : 1 ≤ N) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {G : ℕ → ℝ} (hG : ∀ k : ℕ, 2 ≤ k → |G k| ≤ A / (k : ℝ) ^ 2 + B / (k : ℝ)) :
    ∑ k ∈ Finset.Icc 2 N, Real.log k * |G k|
      ≤ A * logLinTailSum + B * (Real.log N ^ 2 / 2 + 1) := by
  have hterm : ∀ k ∈ Finset.Icc 2 N, Real.log k * |G k|
      ≤ A * (Real.log k / (k : ℝ) ^ 2) + B * (Real.log k / (k : ℝ)) := by
    intro k hk
    obtain ⟨hk2, -⟩ := Finset.mem_Icc.mp hk
    have hklog : 0 ≤ Real.log k := by
      refine Real.log_nonneg ?_
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
    have hb := hG k hk2
    calc Real.log k * |G k| ≤ Real.log k * (A / (k : ℝ) ^ 2 + B / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hklog
      _ = A * (Real.log k / (k : ℝ) ^ 2) + B * (Real.log k / (k : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : A * ∑ k ∈ Finset.Icc 2 N, Real.log k / (k : ℝ) ^ 2 ≤ A * logLinTailSum :=
    mul_le_mul_of_nonneg_left (sum_logLin_div_sq_le N) hA
  have h2 : B * ∑ k ∈ Finset.Icc 2 N, Real.log k / (k : ℝ)
      ≤ B * (Real.log N ^ 2 / 2 + 1) := by
    refine mul_le_mul_of_nonneg_left (le_trans ?_ (_root_.RHTower.sum_log_div_le N hN)) hB
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.Icc_subset_Icc (by omega) le_rfl
    · intro k _ _
      rcases Nat.lt_or_ge k 1 with hk | hk
      · interval_cases k
        · norm_num
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have : 0 ≤ Real.log k := Real.log_nonneg hk1
        positivity
  linarith

/-- **Equation (18), the `o(1)` conclusion.**  Both terms of the bound vanish as the aperture grows. -/
theorem tendsto_firstRowBound_atTop (C T : ℝ) :
    Tendsto (fun c : ℝ => C / Real.sqrt c * T + C / c * (Real.log c ^ 2 / 2 + 1)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun c : ℝ => C / Real.sqrt c * T) atTop (𝓝 0) := by
    have hs : Tendsto (fun c : ℝ => Real.sqrt c) atTop atTop := Real.tendsto_sqrt_atTop
    have hinv : Tendsto (fun c : ℝ => 1 / Real.sqrt c) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp hs
      refine h.congr fun c => ?_
      rw [Function.comp_apply, one_div]
    have := (hinv.const_mul (C * T))
    rw [mul_zero] at this
    refine this.congr fun c => ?_
    ring
  have hlog : Tendsto (fun c : ℝ => Real.log c ^ 2 / (2 * c + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 2 0 2 two_ne_zero
  have hinvc : Tendsto (fun c : ℝ => 1 / c) atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_inv_atTop_zero.congr fun c => ?_
    rw [one_div]
  have hsecond : Tendsto (fun c : ℝ => C / c * (Real.log c ^ 2 / 2 + 1)) atTop (𝓝 0) := by
    have h1 := hlog.const_mul C
    have h2 := hinvc.const_mul C
    rw [mul_zero] at h1 h2
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have hcne : c ≠ 0 := ne_of_gt hc
    field_simp
    ring
  have := hsqrt.add hsecond
  rwa [add_zero] at this

/-! ## The endpoint phase bracket -/

open MeasureTheory Set

/-- The exact Liouville speed, with `s` the squared separation parameter. -/
def xiSpeed (s t : ℝ) : ℝ := Real.sqrt ((t ^ 2 - s) / (t ^ 2 - 1))

/-- The comparison speed `t / sqrt(t² - 1)`.  It is the `s = 0` case and has the exact antiderivative
`sqrt(t² - 1)`, which is what makes the bracket `(4)` explicit rather than asymptotic. -/
def xiCompSpeed (t : ℝ) : ℝ := t / Real.sqrt (t ^ 2 - 1)

/-- The endpoint-normalised phase `xi_s(x) = int_1^x sqrt((t²-s)/(t²-1)) dt`. -/
def xiEndpointPhase (s x : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, xiSpeed s t

theorem sqrt_two_mul_sqrt_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    Real.sqrt 2 * Real.sqrt (t - 1) ≤ Real.sqrt (t ^ 2 - 1) := by
  have hmul : Real.sqrt 2 * Real.sqrt (t - 1) = Real.sqrt (2 * (t - 1)) :=
    (Real.sqrt_mul (by norm_num) _).symm
  rw [hmul]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-- Away from the endpoint the comparison speed is dominated by an integrable power. -/
theorem xiCompSpeed_le {x t : ℝ} (ht1 : 1 < t) (htx : t ≤ x) :
    xiCompSpeed t ≤ (x / Real.sqrt 2) * (t - 1) ^ (-(1 : ℝ) / 2) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
  have hsub : (0 : ℝ) < t - 1 := by linarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : (0 : ℝ) < Real.sqrt (t - 1) := Real.sqrt_pos.mpr hsub
  have hrpow : (t - 1) ^ (-(1 : ℝ) / 2) = (Real.sqrt (t - 1))⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) from by ring, Real.rpow_neg hsub.le,
      ← Real.sqrt_eq_rpow]
  have hden : Real.sqrt 2 * Real.sqrt (t - 1) ≤ Real.sqrt (t ^ 2 - 1) :=
    sqrt_two_mul_sqrt_sub_one_le ht1.le
  have hpos : (0 : ℝ) < Real.sqrt 2 * Real.sqrt (t - 1) := by positivity
  rw [xiCompSpeed, hrpow]
  calc t / Real.sqrt (t ^ 2 - 1) ≤ t / (Real.sqrt 2 * Real.sqrt (t - 1)) := by gcongr
    _ ≤ x / (Real.sqrt 2 * Real.sqrt (t - 1)) := by gcongr
    _ = x / Real.sqrt 2 * (Real.sqrt (t - 1))⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv]
        ring

theorem intervalIntegrable_rpow_sub_one {x : ℝ} :
    IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 : ℝ) / 2)) volume 1 x := by
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 (x - 1) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h := hbase.comp_sub_right 1
  simpa using h

theorem intervalIntegrable_xiCompSpeed {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable xiCompSpeed volume 1 x := by
  have hmeas : Measurable xiCompSpeed := by
    unfold xiCompSpeed
    fun_prop
  have hdom : IntervalIntegrable
      (fun t : ℝ => (x / Real.sqrt 2) * (t - 1) ^ (-(1 : ℝ) / 2)) volume 1 x :=
    (intervalIntegrable_rpow_sub_one).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx] at hdom ⊢
  refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, htx⟩ := ht
  have hnn : 0 ≤ xiCompSpeed t := by
    rw [xiCompSpeed]
    have : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact xiCompSpeed_le ht1 htx

/-- The exact antiderivative: `int_1^x t/sqrt(t²-1) dt = sqrt(x²-1)`.  The integrand blows up at the
endpoint, so this is the improper form of the fundamental theorem, with integrability supplied by the
`(t-1)^{-1/2}` comparison. -/
theorem integral_xiCompSpeed {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, xiCompSpeed t) = Real.sqrt (x ^ 2 - 1) := by
  have hcont : ContinuousOn (fun t : ℝ => Real.sqrt (t ^ 2 - 1)) (Icc 1 x) := by
    fun_prop
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
      HasDerivWithinAt (fun t : ℝ => Real.sqrt (t ^ 2 - 1)) (xiCompSpeed t) (Ioi t) t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hne : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hinner : HasDerivAt (fun u : ℝ => u ^ 2 - 1) (2 * t) t := by
      have h := (hasDerivAt_pow 2 t).sub_const 1
      simpa using h
    have hsq := (Real.hasDerivAt_sqrt hne).comp t hinner
    have hval : 1 / (2 * Real.sqrt (t ^ 2 - 1)) * (2 * t) = xiCompSpeed t := by
      have hpos : (0 : ℝ) < Real.sqrt (t ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
      rw [xiCompSpeed]
      field_simp
    rw [hval] at hsq
    exact hsq.hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv
    (intervalIntegrable_xiCompSpeed hx)
  rw [h]
  norm_num

/-- **Equation (4), upper half of the integrand comparison.** -/
theorem xiSpeed_le_xiCompSpeed {s t : ℝ} (hs : 0 ≤ s) (ht : 1 < t) :
    xiSpeed s t ≤ xiCompSpeed t := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hden : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hcomp : (t ^ 2 - s) / (t ^ 2 - 1) ≤ t ^ 2 / (t ^ 2 - 1) := by
    gcongr
    linarith
  have hsqrt : Real.sqrt (t ^ 2 / (t ^ 2 - 1)) = xiCompSpeed t := by
    rw [xiCompSpeed, Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht0.le]
  rw [xiSpeed, ← hsqrt]
  exact Real.sqrt_le_sqrt hcomp

/-- **Equation (4), lower half of the integrand comparison.** -/
theorem sqrt_one_sub_mul_xiCompSpeed_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 1 < t) :
    Real.sqrt (1 - s) * xiCompSpeed t ≤ xiSpeed s t := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have hden : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hcomp : (1 - s) * t ^ 2 / (t ^ 2 - 1) ≤ (t ^ 2 - s) / (t ^ 2 - 1) := by
    rw [div_le_div_iff_of_pos_right hden]
    nlinarith
  have hsqrt : Real.sqrt ((1 - s) * t ^ 2 / (t ^ 2 - 1))
      = Real.sqrt (1 - s) * xiCompSpeed t := by
    rw [xiCompSpeed, mul_div_assoc, Real.sqrt_mul (by linarith), Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq ht0.le]
  rw [xiSpeed, ← hsqrt]
  exact Real.sqrt_le_sqrt hcomp

theorem intervalIntegrable_xiSpeed {s x : ℝ} (hs : 0 ≤ s) (hx : 1 ≤ x) :
    IntervalIntegrable (xiSpeed s) volume 1 x := by
  have hmeas : Measurable (xiSpeed s) := by
    unfold xiSpeed
    fun_prop
  have hdom := intervalIntegrable_xiCompSpeed hx
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx] at hdom ⊢
  refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have hnn : 0 ≤ xiSpeed s t := by
    rw [xiSpeed]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact xiSpeed_le_xiCompSpeed hs ht.1

/-- **Equation (4).**  The endpoint phase is bracketed by `sqrt(x²-1)` on both sides, with the exact
constant `sqrt(1-s)` below.  The endpoint value of both integrands is the Lean junk value `0`, which is
harmless: the closed-interval comparison holds there too. -/
theorem xiEndpointPhase_bounds {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : 1 ≤ x) :
    Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) ≤ xiEndpointPhase s x
      ∧ xiEndpointPhase s x ≤ Real.sqrt (x ^ 2 - 1) := by
  have hcomp := intervalIntegrable_xiCompSpeed hx
  have hspeed := intervalIntegrable_xiSpeed hs0 hx
  have hend : xiSpeed s 1 = 0 ∧ xiCompSpeed 1 = 0 := by
    constructor
    · rw [xiSpeed]
      norm_num
    · rw [xiCompSpeed]
      norm_num
  refine ⟨?_, ?_⟩
  · have hmono : (∫ t in (1 : ℝ)..x, Real.sqrt (1 - s) * xiCompSpeed t)
        ≤ ∫ t in (1 : ℝ)..x, xiSpeed s t := by
      refine intervalIntegral.integral_mono_on hx (hcomp.const_mul _) hspeed fun t ht => ?_
      rcases eq_or_lt_of_le ht.1 with h1 | h1
      · rw [← h1, hend.1, hend.2, mul_zero]
      · exact sqrt_one_sub_mul_xiCompSpeed_le hs0 hs1 h1
    rw [intervalIntegral.integral_const_mul, integral_xiCompSpeed hx] at hmono
    exact hmono
  · have hmono : (∫ t in (1 : ℝ)..x, xiSpeed s t) ≤ ∫ t in (1 : ℝ)..x, xiCompSpeed t := by
      refine intervalIntegral.integral_mono_on hx hspeed hcomp fun t ht => ?_
      rcases eq_or_lt_of_le ht.1 with h1 | h1
      · rw [← h1, hend.1, hend.2]
      · exact xiSpeed_le_xiCompSpeed hs0 h1
    rw [integral_xiCompSpeed hx] at hmono
    exact hmono

/-! ## The Liouville–Green amplitude -/

/-- The amplitude `A_s(x) = xi_s(x)^{1/2} / [(x²-1)(x²-s)]^{1/4}`, with the fourth root written as an
iterated square root. -/
def xiAmplitude (s x : ℝ) : ℝ :=
  Real.sqrt (xiEndpointPhase s x) / Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))

/-- **Equation (4), amplitude half.**  The amplitude obeys the square-root decay `x^{-1/2}` with the
absolute constant `2^{1/4}`.  Both inputs are exact: the phase upper bound `xi_s(x) <= sqrt(x²-1)`
cancels the first factor of the fourth root, and `x² - s >= x²/2` converts the second one. -/
theorem xiAmplitude_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiAmplitude s x ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hA : (0 : ℝ) < Real.sqrt (Real.sqrt (x ^ 2 - 1)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h1)
  have hB : (0 : ℝ) < Real.sqrt (Real.sqrt (x ^ 2 - s)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr h2)
  have hden : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))
      = Real.sqrt (Real.sqrt (x ^ 2 - 1)) * Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
    rw [Real.sqrt_mul h1.le, Real.sqrt_mul (Real.sqrt_nonneg _)]
  have hnum : Real.sqrt (xiEndpointPhase s x) ≤ Real.sqrt (Real.sqrt (x ^ 2 - 1)) :=
    Real.sqrt_le_sqrt (xiEndpointPhase_bounds hs0 (by linarith) hx.le).2
  have hstep : xiAmplitude s x ≤ 1 / Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
    rw [xiAmplitude, hden]
    calc Real.sqrt (xiEndpointPhase s x)
          / (Real.sqrt (Real.sqrt (x ^ 2 - 1)) * Real.sqrt (Real.sqrt (x ^ 2 - s)))
        ≤ Real.sqrt (Real.sqrt (x ^ 2 - 1))
          / (Real.sqrt (Real.sqrt (x ^ 2 - 1)) * Real.sqrt (Real.sqrt (x ^ 2 - s))) := by
          gcongr
      _ = 1 / Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
          rw [← div_div, div_self hA.ne']
  refine hstep.trans ?_
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlow : Real.sqrt x / Real.sqrt (Real.sqrt 2) ≤ Real.sqrt (Real.sqrt (x ^ 2 - s)) := by
    have hmid : x / Real.sqrt 2 ≤ Real.sqrt (x ^ 2 - s) := by
      have hle : x ^ 2 / 2 ≤ x ^ 2 - s := by nlinarith
      have hstep2 : Real.sqrt (x ^ 2 / 2) ≤ Real.sqrt (x ^ 2 - s) := Real.sqrt_le_sqrt hle
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hx0.le] at hstep2
      exact hstep2
    have hstep3 : Real.sqrt (x / Real.sqrt 2) ≤ Real.sqrt (Real.sqrt (x ^ 2 - s)) :=
      Real.sqrt_le_sqrt hmid
    rwa [Real.sqrt_div' _ (Real.sqrt_nonneg 2)] at hstep3
  have hs2s : (0 : ℝ) < Real.sqrt (Real.sqrt 2) := Real.sqrt_pos.mpr hs2
  have hxs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [div_le_div_iff₀ hB hxs]
  calc (1 : ℝ) * Real.sqrt x = Real.sqrt (Real.sqrt 2) * (Real.sqrt x / Real.sqrt (Real.sqrt 2)) := by
        rw [one_mul, mul_div_cancel₀ _ hs2s.ne']
    _ ≤ Real.sqrt (Real.sqrt 2) * Real.sqrt (Real.sqrt (x ^ 2 - s)) :=
        mul_le_mul_of_nonneg_left hlow hs2s.le

/-! ## The phase derivatives -/

theorem continuousAt_xiSpeed {s x : ℝ} (hx : 1 < x) : ContinuousAt (xiSpeed s) x := by
  have hne : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : ContinuousAt (fun t : ℝ => (t ^ 2 - s) / (t ^ 2 - 1)) x :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hne
  exact hq.sqrt

theorem continuousOn_xiSpeed (s : ℝ) : ContinuousOn (xiSpeed s) (Set.Ioi 1) :=
  fun _ hx => (continuousAt_xiSpeed (s := s) hx).continuousWithinAt

/-- The endpoint phase is differentiable in the interior with derivative the Liouville speed.  The
integrand is singular at the endpoint, so the one-sided fundamental theorem is applied at an interior
point, with integrability supplied by the endpoint comparison. -/
theorem hasDerivAt_xiEndpointPhase {s x : ℝ} (hs : 0 ≤ s) (hx : 1 < x) :
    HasDerivAt (xiEndpointPhase s) (xiSpeed s x) x := by
  have hint : IntervalIntegrable (xiSpeed s) volume 1 x := intervalIntegrable_xiSpeed hs hx.le
  have hmeas : StronglyMeasurableAtFilter (xiSpeed s) (nhds x) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (continuousOn_xiSpeed s) x hx
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas (continuousAt_xiSpeed hx)

theorem xiSpeed_mul (s r x : ℝ) :
    xiSpeed s (r * x) = Real.sqrt ((r ^ 2 * x ^ 2 - s) / (r ^ 2 * x ^ 2 - 1)) := by
  rw [xiSpeed, mul_pow]

/-- **Equation (10).**  The dilated phase differentiates to `r` times the speed at the dilated
argument. -/
theorem hasDerivAt_xiEndpointPhase_dilate {s r x : ℝ} (hs : 0 ≤ s) (hrx : 1 < r * x) :
    HasDerivAt (fun x : ℝ => xiEndpointPhase s (r * x))
      (r * Real.sqrt ((r ^ 2 * x ^ 2 - s) / (r ^ 2 * x ^ 2 - 1))) x := by
  have h1 : HasDerivAt (xiEndpointPhase s) (xiSpeed s (r * x)) (r * x) :=
    hasDerivAt_xiEndpointPhase hs hrx
  have h2 : HasDerivAt (fun x : ℝ => r * x) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  have h := h1.comp x h2
  rw [xiSpeed_mul] at h
  simpa [Function.comp_def, mul_comm] using h

/-- The Liouville speed differentiates in closed form: the numerator `x(s-1)` is negative on the
admissible parameter range, which is the sign that makes the difference phase concave. -/
theorem hasDerivAt_xiSpeed {s x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x) :
    HasDerivAt (xiSpeed s) (x * (s - 1) / ((x ^ 2 - 1) ^ 2 * xiSpeed s x)) x := by
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hq : (0 : ℝ) < (x ^ 2 - s) / (x ^ 2 - 1) := div_pos h2 h1
  have hsq : (0 : ℝ) < xiSpeed s x := by
    rw [xiSpeed]
    exact Real.sqrt_pos.mpr hq
  have hinner : HasDerivAt (fun t : ℝ => (t ^ 2 - s) / (t ^ 2 - 1))
      (2 * x * (s - 1) / (x ^ 2 - 1) ^ 2) x := by
    have hc : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const s
    have hd : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have h := hc.fun_div hd h1.ne'
    have hval : (2 * x * (x ^ 2 - 1) - (x ^ 2 - s) * (2 * x)) / (x ^ 2 - 1) ^ 2
        = 2 * x * (s - 1) / (x ^ 2 - 1) ^ 2 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [hval] at h
    exact h
  have h := hinner.sqrt hq.ne'
  have hval : (2 * x * (s - 1) / (x ^ 2 - 1) ^ 2)
        / (2 * Real.sqrt ((x ^ 2 - s) / (x ^ 2 - 1)))
      = x * (s - 1) / ((x ^ 2 - 1) ^ 2 * xiSpeed s x) := by
    rw [xiSpeed]
    have hne : Real.sqrt ((x ^ 2 - s) / (x ^ 2 - 1)) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp
  rw [hval] at h
  exact h

/-! ## The difference phase and its two derivatives -/

/-- The closed-form derivative of the Liouville speed. -/
def xiSpeedDeriv (s t : ℝ) : ℝ := t * (s - 1) / ((t ^ 2 - 1) ^ 2 * xiSpeed s t)

/-- The difference phase `phi_(s,k)(x) = xi_s(x) - xi_s(k x)`. -/
def xiDiffPhase (s k x : ℝ) : ℝ := xiEndpointPhase s x - xiEndpointPhase s (k * x)

/-- Its first derivative. -/
def xiDiffSpeed (s k x : ℝ) : ℝ := xiSpeed s x - k * xiSpeed s (k * x)

theorem hasDerivAt_xiDiffPhase {s k x : ℝ} (hs : 0 ≤ s) (hx : 1 < x) (hkx : 1 < k * x) :
    HasDerivAt (xiDiffPhase s k) (xiDiffSpeed s k x) x := by
  have h1 := hasDerivAt_xiEndpointPhase hs hx
  have h2 := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := k) (x := x) hs hkx
  have h2' : HasDerivAt (fun x : ℝ => xiEndpointPhase s (k * x)) (k * xiSpeed s (k * x)) x := by
    rw [xiSpeed_mul]
    exact h2
  exact h1.sub h2'

theorem hasDerivAt_xiDiffSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x) (hkx : 1 < k * x) :
    HasDerivAt (xiDiffSpeed s k) (xiSpeedDeriv s x - k ^ 2 * xiSpeedDeriv s (k * x)) x := by
  have h1 : HasDerivAt (xiSpeed s) (xiSpeedDeriv s x) x := hasDerivAt_xiSpeed hs1 hx
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have h2 : HasDerivAt (fun t : ℝ => xiSpeed s (k * t)) (xiSpeedDeriv s (k * x) * k) x :=
    (hasDerivAt_xiSpeed hs1 hkx).comp x hlin
  have h3 := h2.const_mul k
  have hval : k * (xiSpeedDeriv s (k * x) * k) = k ^ 2 * xiSpeedDeriv s (k * x) := by ring
  rw [hval] at h3
  exact h1.sub h3

/-! ## The stationary point -/

/-- The stationary point itself, `x = sqrt(y_(s,k))`. -/
def stationaryPoint (s k : ℝ) : ℝ := Real.sqrt (stationaryRoot s k)

theorem stationaryPoint_nonneg (s k : ℝ) : 0 ≤ stationaryPoint s k := Real.sqrt_nonneg _

theorem one_lt_stationaryRoot {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    1 < stationaryRoot s k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have h := (stationaryRoot_sub_one_bounds hk hs0 hs1).1
  have hpos : (0 : ℝ) < 1 / (2 * k ^ 2) := by positivity
  linarith

theorem stationaryPoint_sq {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    stationaryPoint s k ^ 2 = stationaryRoot s k :=
  Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one (one_lt_stationaryRoot hk hs0 hs1)))

theorem one_lt_stationaryPoint {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    1 < stationaryPoint s k := by
  have h := one_lt_stationaryRoot hk hs0 hs1
  rw [stationaryPoint, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) h

/-- The exact relation `(k²y - 1)(y - 1) = 1 - s` at the stationary root: the root equation in the
form that makes the far Bessel argument explicit. -/
theorem stationaryRoot_mul_identity {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    (k ^ 2 * stationaryRoot s k - 1) * (stationaryRoot s k - 1) = 1 - s := by
  have hk0 : k ≠ 0 := (lt_of_lt_of_le zero_lt_one hk).ne'
  have hroot := stationaryRoot_isRoot hk0 hs0 hs1
  linear_combination hroot

theorem zero_lt_stationaryRoot_far {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    0 < k ^ 2 * stationaryRoot s k - 1 := by
  have hid := stationaryRoot_mul_identity hk hs0 hs1
  have hd : 0 < stationaryRoot s k - 1 := by
    have := one_lt_stationaryRoot hk hs0 hs1
    linarith
  have hs : 0 < 1 - s := by linarith
  nlinarith [hid, hd, hs]

/-- The near speed at the stationary point is exactly `k x`. -/
theorem xiSpeed_stationaryPoint {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    xiSpeed s (stationaryPoint s k) = k * stationaryPoint s k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hy := one_lt_stationaryRoot hk hs0 hs1
  have hsq := stationaryPoint_sq hk hs0 hs1
  have hd : 0 < stationaryRoot s k - 1 := by linarith
  have hroot := stationaryRoot_isRoot hk0.ne' hs0 hs1
  have hquot : (stationaryRoot s k - s) / (stationaryRoot s k - 1)
      = (k * stationaryPoint s k) ^ 2 := by
    rw [mul_pow, hsq]
    rw [div_eq_iff hd.ne']
    linear_combination -hroot
  rw [xiSpeed, hsq, hquot]
  exact Real.sqrt_sq (by positivity [stationaryPoint_nonneg s k])

/-- The far speed at the stationary point is exactly `x`. -/
theorem xiSpeed_far_stationaryPoint {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    xiSpeed s (k * stationaryPoint s k) = stationaryPoint s k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hy := one_lt_stationaryRoot hk hs0 hs1
  have hsq := stationaryPoint_sq hk hs0 hs1
  have hfar := zero_lt_stationaryRoot_far hk hs0 hs1
  have hroot := stationaryRoot_isRoot hk0.ne' hs0 hs1
  have hquot : ((k * stationaryPoint s k) ^ 2 - s) / ((k * stationaryPoint s k) ^ 2 - 1)
      = stationaryPoint s k ^ 2 := by
    rw [mul_pow, hsq, div_eq_iff (by linarith : k ^ 2 * stationaryRoot s k - 1 ≠ 0)]
    linear_combination -hroot
  rw [xiSpeed, hquot]
  exact Real.sqrt_sq (stationaryPoint_nonneg s k)

/-- **Equation (11), closed form.**  At the stationary point both Liouville speeds collapse to
explicit algebraic values, so the second derivative of the difference phase is a rational expression
in `k` and `y - 1`. -/
theorem xiDiffSecond_stationaryPoint_eq {s k : ℝ} (hk : 1 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    xiSpeedDeriv s (stationaryPoint s k)
        - k ^ 2 * xiSpeedDeriv s (k * stationaryPoint s k)
      = (s - 1) * (1 / (k * (stationaryRoot s k - 1) ^ 2)
          - k ^ 3 * (stationaryRoot s k - 1) ^ 2 / (1 - s) ^ 2) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hy := one_lt_stationaryRoot hk hs0 hs1
  have hsq := stationaryPoint_sq hk hs0 hs1
  have hx0 : 0 < stationaryPoint s k := lt_trans zero_lt_one (one_lt_stationaryPoint hk hs0 hs1)
  have hd : 0 < stationaryRoot s k - 1 := by linarith
  have hfar := zero_lt_stationaryRoot_far hk hs0 hs1
  have hid := stationaryRoot_mul_identity hk hs0 hs1
  have hs : 0 < 1 - s := by linarith
  have hnear : xiSpeedDeriv s (stationaryPoint s k)
      = (s - 1) / (k * (stationaryRoot s k - 1) ^ 2) := by
    rw [xiSpeedDeriv, xiSpeed_stationaryPoint hk hs0 hs1, hsq]
    have hdne : stationaryRoot s k - 1 ≠ 0 := hd.ne'
    have hxne : stationaryPoint s k ≠ 0 := hx0.ne'
    have hkne : k ≠ 0 := hk0.ne'
    field_simp
  have hfarval : xiSpeedDeriv s (k * stationaryPoint s k)
      = k * (s - 1) * (stationaryRoot s k - 1) ^ 2 / (1 - s) ^ 2 := by
    rw [xiSpeedDeriv, xiSpeed_far_stationaryPoint hk hs0 hs1, mul_pow, hsq]
    have hdne : stationaryRoot s k - 1 ≠ 0 := hd.ne'
    have hxne : stationaryPoint s k ≠ 0 := hx0.ne'
    have hkne : k ≠ 0 := hk0.ne'
    have hfne : k ^ 2 * stationaryRoot s k - 1 ≠ 0 := hfar.ne'
    have hsne : (1 : ℝ) - s ≠ 0 := hs.ne'
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have hsqid : (k ^ 2 * stationaryRoot s k - 1) ^ 2 * (stationaryRoot s k - 1) ^ 2
        = (1 - s) ^ 2 := by
      rw [← mul_pow, hid]
    calc k * stationaryPoint s k * (s - 1) * ((1 - s) ^ 2)
        = k * stationaryPoint s k * (s - 1)
            * ((k ^ 2 * stationaryRoot s k - 1) ^ 2 * (stationaryRoot s k - 1) ^ 2) := by
          rw [hsqid]
      _ = k * (s - 1) * (stationaryRoot s k - 1) ^ 2
            * ((k ^ 2 * stationaryRoot s k - 1) ^ 2 * stationaryPoint s k) := by ring
  rw [hnear, hfarval]
  have hdne : stationaryRoot s k - 1 ≠ 0 := hd.ne'
  have hkne : k ≠ 0 := hk0.ne'
  have hsne : (1 : ℝ) - s ≠ 0 := hs.ne'
  field_simp

/-! ## The `k³` law -/

/-- A sharpened upper bound on `y - 1`: the discriminant lower bound `k² ≤ sqrt(disc)` improves the
crude `2 k^{-2}` to `(8/7) k^{-2}` once `k ≥ 2`, which is what separates the two blocks of the second
derivative. -/
theorem stationaryRoot_sub_one_le_sharp {s k : ℝ} (hk : 2 ≤ k) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    stationaryRoot s k - 1 ≤ 8 / (7 * k ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hsqrt : k ^ 2 ≤ Real.sqrt (stationaryDisc s k) := sq_le_sqrt_stationaryDisc hs0 hs1
  have heq := stationaryRoot_sub_one hk1 hs0 hs1
  have hden : 0 < Real.sqrt (stationaryDisc s k) + k ^ 2 - 1 := by nlinarith
  have hk2 : (4 : ℝ) ≤ k ^ 2 := by nlinarith
  rw [heq, div_le_div_iff₀ hden (by positivity)]
  nlinarith [hsqrt, hk2, hs0, hs1]

/-- **Equation (11).**  At the stationary point the second derivative of the difference phase has
size exactly of order `k³`, with absolute constants on the whole admissible parameter range. -/
theorem abs_xiDiffSecond_stationaryPoint_bounds {s k : ℝ} (hk : 2 ≤ k) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) :
    k ^ 3 / 20 ≤ |xiSpeedDeriv s (stationaryPoint s k)
        - k ^ 2 * xiSpeedDeriv s (k * stationaryPoint s k)|
      ∧ |xiSpeedDeriv s (stationaryPoint s k)
        - k ^ 2 * xiSpeedDeriv s (k * stationaryPoint s k)| ≤ 4 * k ^ 3 := by
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hksq : (4 : ℝ) ≤ k ^ 2 := by nlinarith
  have hk4 : (16 : ℝ) ≤ k ^ 4 := by nlinarith [hksq, sq_nonneg (k ^ 2 - 4)]
  set d : ℝ := stationaryRoot s k - 1 with hddef
  have hd0 : 0 < d := by
    have := one_lt_stationaryRoot hk1 hs0 hs1
    rw [hddef]; linarith
  have hdu : d ≤ 8 / (7 * k ^ 2) := stationaryRoot_sub_one_le_sharp hk hs0 hs1
  have hdl : 1 / (2 * k ^ 2) ≤ d := (stationaryRoot_sub_one_bounds hk1 hs0 hs1).1
  have hs : (1 : ℝ) / 2 ≤ 1 - s := by linarith
  have hs' : (1 : ℝ) - s ≤ 1 := by linarith
  have hdsq : d ^ 2 ≤ 64 / (49 * k ^ 4) := by
    have h : d ^ 2 ≤ (8 / (7 * k ^ 2)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ d := hd0.le
      gcongr
    calc d ^ 2 ≤ (8 / (7 * k ^ 2)) ^ 2 := h
      _ = 64 / (49 * k ^ 4) := by
          field_simp
          ring
  have hdsq' : 1 / (4 * k ^ 4) ≤ d ^ 2 := by
    have h : (1 / (2 * k ^ 2)) ^ 2 ≤ d ^ 2 := by
      have h0 : (0 : ℝ) ≤ 1 / (2 * k ^ 2) := by positivity
      gcongr
    calc 1 / (4 * k ^ 4) = (1 / (2 * k ^ 2)) ^ 2 := by
          field_simp
          ring
      _ ≤ d ^ 2 := h
  -- the two blocks
  have hL : 49 * k ^ 3 / 64 ≤ 1 / (k * d ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc 49 * k ^ 3 / 64 * (k * d ^ 2) = 49 * k ^ 4 / 64 * d ^ 2 := by ring
      _ ≤ 49 * k ^ 4 / 64 * (64 / (49 * k ^ 4)) := by gcongr
      _ = 1 := by field_simp
  have hLub : 1 / (k * d ^ 2) ≤ 4 * k ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = 4 * k ^ 4 * (1 / (4 * k ^ 4)) := by field_simp
      _ ≤ 4 * k ^ 4 * d ^ 2 := by gcongr
      _ = 4 * k ^ 3 * (k * d ^ 2) := by ring
  have hM : k ^ 3 * d ^ 2 / (1 - s) ^ 2 ≤ 256 / (49 * k) := by
    calc k ^ 3 * d ^ 2 / (1 - s) ^ 2 ≤ k ^ 3 * (64 / (49 * k ^ 4)) / (1 / 2) ^ 2 := by
          gcongr
      _ = 256 / (49 * k) := by
          field_simp
          ring
  have hMnn : 0 ≤ k ^ 3 * d ^ 2 / (1 - s) ^ 2 := by positivity
  have hgap : 256 / (49 * k) ≤ 49 * k ^ 3 / 64 - k ^ 3 / 10 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hk4, hk0]
  have hbrl : k ^ 3 / 10 ≤ 1 / (k * d ^ 2) - k ^ 3 * d ^ 2 / (1 - s) ^ 2 := by linarith
  have hbru : 1 / (k * d ^ 2) - k ^ 3 * d ^ 2 / (1 - s) ^ 2 ≤ 4 * k ^ 3 := by linarith
  have hbrpos : 0 < 1 / (k * d ^ 2) - k ^ 3 * d ^ 2 / (1 - s) ^ 2 := by
    have : (0 : ℝ) < k ^ 3 / 10 := by positivity
    linarith
  have heq := xiDiffSecond_stationaryPoint_eq hk1 hs0 hs1
  rw [heq, abs_mul, abs_of_nonpos (by linarith : s - 1 ≤ 0),
    abs_of_pos hbrpos, neg_sub]
  constructor
  · calc k ^ 3 / 20 = (1 / 2) * (k ^ 3 / 10) := by ring
      _ ≤ (1 - s) * (1 / (k * d ^ 2) - k ^ 3 * d ^ 2 / (1 - s) ^ 2) := by
          exact mul_le_mul hs hbrl (by positivity) (by linarith)
  · calc (1 - s) * (1 / (k * d ^ 2) - k ^ 3 * d ^ 2 / (1 - s) ^ 2)
        ≤ 1 * (4 * k ^ 3) := by
          exact mul_le_mul hs' hbru hbrpos.le (by norm_num)
      _ = 4 * k ^ 3 := by ring

end GaloisForLFunctions.RHTower

end
