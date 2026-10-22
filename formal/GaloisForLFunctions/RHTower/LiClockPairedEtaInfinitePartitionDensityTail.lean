import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionMeasure

/-!
# Tail of the infinite paired-eta half-tilt difference density

The paired-eta logarithmic support `⋃_n (log(2n+1), log(2n+2)]` corresponds under `w = e^u` to
the arithmetic indicator `α(w)` of `⋃_k (2k+1, 2k+2]`. Its raw half-tilt difference density
`ρ(x) = ∫ w(v+x) w(v) dv` (with `w(v) = e^{-v/2}` on the support) satisfies
`ρ(x) = e^{-|x|/2} H(e^{|x|})`, where `H(r) = ∫_1^∞ α(w) α(rw)/w² dw`. Integrating by parts
against the periodic primitives `B` of `α - 1/2` (with `|B| ≤ 1/4`) and `D` of `B`
(with `|D| ≤ 1/16`) gives `|H(r) - (log 2)/2| ≤ π²/(16 r)` and the second-order expansion
`H(r) = (log 2)/2 + P(r)/r + O(1/r²)` with an explicit continuous 2-periodic correction `P`,
equal to `-π²/48` at even integers and `π²/24` at odd integers. Consequently
`ρ(x) = (log 2/2) e^{-|x|/2} + O(e^{-3|x|/2})` with an oscillating, non-vanishing
`e^{-3x/2}` correction. The module also evaluates the normalizer `Z = ∫ e^{-u/2} dη(u)` as
`2 ∑_n (1/√(2n+1) - 1/√(2n+2))`, bounds it below by `71/60`, and shows the limiting ratio
`2 log 2/Z²` of the normalized density to the half-line reference density lies in `(0, 1)`.

## Main results

- `liClockPairedEtaInfinitePartitionPrimitiveB_interval_error_le`:
  `|∫_a^b (α(rw) - 1/2)/w² dw| ≤ 1/(2 r a²)` for `r > 0`, `0 < a ≤ b`.
- `liClockPairedEtaInfinitePartition_retained_inverse_mass`: `∫_1^∞ α(w)/w² dw = log 2`.
- `liClockPairedEtaInfinitePartitionAveragingH_error_le`: `|H(r) - (log 2)/2| ≤ π²/(16 r)` for `r ≥ 1`.
- `liClockPairedEtaInfinitePartitionAveragingH_correction_error_le`:
  `|H(r) - (log 2)/2 - P(r)/r| ≤ (∑_n (2n+1)^{-3})/(4 r²)` for `r ≥ 1`.
- `liClockPairedEtaInfinitePartitionCorrectionP_even_nat`, `..._odd_nat`: `P(2m) = -π²/48`,
  `P(2m+1) = π²/24`.
- `liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_H`: `ρ(x) = e^{-|x|/2} H(e^{|x|})`.
- `liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_le`:
  `|ρ(x) - (log 2/2) e^{-|x|/2}| ≤ (π²/16) e^{-3|x|/2}`.
- `liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_not_isLittleO`: the error is not
  `o(e^{-3x/2})`.
- `liClockPairedEtaInfinitePartitionNormalizer_eq_tsum`: `Z = 2 ∑_n (1/√(2n+1) - 1/√(2n+2))`.
- `liClockPairedEtaInfinitePartitionNormalizer_gt_seventy_one_div_sixty`: `71/60 < Z`.
- `liClockPairedEtaInfinitePartitionDifferenceDensity_ratio_tendsto`: the normalized density
  divided by the half-line reference density tends to `2 log 2/Z²`.
- `liClockPairedEtaInfinitePartitionComparisonLimit_lt_one`: `0 < 2 log 2/Z² < 1`.

## Hypotheses

All results are unconditional. The analytic estimates assume only the stated ranges of the
real variables (`r > 0` or `r ≥ 1`, `0 < a ≤ b`, `x ≥ 0` where indicated).
-/

noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology
namespace RHTower

/-- The arithmetic indicator `α(w)`: `1` when `{w/2} > 1/2` or `{w/2} = 0`, i.e. on
`⋃_k (2k+1, 2k+2]`, and `0` otherwise. -/
def liClockPairedEtaInfinitePartitionArithmeticIndicator (w : ℝ) : ℝ :=
  if 1 / 2 < Int.fract (w / 2) ∨ Int.fract (w / 2) = 0 then 1 else 0

/-- The periodic sawtooth `B(s) = |{s/2} - 1/2| - 1/4`, a primitive of `α - 1/2`. -/
def liClockPairedEtaInfinitePartitionPrimitiveB (s : ℝ) : ℝ :=
  |Int.fract (s / 2) - 1 / 2| - 1 / 4

/-- The second primitive `D(s) = ∫_0^s B(u) du`. -/
def liClockPairedEtaInfinitePartitionPrimitiveD (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..s, liClockPairedEtaInfinitePartitionPrimitiveB u

private theorem indicator_mem_iff (w : ℝ) :
    (1 / 2 < Int.fract (w / 2) ∨ Int.fract (w / 2) = 0) ↔
      ∃ k : ℤ, 2 * (k : ℝ) + 1 < w ∧ w ≤ 2 * (k : ℝ) + 2 := by
  have hfloor := Int.floor_le (w / 2)
  have hlt := Int.lt_floor_add_one (w / 2)
  constructor
  · rintro (h | h)
    · refine ⟨⌊w / 2⌋, ?_, ?_⟩
      · simp only [Int.fract] at h
        linarith
      · linarith
    · refine ⟨⌊w / 2⌋ - 1, ?_, ?_⟩
      all_goals simp only [Int.fract, Int.cast_sub, Int.cast_one] at *; linarith
  · rintro ⟨k, hlo, hhi⟩
    rcases lt_or_eq_of_le hhi with hhi | hhi
    · have hk : ⌊w / 2⌋ = k := Int.floor_eq_on_Ico k _ ⟨by linarith, by linarith⟩
      left
      simp only [Int.fract, hk]
      linarith
    · right
      rw [hhi]
      have heq : (2 * (k : ℝ) + 2) / 2 = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [heq, Int.fract_intCast]

/-- `α` is the indicator of the union of intervals `⋃_{k ∈ ℤ} (2k+1, 2k+2]`. -/
theorem liClockPairedEtaInfinitePartitionArithmeticIndicator_eq_indicator (w : ℝ) :
    liClockPairedEtaInfinitePartitionArithmeticIndicator w =
      (⋃ k : ℤ, Ioc (2 * (k : ℝ) + 1) (2 * (k : ℝ) + 2)).indicator (fun _ => (1 : ℝ)) w := by
  classical
  simp only [liClockPairedEtaInfinitePartitionArithmeticIndicator, indicator,
    mem_iUnion, mem_Ioc, indicator_mem_iff]

theorem measurable_liClockPairedEtaInfinitePartitionArithmeticIndicator :
    Measurable liClockPairedEtaInfinitePartitionArithmeticIndicator := by
  have h : Measurable (fun w : ℝ => Int.fract (w / 2)) :=
    measurable_fract.comp (measurable_id.div_const 2)
  exact Measurable.ite ((measurableSet_lt measurable_const h).union (h (measurableSet_singleton 0)))
    measurable_const measurable_const

theorem liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg (w : ℝ) :
    0 ≤ liClockPairedEtaInfinitePartitionArithmeticIndicator w := by
  unfold liClockPairedEtaInfinitePartitionArithmeticIndicator
  split_ifs <;> norm_num

theorem liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (w : ℝ) :
    liClockPairedEtaInfinitePartitionArithmeticIndicator w ≤ 1 := by
  unfold liClockPairedEtaInfinitePartitionArithmeticIndicator
  split_ifs <;> norm_num

/-- The arithmetic indicator `α` is `2`-periodic. -/
theorem liClockPairedEtaInfinitePartitionArithmeticIndicator_periodic :
    Periodic liClockPairedEtaInfinitePartitionArithmeticIndicator 2 := by
  intro w
  unfold liClockPairedEtaInfinitePartitionArithmeticIndicator
  rw [show (w + 2) / 2 = w / 2 + 1 by ring, Int.fract_add_one]

theorem continuous_liClockPairedEtaInfinitePartitionPrimitiveB :
    Continuous liClockPairedEtaInfinitePartitionPrimitiveB := by
  have h : Continuous (fun u : ℝ => |u - 1 / 2| - 1 / 4) :=
    (continuous_id.sub continuous_const).abs.sub continuous_const
  have hp := h.continuousOn.comp_fract'' (by norm_num)
  exact hp.comp (continuous_id.div_const 2)

theorem liClockPairedEtaInfinitePartitionPrimitiveB_periodic :
    Periodic liClockPairedEtaInfinitePartitionPrimitiveB 2 := by
  intro w
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  rw [show (w + 2) / 2 = w / 2 + 1 by ring, Int.fract_add_one]

/-- The sawtooth is bounded: `|B(s)| ≤ 1/4`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveB_abs_le (s : ℝ) :
    |liClockPairedEtaInfinitePartitionPrimitiveB s| ≤ 1 / 4 := by
  have h0 := Int.fract_nonneg (s / 2)
  have h1 := (Int.fract_lt_one (s / 2)).le
  have ha : |Int.fract (s / 2) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  exact abs_le.mpr ⟨by linarith [abs_nonneg (Int.fract (s / 2) - 1 / 2)], by linarith⟩

theorem liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_zero_one {s : ℝ}
    (hs : s ∈ Icc 0 1) : liClockPairedEtaInfinitePartitionPrimitiveB s = 1 / 4 - s / 2 := by
  have hf : Int.fract (s / 2) = s / 2 := Int.fract_eq_self.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  rw [hf, abs_of_nonpos (by linarith [hs.2])]
  ring

theorem liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_one_two {s : ℝ}
    (hs : s ∈ Icc 1 2) : liClockPairedEtaInfinitePartitionPrimitiveB s = s / 2 - 3 / 4 := by
  rcases lt_or_eq_of_le hs.2 with h | rfl
  · have hf : Int.fract (s / 2) = s / 2 := Int.fract_eq_self.mpr ⟨by linarith [hs.1], by linarith⟩
    unfold liClockPairedEtaInfinitePartitionPrimitiveB
    rw [hf, abs_of_nonneg (by linarith [hs.1])]
    ring
  · norm_num [liClockPairedEtaInfinitePartitionPrimitiveB]

private theorem intervalIntegrable_B (a b : ℝ) :
    IntervalIntegrable liClockPairedEtaInfinitePartitionPrimitiveB volume a b :=
  continuous_liClockPairedEtaInfinitePartitionPrimitiveB.intervalIntegrable _ _

private theorem integral_B_zero_one :
    (∫ s in (0 : ℝ)..1, liClockPairedEtaInfinitePartitionPrimitiveB s) = 0 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, (1 / 4 - s / 2) :=
      intervalIntegral.integral_congr (fun s hs =>
        liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_zero_one (by simpa using hs))
    _ = 0 := by
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1 / 4) (g := fun s : ℝ => s / 2) (intervalIntegrable_const)
        ((continuous_id.div_const 2).intervalIntegrable 0 1),
        intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
      norm_num

private theorem integral_B_one_two :
    (∫ s in (1 : ℝ)..2, liClockPairedEtaInfinitePartitionPrimitiveB s) = 0 := by
  calc
    _ = ∫ s in (1 : ℝ)..2, (s / 2 - 3 / 4) :=
      intervalIntegral.integral_congr (fun s hs =>
        liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_one_two (by simpa using hs))
    _ = 0 := by
      rw [intervalIntegral.integral_sub (f := fun s : ℝ => s / 2) (g := fun _ : ℝ => 3 / 4) ((continuous_id.div_const 2).intervalIntegrable 1 2)
        intervalIntegrable_const, intervalIntegral.integral_div, integral_id,
        intervalIntegral.integral_const]
      norm_num

/-- The sawtooth `B` has mean zero over a period: `∫_0^2 B = 0`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveB_integral_period :
    (∫ s in (0 : ℝ)..2, liClockPairedEtaInfinitePartitionPrimitiveB s) = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_B 0 1) (intervalIntegrable_B 1 2),
    integral_B_zero_one, integral_B_one_two, add_zero]

theorem continuous_liClockPairedEtaInfinitePartitionPrimitiveD :
    Continuous liClockPairedEtaInfinitePartitionPrimitiveD :=
  intervalIntegral.continuous_primitive intervalIntegrable_B 0

theorem hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveD (s : ℝ) :
    HasDerivAt liClockPairedEtaInfinitePartitionPrimitiveD
      (liClockPairedEtaInfinitePartitionPrimitiveB s) s :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_B 0 s)
    continuous_liClockPairedEtaInfinitePartitionPrimitiveB.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_liClockPairedEtaInfinitePartitionPrimitiveB.continuousAt

/-- The second primitive `D` is `2`-periodic, since `B` has mean zero. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveD_periodic :
    Periodic liClockPairedEtaInfinitePartitionPrimitiveD 2 := by
  intro s
  unfold liClockPairedEtaInfinitePartitionPrimitiveD
  simpa only [zero_add, liClockPairedEtaInfinitePartitionPrimitiveB_integral_period, add_zero] using
    liClockPairedEtaInfinitePartitionPrimitiveB_periodic.intervalIntegral_add_eq_add 0 s intervalIntegrable_B


private theorem hasDerivAt_fract_off_integer {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    HasDerivAt (Int.fract : ℝ → ℝ) 1 x := by
  have hlo : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) hx.symm
  have heq : (Int.fract : ℝ → ℝ) =ᶠ[𝓝 x] (fun y => y - (⌊x⌋ : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hlo (Int.lt_floor_add_one x)] with y hy
    simp only [Int.fract, Int.floor_eq_on_Ico ⌊x⌋ y ⟨hy.1.le, hy.2⟩]
  simpa using ((hasDerivAt_id x).sub_const (⌊x⌋ : ℝ)).congr_of_eventuallyEq heq

private theorem fract_half_ne_zero {x : ℝ} (hx : x ∉ range (fun k : ℤ => (k : ℝ))) :
    Int.fract (x / 2) ≠ 0 := by
  intro h
  apply hx
  refine ⟨2 * ⌊x / 2⌋, ?_⟩
  simp only [Int.fract] at h
  push_cast
  linarith

private theorem fract_half_ne_half {x : ℝ} (hx : x ∉ range (fun k : ℤ => (k : ℝ))) :
    Int.fract (x / 2) ≠ 1 / 2 := by
  intro h
  apply hx
  refine ⟨2 * ⌊x / 2⌋ + 1, ?_⟩
  simp only [Int.fract] at h
  push_cast
  linarith

/-- Off the integers, `B` is differentiable with `B'(x) = α(x) - 1/2`. -/
theorem hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveB {x : ℝ}
    (hx : x ∉ range (fun k : ℤ => (k : ℝ))) :
    HasDerivAt liClockPairedEtaInfinitePartitionPrimitiveB
      (liClockPairedEtaInfinitePartitionArithmeticIndicator x - 1 / 2) x := by
  have h0 := fract_half_ne_zero hx
  have hh := fract_half_ne_half hx
  have hf : HasDerivAt (fun y : ℝ => Int.fract (y / 2)) (1 / 2) x := by
    have hx' : x / 2 ≠ (⌊x / 2⌋ : ℝ) := by
      intro he
      apply h0
      change x / 2 - (⌊x / 2⌋ : ℝ) = 0
      exact sub_eq_zero.mpr he
    convert! (hasDerivAt_fract_off_integer hx').comp x ((hasDerivAt_id x).div_const 2) using 1
    simp only [one_mul]
  rcases lt_or_gt_of_ne hh with h | h
  · have ha := (hasDerivAt_abs_neg (by linarith : Int.fract (x / 2) - 1 / 2 < 0)).comp x
      (hf.sub_const (1 / 2))
    have hi : liClockPairedEtaInfinitePartitionArithmeticIndicator x = 0 := by
      exact if_neg (not_or.mpr ⟨not_lt.mpr h.le, h0⟩)
    rw [hi]
    convert! ha.sub_const (1 / 4) using 1
    simp only [zero_sub, neg_one_mul]
  · have ha := (hasDerivAt_abs_pos (by linarith : 0 < Int.fract (x / 2) - 1 / 2)).comp x
      (hf.sub_const (1 / 2))
    have hi : liClockPairedEtaInfinitePartitionArithmeticIndicator x = 1 := by
      exact if_pos (Or.inl h)
    rw [hi]
    have hnum : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [hnum]
    convert! ha.sub_const (1 / 4) using 1
    simp only [one_mul]

theorem liClockPairedEtaInfinitePartitionPrimitiveD_eq_on_Icc_zero_one {s : ℝ}
    (hs : s ∈ Icc 0 1) : liClockPairedEtaInfinitePartitionPrimitiveD s = (s - s ^ 2) / 4 := by
  unfold liClockPairedEtaInfinitePartitionPrimitiveD
  calc
    _ = ∫ u in (0 : ℝ)..s, (1 / 4 - u / 2) :=
      intervalIntegral.integral_congr (fun u hu => by
        have hu' : u ∈ Icc (0 : ℝ) s := by simpa only [uIcc_of_le hs.1] using hu
        exact liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_zero_one ⟨hu'.1, hu'.2.trans hs.2⟩)
    _ = (s - s ^ 2) / 4 := by
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1 / 4) (g := fun u : ℝ => u / 2)
        intervalIntegrable_const ((continuous_id.div_const 2).intervalIntegrable 0 s),
        intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
      simp only [sub_zero, zero_pow (by omega : 2 ≠ 0), smul_eq_mul]
      ring

theorem liClockPairedEtaInfinitePartitionPrimitiveD_eq_on_Icc_one_two {s : ℝ}
    (hs : s ∈ Icc 1 2) : liClockPairedEtaInfinitePartitionPrimitiveD s = (s ^ 2 - 3 * s + 2) / 4 := by
  unfold liClockPairedEtaInfinitePartitionPrimitiveD
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_B 0 1) (intervalIntegrable_B 1 s),
    integral_B_zero_one, zero_add]
  calc
    _ = ∫ u in (1 : ℝ)..s, (u / 2 - 3 / 4) :=
      intervalIntegral.integral_congr (fun u hu => by
        have hu' : u ∈ Icc (1 : ℝ) s := by simpa only [uIcc_of_le hs.1] using hu
        exact liClockPairedEtaInfinitePartitionPrimitiveB_eq_on_Icc_one_two ⟨hu'.1, hu'.2.trans hs.2⟩)
    _ = (s ^ 2 - 3 * s + 2) / 4 := by
      rw [intervalIntegral.integral_sub (f := fun u : ℝ => u / 2) (g := fun _ : ℝ => 3 / 4)
        ((continuous_id.div_const 2).intervalIntegrable 1 s) intervalIntegrable_const,
        intervalIntegral.integral_div, integral_id, intervalIntegral.integral_const]
      simp only [smul_eq_mul, one_pow]
      ring

/-- The second primitive is bounded: `|D(s)| ≤ 1/16`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveD_abs_le (s : ℝ) :
    |liClockPairedEtaInfinitePartitionPrimitiveD s| ≤ 1 / 16 := by
  have hmem : liClockPairedEtaInfinitePartitionPrimitiveD s ∈
      liClockPairedEtaInfinitePartitionPrimitiveD '' uIcc (0 : ℝ) (0 + 2) := by
    rw [liClockPairedEtaInfinitePartitionPrimitiveD_periodic.image_uIcc (by norm_num : (2 : ℝ) ≠ 0)]
    exact mem_range_self s
  rcases hmem with ⟨u, hu, he⟩
  have hu' : u ∈ Icc (0 : ℝ) 2 := by simpa only [zero_add, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hu
  rw [← he]
  by_cases h : u ≤ 1
  · rw [liClockPairedEtaInfinitePartitionPrimitiveD_eq_on_Icc_zero_one ⟨hu'.1, h⟩]
    have hp := mul_nonneg hu'.1 (sub_nonneg.mpr h)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith [sq_nonneg (u - 1 / 2)]⟩
  · rw [liClockPairedEtaInfinitePartitionPrimitiveD_eq_on_Icc_one_two ⟨(not_le.mp h).le, hu'.2⟩]
    have hp := mul_nonneg (sub_nonneg.mpr (not_le.mp h).le) (sub_nonneg.mpr hu'.2)
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (u - 3 / 2)], by nlinarith⟩


local notation "αₑ" => liClockPairedEtaInfinitePartitionArithmeticIndicator
local notation "Bₑ" => liClockPairedEtaInfinitePartitionPrimitiveB
local notation "Dₑ" => liClockPairedEtaInfinitePartitionPrimitiveD

private theorem intervalIntegrable_indicator_mul (r a b : ℝ) :
    IntervalIntegrable (fun w : ℝ => αₑ (r * w)) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    ((measurable_liClockPairedEtaInfinitePartitionArithmeticIndicator.comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable) ?_
  exact Eventually.of_forall (fun w => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg _),
      norm_one] using liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (r * w))

private theorem reciprocal_continuousOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    ContinuousOn (fun w : ℝ => 1 / w ^ n) (uIcc a b) := by
  refine continuousOn_const.div (continuousOn_id.pow n) ?_
  intro w hw
  have hw' : w ∈ Icc a b := by simpa only [uIcc_of_le hab] using hw
  exact pow_ne_zero n (ne_of_gt (ha.trans_le hw'.1))

private theorem intervalIntegrable_indicator_weight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (r : ℝ) (n : ℕ) :
    IntervalIntegrable (fun w : ℝ => (αₑ (r * w) - 1 / 2) / w ^ n) volume a b := by
  simpa only [div_eq_mul_inv, one_mul] using
    ((intervalIntegrable_indicator_mul r a b).sub intervalIntegrable_const).mul_continuousOn
      (reciprocal_continuousOn ha hab n)

private theorem intervalIntegrable_B_weight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (r : ℝ) (n : ℕ) : IntervalIntegrable (fun w : ℝ => Bₑ (r * w) / w ^ n) volume a b := by
  simpa only [div_eq_mul_inv, one_mul, Function.comp_def, Pi.mul_apply, id_eq] using
    ((continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp
      (continuous_const.mul continuous_id)).intervalIntegrable a b).mul_continuousOn
      (reciprocal_continuousOn ha hab n)

private theorem intervalIntegrable_D_weight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (r : ℝ) (n : ℕ) : IntervalIntegrable (fun w : ℝ => Dₑ (r * w) / w ^ n) volume a b := by
  simpa only [div_eq_mul_inv, one_mul, Function.comp_def, Pi.mul_apply, id_eq] using
    ((continuous_liClockPairedEtaInfinitePartitionPrimitiveD.comp
      (continuous_const.mul continuous_id)).intervalIntegrable a b).mul_continuousOn
      (reciprocal_continuousOn ha hab n)

private theorem reciprocal_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    (∫ w in a..b, (1 : ℝ) / w ^ (n + 2)) =
      (1 / a ^ (n + 1) - 1 / b ^ (n + 1)) / (n + 1 : ℝ) := by
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    exact (not_le_of_gt ha) h.1
  have h := integral_zpow (a := a) (b := b) (n := -((n : ℤ) + 2))
    (Or.inr ⟨by omega, hzero⟩)
  have hn2 : -((n : ℤ) + 2) = -((n + 2 : ℕ) : ℤ) := by push_cast; rfl
  have hn1 : -((n : ℤ) + 2) + 1 = -((n + 1 : ℕ) : ℤ) := by push_cast; omega
  rw [hn1, hn2] at h
  simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at h
  have hcast : -(↑(n + 2) : ℝ) + 1 = -(↑(n + 1) : ℝ) := by push_cast; ring
  rw [hcast] at h
  calc
    _ = ((b ^ (n + 1))⁻¹ - (a ^ (n + 1))⁻¹) / (-((n + 1 : ℕ) : ℝ)) := by
      simpa only [one_div] using h
    _ = _ := by rw [div_neg]; simp only [Nat.cast_add, Nat.cast_one, one_div]; ring

/-- Integration by parts against `B`: for `r > 0`, `0 < a ≤ b`,
`∫_a^b (α(rw) - 1/2)/w² dw = B(rb)/(r b²) - B(ra)/(r a²) + (2/r) ∫_a^b B(rw)/w³ dw`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveB_interval_ibp {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in a..b, (αₑ (r * w) - 1 / 2) / w ^ 2) =
      Bₑ (r * b) / (r * b ^ 2) - Bₑ (r * a) / (r * a ^ 2) +
        (2 / r) * ∫ w in a..b, Bₑ (r * w) / w ^ 3 := by
  let F : ℝ → ℝ := fun w => Bₑ (r * w) / (r * w ^ 2)
  let F' : ℝ → ℝ := fun w => (αₑ (r * w) - 1 / 2) / w ^ 2 - (2 / r) * (Bₑ (r * w) / w ^ 3)
  have hc : ContinuousOn F (Icc a b) := by
    refine (continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp
      (continuous_const.mul continuous_id)).continuousOn.div
        (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
    intro w hw
    exact mul_ne_zero hr.ne' (pow_ne_zero 2 (ne_of_gt (ha.trans_le hw.1)))
  have hd : ∀ w ∈ Ioo a b \ range (fun k : ℤ => (k : ℝ) / r), HasDerivAt F (F' w) w := by
    intro w hw
    have hw0 : w ≠ 0 := ne_of_gt (ha.trans hw.1.1)
    have hwr : r * w ∉ range (fun k : ℤ => (k : ℝ)) := by
      rintro ⟨k, hk⟩
      apply hw.2
      refine ⟨k, ?_⟩
      dsimp only at hk ⊢
      rw [hk]
      field_simp [hr.ne']
    have hb := (hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveB hwr).comp w
      ((hasDerivAt_id w).const_mul r)
    have hq := (hb.div_const r).div ((hasDerivAt_id w).pow 2) (pow_ne_zero 2 hw0)
    convert! hq using 1
    · funext u
      dsimp [F]
      rw [div_div]
    · dsimp [F']
      field_simp [hr.ne', hw0]
  have hi : IntervalIntegrable F' volume a b :=
    (intervalIntegrable_indicator_weight ha hab r 2).sub
      ((intervalIntegrable_B_weight ha hab r 3).const_mul (2 / r))
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F' hab
    (countable_range (fun k : ℤ => (k : ℝ) / r)) hc hd hi
  unfold F' at h
  rw [intervalIntegral.integral_sub (intervalIntegrable_indicator_weight ha hab r 2)
    ((intervalIntegrable_B_weight ha hab r 3).const_mul (2 / r)),
    intervalIntegral.integral_const_mul] at h
  dsimp [F] at h
  linarith

/-- Integration by parts against `D`: for `r > 0`, `0 < a ≤ b`,
`∫_a^b B(rw)/w³ dw = D(rb)/(r b³) - D(ra)/(r a³) + (3/r) ∫_a^b D(rw)/w⁴ dw`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveD_interval_ibp {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in a..b, Bₑ (r * w) / w ^ 3) =
      Dₑ (r * b) / (r * b ^ 3) - Dₑ (r * a) / (r * a ^ 3) +
        (3 / r) * ∫ w in a..b, Dₑ (r * w) / w ^ 4 := by
  let F : ℝ → ℝ := fun w => Dₑ (r * w) / (r * w ^ 3)
  let F' : ℝ → ℝ := fun w => Bₑ (r * w) / w ^ 3 - (3 / r) * (Dₑ (r * w) / w ^ 4)
  have hc : ContinuousOn F (Icc a b) := by
    refine (continuous_liClockPairedEtaInfinitePartitionPrimitiveD.comp
      (continuous_const.mul continuous_id)).continuousOn.div
        (continuousOn_const.mul (continuousOn_id.pow 3)) ?_
    intro w hw
    exact mul_ne_zero hr.ne' (pow_ne_zero 3 (ne_of_gt (ha.trans_le hw.1)))
  have hd : ∀ w ∈ Ioo a b \ (∅ : Set ℝ), HasDerivAt F (F' w) w := by
    intro w hw
    have hw0 : w ≠ 0 := ne_of_gt (ha.trans hw.1.1)
    have hb := (hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveD (r * w)).comp w
      ((hasDerivAt_id w).const_mul r)
    have hq := (hb.div_const r).div ((hasDerivAt_id w).pow 3) (pow_ne_zero 3 hw0)
    convert! hq using 1
    · funext u
      dsimp [F]
      rw [div_div]
    · dsimp [F']
      field_simp [hr.ne', hw0]
  have hi : IntervalIntegrable F' volume a b :=
    (intervalIntegrable_B_weight ha hab r 3).sub
      ((intervalIntegrable_D_weight ha hab r 4).const_mul (3 / r))
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F' hab
    countable_empty hc hd hi
  unfold F' at h
  rw [intervalIntegral.integral_sub (intervalIntegrable_B_weight ha hab r 3)
    ((intervalIntegrable_D_weight ha hab r 4).const_mul (3 / r)),
    intervalIntegral.integral_const_mul] at h
  dsimp [F] at h
  linarith


private theorem abs_sub_bound (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)

private theorem weighted_integral_norm_le {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ∀ w, |f w| ≤ C) (n : ℕ) :
    |∫ w in a..b, f w / w ^ (n + 2)| ≤
      C * ((1 / a ^ (n + 1) - 1 / b ^ (n + 1)) / (n + 1 : ℝ)) := by
  have hmajor := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun w => f w / w ^ (n + 2)) hab
    (g := fun w => C * (1 / w ^ (n + 2)))
  have hcont := (reciprocal_continuousOn ha hab (n + 2)).const_mul C
  have hb := hmajor (Eventually.of_forall (fun w hw => by
    have hw0 : 0 < w := ha.trans hw.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hw0 _)]
    simpa only [mul_one_div] using (div_le_div_of_nonneg_right (hf w) (pow_pos hw0 _).le)))
    hcont.intervalIntegrable
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, reciprocal_integral ha hab n] at hb
  exact hb

private theorem B_endpoint_norm_le {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    |Bₑ (r * w) / (r * w ^ 2)| ≤ (1 / 4) / (r * w ^ 2) := by
  rw [abs_div, abs_of_pos (mul_pos hr (pow_pos hw _))]
  exact div_le_div_of_nonneg_right (liClockPairedEtaInfinitePartitionPrimitiveB_abs_le _)
    (mul_pos hr (pow_pos hw _)).le

private theorem D_endpoint_norm_le {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    |Dₑ (r * w) / (r * w ^ 3)| ≤ (1 / 16) / (r * w ^ 3) := by
  rw [abs_div, abs_of_pos (mul_pos hr (pow_pos hw _))]
  exact div_le_div_of_nonneg_right (liClockPairedEtaInfinitePartitionPrimitiveD_abs_le _)
    (mul_pos hr (pow_pos hw _)).le

/-- For `r > 0`, `0 < a ≤ b`: `|∫_a^b (α(rw) - 1/2)/w² dw| ≤ 1/(2 r a²)`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveB_interval_error_le {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    |∫ w in a..b, (αₑ (r * w) - 1 / 2) / w ^ 2| ≤ 1 / (2 * r * a ^ 2) := by
  have hb : 0 < b := ha.trans_le hab
  have hint := weighted_integral_norm_le ha hab (fun w => Bₑ (r * w))
    (fun w => liClockPairedEtaInfinitePartitionPrimitiveB_abs_le (r * w)) 1
  rw [liClockPairedEtaInfinitePartitionPrimitiveB_interval_ibp hr ha hab]
  calc
    _ ≤ |Bₑ (r * b) / (r * b ^ 2)| + |Bₑ (r * a) / (r * a ^ 2)| +
        (2 / r) * |∫ w in a..b, Bₑ (r * w) / w ^ 3| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub_bound _ _)
        (by rw [abs_mul, abs_of_pos (div_pos (by norm_num) hr)]))
    _ ≤ (1 / 4) / (r * b ^ 2) + (1 / 4) / (r * a ^ 2) +
        (2 / r) * ((1 / 4) * ((1 / a ^ 2 - 1 / b ^ 2) / 2)) := by
      gcongr
      · exact B_endpoint_norm_le hr hb
      · exact B_endpoint_norm_le hr ha
      · norm_num at hint ⊢; exact hint
    _ = _ := by field_simp; ring

/-- For `r > 0`, `0 < a ≤ b`: `|∫_a^b B(rw)/w³ dw| ≤ 1/(8 r a³)`. -/
theorem liClockPairedEtaInfinitePartitionPrimitiveD_interval_error_le {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    |∫ w in a..b, Bₑ (r * w) / w ^ 3| ≤ 1 / (8 * r * a ^ 3) := by
  have hb : 0 < b := ha.trans_le hab
  have hint := weighted_integral_norm_le ha hab (fun w => Dₑ (r * w))
    (fun w => liClockPairedEtaInfinitePartitionPrimitiveD_abs_le (r * w)) 2
  rw [liClockPairedEtaInfinitePartitionPrimitiveD_interval_ibp hr ha hab]
  calc
    _ ≤ |Dₑ (r * b) / (r * b ^ 3)| + |Dₑ (r * a) / (r * a ^ 3)| +
        (3 / r) * |∫ w in a..b, Dₑ (r * w) / w ^ 4| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub_bound _ _)
        (by rw [abs_mul, abs_of_pos (div_pos (by norm_num) hr)]))
    _ ≤ (1 / 16) / (r * b ^ 3) + (1 / 16) / (r * a ^ 3) +
        (3 / r) * ((1 / 16) * ((1 / a ^ 3 - 1 / b ^ 3) / 3)) := by
      gcongr
      · exact D_endpoint_norm_le hr hb
      · exact D_endpoint_norm_le hr ha
      · norm_num at hint ⊢; exact hint
    _ = _ := by field_simp; ring

private theorem summable_reciprocal_odd_square :
    Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2) := by
  convert! hasSum_zeta_two.summable.comp_injective
    (show Injective (fun n : ℕ => 2 * n + 1) by intro n m h; dsimp only at h; omega) using 1
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

private theorem summable_reciprocal_even_square :
    Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 2) ^ 2) := by
  convert! hasSum_zeta_two.summable.comp_injective
    (show Injective (fun n : ℕ => 2 * n + 2) by intro n m h; dsimp only at h; omega) using 1
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- `∑_{n ≥ 0} 1/(2n+1)² = π²/8`. -/
theorem liClockPairedEtaInfinitePartition_odd_square_mass :
    (∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 8 := by
  have he : Summable (fun n : ℕ => 1 / (2 * (n : ℝ)) ^ 2) := by
    convert! hasSum_zeta_two.summable.comp_injective
      (show Injective (fun n : ℕ => 2 * n) by intro n m h; dsimp only at h; omega) using 1
    simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat]
  have heq : (∑' n : ℕ, 1 / (2 * (n : ℝ)) ^ 2) = Real.pi ^ 2 / 24 := by
    calc
      _ = ∑' n : ℕ, (1 / 4 : ℝ) * (1 / (n : ℝ) ^ 2) := by
        apply tsum_congr
        intro n
        rw [mul_pow, div_mul_eq_div_div]
        norm_num
        rfl
      _ = (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
        rw [hasSum_zeta_two.summable.tsum_mul_left, hasSum_zeta_two.tsum_eq]
      _ = _ := by ring
  have h := tsum_even_add_odd
    (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using he)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_reciprocal_odd_square)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  rw [heq, hasSum_zeta_two.tsum_eq] at h
  linarith

/-- `∑_{n ≥ 0} 1/(2n+2)² = π²/24`. -/
theorem liClockPairedEtaInfinitePartition_even_square_mass :
    (∑' n : ℕ, 1 / (2 * (n : ℝ) + 2) ^ 2) = Real.pi ^ 2 / 24 := by
  have he : Summable (fun n : ℕ => 1 / (2 * (n : ℝ)) ^ 2) := by
    convert! hasSum_zeta_two.summable.comp_injective
      (show Injective (fun n : ℕ => 2 * n) by intro n m h; dsimp only at h; omega) using 1
    simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat]
  have h := tsum_even_add_odd
    (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using he)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using summable_reciprocal_odd_square)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  rw [liClockPairedEtaInfinitePartition_odd_square_mass, hasSum_zeta_two.tsum_eq] at h
  have hs := he.tsum_eq_zero_add
  simp only [Nat.cast_zero, mul_zero, zero_pow (by omega : 2 ≠ 0), div_zero, zero_add,
    Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hs
  rw [← hs]
  linarith

/-- The odd cube mass `∑_{n ≥ 0} 1/(2n+1)³`. -/
def liClockPairedEtaInfinitePartitionOddCubeMass : ℝ :=
  ∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ 3

theorem summable_liClockPairedEtaInfinitePartitionOddCubeMass :
    Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 3) := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < (3 : ℕ)))
  convert! hs.comp_injective
    (show Injective (fun n : ℕ => 2 * n + 1) by intro n m h; dsimp only at h; omega) using 1
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]


private def arithmeticSupport : Set ℝ :=
  ⋃ n : ℕ, Ioc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2)

private theorem measurableSet_arithmeticSupport : MeasurableSet arithmeticSupport :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioc)

private theorem arithmeticSupport_subset_Ioi_one : arithmeticSupport ⊆ Ioi (1 : ℝ) := by
  intro w hw
  obtain ⟨n, hn⟩ := mem_iUnion.mp hw
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact show 1 < w by linarith [hn.1]

private theorem indicator_nat_mem_iff {w : ℝ} (hw : 1 ≤ w) :
    (1 / 2 < Int.fract (w / 2) ∨ Int.fract (w / 2) = 0) ↔ w ∈ arithmeticSupport := by
  rw [indicator_mem_iff]
  constructor
  · rintro ⟨k, hklo, hkhi⟩
    have hk : 0 ≤ k := by
      by_contra h
      have hk' : k ≤ -1 := by omega
      have hreal : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
      linarith
    have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    exact mem_iUnion.mpr ⟨k.toNat, by simpa only [hcast, mem_Ioc] using And.intro hklo hkhi⟩
  · intro hw'
    obtain ⟨n, hn⟩ := mem_iUnion.mp hw'
    exact ⟨(n : ℤ), by simpa only [Int.cast_natCast, mem_Ioc] using hn⟩

private theorem indicator_nat_eq {w : ℝ} (hw : 1 ≤ w) :
    αₑ w = arithmeticSupport.indicator (fun _ => (1 : ℝ)) w := by
  classical
  simp only [liClockPairedEtaInfinitePartitionArithmeticIndicator, indicator,
    indicator_nat_mem_iff hw]

private theorem arithmeticSupport_measure_eq :
    volume.restrict arithmeticSupport = Measure.sum (fun n : ℕ =>
      volume.restrict (Ioc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2))) := by
  apply Measure.restrict_iUnion _ (fun _ => measurableSet_Ioc)
  intro n m hnm
  apply disjoint_left.mpr
  intro w hwn hwm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast (show n + 1 ≤ m by omega)
    linarith [hwn.2, hwm.1]
  · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
    linarith [hwm.2, hwn.1]

private theorem integrableOn_reciprocal_Ioi (n : ℕ) :
    IntegrableOn (fun w : ℝ => 1 / w ^ (n + 2)) (Ioi (1 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -((n + 2 : ℕ) : ℝ))
    (by push_cast; linarith [(show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]) (by norm_num : (0 : ℝ) < 1)
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div] using h

private theorem integrableOn_bounded_weight (f : ℝ → ℝ) (hm : Measurable f)
    {C : ℝ} (hf : ∀ w, |f w| ≤ C) (n : ℕ) :
    IntegrableOn (fun w : ℝ => f w / w ^ (n + 2)) (Ioi (1 : ℝ)) := by
  refine ((integrableOn_reciprocal_Ioi n).const_mul C).mono'
    ((hm.div (measurable_id.pow_const (n + 2))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw0 : 0 < w := lt_trans (by norm_num) hw
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hw0 _)]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (hf w) (pow_pos hw0 _).le

private theorem integral_alpha_eq_tsum (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (1 : ℝ))) :
    (∫ w in Ioi (1 : ℝ), αₑ w * f w) =
      ∑' n : ℕ, ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), f w := by
  have hi : IntegrableOn f arithmeticSupport := hf.mono_set arithmeticSupport_subset_Ioi_one
  have heq : (Ioi (1 : ℝ)).indicator (fun w => αₑ w * f w) = arithmeticSupport.indicator f := by
    funext w
    by_cases hw : 1 < w
    · rw [indicator_of_mem (show w ∈ Ioi (1 : ℝ) from hw), indicator_nat_eq hw.le]
      by_cases ha : w ∈ arithmeticSupport <;> simp only [indicator_of_mem, indicator_of_notMem, ha, not_false_eq_true, one_mul, zero_mul]
    · have ha : w ∉ arithmeticSupport := fun h => hw (arithmeticSupport_subset_Ioi_one h)
      simp only [indicator_of_notMem (show w ∉ Ioi (1 : ℝ) from hw), indicator_of_notMem ha]
  rw [← integral_indicator measurableSet_Ioi, heq, integral_indicator measurableSet_arithmeticSupport]
  change Integrable f (volume.restrict arithmeticSupport) at hi
  rw [arithmeticSupport_measure_eq] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)).symm

private theorem summable_arithmetic_intervals (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (1 : ℝ))) :
    Summable (fun n : ℕ => ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), f w) := by
  have hi : IntegrableOn f arithmeticSupport := hf.mono_set arithmeticSupport_subset_Ioi_one
  change Integrable f (volume.restrict arithmeticSupport) at hi
  rw [arithmeticSupport_measure_eq] at hi
  exact (hasSum_integral_measure hi).summable.congr
    (fun n => (intervalIntegral.integral_of_le (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)).symm)

/-- The averaging function `H(r) = ∫_1^∞ α(w) α(rw)/w² dw`. -/
def liClockPairedEtaInfinitePartitionAveragingH (r : ℝ) : ℝ :=
  ∫ w in Ioi (1 : ℝ), αₑ w * (αₑ (r * w) / w ^ 2)

private theorem integrableOn_indicator_weight_Ioi (r : ℝ) :
    IntegrableOn (fun w : ℝ => αₑ (r * w) / w ^ 2) (Ioi (1 : ℝ)) := by
  exact integrableOn_bounded_weight (fun w => αₑ (r * w))
    (measurable_liClockPairedEtaInfinitePartitionArithmeticIndicator.comp
      (measurable_const.mul measurable_id))
    (fun w => by simpa only [abs_of_nonneg (liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg _)] using
      liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (r * w)) 0

/-- `H(r) = ∑_n ∫_{2n+1}^{2n+2} α(rw)/w² dw`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_eq_tsum (r : ℝ) :
    liClockPairedEtaInfinitePartitionAveragingH r =
      ∑' n : ℕ, ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), αₑ (r * w) / w ^ 2 := by
  exact integral_alpha_eq_tsum _ (integrableOn_indicator_weight_Ioi r)

/-- `∫_1^∞ α(w)/w² dw = ∑_n (1/(2n+1) - 1/(2n+2)) = log 2`. -/
theorem liClockPairedEtaInfinitePartition_retained_inverse_mass :
    (∫ w in Ioi (1 : ℝ), αₑ w / w ^ 2) = Real.log 2 := by
  have h := integral_alpha_eq_tsum (fun w : ℝ => 1 / w ^ 2) (integrableOn_reciprocal_Ioi 0)
  simp only [mul_one_div] at h
  rw [h]
  have hs : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 2)) (Real.log 2) :=
    GaloisForLFunctions.HTGeometry.hasSum_alternatingHarmonicPair.congr_fun (fun _ => rfl)
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  have ha : 0 < 2 * (n : ℝ) + 1 := by positivity
  have he := reciprocal_integral ha (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2) 0
  simpa only [zero_add, Nat.cast_zero, add_zero, pow_one, div_one] using he


private theorem B_even_nat (m : ℕ) : Bₑ (2 * (m : ℝ)) = 1 / 4 := by
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  rw [show 2 * (m : ℝ) / 2 = (m : ℝ) by ring, Int.fract_natCast]
  norm_num

private theorem B_odd_nat (m : ℕ) : Bₑ (2 * (m : ℝ) + 1) = -1 / 4 := by
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  rw [show (2 * (m : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 by ring, Int.fract_natCast_add,
    Int.fract_eq_self.mpr (by norm_num : 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1)]
  norm_num

private theorem B_shift_two_nat (r : ℝ) (m : ℕ) :
    Bₑ ((r + 2) * (m : ℝ)) = Bₑ (r * (m : ℝ)) := by
  unfold liClockPairedEtaInfinitePartitionPrimitiveB
  rw [show (r + 2) * (m : ℝ) / 2 = r * (m : ℝ) / 2 + (m : ℝ) by ring,
    Int.fract_add_natCast]

private def correctionTerm (n : ℕ) (r : ℝ) : ℝ :=
  Bₑ (r * (2 * (n : ℝ) + 2)) / (2 * (n : ℝ) + 2) ^ 2 -
    Bₑ (r * (2 * (n : ℝ) + 1)) / (2 * (n : ℝ) + 1) ^ 2

private def correctionMajorant (n : ℕ) : ℝ :=
  (1 / 4) * (1 / (2 * (n : ℝ) + 2) ^ 2 + 1 / (2 * (n : ℝ) + 1) ^ 2)

private theorem summable_correctionMajorant : Summable correctionMajorant :=
  (summable_reciprocal_even_square.add summable_reciprocal_odd_square).mul_left (1 / 4)

private theorem correctionTerm_norm_le (n : ℕ) (r : ℝ) :
    ‖correctionTerm n r‖ ≤ correctionMajorant n := by
  have ha : 0 < (2 * (n : ℝ) + 1) ^ 2 := by positivity
  have hb : 0 < (2 * (n : ℝ) + 2) ^ 2 := by positivity
  rw [Real.norm_eq_abs]
  unfold correctionTerm correctionMajorant
  calc
    _ ≤ |Bₑ (r * (2 * (n : ℝ) + 2)) / (2 * (n : ℝ) + 2) ^ 2| +
        |Bₑ (r * (2 * (n : ℝ) + 1)) / (2 * (n : ℝ) + 1) ^ 2| := abs_sub_bound _ _
    _ ≤ (1 / 4) / (2 * (n : ℝ) + 2) ^ 2 + (1 / 4) / (2 * (n : ℝ) + 1) ^ 2 := by
      rw [abs_div, abs_div, abs_of_pos ha, abs_of_pos hb]
      exact add_le_add
        (div_le_div_of_nonneg_right (liClockPairedEtaInfinitePartitionPrimitiveB_abs_le _) hb.le)
        (div_le_div_of_nonneg_right (liClockPairedEtaInfinitePartitionPrimitiveB_abs_le _) ha.le)
    _ = _ := by ring

/-- The correction `P(r) = ∑_n (B(r(2n+2))/(2n+2)² - B(r(2n+1))/(2n+1)²)`. -/
def liClockPairedEtaInfinitePartitionCorrectionP (r : ℝ) : ℝ :=
  ∑' n : ℕ, correctionTerm n r

theorem summable_liClockPairedEtaInfinitePartitionCorrectionP (r : ℝ) :
    Summable (fun n : ℕ => correctionTerm n r) :=
  summable_correctionMajorant.of_norm_bounded (fun n => correctionTerm_norm_le n r)

theorem summable_norm_liClockPairedEtaInfinitePartitionCorrectionP (r : ℝ) :
    Summable (fun n : ℕ => ‖correctionTerm n r‖) :=
  (summable_liClockPairedEtaInfinitePartitionCorrectionP r).norm

/-- The series defining `P` converges uniformly on `ℝ`. -/
theorem hasSumUniformlyOn_liClockPairedEtaInfinitePartitionCorrectionP :
    HasSumUniformlyOn correctionTerm liClockPairedEtaInfinitePartitionCorrectionP univ := by
  exact HasSumUniformlyOn.of_norm_le_summable summable_correctionMajorant
    (fun n r _ => correctionTerm_norm_le n r)

theorem continuous_liClockPairedEtaInfinitePartitionCorrectionP :
    Continuous liClockPairedEtaInfinitePartitionCorrectionP := by
  refine continuous_tsum (fun n => ?_) summable_correctionMajorant correctionTerm_norm_le
  exact ((continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp
    (continuous_id.mul continuous_const)).div_const _).sub
    ((continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp
      (continuous_id.mul continuous_const)).div_const _)

/-- The correction `P` is `2`-periodic. -/
theorem liClockPairedEtaInfinitePartitionCorrectionP_periodic :
    Periodic liClockPairedEtaInfinitePartitionCorrectionP 2 := by
  intro r
  unfold liClockPairedEtaInfinitePartitionCorrectionP
  apply tsum_congr
  intro n
  unfold correctionTerm
  have ha : 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; rfl
  have hb : 2 * (n : ℝ) + 2 = ((2 * n + 2 : ℕ) : ℝ) := by push_cast; rfl
  rw [ha, hb, B_shift_two_nat, B_shift_two_nat]

/-- At even natural numbers the correction is `P(2m) = -π²/48`. -/
theorem liClockPairedEtaInfinitePartitionCorrectionP_even_nat (m : ℕ) :
    liClockPairedEtaInfinitePartitionCorrectionP (2 * (m : ℝ)) = -Real.pi ^ 2 / 48 := by
  calc
    _ = ∑' n : ℕ, (1 / 4 : ℝ) * (1 / (2 * (n : ℝ) + 2) ^ 2 - 1 / (2 * (n : ℝ) + 1) ^ 2) := by
      apply tsum_congr
      intro n
      have ha : 2 * (m : ℝ) * (2 * (n : ℝ) + 1) = 2 * ((m * (2 * n + 1) : ℕ) : ℝ) := by push_cast; ring
      have hb : 2 * (m : ℝ) * (2 * (n : ℝ) + 2) = 2 * ((m * (2 * n + 2) : ℕ) : ℝ) := by push_cast; ring
      unfold correctionTerm
      rw [ha, hb, B_even_nat, B_even_nat]
      ring
    _ = (1 / 4 : ℝ) * ((Real.pi ^ 2 / 24) - (Real.pi ^ 2 / 8)) := by
      rw [(summable_reciprocal_even_square.sub summable_reciprocal_odd_square).tsum_mul_left,
        summable_reciprocal_even_square.tsum_sub summable_reciprocal_odd_square,
        liClockPairedEtaInfinitePartition_even_square_mass, liClockPairedEtaInfinitePartition_odd_square_mass]
    _ = _ := by ring

/-- At odd natural numbers the correction is `P(2m+1) = π²/24`. -/
theorem liClockPairedEtaInfinitePartitionCorrectionP_odd_nat (m : ℕ) :
    liClockPairedEtaInfinitePartitionCorrectionP (2 * (m : ℝ) + 1) = Real.pi ^ 2 / 24 := by
  calc
    _ = ∑' n : ℕ, (1 / 4 : ℝ) * (1 / (2 * (n : ℝ) + 2) ^ 2 + 1 / (2 * (n : ℝ) + 1) ^ 2) := by
      apply tsum_congr
      intro n
      have ha : (2 * (m : ℝ) + 1) * (2 * (n : ℝ) + 1) = 2 * ((2 * m * n + m + n : ℕ) : ℝ) + 1 := by push_cast; ring
      have hb : (2 * (m : ℝ) + 1) * (2 * (n : ℝ) + 2) = 2 * (((2 * m + 1) * (n + 1) : ℕ) : ℝ) := by push_cast; ring
      unfold correctionTerm
      rw [ha, hb, B_even_nat, B_odd_nat]
      ring
    _ = (1 / 4 : ℝ) * ((Real.pi ^ 2 / 24) + (Real.pi ^ 2 / 8)) := by
      rw [(summable_reciprocal_even_square.add summable_reciprocal_odd_square).tsum_mul_left,
        summable_reciprocal_even_square.tsum_add summable_reciprocal_odd_square,
        liClockPairedEtaInfinitePartition_even_square_mass, liClockPairedEtaInfinitePartition_odd_square_mass]
    _ = _ := by ring


private theorem intervalIntegrable_indicator_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (r : ℝ) (n : ℕ) : IntervalIntegrable (fun w : ℝ => αₑ (r * w) / w ^ n) volume a b := by
  simpa only [div_eq_mul_inv, one_mul] using
    (intervalIntegrable_indicator_mul r a b).mul_continuousOn (reciprocal_continuousOn ha hab n)

private theorem abs_tsum_le_bound (f g : ℕ → ℝ) (hg : Summable g)
    (hle : ∀ n, |f n| ≤ g n) : |∑' n, f n| ≤ ∑' n, g n := by
  have hf : Summable f := hg.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using hle n)
  have hn : |∑' n, f n| ≤ ∑' n, ‖f n‖ := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
  exact hn.trans (hf.norm.tsum_le_tsum (fun n => by simpa only [Real.norm_eq_abs] using hle n) hg)

private def deviationTerm (n : ℕ) (r : ℝ) : ℝ :=
  ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), (αₑ (r * w) - 1 / 2) / w ^ 2

private def BIntervalTerm (n : ℕ) (r : ℝ) : ℝ :=
  ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), Bₑ (r * w) / w ^ 3

private theorem summable_deviationTerm (r : ℝ) : Summable (fun n => deviationTerm n r) := by
  have hm : Measurable (fun w : ℝ => αₑ (r * w) - 1 / 2) :=
    (measurable_liClockPairedEtaInfinitePartitionArithmeticIndicator.comp
      (measurable_const.mul measurable_id)).sub measurable_const
  have hb : ∀ w : ℝ, |αₑ (r * w) - 1 / 2| ≤ 1 / 2 := fun w => abs_le.mpr
    ⟨by linarith [liClockPairedEtaInfinitePartitionArithmeticIndicator_nonneg (r * w)],
      by linarith [liClockPairedEtaInfinitePartitionArithmeticIndicator_le_one (r * w)]⟩
  exact summable_arithmetic_intervals _ (integrableOn_bounded_weight _ hm hb 0)

private theorem summable_BIntervalTerm (r : ℝ) : Summable (fun n => BIntervalTerm n r) :=
  summable_arithmetic_intervals _ (integrableOn_bounded_weight _
    (continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp (continuous_const.mul continuous_id)).measurable
    (fun w => liClockPairedEtaInfinitePartitionPrimitiveB_abs_le (r * w)) 1)

private theorem retained_interval_mass_hasSum :
    HasSum (fun n : ℕ => ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), (1 : ℝ) / w ^ 2)
      (Real.log 2) := by
  refine GaloisForLFunctions.HTGeometry.hasSum_alternatingHarmonicPair.congr_fun ?_
  intro n
  have he := reciprocal_integral (by positivity : 0 < 2 * (n : ℝ) + 1)
    (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2) 0
  have he' : (∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), (1 : ℝ) / w ^ 2) =
      1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 2) := by
    simpa only [zero_add, Nat.cast_zero, add_zero, pow_one, div_one] using he
  exact he'

private theorem deviation_tsum_eq (r : ℝ) :
    (∑' n, deviationTerm n r) = liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 := by
  have hs := summable_arithmetic_intervals _ (integrableOn_indicator_weight_Ioi r)
  calc
    _ = ∑' n : ℕ, ((∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), αₑ (r * w) / w ^ 2) -
        (1 / 2) * ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), (1 : ℝ) / w ^ 2) := by
      apply tsum_congr
      intro n
      have ha : 0 < 2 * (n : ℝ) + 1 := by positivity
      have hab : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2 := by linarith
      have he : (fun w : ℝ => (αₑ (r * w) - 1 / 2) / w ^ 2) =
          fun w => αₑ (r * w) / w ^ 2 - (1 / 2) * (1 / w ^ 2) := by funext w; ring
      unfold deviationTerm
      rw [he, intervalIntegral.integral_sub (intervalIntegrable_indicator_div ha hab r 2)
        ((reciprocal_continuousOn ha hab 2).const_mul (1 / 2)).intervalIntegrable,
        intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [hs.tsum_sub (retained_interval_mass_hasSum.summable.mul_left (1 / 2)),
        retained_interval_mass_hasSum.summable.tsum_mul_left, retained_interval_mass_hasSum.tsum_eq,
        ← liClockPairedEtaInfinitePartitionAveragingH_eq_tsum]
      ring

/-- First-order tail: for `r ≥ 1`, `|H(r) - (log 2)/2| ≤ π²/(16 r)`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_error_le {r : ℝ} (hr : 1 ≤ r) :
    |liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2| ≤ Real.pi ^ 2 / (16 * r) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  rw [← deviation_tsum_eq]
  have h := abs_tsum_le_bound (fun n => deviationTerm n r)
    (fun n => (1 / (2 * r)) * (1 / (2 * (n : ℝ) + 1) ^ 2))
    (summable_reciprocal_odd_square.mul_left (1 / (2 * r))) (fun n => by
      have hn := liClockPairedEtaInfinitePartitionPrimitiveB_interval_error_le hr0
        (by positivity : 0 < 2 * (n : ℝ) + 1) (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)
      calc
        |deviationTerm n r| ≤ 1 / (2 * r * (2 * (n : ℝ) + 1) ^ 2) := hn
        _ = _ := by rw [div_mul_eq_div_div]; ring)
  rw [summable_reciprocal_odd_square.tsum_mul_left,
    liClockPairedEtaInfinitePartition_odd_square_mass] at h
  convert h using 1
  field_simp
  ring

/-- For `r > 0`, `H(r) - (log 2)/2 = P(r)/r + (2/r) ∑_n ∫_{2n+1}^{2n+2} B(rw)/w³ dw`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_eq_correction {r : ℝ} (hr : 0 < r) :
    liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 =
      liClockPairedEtaInfinitePartitionCorrectionP r / r + (2 / r) * ∑' n, BIntervalTerm n r := by
  rw [← deviation_tsum_eq]
  calc
    _ = ∑' n : ℕ, ((1 / r) * correctionTerm n r + (2 / r) * BIntervalTerm n r) := by
      apply tsum_congr
      intro n
      unfold deviationTerm BIntervalTerm
      rw [liClockPairedEtaInfinitePartitionPrimitiveB_interval_ibp hr
        (by positivity : 0 < 2 * (n : ℝ) + 1) (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)]
      simp only [correctionTerm, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by
      rw [((summable_liClockPairedEtaInfinitePartitionCorrectionP r).mul_left (1 / r)).tsum_add
        ((summable_BIntervalTerm r).mul_left (2 / r)),
        (summable_liClockPairedEtaInfinitePartitionCorrectionP r).tsum_mul_left,
        (summable_BIntervalTerm r).tsum_mul_left]
      simp only [liClockPairedEtaInfinitePartitionCorrectionP, one_div_mul_eq_div]

/-- Second-order tail: for `r ≥ 1`,
`|H(r) - (log 2)/2 - P(r)/r| ≤ (∑_n 1/(2n+1)³)/(4 r²)`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_correction_error_le {r : ℝ} (hr : 1 ≤ r) :
    |liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 -
      liClockPairedEtaInfinitePartitionCorrectionP r / r| ≤
        liClockPairedEtaInfinitePartitionOddCubeMass / (4 * r ^ 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have h := abs_tsum_le_bound (fun n => BIntervalTerm n r)
    (fun n => (1 / (8 * r)) * (1 / (2 * (n : ℝ) + 1) ^ 3))
    (summable_liClockPairedEtaInfinitePartitionOddCubeMass.mul_left (1 / (8 * r))) (fun n => by
      have hn := liClockPairedEtaInfinitePartitionPrimitiveD_interval_error_le hr0
        (by positivity : 0 < 2 * (n : ℝ) + 1) (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)
      calc
        |BIntervalTerm n r| ≤ 1 / (8 * r * (2 * (n : ℝ) + 1) ^ 3) := hn
        _ = _ := by rw [div_mul_eq_div_div]; ring)
  rw [summable_liClockPairedEtaInfinitePartitionOddCubeMass.tsum_mul_left] at h
  rw [liClockPairedEtaInfinitePartitionAveragingH_eq_correction hr0, add_sub_cancel_left,
    abs_mul, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hr0)]
  calc
    _ ≤ (2 / r) * ((1 / (8 * r)) * liClockPairedEtaInfinitePartitionOddCubeMass) :=
      mul_le_mul_of_nonneg_left h (div_pos (by norm_num) hr0).le
    _ = _ := by field_simp; ring

private theorem continuous_BIntervalTerm (n : ℕ) : Continuous (BIntervalTerm n) := by
  have ha : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hab : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2 := by linarith
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun w : ℝ => (1 / 4) * (1 / w ^ 3))
    (fun r => ?_) (fun r => ?_)
    ((reciprocal_continuousOn ha hab 3).const_mul (1 / 4)).intervalIntegrable ?_
  · exact ((continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp
      (continuous_const.mul continuous_id)).measurable.div (measurable_id.pow_const 3)).aestronglyMeasurable
  · exact Eventually.of_forall (fun w hw => by
      have hw' : w ∈ Ioc (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2) := by simpa only [uIoc_of_le hab] using hw
      have hw0 : 0 < w := ha.trans hw'.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hw0 3)]
      simpa only [mul_one_div] using
        div_le_div_of_nonneg_right (liClockPairedEtaInfinitePartitionPrimitiveB_abs_le (r * w)) (pow_pos hw0 3).le)
  · exact Eventually.of_forall (fun w _ =>
      (continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp (continuous_id.mul continuous_const)).div_const _)

private theorem continuous_BInterval_tsum : Continuous (fun r : ℝ => ∑' n, BIntervalTerm n r) := by
  have hs : Summable (fun n : ℕ => (1 / 8 : ℝ) *
      (1 / (2 * (n : ℝ) + 1) ^ 2 - 1 / (2 * (n : ℝ) + 2) ^ 2)) :=
    (summable_reciprocal_odd_square.sub summable_reciprocal_even_square).mul_left (1 / 8)
  refine continuous_tsum continuous_BIntervalTerm hs ?_
  intro n r
  have h := weighted_integral_norm_le (by positivity : 0 < 2 * (n : ℝ) + 1)
    (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2)
    (fun w => Bₑ (r * w)) (fun w => liClockPairedEtaInfinitePartitionPrimitiveB_abs_le _) 1
  norm_num only [Nat.add_one, Nat.reduceAdd, Nat.cast_one] at h
  rw [Real.norm_eq_abs]
  convert h using 1
  simp only [BIntervalTerm, div_eq_mul_inv]
  ring

/-- `H` is continuous on `(0, ∞)`. -/
theorem continuousOn_liClockPairedEtaInfinitePartitionAveragingH :
    ContinuousOn liClockPairedEtaInfinitePartitionAveragingH (Ioi (0 : ℝ)) := by
  have hc : ContinuousOn (fun r : ℝ => Real.log 2 / 2 +
      liClockPairedEtaInfinitePartitionCorrectionP r / r + (2 / r) * ∑' n, BIntervalTerm n r) (Ioi (0 : ℝ)) := by
    exact (continuousOn_const.add
      (continuous_liClockPairedEtaInfinitePartitionCorrectionP.continuousOn.div continuousOn_id
        (fun r hr => ne_of_gt hr))).add
      ((continuousOn_const.div continuousOn_id (fun r hr => ne_of_gt hr)).mul
        continuous_BInterval_tsum.continuousOn)
  apply hc.congr
  intro r hr
  have h := liClockPairedEtaInfinitePartitionAveragingH_eq_correction hr
  linarith

private theorem tendsto_zero_of_abs_le_const_div {f : ℝ → ℝ} {C : ℝ}
    (h : ∀ r, 1 ≤ r → |f r| ≤ C / r) : Tendsto f atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => C / r) atTop (𝓝 0) := tendsto_id.const_div_atTop C
  have ha : Tendsto (fun r : ℝ => |f r|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      ((eventually_ge_atTop (1 : ℝ)).mono (fun r hr => h r hr)) ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, Real.norm_eq_abs] using ha

/-- `H(r) → (log 2)/2` as `r → ∞`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_tendsto :
    Tendsto liClockPairedEtaInfinitePartitionAveragingH atTop (𝓝 (Real.log 2 / 2)) := by
  have h := tendsto_zero_of_abs_le_const_div
    (f := fun r => liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2)
    (C := Real.pi ^ 2 / 16) (fun r hr => by
      simpa only [div_mul_eq_div_div] using
        liClockPairedEtaInfinitePartitionAveragingH_error_le hr)
  exact (tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa only [sub_zero, Real.norm_eq_abs] using
      (tendsto_iff_norm_sub_tendsto_zero.mp h)))

/-- `r (H(r) - (log 2)/2) - P(r) → 0` as `r → ∞`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_scaled_correction_tendsto :
    Tendsto (fun r : ℝ => r * (liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2) -
      liClockPairedEtaInfinitePartitionCorrectionP r) atTop (𝓝 0) := by
  apply tendsto_zero_of_abs_le_const_div (C := liClockPairedEtaInfinitePartitionOddCubeMass / 4)
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have heq : r * (liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 -
      liClockPairedEtaInfinitePartitionCorrectionP r / r) =
      r * (liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2) -
      liClockPairedEtaInfinitePartitionCorrectionP r := by field_simp
  calc
    _ = r * |liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 -
        liClockPairedEtaInfinitePartitionCorrectionP r / r| := by
      rw [← heq, abs_mul, abs_of_pos hr0]
    _ ≤ r * (liClockPairedEtaInfinitePartitionOddCubeMass / (4 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left (liClockPairedEtaInfinitePartitionAveragingH_correction_error_le hr) hr0.le
    _ = _ := by field_simp

/-- Along even integers `r = 2(n+1)`, `r (H(r) - (log 2)/2) → -π²/48`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_even_lattice_tendsto :
    Tendsto (fun n : ℕ => (2 * ((n : ℝ) + 1)) *
      (liClockPairedEtaInfinitePartitionAveragingH (2 * ((n : ℝ) + 1)) - Real.log 2 / 2))
      atTop (𝓝 (-Real.pi ^ 2 / 48)) := by
  have hg : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have h := liClockPairedEtaInfinitePartitionAveragingH_scaled_correction_tendsto.comp hg
  have heq : ∀ n : ℕ, liClockPairedEtaInfinitePartitionCorrectionP (2 * ((n : ℝ) + 1)) =
      -Real.pi ^ 2 / 48 := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using
      liClockPairedEtaInfinitePartitionCorrectionP_even_nat (n + 1)
  have ha := h.add_const (-Real.pi ^ 2 / 48)
  simpa only [Function.comp_apply, heq, sub_add_cancel, zero_add] using ha

/-- Along odd integers `r = 2n+1`, `r (H(r) - (log 2)/2) → π²/24`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_odd_lattice_tendsto :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) *
      (liClockPairedEtaInfinitePartitionAveragingH (2 * (n : ℝ) + 1) - Real.log 2 / 2))
      atTop (𝓝 (Real.pi ^ 2 / 24)) := by
  have hg : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h := liClockPairedEtaInfinitePartitionAveragingH_scaled_correction_tendsto.comp hg
  have heq := liClockPairedEtaInfinitePartitionCorrectionP_odd_nat
  have ha := h.add_const (Real.pi ^ 2 / 24)
  simpa only [Function.comp_apply, heq, sub_add_cancel, zero_add] using ha

private theorem log_mem_source_iff {w : ℝ} (hw : 0 < w) :
    Real.log w ∈ RiemannGaussian.pairedEtaLogSupport ↔ w ∈ arithmeticSupport := by
  simp only [RiemannGaussian.pairedEtaLogSupport, RiemannGaussian.pairedEtaLogInterval,
    arithmeticSupport, mem_iUnion, mem_Ioc]
  apply exists_congr
  intro n
  exact and_congr (Real.log_lt_log_iff (by positivity) hw) (Real.log_le_log_iff hw (by positivity))

private theorem source_indicator_exp {u : ℝ} (hu : 0 ≤ u) :
    RiemannGaussian.pairedEtaLogSupport.indicator (fun _ => (1 : ℝ)) u = αₑ (Real.exp u) := by
  classical
  have hw : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  rw [indicator_nat_eq hw]
  have hm : u ∈ RiemannGaussian.pairedEtaLogSupport ↔ Real.exp u ∈ arithmeticSupport := by
    simpa only [Real.log_exp] using log_mem_source_iff (Real.exp_pos u)
  simp only [indicator, hm]

private theorem source_weight_exp {u : ℝ} (hu : 0 ≤ u) :
    RiemannGaussian.pairedEtaLogSupport.indicator (fun v => Real.exp (-v / 2)) u =
      αₑ (Real.exp u) * Real.exp (-u / 2) := by
  classical
  have hi := source_indicator_exp hu
  by_cases h : u ∈ RiemannGaussian.pairedEtaLogSupport
  · simp only [indicator_of_mem h] at hi ⊢
    rw [← hi, one_mul]
  · simp only [indicator_of_notMem h] at hi ⊢
    rw [← hi, zero_mul]

private theorem source_weight_zero {u : ℝ} (hu : u ≤ 0) :
    RiemannGaussian.pairedEtaLogSupport.indicator (fun v => Real.exp (-v / 2)) u = 0 := by
  exact indicator_of_notMem (fun h => not_lt_of_ge hu
    (RiemannGaussian.pairedEtaLogSupport_subset_Ioi_zero h)) _

private theorem integral_eq_Ioi_zero_of_support (f : ℝ → ℝ) (hf : ∀ u, u ≤ 0 → f u = 0) :
    (∫ u, f u) = ∫ u in Ioi (0 : ℝ), f u := by
  classical
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by
    by_cases hu : 0 < u
    · rw [indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    · rw [indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu), hf u (le_of_not_gt hu)])

private theorem source_exp_image_Ioi_zero : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_exp_iff.mpr hu
  · intro hw
    exact ⟨Real.log w, Real.log_pos hw, Real.exp_log (lt_trans zero_lt_one hw)⟩

private theorem raw_density_eq_arithmetic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x / 2) * (∫ v : ℝ,
      RiemannGaussian.pairedEtaLogSupport.indicator (fun u => Real.exp (-u / 2)) (v + x) *
      RiemannGaussian.pairedEtaLogSupport.indicator (fun u => Real.exp (-u / 2)) v) =
      liClockPairedEtaInfinitePartitionAveragingH (Real.exp x) := by
  rw [integral_eq_Ioi_zero_of_support _ (fun v hv => by rw [source_weight_zero hv, mul_zero])]
  have hj := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
    (fun u (_hu : u ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (Real.exp_monotone.monotoneOn _) (fun w : ℝ => αₑ w * (αₑ (Real.exp x * w) / w ^ 2))
  rw [source_exp_image_Ioi_zero] at hj
  unfold liClockPairedEtaInfinitePartitionAveragingH
  rw [hj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := hv
  rw [source_weight_exp (by linarith), source_weight_exp hv0.le, smul_eq_mul]
  have ha : Real.exp (v + x) = Real.exp x * Real.exp v := by rw [Real.exp_add]; ring
  rw [ha]
  have heq : Real.exp (x / 2) * (Real.exp (-(v + x) / 2) * Real.exp (-v / 2)) =
      (Real.exp v)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have he : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
  calc
    _ = (αₑ (Real.exp x * Real.exp v) * αₑ (Real.exp v)) * (Real.exp v)⁻¹ := by
      rw [← heq]
      ring
    _ = _ := by field_simp

private theorem normalizer_integral_arithmetic :
    (∫ u : ℝ, Real.exp (-u / 2) ∂ RiemannGaussian.pairedEtaLogMeasure) =
      ∫ w in Ioi (1 : ℝ), αₑ w * w ^ (-3 / 2 : ℝ) := by
  rw [RiemannGaussian.pairedEtaLogMeasure, ← integral_indicator
    RiemannGaussian.measurableSet_pairedEtaLogSupport]
  rw [integral_eq_Ioi_zero_of_support _ (fun u hu => source_weight_zero hu)]
  have hj := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
    (fun u (_hu : u ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (Real.exp_monotone.monotoneOn _) (fun w : ℝ => αₑ w * w ^ (-3 / 2 : ℝ))
  rw [source_exp_image_Ioi_zero] at hj
  rw [hj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [source_weight_exp (le_of_lt hu), smul_eq_mul]
  have heq : Real.exp u * (Real.exp u) ^ (-3 / 2 : ℝ) = Real.exp (-u / 2) := by
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [← heq]
  ring

private theorem normalizer_integral_intervals :
    (∫ u : ℝ, Real.exp (-u / 2) ∂ RiemannGaussian.pairedEtaLogMeasure) =
      ∑' n : ℕ, ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), w ^ (-3 / 2 : ℝ) := by
  rw [normalizer_integral_arithmetic]
  exact integral_alpha_eq_tsum (fun w : ℝ => w ^ (-3 / 2 : ℝ))
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))

private theorem summable_normalizer_intervals :
    Summable (fun n : ℕ => ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), w ^ (-3 / 2 : ℝ)) := by
  exact summable_arithmetic_intervals (fun w : ℝ => w ^ (-3 / 2 : ℝ))
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))

private theorem half_power_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun w : ℝ => w ^ (-3 / 2 : ℝ)) (Icc a b) :=
  continuousOn_id.rpow_const (fun _ hw => Or.inl (ha.trans_le hw.1).ne')

private theorem half_power_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in a..b, w ^ (-3 / 2 : ℝ)) = 2 * (1 / Real.sqrt a - 1 / Real.sqrt b) := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_rpow (Or.inr ⟨by norm_num, by rw [uIcc_of_le hab]; simp only [mem_Icc, not_and_or]; exact Or.inl (not_le_of_gt ha)⟩)]
  rw [show (-3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg ha.le, Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  ring

private theorem retained_half_period_ge_half_full {a : ℝ} (ha : 0 < a) :
    (1 / 2 : ℝ) * (∫ w in a..(a + 2), w ^ (-3 / 2 : ℝ)) ≤
      ∫ w in a..(a + 1), w ^ (-3 / 2 : ℝ) := by
  have hf : IntervalIntegrable (fun w : ℝ => w ^ (-3 / 2 : ℝ)) volume a (a + 1) :=
    (half_power_continuousOn ha).intervalIntegrable_of_Icc (by linarith)
  have hg : IntervalIntegrable (fun w : ℝ => w ^ (-3 / 2 : ℝ)) volume (a + 1) (a + 2) :=
    (half_power_continuousOn (by linarith : 0 < a + 1)).intervalIntegrable_of_Icc (by linarith)
  have hc : ContinuousOn (fun w : ℝ => (w + 1) ^ (-3 / 2 : ℝ)) (Icc a (a + 1)) :=
    (continuousOn_id.add continuousOn_const).rpow_const (fun w hw => Or.inl (show w + 1 ≠ 0 from ne_of_gt (by linarith [hw.1])))
  have hm := intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1)
    (hc.intervalIntegrable_of_Icc (by linarith)) hf (fun w hw =>
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-3 / 2 : ℝ) ≤ 0)
        (show w ∈ Ioi (0 : ℝ) from ha.trans_le hw.1)
        (show w + 1 ∈ Ioi (0 : ℝ) from lt_trans (ha.trans_le hw.1) (by linarith)) (by linarith))
  have hshift := intervalIntegral.integral_comp_add_right (a := a) (b := a + 1)
    (fun w : ℝ => w ^ (-3 / 2 : ℝ)) 1
  rw [hshift] at hm
  norm_num only [show a + 1 + 1 = a + 2 by ring] at hm
  have ha' := intervalIntegral.integral_add_adjacent_intervals hf hg
  linarith

private theorem normalizer_retained_tail_lower :
    (∫ u : ℝ, Real.exp (-u / 2) ∂ RiemannGaussian.pairedEtaLogMeasure) ≥
      1 - Real.sqrt 2 + 2 / Real.sqrt 3 + 1 / Real.sqrt 5 := by
  let f : ℕ → ℝ := fun n => ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), w ^ (-3 / 2 : ℝ)
  have hfs : Summable f := summable_normalizer_intervals
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    change 0 ≤ ∫ w in (2 * (n : ℝ) + 1)..(2 * (n : ℝ) + 2), w ^ (-3 / 2 : ℝ)
    apply intervalIntegral.integral_nonneg (by linarith)
    intro w hw
    exact Real.rpow_nonneg (by linarith [hw.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]) _
  have hp : ∀ m : ℕ,
      f 0 + f 1 + (1 / 2) * (∫ w in (5 : ℝ)..(2 * (m : ℝ) + 5), w ^ (-3 / 2 : ℝ)) ≤
      (∫ u : ℝ, Real.exp (-u / 2) ∂ RiemannGaussian.pairedEtaLogMeasure) := by
    intro m
    have hparts := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun w : ℝ => w ^ (-3 / 2 : ℝ)) (a := fun k : ℕ => 2 * (k : ℝ) + 5) (n := m)
      (fun k _ => (half_power_continuousOn (by positivity : 0 < 2 * (k : ℝ) + 5)).intervalIntegrable_of_Icc (by push_cast; linarith))
    have hsum : (1 / 2) * (∫ w in (5 : ℝ)..(2 * (m : ℝ) + 5), w ^ (-3 / 2 : ℝ)) ≤
        ∑ k ∈ Finset.range m, f (k + 2) := by
      have hm := Finset.sum_le_sum (s := Finset.range m) (fun k _ =>
        retained_half_period_ge_half_full (by positivity : 0 < 2 * (k : ℝ) + 5))
      rw [← Finset.mul_sum] at hm
      have hfull : (∑ i ∈ Finset.range m, ∫ w in (2 * (i : ℝ) + 5)..(2 * (i : ℝ) + 5 + 2), w ^ (-3 / 2 : ℝ)) =
          ∫ w in (5 : ℝ)..(2 * (m : ℝ) + 5), w ^ (-3 / 2 : ℝ) := by
        calc
          _ = ∑ i ∈ Finset.range m, ∫ w in (2 * (i : ℝ) + 5)..(2 * ((i + 1 : ℕ) : ℝ) + 5), w ^ (-3 / 2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            push_cast
            ring
          _ = _ := by simpa only [Nat.cast_zero, mul_zero, zero_add] using hparts
      have hret : (∑ i ∈ Finset.range m, ∫ w in (2 * (i : ℝ) + 5)..(2 * (i : ℝ) + 5 + 1), w ^ (-3 / 2 : ℝ)) =
          ∑ i ∈ Finset.range m, f (i + 2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        congr 1 <;> push_cast <;> ring
      rw [hfull, hret] at hm
      exact hm
    have hfinite := hfs.sum_le_tsum (Finset.range (2 + m)) (fun n _ => hf0 n)
    rw [← normalizer_integral_intervals] at hfinite
    rw [Finset.sum_range_add, show (∑ n ∈ Finset.range 2, f n) = f 0 + f 1 by simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]] at hfinite
    have hshift : (∑ k ∈ Finset.range m, f (2 + k)) = ∑ k ∈ Finset.range m, f (k + 2) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_comm]
    rw [hshift] at hfinite
    linarith
  have ht := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (5 : ℝ)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) (by norm_num))
    (tendsto_atTop_add_const_right _ 5 (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hb := le_of_tendsto (((tendsto_const_nhds (x := f 0)).add
    (tendsto_const_nhds (x := f 1))).add (ht.const_mul (1 / 2))) (Eventually.of_forall hp)
  have h0 : f 0 = 2 * (1 - 1 / Real.sqrt 2) := by
    dsimp [f]
    rw [half_power_integral (by norm_num) (by norm_num)]
    norm_num
  have h1 : f 1 = 2 * (1 / Real.sqrt 3 - 1 / 2) := by
    dsimp [f]
    convert half_power_integral (a := 3) (b := 4) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hi : (∫ w in Ioi (5 : ℝ), w ^ (-3 / 2 : ℝ)) = 2 / Real.sqrt 5 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5), ← Real.sqrt_eq_rpow]
    ring
  rw [h0, h1, hi] at hb
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs2p := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have heq : 2 / Real.sqrt 2 = Real.sqrt 2 := by apply (div_eq_iff hs2p.ne').mpr; nlinarith
  rw [show 2 * (1 - 1 / Real.sqrt 2) = 2 - 2 / Real.sqrt 2 by ring, heq] at hb
  calc
    _ = 2 - Real.sqrt 2 + 2 * (1 / Real.sqrt 3 - 1 / 2) + (1 / 2) * (2 / Real.sqrt 5) := by ring
    _ ≤ _ := hb

/-- For `w ≥ 1`, `α(w)` is the indicator of the paired-eta log support evaluated at `log w`. -/
theorem liClockPairedEtaInfinitePartitionArithmeticIndicator_eq_log_support {w : ℝ} (hw : 1 ≤ w) :
    αₑ w = RiemannGaussian.pairedEtaLogSupport.indicator (fun _ => (1 : ℝ)) (Real.log w) := by
  have hp : 0 < w := zero_lt_one.trans_le hw
  have h := source_indicator_exp (Real.log_nonneg hw)
  rw [Real.exp_log hp] at h
  exact h.symm

theorem liClockPairedEtaInfinitePartitionPrimitiveB_even_nat (m : ℕ) :
    Bₑ (2 * (m : ℝ)) = 1 / 4 := B_even_nat m

theorem liClockPairedEtaInfinitePartitionPrimitiveB_odd_nat (m : ℕ) :
    Bₑ (2 * (m : ℝ) + 1) = -1 / 4 := B_odd_nat m

/-- For almost every `x`, `B'(x) = α(x) - 1/2`. -/
theorem hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveB_ae :
    ∀ᵐ x : ℝ, HasDerivAt liClockPairedEtaInfinitePartitionPrimitiveB (αₑ x - 1 / 2) x := by
  filter_upwards [(Set.countable_range (fun k : ℤ => (k : ℝ))).ae_notMem volume] with x hx
  exact hasDerivAt_liClockPairedEtaInfinitePartitionPrimitiveB hx
private theorem normalizer_scalar_certificate {Z : ℝ}
    (hZ : 1 - Real.sqrt 2 + 2 / Real.sqrt 3 + 1 / Real.sqrt 5 ≤ Z) :
    (9697 / 8190 : ℝ) < Z := by
  have h2 : Real.sqrt 2 < (99 / 70 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h3 : Real.sqrt 3 < (26 / 15 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 5 < (9 / 4 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h3' : (15 / 13 : ℝ) < 2 / Real.sqrt 3 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have h5' : (4 / 9 : ℝ) < 1 / Real.sqrt 5 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith
  have hb : (9697 / 8190 : ℝ) < 1 - Real.sqrt 2 + 2 / Real.sqrt 3 + 1 / Real.sqrt 5 := by
    linarith
  exact hb.trans_le hZ

/-- Numerical bound `log 2 < 7/10`. -/
theorem liClockPairedEtaInfinitePartition_log_two_lt_seven_div_ten : Real.log 2 < (7 / 10 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 10) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem liClockPairedEtaInfinitePartition_rational_certificate_eq :
    (9697 / 8190 : ℝ) = 71 / 60 + 11 / 16380 := by norm_num


/-- The half-tilt normalizer is `Z = ∫_1^∞ α(w) w^{-3/2} dw`. -/
theorem liClockPairedEtaInfinitePartitionNormalizer_eq_arithmetic :
    liClockPairedEtaInfinitePartitionNormalizer = ∫ w in Ioi (1 : ℝ), αₑ w * w ^ (-3 / 2 : ℝ) :=
  normalizer_integral_arithmetic

theorem summable_liClockPairedEtaInfinitePartitionNormalizer :
    Summable (fun n : ℕ =>
      (1 / Real.sqrt (2 * (n : ℝ) + 1) - 1 / Real.sqrt (2 * (n : ℝ) + 2))) := by
  apply (summable_normalizer_intervals.mul_left (1 / 2)).congr
  intro n
  rw [half_power_integral (by positivity) (by linarith)]
  ring

/-- `Z = 2 ∑_{n ≥ 0} (1/√(2n+1) - 1/√(2n+2))`. -/
theorem liClockPairedEtaInfinitePartitionNormalizer_eq_tsum :
    liClockPairedEtaInfinitePartitionNormalizer = 2 * ∑' n : ℕ,
      (1 / Real.sqrt (2 * (n : ℝ) + 1) - 1 / Real.sqrt (2 * (n : ℝ) + 2)) := by
  rw [liClockPairedEtaInfinitePartitionNormalizer, normalizer_integral_intervals, ← tsum_mul_left]
  exact tsum_congr (fun n => half_power_integral (by positivity) (by linarith))

/-- For `x ≥ 0`, the raw difference density satisfies `e^{x/2} ρ(x) = H(e^x)`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_arithmetic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (x / 2) * liClockPairedEtaInfinitePartitionRawDifferenceDensity x =
      liClockPairedEtaInfinitePartitionAveragingH (Real.exp x) := raw_density_eq_arithmetic hx

private theorem raw_density_abs (x : ℝ) :
    liClockPairedEtaInfinitePartitionRawDifferenceDensity |x| =
      liClockPairedEtaInfinitePartitionRawDifferenceDensity x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, liClockPairedEtaInfinitePartitionRawDifferenceDensity_even]

/-- For all real `x`, `ρ(x) = e^{-|x|/2} H(e^{|x|})`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_H (x : ℝ) :
    liClockPairedEtaInfinitePartitionRawDifferenceDensity x = Real.exp (-|x| / 2) *
      liClockPairedEtaInfinitePartitionAveragingH (Real.exp |x|) := by
  have h := liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_arithmetic (abs_nonneg x)
  rw [raw_density_abs] at h
  have he : Real.exp (-|x| / 2) * Real.exp (|x| / 2) = 1 := by
    rw [← Real.exp_add, show -|x| / 2 + |x| / 2 = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (-|x| / 2) * Real.exp (|x| / 2)) *
      liClockPairedEtaInfinitePartitionRawDifferenceDensity x := by rw [he, one_mul]
    _ = _ := by rw [mul_assoc, h]

/-- Uniform tail bound: `|ρ(x) - (log 2/2) e^{-|x|/2}| ≤ (π²/16) e^{-3|x|/2}` for all `x`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_le (x : ℝ) :
    |liClockPairedEtaInfinitePartitionRawDifferenceDensity x - (Real.log 2 / 2) * Real.exp (-|x| / 2)| ≤
      (Real.pi ^ 2 / 16) * Real.exp (-3 * |x| / 2) := by
  have h := liClockPairedEtaInfinitePartitionAveragingH_error_le
    (Real.one_le_exp_iff.mpr (abs_nonneg x))
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_H]
  have heq : Real.exp (-|x| / 2) / Real.exp |x| = Real.exp (-3 * |x| / 2) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (-|x| / 2) * |liClockPairedEtaInfinitePartitionAveragingH (Real.exp |x|) - Real.log 2 / 2| := by
      rw [show Real.exp (-|x| / 2) * liClockPairedEtaInfinitePartitionAveragingH (Real.exp |x|) -
        Real.log 2 / 2 * Real.exp (-|x| / 2) = Real.exp (-|x| / 2) *
        (liClockPairedEtaInfinitePartitionAveragingH (Real.exp |x|) - Real.log 2 / 2) by ring,
        abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-|x| / 2) * (Real.pi ^ 2 / (16 * Real.exp |x|)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      rw [show Real.exp (-|x| / 2) * (Real.pi ^ 2 / (16 * Real.exp |x|)) =
        (Real.pi ^ 2 / 16) * (Real.exp (-|x| / 2) / Real.exp |x|) by rw [div_mul_eq_div_div]; ring, heq]

/-- For `x ≥ 0`, `|e^{x/2} ρ(x) - (log 2)/2| ≤ (π²/16) e^{-x}`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_error_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (x / 2) * liClockPairedEtaInfinitePartitionRawDifferenceDensity x - Real.log 2 / 2| ≤
      (Real.pi ^ 2 / 16) * Real.exp (-x) := by
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_arithmetic hx]
  calc
    _ ≤ Real.pi ^ 2 / (16 * Real.exp x) :=
      liClockPairedEtaInfinitePartitionAveragingH_error_le (Real.one_le_exp_iff.mpr hx)
    _ = _ := by rw [div_mul_eq_div_div, div_eq_mul_inv, ← Real.exp_neg]

/-- The raw difference density `ρ` is continuous on `ℝ`. -/
theorem continuous_liClockPairedEtaInfinitePartitionRawDifferenceDensity :
    Continuous liClockPairedEtaInfinitePartitionRawDifferenceDensity := by
  have hH : Continuous (fun x : ℝ => liClockPairedEtaInfinitePartitionAveragingH (Real.exp |x|)) :=
    continuousOn_liClockPairedEtaInfinitePartitionAveragingH.comp_continuous
      (Real.continuous_exp.comp (continuous_abs : Continuous (fun x : ℝ => |x|))) (fun x => Real.exp_pos |x|)
  exact ((Real.continuous_exp.comp ((continuous_abs : Continuous (fun x : ℝ => |x|)).neg.div_const 2)).mul hH).congr
    (fun x => (liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_H x).symm)

/-- `e^{x/2} ρ(x) → (log 2)/2` as `x → ∞`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_tendsto :
    Tendsto (fun x : ℝ => Real.exp (x / 2) * liClockPairedEtaInfinitePartitionRawDifferenceDensity x)
      atTop (𝓝 (Real.log 2 / 2)) := by
  have h := liClockPairedEtaInfinitePartitionAveragingH_tendsto.comp Real.tendsto_exp_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_arithmetic hx).symm

/-- The normalized infinite-partition difference density divided by the half-line reference
density tends to the comparison limit `2 log 2/Z²` as `x → ∞`. -/
theorem liClockPairedEtaInfinitePartitionDifferenceDensity_ratio_tendsto :
    Tendsto (fun x : ℝ => liClockPairedEtaInfinitePartitionDifferenceDensity x /
      liClockPairedEtaHalfLineDifferenceDensity x) atTop
        (𝓝 liClockPairedEtaInfinitePartitionComparisonLimit) := by
  have h := liClockPairedEtaInfinitePartitionRawDifferenceDensity_scaled_tendsto.const_mul
    (4 / liClockPairedEtaInfinitePartitionNormalizer ^ 2)
  have hl : (4 / liClockPairedEtaInfinitePartitionNormalizer ^ 2) * (Real.log 2 / 2) =
      liClockPairedEtaInfinitePartitionComparisonLimit := by
    unfold liClockPairedEtaInfinitePartitionComparisonLimit
    ring
  rw [hl] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  unfold liClockPairedEtaInfinitePartitionDifferenceDensity liClockPairedEtaHalfLineDifferenceDensity
  rw [liClockPairedEtaHalfLineRawDifferenceDensity_eq, abs_of_nonneg hx,
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two]
  rw [show -x / 2 = -(x / 2) by ring, Real.exp_neg]
  have hZ : liClockPairedEtaInfinitePartitionNormalizer ≠ 0 :=
    liClockPairedEtaInfinitePartitionNormalizer_pos.ne'
  have he : Real.exp (x / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  norm_num

private theorem raw_density_scaled_error_eq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (3 * x / 2) * (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
      (Real.log 2 / 2) * Real.exp (-x / 2)) =
      Real.exp x * (liClockPairedEtaInfinitePartitionAveragingH (Real.exp x) - Real.log 2 / 2) := by
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_eq_H, abs_of_nonneg hx]
  calc
    _ = (Real.exp (3 * x / 2) * Real.exp (-x / 2)) *
      (liClockPairedEtaInfinitePartitionAveragingH (Real.exp x) - Real.log 2 / 2) := by ring
    _ = _ := by rw [← Real.exp_add, show 3 * x / 2 + -x / 2 = x by ring]

/-- Along `x = log(2(n+1))`, `e^{3x/2} (ρ(x) - (log 2/2) e^{-x/2}) → -π²/48`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_even_lattice_tendsto :
    Tendsto (fun n : ℕ =>
      let x := Real.log (2 * ((n : ℝ) + 1))
      Real.exp (3 * x / 2) * (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
        (Real.log 2 / 2) * Real.exp (-x / 2))) atTop (𝓝 (-Real.pi ^ 2 / 48)) := by
  apply liClockPairedEtaInfinitePartitionAveragingH_even_lattice_tendsto.congr'
  exact Eventually.of_forall (fun n => by
    have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
    dsimp only
    rw [raw_density_scaled_error_eq (Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])), Real.exp_log hp])

/-- Along `x = log(2n+1)`, `e^{3x/2} (ρ(x) - (log 2/2) e^{-x/2}) → π²/24`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_odd_lattice_tendsto :
    Tendsto (fun n : ℕ =>
      let x := Real.log (2 * (n : ℝ) + 1)
      Real.exp (3 * x / 2) * (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
        (Real.log 2 / 2) * Real.exp (-x / 2))) atTop (𝓝 (Real.pi ^ 2 / 24)) := by
  apply liClockPairedEtaInfinitePartitionAveragingH_odd_lattice_tendsto.congr'
  exact Eventually.of_forall (fun n => by
    have hp : 0 < 2 * (n : ℝ) + 1 := by positivity
    dsimp only
    rw [raw_density_scaled_error_eq (Real.log_nonneg (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])), Real.exp_log hp])

/-- Sharpness: `ρ(x) - (log 2/2) e^{-x/2}` is not `o(e^{-3x/2})` as `x → ∞`. -/
theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_error_not_isLittleO :
    ¬Asymptotics.IsLittleO atTop
      (fun x : ℝ => liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
        (Real.log 2 / 2) * Real.exp (-x / 2))
      (fun x : ℝ => Real.exp (-3 * x / 2)) := by
  intro h
  have ht := h.tendsto_div_nhds_zero
  have hs : Tendsto (fun x : ℝ => Real.exp (3 * x / 2) *
      (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
        (Real.log 2 / 2) * Real.exp (-x / 2))) atTop (𝓝 0) := by
    apply ht.congr'
    exact Eventually.of_forall (fun x => by
      change (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
        (Real.log 2 / 2) * Real.exp (-x / 2)) / Real.exp (-3 * x / 2) =
        Real.exp (3 * x / 2) * (liClockPairedEtaInfinitePartitionRawDifferenceDensity x -
          (Real.log 2 / 2) * Real.exp (-x / 2))
      rw [div_eq_mul_inv, ← Real.exp_neg, show -(-3 * x / 2) = 3 * x / 2 by ring]
      ring)
  have hx : Tendsto (fun n : ℕ => Real.log (2 * ((n : ℝ) + 1))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  have hz := tendsto_nhds_unique (hs.comp hx)
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_even_lattice_tendsto
  have hp : 0 < Real.pi ^ 2 := by positivity
  linarith

/-- Lower bound `Z ≥ 1 - √2 + 2/√3 + 1/√5` from the first two intervals and a half-period tail. -/
theorem liClockPairedEtaInfinitePartitionNormalizer_ge_halfPeriodTail :
    1 - Real.sqrt 2 + 2 / Real.sqrt 3 + 1 / Real.sqrt 5 ≤
      liClockPairedEtaInfinitePartitionNormalizer := normalizer_retained_tail_lower

/-- `9697/8190 < Z`. -/
theorem liClockPairedEtaInfinitePartitionNormalizer_gt_9697_div_8190 :
    (9697 / 8190 : ℝ) < liClockPairedEtaInfinitePartitionNormalizer :=
  normalizer_scalar_certificate liClockPairedEtaInfinitePartitionNormalizer_ge_halfPeriodTail

/-- `71/60 < Z`. -/
theorem liClockPairedEtaInfinitePartitionNormalizer_gt_seventy_one_div_sixty :
    (71 / 60 : ℝ) < liClockPairedEtaInfinitePartitionNormalizer :=
  lt_trans (by norm_num) liClockPairedEtaInfinitePartitionNormalizer_gt_9697_div_8190

/-- The comparison limit `2 log 2/Z²` is positive. -/
theorem liClockPairedEtaInfinitePartitionComparisonLimit_pos :
    0 < liClockPairedEtaInfinitePartitionComparisonLimit := by
  unfold liClockPairedEtaInfinitePartitionComparisonLimit
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos)

/-- `2 log 2/Z² < 5040/5041`, using `log 2 < 7/10` and `Z > 71/60`. -/
theorem liClockPairedEtaInfinitePartitionComparisonLimit_lt_5040_div_5041 :
    liClockPairedEtaInfinitePartitionComparisonLimit < (5040 / 5041 : ℝ) := by
  unfold liClockPairedEtaInfinitePartitionComparisonLimit
  apply (div_lt_iff₀ (sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos)).mpr
  have hZ := liClockPairedEtaInfinitePartitionNormalizer_gt_seventy_one_div_sixty
  have hZp := liClockPairedEtaInfinitePartitionNormalizer_pos
  have hl := liClockPairedEtaInfinitePartition_log_two_lt_seven_div_ten
  nlinarith [sq_nonneg (liClockPairedEtaInfinitePartitionNormalizer - 71 / 60)]

/-- The comparison limit `2 log 2/Z²` is strictly less than `1`. -/
theorem liClockPairedEtaInfinitePartitionComparisonLimit_lt_one :
    liClockPairedEtaInfinitePartitionComparisonLimit < 1 :=
  lt_trans liClockPairedEtaInfinitePartitionComparisonLimit_lt_5040_div_5041 (by norm_num)

/-- For `r > 0`, `H(r) - (log 2)/2 = P(r)/r + (2/r) ∫_1^∞ α(w) B(rw)/w³ dw`. -/
theorem liClockPairedEtaInfinitePartitionAveragingH_eq_correction_integral {r : ℝ} (hr : 0 < r) :
    liClockPairedEtaInfinitePartitionAveragingH r - Real.log 2 / 2 =
      liClockPairedEtaInfinitePartitionCorrectionP r / r + (2 / r) *
        ∫ w in Ioi (1 : ℝ), αₑ w * (Bₑ (r * w) / w ^ 3) := by
  have hf : IntegrableOn (fun w : ℝ => Bₑ (r * w) / w ^ 3) (Ioi (1 : ℝ)) :=
    integrableOn_bounded_weight (fun w => Bₑ (r * w))
      (continuous_liClockPairedEtaInfinitePartitionPrimitiveB.comp (continuous_const.mul continuous_id)).measurable
      (fun w => liClockPairedEtaInfinitePartitionPrimitiveB_abs_le _) 1
  rw [integral_alpha_eq_tsum _ hf]
  exact liClockPairedEtaInfinitePartitionAveragingH_eq_correction hr

end RHTower
