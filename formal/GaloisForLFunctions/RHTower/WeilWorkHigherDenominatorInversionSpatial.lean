import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionFourier
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorWeakTrace

/-!
# Actual inverted Bessel-series pairing

The compact inversion path lies in a positive horizontal strip at every fixed
positive height. Its summable mode bound justifies spatial sum/integral
interchange, after which the checked moving Fourier limit applies.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower.BesselKZero RHTower.MaassBesselSeries
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

def inversionBoundaryPoint (y x : ℝ) : ℂ := invS ((x : ℂ) + (y : ℂ) * I)

theorem inversionBoundaryPoint_re (y x : ℝ) :
    (inversionBoundaryPoint y x).re = -inversionBoundaryPhase y x := by
  simp [inversionBoundaryPoint, invS, inversionBoundaryPhase, Complex.inv_re,
    Complex.normSq_apply, sq]

theorem inversionBoundaryPoint_im (y x : ℝ) :
    (inversionBoundaryPoint y x).im = y / (x ^ 2 + y ^ 2) := by
  simp [inversionBoundaryPoint, invS_im, Complex.normSq_apply, sq]

theorem inversionBoundaryPoint_im_pos {y : ℝ} (hy : 0 < y) (x : ℝ) :
    0 < (inversionBoundaryPoint y x).im :=
  invS_mem_upper (by
    change 0 < (((x : ℂ) + (y : ℂ) * I).im)
    simpa using hy)

theorem continuous_inversionBoundaryPoint {y : ℝ} (hy : 0 < y) :
    Continuous (inversionBoundaryPoint y) := by
  have hc : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) := by fun_prop
  have hn : ∀ x : ℝ, (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add, zero_im] at hi
    exact hy.ne' hi
  exact (hc.inv₀ hn).neg

/-- The whole compact inversion path fits one fixed positive strip. -/
theorem inversionBoundaryPoint_strip {a b y x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hy : 0 < y) (hx : x ∈ Icc a b) :
    y / (b ^ 2 + y ^ 2) ≤ (inversionBoundaryPoint y x).im ∧
      (inversionBoundaryPoint y x).im ≤ y / a ^ 2 := by
  rw [inversionBoundaryPoint_im]
  have hx0 := ha.trans_le hx.1
  have hb0 := ha.trans_le hab
  have hdx := inversionBoundaryDenom_pos hx0 y
  have hx2 : x ^ 2 ≤ b ^ 2 := by nlinarith [hx.2]
  have ha2 : a ^ 2 ≤ x ^ 2 + y ^ 2 := by nlinarith [hx.1, sq_nonneg y]
  exact ⟨div_le_div_of_nonneg_left hy.le hdx (by linarith),
    div_le_div_of_nonneg_left hy.le (sq_pos_of_pos ha) ha2⟩

theorem continuous_sterm_inversion (q : ℕ → ℂ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasFDerivAt_sterm (g := q) (1 / 2) 0 0 false n
    (inversionBoundaryPoint_im_pos hy x)).continuousAt.comp
      (continuous_inversionBoundaryPoint hy).continuousAt

/-- Normalize a genuine inverted Bessel mode; its cosine is even under inversion. -/
theorem normalized_sterm_inversion (q : ℕ → ℂ) (φ : ℝ → ℂ) (n : ℕ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : Real.log y ≠ 0) :
    φ x * sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x) /
        ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ) =
      q (n + 1) * ((Real.cos (2 * Real.pi * (n + 1) * inversionBoundaryPhase y x) : ℂ) *
        inversionAmplitude φ (n + 1) y x) := by
  have hd := inversionBoundaryDenom_pos hx y
  have hp : (y / (x ^ 2 + y ^ 2)) ^ (1 / 2 : ℝ) =
      y ^ (1 / 2 : ℝ) * inversionBoundaryWeight y x := by
    rw [Real.div_rpow hy.le hd.le, inversionBoundaryWeight, Real.rpow_neg hd.le]
    rfl
  have harg : 2 * Real.pi * (n + 1) * (y / (x ^ 2 + y ^ 2)) =
      (n + 1) * y * inversionBoundaryScale y x := by dsimp [inversionBoundaryScale]; ring
  have hpow : ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy _).ne'
  have hlog : (Real.log y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  simp only [sterm, bterm, yPart, xPart, trigFun, Bool.false_eq_true, ↓reduceIte,
    pow_zero, one_mul, Nat.cast_add, Nat.cast_one, inversionBoundaryPoint_im,
    inversionBoundaryPoint_re, mul_neg, Real.cos_neg, hp, harg]
  dsimp only [inversionAmplitude, inversionTestWeight, scaledKLog]
  push_cast
  field_simp [hpow, hlog]

/-- Positive-height strip domination justifies the actual infinite spatial interchange. -/
theorem cosSeries_inversion_test_integral {q : ℕ → ℂ} (hq : PolyGrowth q)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : 0 < y) :
    (∫ x in a..b, φ x * cosSeries q (inversionBoundaryPoint y x)) =
      ∑' n : ℕ, ∫ x in a..b, φ x * sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x) := by
  obtain ⟨u, hu, hbound⟩ := norm_sterm_le hq (1 / 2) 0 0 false
    (y₂ := y / a ^ 2) (div_pos hy (inversionBoundaryDenom_pos (ha.trans_le hab) y))
  have hint (n : ℕ) : IntervalIntegrable
      (fun x => φ x * sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x)) volume a b :=
    (hφ.mul (continuous_sterm_inversion q n hy)).intervalIntegrable _ _
  have hsum : Summable fun n : ℕ => ∫ x in Ioc a b,
      ‖φ x * sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x)‖ := by
    refine (hu.mul_right (∫ x in Ioc a b, ‖φ x‖)).of_norm_bounded fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    calc
      _ ≤ ∫ x in Ioc a b, u n * ‖φ x‖ := by
        apply integral_mono_ae (hint n).1.norm ((hφ.norm.intervalIntegrable a b).1.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hb := inversionBoundaryPoint_strip ha hab hy (Ioc_subset_Icc_self hx)
        rw [norm_mul, mul_comm (u n)]
        exact mul_le_mul_of_nonneg_left (hbound n _ hb.1 hb.2) (norm_nonneg _)
      _ = u n * (∫ x in Ioc a b, ‖φ x‖) := integral_const_mul _ _
  simp only [intervalIntegral.integral_of_le hab]
  calc
    (∫ x in Ioc a b, φ x * cosSeries q (inversionBoundaryPoint y x)) =
        ∫ x in Ioc a b, ∑' n : ℕ,
          φ x * sterm q (1 / 2) 0 0 false n (inversionBoundaryPoint y x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [cosSeries, besselSeries, tsum_mul_left]
    _ = _ := (integral_tsum_of_summable_integral_norm (fun n => (hint n).1) hsum).symm

/-- The normalized spatial integral is exactly the full moving Fourier pairing. -/
theorem normalized_cosSeries_inversion_integral {q : ℕ → ℂ} (hq : PolyGrowth q)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {a b y : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hy : 0 < y) (hl : Real.log y ≠ 0) :
    (∫ x in a..b, φ x * cosSeries q (inversionBoundaryPoint y x) /
      ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) =
      ∑' n : ℕ, q (n + 1) * inversionCosinePairing φ a b (n + 1) y := by
  rw [intervalIntegral.integral_div, cosSeries_inversion_test_integral hq hφ ha hab hy,
    ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [← intervalIntegral.integral_div, inversionCosinePairing,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  exact normalized_sterm_inversion q φ n (ha.trans_le (uIcc_of_le hab ▸ hx).1) hy hl

/-- The actual inverted spatial series has its checked logarithmic boundary trace. -/
theorem tendsto_cosSeries_inversion_integral {q : ℕ → ℂ} (hq : PolyGrowth q)
    (hsum : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (fun y : ℝ => ∫ x in a..b, φ x * cosSeries q (inversionBoundaryPoint y x) /
      ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (-∑' n : ℕ, q (n + 1) * inversionCosineBoundaryPairing φ a b (n + 1))) := by
  apply (tendsto_inversionFourierPairing hsum hφ ha hab hs).congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with y hy hy1
  exact (normalized_cosSeries_inversion_integral hq hφ.continuous ha hab hy
    (Real.log_neg hy hy1).ne).symm

end RHTower.WeilHigherDenominator
