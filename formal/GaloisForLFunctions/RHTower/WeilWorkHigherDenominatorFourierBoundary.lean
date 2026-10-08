import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorBesselBoundary
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorQuotientMellin
import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The infinite Fourier logarithmic trace

Compact smooth tests have quadratic Fourier decay. Combined with the actual
quotient's weighted summability and a uniform Bessel bound, this permits the
logarithmic boundary limit under the full Fourier sum. No residue expansion or
extra coefficient bound is assumed. Spatial and moving-inversion transport are
separate obligations; this module identifies the coefficient-side weak trace.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

/-- The cosine Fourier coefficient of a compact test, with the `2π` normalization. -/
def cosineTestCoefficient (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (testTransformTwoPi φ (x : ℂ) + testTransformTwoPi φ (-(x : ℂ))) / 2

theorem cosineTestCoefficient_eq_integral {φ : ℝ → ℂ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) (x : ℝ) :
    cosineTestCoefficient φ x = ∫ t : ℝ, φ t * (Real.cos (2 * Real.pi * x * t) : ℂ) := by
  have hp := integrable_testTransform_integrand hc hs (((2 * Real.pi : ℝ) : ℂ) * (x : ℂ))
  have hm := integrable_testTransform_integrand hc hs (-(((2 * Real.pi : ℝ) : ℂ) * (x : ℂ)))
  simp only [mul_neg] at hm
  simp only [cosineTestCoefficient, testTransformTwoPi, mul_neg, testTransform]
  rw [← integral_add hp hm, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_cos, Complex.cos]
  have h₁ : I * (((2 * Real.pi : ℝ) : ℂ) * (x : ℂ)) * (t : ℂ) =
      ((2 * Real.pi * x * t : ℝ) : ℂ) * I := by push_cast; ring
  have h₂ : -(I * (((2 * Real.pi : ℝ) : ℂ) * (x : ℂ))) * (t : ℂ) =
      -((2 * Real.pi * x * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [h₁, h₂]
  ring

/-- A test-dependent constant controls every positive Fourier frequency. -/
theorem cosineTestCoefficient_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖cosineTestCoefficient φ x‖ ≤ C / x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransformTwoPi_decay_order hφ hs 0 0 2
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp := hC (x : ℂ) (by simp)
  have hm := hC (-(x : ℂ)) (by simp)
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hp hm
  calc
    ‖cosineTestCoefficient φ x‖ =
        ‖testTransformTwoPi φ (x : ℂ) + testTransformTwoPi φ (-(x : ℂ))‖ / 2 := by
      simp [cosineTestCoefficient]
    _ ≤ (‖testTransformTwoPi φ (x : ℂ)‖ + ‖testTransformTwoPi φ (-(x : ℂ))‖) / 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ C / (1 + x) ^ 2 := by linarith
    _ ≤ C / x ^ 2 := div_le_div_of_nonneg_left hC0 (by positivity) (by nlinarith)

theorem summable_cosineTestCoefficient {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Summable fun n : ℕ => q (n + 1) * cosineTestCoefficient φ (n + 1) := by
  obtain ⟨C, _, hC⟩ := cosineTestCoefficient_decay hφ hs
  refine (hq.mul_right C).of_norm_bounded fun n => ?_
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (hC (n + 1) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) (norm_nonneg (q (n + 1)))
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc, div_mul_eq_mul_div, mul_comm C] using h

/-- The actual quotient supplies the weighted coefficient hypothesis. -/
theorem degreeTwoQuotientCoeff_summable_shift_square {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) :
    Summable fun n : ℕ => ‖degreeTwoQuotientCoeff g (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr
    (degreeTwoQuotientCoeff_weighted_summable hD (σ := 2) (by norm_num))
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _) (2 : ℝ), Real.rpow_two]
  exact (div_eq_mul_inv _ _).symm

/-- The arithmetic distribution's action on a test. -/
def fourierBoundaryPairing (q : ℕ → ℂ) (a : ℂ) (φ : ℝ → ℂ) : ℂ :=
  a * (∫ x : ℝ, φ x) - 4 * ∑' n : ℕ, q (n + 1) * cosineTestCoefficient φ (n + 1)

/-- The Fourier-side pairing of the normalized Maass logarithmic trace. -/
def fourierLogPairing (q : ℕ → ℂ) (a b : ℂ) (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  (a + b / (Real.log y : ℂ)) * (∫ x : ℝ, φ x) +
    4 * ∑' n : ℕ, q (n + 1) *
      ((kMoment 0 (2 * Real.pi * (n + 1) * y) / Real.log y : ℝ) : ℂ) *
        cosineTestCoefficient φ (n + 1)

/-- The infinite coefficient-side logarithmic trace; domination is uniform in frequency. -/
theorem tendsto_fourierLogPairing {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (a b : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Tendsto (fourierLogPairing q a b φ) (𝓝[>] 0) (𝓝 (fourierBoundaryPairing q a φ)) := by
  obtain ⟨C, hC0, hC⟩ := cosineTestCoefficient_decay hφ hs
  let B := kMoment 0 1 + |Real.log (2 * Real.pi)| + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [kMoment_nonneg 0 1, abs_nonneg (Real.log (2 * Real.pi))]
  have hπ : 0 < 2 * Real.pi := by positivity
  let f : ℝ → ℕ → ℂ := fun y n => q (n + 1) *
    ((kMoment 0 (2 * Real.pi * (n + 1) * y) / Real.log y : ℝ) : ℂ) *
      cosineTestCoefficient φ (n + 1)
  have hlim (n : ℕ) : Tendsto (fun y => f y n) (𝓝[>] 0)
      (𝓝 (-(q (n + 1) * cosineTestCoefficient φ (n + 1)))) := by
    have hn : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_kMoment_zero_mul_div_log hn)
    simpa only [f, Function.comp_def, ofReal_neg, ofReal_one, mul_neg_one, neg_mul] using
      (ht.const_mul (q (n + 1))).mul_const (cosineTestCoefficient φ (n + 1))
  have hb : ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      ‖f y n‖ ≤ (‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) * (B * C) := by
    have hy0 : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hcy : Tendsto (fun y : ℝ => (2 * Real.pi) * y) (𝓝[>] 0) (𝓝 0) := by
      simpa only [id, mul_zero] using hy0.const_mul (2 * Real.pi)
    filter_upwards [self_mem_nhdsWithin,
      hcy.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      Real.tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot (-1))] with y hy hy1 hlog
    intro n
    have hr : (2 * Real.pi) * y ≤ 2 * Real.pi * ((n : ℝ) + 1) * y := by
      apply mul_le_mul_of_nonneg_right _ hy.le
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hk := kMoment_zero_div_log_bound hπ hy hy1.le hlog hr
    have ht := hC ((n : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    dsimp only [f]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖q (n + 1)‖ * |kMoment 0 (2 * Real.pi * (↑n + 1) * y) / Real.log y| *
          ‖cosineTestCoefficient φ (↑n + 1)‖ ≤
          (‖q (n + 1)‖ * B) * (C / ((n : ℝ) + 1) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) ht
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB)
      _ = _ := by push_cast; ring
  have ht := tendsto_tsum_of_dominated_convergence (hq.mul_right (B * C)) hlim hb
  simp only [tsum_neg] at ht
  have hi : Tendsto (fun y : ℝ => (Real.log y : ℂ)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero)
    simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using hh
  have hc : Tendsto (fun y : ℝ => (a + b / (Real.log y : ℂ)) * (∫ x : ℝ, φ x))
      (𝓝[>] 0) (𝓝 (a * (∫ x : ℝ, φ x))) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds.add (hi.const_mul b)).mul_const (∫ x : ℝ, φ x)
  change Tendsto (fun y => fourierLogPairing q a b φ y) _ _
  simpa only [fourierLogPairing, fourierBoundaryPairing, f, mul_neg, ← sub_eq_add_neg] using
    hc.add (ht.const_mul 4)

/-- The original cubic datum supplies every coefficient estimate required for the trace. -/
theorem degreeTwoQuotient_tendsto_fourierLogPairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (a b : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Tendsto (fourierLogPairing (degreeTwoQuotientCoeff g) a b φ) (𝓝[>] 0)
      (𝓝 (fourierBoundaryPairing (degreeTwoQuotientCoeff g) a φ)) :=
  tendsto_fourierLogPairing (degreeTwoQuotientCoeff_summable_shift_square hD) a b hφ hs

end RHTower.WeilHigherDenominator
