import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFourierBoundary
import GaloisForLFunctions.RHTower.MaassConverseLevelOne
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The weak logarithmic trace of the actual Maass function

The positive-height strip majorant justifies integrating the infinite series.
The coefficient-side boundary theorem then applies to the actual spatial pairing.
This pays the horizontal trace only; moving inversion and sparse-pole regularity
remain separate obligations.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower.BesselKZero RHTower.MaassBesselSeries
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

private lemma sterm_horizontal (q : ℕ → ℂ) (n : ℕ) (x y : ℝ) :
    sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I) =
      (q (n + 1) * ((y ^ (1 / 2 : ℝ) *
        kMoment 0 (2 * Real.pi * (n + 1) * y) : ℝ) : ℂ)) *
          (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) := by
  simp [sterm, bterm, yPart, xPart, trigFun, mul_assoc]

private lemma integrable_test_sterm (q : ℕ → ℂ) (n : ℕ) (y : ℝ)
    {φ : ℝ → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable fun x : ℝ => φ x * sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I) := by
  simp_rw [sterm_horizontal]
  apply Continuous.integrable_of_hasCompactSupport
  · exact hc.mul (by fun_prop)
  · exact hs.mul_right

/-- The genuine spatial cosine series pairs with the complete Fourier coefficient series. -/
theorem cosSeries_test_integral {q : ℕ → ℂ} (hq : PolyGrowth q)
    {φ : ℝ → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ) {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ, φ x * cosSeries q ((x : ℂ) + y * I)) =
      ∑' n : ℕ, (q (n + 1) * ((y ^ (1 / 2 : ℝ) *
        kMoment 0 (2 * Real.pi * (n + 1) * y) : ℝ) : ℂ)) *
          cosineTestCoefficient φ (n + 1) := by
  obtain ⟨u, hu, hbound⟩ := norm_sterm_le hq (1 / 2) 0 0 false (y₂ := y) hy
  have hint := hc.integrable_of_hasCompactSupport hs (μ := volume)
  have hsum : Summable fun n : ℕ => ∫ x : ℝ,
      ‖φ x * sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I)‖ := by
    refine (hu.mul_right (∫ x : ℝ, ‖φ x‖)).of_norm_bounded fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    calc
      (∫ x : ℝ, ‖φ x * sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I)‖) ≤
          ∫ x : ℝ, u n * ‖φ x‖ := by
        apply integral_mono (integrable_test_sterm q n y hc hs).norm (hint.norm.const_mul _)
        intro x
        dsimp only
        rw [norm_mul, mul_comm (u n)]
        exact mul_le_mul_of_nonneg_left (hbound n _ (by simp) (by simp)) (norm_nonneg _)
      _ = u n * (∫ x : ℝ, ‖φ x‖) := integral_const_mul _ _
  calc
    (∫ x : ℝ, φ x * cosSeries q ((x : ℂ) + y * I)) =
        ∫ x : ℝ, ∑' n : ℕ, φ x * sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [cosSeries, besselSeries, tsum_mul_left]
    _ = ∑' n : ℕ, ∫ x : ℝ, φ x * sterm q (1 / 2) 0 0 false n ((x : ℂ) + y * I) :=
      (integral_tsum_of_summable_integral_norm (fun n => integrable_test_sterm q n y hc hs) hsum).symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [cosineTestCoefficient_eq_integral hc hs, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [sterm_horizontal]
      ring

private lemma continuous_cosSeries_horizontal {q : ℕ → ℂ} (hq : PolyGrowth q)
    {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => cosSeries q ((x : ℂ) + y * I) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasFDerivAt_besselSeries_tsum hq (1 / 2) 0 0 false
    (z := (x : ℂ) + y * I) (by simpa using hy)).continuousAt.comp
      (f := fun t : ℝ => (t : ℂ) + y * I)
      (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ) + y * I) x)

/-- Pair the actual normalized Maass function with a compact test. -/
def maassLogPairing (q : ℕ → ℂ) (a b : ℂ) (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, φ x * maassFun q a b ((x : ℂ) + y * I) /
    ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)

/-- Spatial integration agrees with the Fourier pairing, retaining both endpoint terms. -/
theorem maassLogPairing_eq_fourierLogPairing {q : ℕ → ℂ} (hq : PolyGrowth q)
    (a b : ℂ) {φ : ℝ → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ)
    {y : ℝ} (hy : 0 < y) (hl : Real.log y ≠ 0) :
    maassLogPairing q a b φ y = fourierLogPairing q a b φ y := by
  have hint := hc.integrable_of_hasCompactSupport hs (μ := volume)
  have hS : Integrable fun x : ℝ => φ x * cosSeries q ((x : ℂ) + y * I) :=
    (hc.mul (continuous_cosSeries_horizontal hq hy)).integrable_of_hasCompactSupport hs.mul_right
  have he : (∫ x : ℝ, φ x * maassFun q a b ((x : ℂ) + y * I)) =
      4 * (∑' n : ℕ, (q (n + 1) * ((y ^ (1 / 2 : ℝ) *
        kMoment 0 (2 * Real.pi * (n + 1) * y) : ℝ) : ℂ)) *
          cosineTestCoefficient φ (n + 1)) +
        (b * ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
          a * ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) * (∫ x : ℝ, φ x) := by
    calc
      (∫ x : ℝ, φ x * maassFun q a b ((x : ℂ) + y * I)) =
          ∫ x : ℝ, (4 : ℂ) * (φ x * cosSeries q ((x : ℂ) + y * I)) +
            (b * ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
              a * ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) * φ x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [maassFun, constTerm, MaassBesselSeries.sqrtPart, MaassBesselSeries.sqrtLogPart]
        simp
        ring
      _ = _ := by
        rw [integral_add (hS.const_mul 4) (hint.const_mul _), integral_const_mul,
          integral_const_mul, cosSeries_test_integral hq hc hs hy]
  have hr : ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hy (1 / 2 : ℝ)).ne'
  have hlc : (Real.log y : ℂ) ≠ 0 := by exact_mod_cast hl
  have hsum : (∑' n : ℕ, (q (n + 1) * ((y ^ (1 / 2 : ℝ) *
      kMoment 0 (2 * Real.pi * (n + 1) * y) : ℝ) : ℂ)) *
        cosineTestCoefficient φ (n + 1)) / ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ) =
      ∑' n : ℕ, q (n + 1) *
        ((kMoment 0 (2 * Real.pi * (n + 1) * y) / Real.log y : ℝ) : ℂ) *
          cosineTestCoefficient φ (n + 1) := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    push_cast
    field_simp [hr, hlc]
  rw [maassLogPairing, integral_div, he]
  unfold fourierLogPairing
  rw [← hsum]
  let S := ∑' n : ℕ, (q (n + 1) * ((y ^ (1 / 2 : ℝ) *
    kMoment 0 (2 * Real.pi * (n + 1) * y) : ℝ) : ℂ)) *
      cosineTestCoefficient φ (n + 1)
  change (4 * S + (b * ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
      a * ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) * (∫ x : ℝ, φ x)) /
      ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ) =
    (a + b / (Real.log y : ℂ)) * (∫ x : ℝ, φ x) +
      4 * (S / ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ))
  simp only [ofReal_mul]
  field_simp [hr, hlc]
  ring

/-- The actual Maass function has the Fourier distribution as its horizontal log trace. -/
theorem tendsto_maassLogPairing {q : ℕ → ℂ} (hq : PolyGrowth q)
    (hsum : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (a b : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Tendsto (maassLogPairing q a b φ) (𝓝[>] 0) (𝓝 (fourierBoundaryPairing q a φ)) := by
  apply (tendsto_fourierLogPairing hsum a b hφ hs).congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with y hy hy1
  exact (maassLogPairing_eq_fourierLogPairing hq a b hφ.continuous hs hy
    (Real.log_neg hy hy1).ne).symm

/-- Original cubic data pay both summability and polynomial growth, without new premises. -/
theorem degreeTwoQuotient_tendsto_maassLogPairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (a b : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    Tendsto (maassLogPairing (degreeTwoQuotientCoeff g) a b φ) (𝓝[>] 0)
      (𝓝 (fourierBoundaryPairing (degreeTwoQuotientCoeff g) a φ)) := by
  exact tendsto_maassLogPairing
    (MaassConverseLevelOne.polyGrowth_of_summable fun _ hσ =>
      degreeTwoQuotientCoeff_weighted_summable hD hσ)
    (degreeTwoQuotientCoeff_summable_shift_square hD) a b hφ hs

end RHTower.WeilHigherDenominator
