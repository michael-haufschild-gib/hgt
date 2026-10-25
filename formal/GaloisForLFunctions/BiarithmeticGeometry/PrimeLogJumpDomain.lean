import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Energy
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The domain of positive prime-log jump forms

In the ordinary Lebesgue translation representation every nonzero vector has a positive
limiting jump cost. Consequently the positive prime-log jump form has full domain exactly
for summable weights; otherwise its finite-energy domain consists only of zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace NNReal
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Translation matrix coefficients vanish at infinity for every ordinary real L² vector. -/
theorem tendsto_physical_autocorr_zero (q : Velocity) :
    Tendsto (autocorr q) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := 2 * ‖q‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := min 1 (ε / (2 * C))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (mul_pos (by norm_num) hC))
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (E := ℝ) (F := ℝ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)
  obtain ⟨r, ⟨g, hrg, hgc, _⟩, hdist⟩ := hdense.exists_dist_lt q hδ
  have hqr : ‖q-r‖ < δ := by simpa only [dist_eq_norm] using hdist
  have hr : ‖r‖ ≤ ‖q‖ + 1 := by
    have htri : ‖r‖ ≤ ‖q‖ + ‖q-r‖ := by
      simpa only [norm_sub_rev] using norm_le_insert' r q
    have hd1 := min_le_left (1 : ℝ) (ε / (2 * C))
    linarith only [htri, hqr, hd1]
  obtain ⟨D, hD, hsupport⟩ := exists_pos_autocorr_support_radius hgc
  refine ⟨D + 1, fun t ht => ?_⟩
  have hrgzero : autocorr r t = 0 := by
    rw [autocorr_congr_ae hrg]
    apply hsupport
    exact lt_of_lt_of_le (by linarith only [ht]) (le_abs_self t)
  have herror := autocorr_sub_le_L2_norms q r t
  rw [hrgzero, sub_zero] at herror
  have hfactor : ‖q‖ + ‖r‖ ≤ C := by dsimp [C]; linarith only [hr]
  have hsmall : C * ‖q-r‖ < ε := by
    have hbound : ‖q-r‖ < ε / (2 * C) := hqr.trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ (mul_pos (by norm_num) hC)).mp hbound
    linarith only [hh, hε]
  simpa only [dist_zero_right, Real.norm_eq_abs] using
    herror.trans_lt ((mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans_lt hsmall)

/-- Squared cost of a physical translation. -/
def physicalJumpSquare (q : Velocity) (t : ℝ) : ℝ := ‖q - physicalTranslation t q‖ ^ 2

theorem physicalJumpSquare_eq (q : Velocity) (t : ℝ) :
    physicalJumpSquare q t = 2 * ‖q‖ ^ 2 - 2 * autocorr q t := by
  rw [physicalJumpSquare, norm_sub_sq_real, physicalTranslation_norm,
    ← autocorr_eq_inner_physicalTranslation]
  ring

theorem physicalJumpSquare_nonneg (q : Velocity) (t : ℝ) : 0 ≤ physicalJumpSquare q t :=
  sq_nonneg _

theorem physicalJumpSquare_le (q : Velocity) (t : ℝ) :
    physicalJumpSquare q t ≤ 4 * ‖q‖ ^ 2 := by
  have hnorm := norm_sub_le q (physicalTranslation t q)
  rw [physicalTranslation_norm] at hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  dsimp [physicalJumpSquare]
  nlinarith only [hsq]

/-- Prime logarithms escape to infinity, so every nonzero vector has a positive limiting cost. -/
theorem tendsto_primeJumpSquare (q : Velocity) :
    Tendsto (fun p : Nat.Primes => physicalJumpSquare q (Real.log (p : ℝ)))
      cofinite (𝓝 (2 * ‖q‖ ^ 2)) := by
  have hcorr := (tendsto_physical_autocorr_zero q).comp
    HTGeometry.tendsto_primeRealLog_cofinite_atTop
  simpa only [physicalJumpSquare_eq, Function.comp_apply, mul_zero, sub_zero] using
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hcorr)

/-- Exact finite-energy domain of every nonnegative prime-log jump weighting. -/
theorem primeJump_summable_iff (w : Nat.Primes → ℝ≥0) (q : Velocity) :
    Summable (fun p : Nat.Primes => (w p : ℝ) * physicalJumpSquare q (Real.log (p : ℝ))) ↔
      Summable (fun p : Nat.Primes => (w p : ℝ)) ∨ q = 0 := by
  constructor
  · intro hs
    by_cases hq : q = 0
    · exact Or.inr hq
    · apply Or.inl
      have hn : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
      have hevent : ∀ᶠ p : Nat.Primes in cofinite,
          ‖q‖ ^ 2 < physicalJumpSquare q (Real.log (p : ℝ)) :=
        (tendsto_order.mp (tendsto_primeJumpSquare q)).1 _ (by linarith only [hn])
      apply (hs.mul_left (1 / ‖q‖ ^ 2)).of_norm_bounded_eventually
      filter_upwards [hevent] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (w p).coe_nonneg]
      have hbound := mul_le_mul_of_nonneg_left hp.le (w p).coe_nonneg
      calc
        _ ≤ ((w p : ℝ) * physicalJumpSquare q (Real.log (p : ℝ))) / ‖q‖ ^ 2 :=
          (le_div_iff₀ hn).mpr hbound
        _ = _ := by ring
  · rintro (hw | rfl)
    · apply (hw.mul_left (4 * ‖q‖ ^ 2)).of_norm_bounded
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (w p).coe_nonneg
        (physicalJumpSquare_nonneg q _))]
      exact (mul_le_mul_of_nonneg_left (physicalJumpSquare_le q _) (w p).coe_nonneg).trans_eq
        (by ring)
    · simp [physicalJumpSquare]

/-- In the full-domain case the form has an explicit uniform bound. -/
theorem primeJump_tsum_le (w : Nat.Primes → ℝ≥0)
    (hw : Summable (fun p : Nat.Primes => (w p : ℝ))) (q : Velocity) :
    (∑' p : Nat.Primes, (w p : ℝ) * physicalJumpSquare q (Real.log (p : ℝ))) ≤
      4 * (∑' p : Nat.Primes, (w p : ℝ)) * ‖q‖ ^ 2 := by
  have hj := (primeJump_summable_iff w q).mpr (Or.inl hw)
  have hb := hw.mul_left (4 * ‖q‖ ^ 2)
  have hle : ∀ p : Nat.Primes,
      (w p : ℝ) * physicalJumpSquare q (Real.log (p : ℝ)) ≤ (4 * ‖q‖ ^ 2) * (w p : ℝ) :=
    fun p => (mul_le_mul_of_nonneg_left (physicalJumpSquare_le q _) (w p).coe_nonneg).trans_eq
      (by ring)
  have h := hj.tsum_le_tsum hle hb
  rw [tsum_mul_left] at h
  nlinarith only [h]

end GaloisForLFunctions.BiarithmeticGeometry
