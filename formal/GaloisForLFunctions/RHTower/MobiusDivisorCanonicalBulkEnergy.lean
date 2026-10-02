import GaloisForLFunctions.RHTower.MobiusDivisorEndpointBulkEnergy
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingCoreObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadAsymptotic

/-!
# Canonical finite-core physical energy escapes every logarithmic scale

The proved negative moving-head asymptotic and uniform source regularity
force energy on intervals ending at the original integer cutoffs. This
rules out a polylogarithmic whole-ray norm controller along the literal
square-root prime cores. It gives no bound for the compensated full source.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

private theorem canonical_head (N : ℕ) (hN : 2 ≤ N) :
    mobiusDivisorContinuousHead (criticalMovingSquareCore N) N =
      criticalMovingPrimeHead N := by
  rw [mobiusDivisorContinuousHead_nat, criticalMovingPrimeHead_eq_selectionFibre N hN]
  intro p hp
  exact (mem_filter.mp (mem_filter.mp hp).1).2

private theorem log_power_div_nat_tendsto_zero (j : ℕ) :
    Tendsto (fun N : ℕ => Real.log N ^ j / (N : ℝ)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one, pow_one, Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop (j : ℝ) (s := 1) zero_lt_one).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

/-- A positive multiple of `N / log(N)^6` is forced by the literal canonical source. -/
theorem mobiusDivisorCanonicalBulkEnergy_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * N / Real.log N ^ (6 : ℕ) ≤
        mobiusDivisorDilationMean (criticalMovingSquareCore N) 1 := by
  let b := divisorHarmonicBoundary / 6
  have hb : 0 < b := by dsimp [b]; exact div_pos divisorHarmonicBoundary_pos (by norm_num)
  have hgap : -(divisorHarmonicBoundary / 3) < -b := by
    dsimp [b]
    linarith only [divisorHarmonicBoundary_pos]
  have ht := tendsto_criticalMovingPrimeHead_pointwise_scaled.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hev := ht.eventually (Iio_mem_nhds hgap)
  refine ⟨b^3/192, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 : ℕ)] with N hval hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hrpow : (N : ℝ) ^ (3/2 : ℝ) = (N : ℝ) * Real.sqrt N := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hN0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  change criticalMovingPrimeHead N * Real.log N ^ (2 : ℕ) /
    (N : ℝ) ^ (3/2 : ℝ) < -b at hval
  rw [hrpow] at hval
  have hm := (div_lt_iff₀ (mul_pos hN0 hs)).mp hval
  let B := b * (N : ℝ) * Real.sqrt N / Real.log N ^ (2 : ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hhead : mobiusDivisorContinuousHead (criticalMovingSquareCore N) N ≤ -B := by
    rw [canonical_head N hN]
    dsimp [B]
    rw [← neg_div]
    apply (le_div_iff₀ (pow_pos hl 2)).mpr
    linarith only [hm]
  have hbulk := mobiusDivisorDilationMean_endpoint_lower
    (criticalMovingSquareCore N) N hN hB hhead
  have heq : B^3 / (192 * Real.sqrt N * (N : ℝ)^3) =
      (b^3/192) * N / Real.log N ^ (6 : ℕ) := by
    dsimp [B]
    field_simp
    ring_nf
    rw [Real.sq_sqrt hN0.le]
  rwa [heq] at hbulk

/-- Every fixed logarithmic energy controller fails on all sufficiently large canonical cores. -/
theorem mobiusDivisorCanonicalBulkEnergy_exceeds_log_power (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, C * Real.log N ^ k <
      mobiusDivisorDilationMean (criticalMovingSquareCore N) 1 := by
  obtain ⟨c, hc, henergy⟩ := mobiusDivisorCanonicalBulkEnergy_lower
  let K := max C 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : C ≤ K := by dsimp [K]; linarith [le_max_left C 0]
  have hz := log_power_div_nat_tendsto_zero (k+6)
  have hsmall := hz.eventually (Iio_mem_nhds (div_pos hc hK))
  filter_upwards [henergy, hsmall, eventually_ge_atTop (2 : ℕ)] with N he hs hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  change Real.log N ^ (k+6) / (N : ℝ) < c/K at hs
  have hh := (div_lt_div_iff₀ hN0 hK).mp hs
  rw [pow_add] at hh
  have hcomp : C * Real.log N ^ k < c * N / Real.log N ^ (6 : ℕ) := by
    apply (lt_div_iff₀ (pow_pos hl 6)).mpr
    calc
      _ ≤ K * (Real.log N ^ k * Real.log N ^ (6 : ℕ)) := by
        nlinarith only [mul_le_mul_of_nonneg_right hCK
          (show 0 ≤ Real.log N ^ k * Real.log N ^ (6 : ℕ) by positivity)]
      _ < _ := by nlinarith only [hh]
  exact hcomp.trans_le he

end RHTower
