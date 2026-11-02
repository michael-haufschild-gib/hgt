import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanControlsItsLaplaceTransform
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHarmonicMeanVariesRegularly

/-!
# Uniform harmonic ratios of sparse prime flips

Positive divisor means have uniform power bounds. Signed recovery transfers
these bounds to the prime flip itself, simultaneously over every larger scale.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

/-- Beyond one logarithmic horizon, all dilation factors obey the power bounds
of index one, with arbitrarily small exponent loss. -/
theorem exists_sparse_signedMean_uniform_power_comparison (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u c : ℝ, U ≤ u → 1 ≤ c →
      (1 / 6) * c ^ (1 - ε) * realLogHarmonicSum (primeSetFlip P) u ≤
        realLogHarmonicSum (primeSetFlip P) (c * u) ∧
      realLogHarmonicSum (primeSetFlip P) (c * u) ≤
        6 * c ^ (1 + ε) * realLogHarmonicSum (primeSetFlip P) u := by
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let L := realLogHarmonicSum (primeSetFlip P)
  obtain ⟨U₁, hU₁, hpower⟩ := exists_positiveDivisorMean_uniform_power_comparison P hP hε
  have hratio := (Metric.tendsto_nhds.mp
    (tendsto_real_signedMean_mul_div_positiveDivisorMean P hP)) 1 (by norm_num)
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp hratio
  refine ⟨max U₁ U₂, hU₁.trans (le_max_left _ _), fun u c huU hc1 => ?_⟩
  have hu1 : 1 ≤ u := hU₁.trans ((le_max_left _ _).trans huU)
  have hu : 0 < u := zero_lt_one.trans_le hu1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hucu : u ≤ c * u := by nlinarith only [hc1, hu]
  have hratio_bounds (v : ℝ) (huv : u ≤ v) : G v ≤ v * L v ∧ v * L v ≤ 3 * G v := by
    have hv : 0 < v := hu.trans_le huv
    have hG : 0 < G v := zero_lt_one.trans_le
      (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hv.le)
    have h := hU₂ v (((le_max_right _ _).trans huU).trans huv)
    rw [Real.dist_eq] at h
    have hlo : 1 ≤ v * L v / G v := by linarith only [(abs_lt.mp h).1]
    have hhi : v * L v / G v ≤ 3 := by linarith only [(abs_lt.mp h).2]
    exact ⟨by simpa only [one_mul] using (le_div_iff₀ hG).mp hlo,
      (div_le_iff₀ hG).mp hhi⟩
  have hbase := hratio_bounds u le_rfl
  have hfar := hratio_bounds (c * u) hucu
  have hpow := hpower u c ((le_max_left _ _).trans huU) hc1
  change (1 / 2) * c ^ (2 - ε) * G u ≤ G (c * u) ∧
    G (c * u) ≤ 2 * c ^ (2 + ε) * G u at hpow
  have hsplitlo : c ^ (2 - ε) = c * c ^ (1 - ε) := by
    rw [show 2 - ε = 1 + (1 - ε) by ring, Real.rpow_add hc, Real.rpow_one]
  have hsplithi : c ^ (2 + ε) = c * c ^ (1 + ε) := by
    rw [show 2 + ε = 1 + (1 + ε) by ring, Real.rpow_add hc, Real.rpow_one]
  change (1 / 6) * c ^ (1 - ε) * L u ≤ L (c * u) ∧
    L (c * u) ≤ 6 * c ^ (1 + ε) * L u
  constructor
  · have hw := mul_le_mul_of_nonneg_right hbase.2 (Real.rpow_nonneg hc.le (2 - ε))
    rw [hsplitlo] at hw hpow
    have hp : (u * c) * (c ^ (1 - ε) * L u) ≤ (u * c) * (6 * L (c * u)) := by
      nlinarith only [hw, hpow.1, hfar.1]
    have h := le_of_mul_le_mul_left hp (mul_pos hu hc)
    nlinarith only [h]
  · have hw := mul_le_mul_of_nonneg_right hbase.1 (Real.rpow_nonneg hc.le (2 + ε))
    rw [hsplithi] at hw hpow
    have hp : (u * c) * L (c * u) ≤ (u * c) * (6 * c ^ (1 + ε) * L u) := by
      nlinarith only [hw, hpow.2, hfar.2]
    exact le_of_mul_le_mul_left hp (mul_pos hu hc)

private theorem realLogHarmonicSum_log_nat (g : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    realLogHarmonicSum g (Real.log N) = gaugeHarmonicSum g N := by
  rw [realLogHarmonicSum, Real.exp_log (by exact_mod_cast hN)]
  simp

/-- Every earlier large integer horizon is bounded by a power of its logarithmic
scale relative to the final horizon, with one threshold for all pairs. -/
theorem exists_sparse_signedMean_uniform_earlier_bound (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 3 ≤ M ∧ ∀ m N : ℕ, M ≤ m → m ≤ N →
      gaugeHarmonicSum (primeSetFlip P) m ≤
        6 * (Real.log m / Real.log N) ^ (1 - ε) * gaugeHarmonicSum (primeSetFlip P) N := by
  obtain ⟨U, _, hscale⟩ := exists_sparse_signedMean_uniform_power_comparison P hP hε
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop U))
  refine ⟨max M₀ 3, le_max_right _ _, fun m N hmM hmN => ?_⟩
  have hm3 : 3 ≤ m := (le_max_right _ _).trans hmM
  have hm1 : 1 ≤ m := by omega
  have hN1 : 1 ≤ N := hm1.trans hmN
  have hlogm1 : 1 ≤ Real.log m := one_le_log_of_three_le hm3
  have hlogm : 0 < Real.log m := zero_lt_one.trans_le hlogm1
  have hlogs : Real.log m ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmN)
  have hlogN : 0 < Real.log N := hlogm.trans_le hlogs
  have hc : 1 ≤ Real.log N / Real.log m :=
    (le_div_iff₀ hlogm).mpr (by simpa only [one_mul] using hlogs)
  have h := (hscale (Real.log m) (Real.log N / Real.log m)
    (hM₀ m ((le_max_left _ _).trans hmM)) hc).1
  rw [div_mul_cancel₀ _ hlogm.ne', realLogHarmonicSum_log_nat _ hm1,
    realLogHarmonicSum_log_nat _ hN1] at h
  have hp : (Real.log m / Real.log N) ^ (1 - ε) *
      (Real.log N / Real.log m) ^ (1 - ε) = 1 := by
    rw [← Real.mul_rpow (div_nonneg hlogm.le hlogN.le) (div_nonneg hlogN.le hlogm.le),
      show (Real.log m / Real.log N) * (Real.log N / Real.log m) = 1 by
        field_simp [hlogm.ne', hlogN.ne'], Real.one_rpow]
  have hw := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 6 * (Real.log m / Real.log N) ^ (1 - ε) by positivity)
  have heq : (6 * (Real.log m / Real.log N) ^ (1 - ε)) *
      ((1 / 6) * (Real.log N / Real.log m) ^ (1 - ε) *
        gaugeHarmonicSum (primeSetFlip P) m) = gaugeHarmonicSum (primeSetFlip P) m := by
    calc
      _ = ((Real.log m / Real.log N) ^ (1 - ε) *
          (Real.log N / Real.log m) ^ (1 - ε)) * gaugeHarmonicSum (primeSetFlip P) m := by ring
      _ = _ := by rw [hp, one_mul]
  rw [heq] at hw
  exact hw

end GaloisForLFunctions.RenormalizedIntersectionTheory

