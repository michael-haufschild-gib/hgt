import GaloisForLFunctions.RenormalizedIntersectionTheory.TheSparseFlipHasAnEventuallyPositiveHarmonicMean

/-!
# Regular variation of sparse signed harmonic means

Integer-horizon signed recovery transfers to real logarithmic horizons because
`log ⌊exp u⌋ / u → 1`. The positive divisor mean supplies both uniform growth
and the exact scale ratio of the original signed mean.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem tendsto_log_floor_exp_div :
    Tendsto (fun u : ℝ => Real.log (⌊Real.exp u⌋₊ : ℕ) / u) atTop (𝓝 1) := by
  have hN : Tendsto (fun u : ℝ => ⌊Real.exp u⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hratio : Tendsto (fun u : ℝ => (⌊Real.exp u⌋₊ : ℝ) / Real.exp u) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop
  have hlog : Tendsto (fun u : ℝ => Real.log ((⌊Real.exp u⌋₊ : ℝ) / Real.exp u)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hsmall := hlog.div_atTop (tendsto_id : Tendsto (fun u : ℝ => u) atTop atTop)
  have h : Tendsto (fun u : ℝ => 1 +
      Real.log ((⌊Real.exp u⌋₊ : ℝ) / Real.exp u) / u) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hsmall :
      Tendsto (fun u : ℝ => 1 + Real.log ((⌊Real.exp u⌋₊ : ℝ) / Real.exp u) / u)
        atTop (𝓝 (1 + 0)))
  apply h.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop (1 : ℕ)),
    eventually_gt_atTop (0 : ℝ)] with u hNu hu
  have hNu0 : (0 : ℝ) < (⌊Real.exp u⌋₊ : ℕ) := by exact_mod_cast hNu
  rw [Real.log_div hNu0.ne' (Real.exp_pos u).ne', Real.log_exp]
  field_simp [hu.ne']
  ring

/-- Real-horizon signed recovery has the same factor two as the integer identity. -/
theorem tendsto_real_signedMean_mul_div_positiveDivisorMean (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun u : ℝ => u * realLogHarmonicSum (primeSetFlip P) u /
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u) atTop (𝓝 2) := by
  have hN : Tendsto (fun u : ℝ => ⌊Real.exp u⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hlogN : Tendsto (fun u : ℝ => Real.log (⌊Real.exp u⌋₊ : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hratio := (tendsto_signedMean_mul_log_div_positiveDivisorMean P hP).comp hN
  have h := hratio.div tendsto_log_floor_exp_div (by norm_num)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [hlogN.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with u hlogu hu
  have hlogu0 : 0 < Real.log (⌊Real.exp u⌋₊ : ℕ) := zero_lt_one.trans_le hlogu
  have hG : 0 < realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u :=
    zero_lt_one.trans_le
      (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  change (realLogHarmonicSum (primeSetFlip P) u * Real.log (⌊Real.exp u⌋₊ : ℕ) /
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u) /
      (Real.log (⌊Real.exp u⌋₊ : ℕ) / u) = _
  field_simp [hu.ne', hlogu0.ne', hG.ne']

/-- Every logarithmic power below one is negligible relative to the sparse signed mean. -/
theorem tendsto_real_sparse_signedMean_div_rpow_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : α < 1) :
    Tendsto (fun u : ℝ => realLogHarmonicSum (primeSetFlip P) u / u ^ α) atTop atTop := by
  have hpositive := tendsto_positive_divisor_harmonicMean_div_rpow_atTop P hP
    (show 1 + α < 2 by linarith only [hα])
  apply tendsto_atTop_mono' atTop ?_ hpositive
  have hratio := (Metric.tendsto_nhds.mp
    (tendsto_real_signedMean_mul_div_positiveDivisorMean P hP)) 1 (by norm_num)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with u hR hu
  have hG : 0 < realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u :=
    zero_lt_one.trans_le
      (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  rw [Real.dist_eq] at hR
  have hR1 : 1 ≤ u * realLogHarmonicSum (primeSetFlip P) u /
      realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u := by
    have h := (abs_lt.mp hR).1
    linarith only [h]
  have hbound := (le_div_iff₀ hG).mp hR1
  simp only [one_mul] at hbound
  calc
    realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u / u ^ (1 + α) =
        (realLogHarmonicSum (signDivisorCount (primeSetFlip P)) u / u) / u ^ α := by
      rw [Real.rpow_add hu, Real.rpow_one, div_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      ((div_le_iff₀ hu).mpr (by simpa only [mul_comm] using hbound)) (Real.rpow_nonneg hu.le _)

/-- Sparse signed harmonic means tend to positive infinity at real logarithmic horizons. -/
theorem tendsto_real_sparse_signedMean_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    Tendsto (realLogHarmonicSum (primeSetFlip P)) atTop atTop := by
  simpa only [Real.rpow_zero, div_one] using
    tendsto_real_sparse_signedMean_div_rpow_atTop P hP (by norm_num : (0 : ℝ) < 1)

/-- The signed harmonic mean of a zero-density prime flip is regularly varying with
index one in the logarithmic horizon, without a prescribed density-error rate. -/
theorem tendsto_sparse_signedMean_scale_ratio (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => realLogHarmonicSum (primeSetFlip P) (c * u) /
      realLogHarmonicSum (primeSetFlip P) u) atTop (𝓝 c) := by
  let L := realLogHarmonicSum (primeSetFlip P)
  let G := realLogHarmonicSum (signDivisorCount (primeSetFlip P))
  let R : ℝ → ℝ := fun u => u * L u / G u
  have hR : Tendsto R atTop (𝓝 2) := tendsto_real_signedMean_mul_div_positiveDivisorMean P hP
  have hscale : Tendsto (fun u : ℝ => c * u) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have h := (((hR.comp hscale).div hR (by norm_num)).mul
    (tendsto_positive_divisor_harmonicMean_ratio P hP hc)).div_const c
  have hvalue : ((2 : ℝ) / 2 * c ^ 2) / c = c := by field_simp [hc.ne']
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [(tendsto_real_sparse_signedMean_atTop P hP).eventually
    (eventually_gt_atTop (0 : ℝ)), eventually_gt_atTop (0 : ℝ)] with u hLu hu
  have hGu : 0 < G u := zero_lt_one.trans_le
    (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hu.le)
  have hGcu : 0 < G (c * u) := zero_lt_one.trans_le
    (one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) (mul_pos hc hu).le)
  change 0 < L u at hLu
  change ((c * u * L (c * u) / G (c * u)) / (u * L u / G u)) *
    (G (c * u) / G u) / c = L (c * u) / L u
  field_simp [hc.ne', hu.ne', hLu.ne', hGu.ne', hGcu.ne']

end GaloisForLFunctions.RenormalizedIntersectionTheory

