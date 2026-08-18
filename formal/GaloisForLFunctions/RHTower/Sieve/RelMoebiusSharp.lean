import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The relative size of the sharp twisted Möbius bound

The disc contribution of a ladder step needs the cofactor polynomial compared with the *length* of
the cofactor block.  The comparison is antitone in the length, so a single value at the shortest
block bounds every step.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The sharp twisted Möbius majorant, relative to the cutoff. -/
def relMoebiusSharp (N : ℝ) : ℝ :=
  3 * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi
    + 1 / smoothRatio N + 1 / N

theorem moebiusSharpBound_eq_mul {N : ℝ} (hN : 0 < N) :
    moebiusSharpBound N = N * relMoebiusSharp N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hr0 : smoothRatio N ≠ 0 := ne_of_gt (smoothRatio_pos N)
  rw [moebiusSharpBound, relMoebiusSharp, smoothWidth]
  field_simp
  ring

theorem relMoebiusSharp_nonneg {N : ℝ} (hN : 0 < N) : 0 ≤ relMoebiusSharp N := by
  have h1 : (0 : ℝ) < smoothRatio N := smoothRatio_pos N
  rw [relMoebiusSharp]
  have h2 : (0 : ℝ) ≤ 3 * Real.exp (-(zeroFreeConst / 8192
      * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi := by positivity
  have h3 : (0 : ℝ) ≤ 1 / smoothRatio N := by positivity
  have h4 : (0 : ℝ) ≤ 1 / N := by positivity
  linarith

/-- **The relative majorant is antitone.** -/
theorem relMoebiusSharp_antitone {M N : ℝ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    relMoebiusSharp N ≤ relMoebiusSharp M := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hM0 hMN
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM
  have hlogMN : Real.log M ≤ Real.log N := Real.log_le_log hM0 hMN
  have hlogN : (0 : ℝ) ≤ Real.log N := le_trans hlogM hlogMN
  have hpow : (Real.log M) ^ ((1 : ℝ) / 20) ≤ (Real.log N) ^ ((1 : ℝ) / 20) :=
    Real.rpow_le_rpow hlogM hlogMN (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (Real.log M) ^ ((1 : ℝ) / 20) := Real.rpow_nonneg hlogM _
  have hzf := zeroFreeConst_pos
  have hexp : Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2))
      ≤ Real.exp (-(zeroFreeConst / 8192 * ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) := by
    refine Real.exp_le_exp.2 ?_
    have hsq : ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 ≤ ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 :=
      pow_le_pow_left₀ hpow0 hpow 2
    nlinarith [hsq, hzf]
  have hratio : smoothRatio M ≤ smoothRatio N := by
    rw [smoothRatio, smoothRatio]
    exact Real.exp_le_exp.2 hpow
  have hrM : (0 : ℝ) < smoothRatio M := smoothRatio_pos M
  have hinv : 1 / smoothRatio N ≤ 1 / smoothRatio M := one_div_le_one_div_of_le hrM hratio
  have hinvN : 1 / N ≤ 1 / M := one_div_le_one_div_of_le hM0 hMN
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfirst : 3 * Real.exp (-(zeroFreeConst / 8192
        * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi
      ≤ 3 * Real.exp (-(zeroFreeConst / 8192
        * ((Real.log M) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi := by
    refine div_le_div_of_nonneg_right ?_ hpi.le
    linarith [hexp]
  rw [relMoebiusSharp, relMoebiusSharp]
  linarith

/-- **The relative majorant vanishes.** -/
theorem tendsto_relMoebiusSharp : Tendsto relMoebiusSharp atTop (𝓝 0) := by
  have hzf := zeroFreeConst_pos
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hpow : Tendsto (fun N : ℝ => (Real.log N) ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlog
  have hsqpow : Tendsto (fun N : ℝ =>
      zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2) atTop atTop := by
    have h1 : Tendsto (fun N : ℝ => ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2) atTop atTop := by
      refine Filter.tendsto_atTop_mono' _ ?_ hpow
      filter_upwards [hpow.eventually_ge_atTop (1 : ℝ)] with N hN
      nlinarith [hN]
    have h2 : Tendsto (fun N : ℝ =>
        zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) h1
    exact h2.atTop_div_const (by norm_num)
  have t1 : Tendsto (fun N : ℝ =>
      3 * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2))
        / Real.pi) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsqpow).const_mul (3 : ℝ)
    have h2 := h.div_const Real.pi
    simpa using h2
  have t2 : Tendsto (fun N : ℝ => 1 / smoothRatio N) atTop (𝓝 0) :=
    tendsto_smoothRatio_atTop.const_div_atTop 1
  have t3 : Tendsto (fun N : ℝ => 1 / N) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have h := (t1.add t2).add t3
  rw [show (0 : ℝ) + 0 + 0 = 0 by norm_num] at h
  show Tendsto (fun N : ℝ => relMoebiusSharp N) atTop (𝓝 0)
  simpa only [relMoebiusSharp] using h

/-- **The cofactor polynomial at low frequency, relative to the block length.**  This is the form
`Sieve/LadderStepMajorant.discMajorant_sq_ge` consumes. -/
theorem exists_norm_logPoly_geomCofactorBlockAt_rel_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (B₀ j : ℕ) (Q η w Nmin : ℝ), 1 ≤ Q → 0 ≤ η → 1 ≤ Nmin →
      N₁ ≤ Nmin → Nmin ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) →
      K₀ ≤ contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
        + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
            + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) : ℕ) : ℝ) →
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ relMoebiusSharp Nmin * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) := by
  obtain ⟨K₀, N₁, hbound⟩ := exists_norm_logPoly_geomCofactorBlockAt_le
  refine ⟨K₀, N₁, ?_⟩
  intro B₀ j Q η w Nmin hQ hη hNmin hN₁ hNle hK hτ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  set N : ℝ := ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := le_trans hNmin hNle
  have hN0 : (0 : ℝ) < N := by linarith
  have hNfl : N ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) := by
    rw [hN]
    exact Nat.floor_le (by positivity)
  have hstep := hbound B₀ j Q η w hQ hη (le_trans hN₁ hNle) hK hτ
  rw [moebiusSharpBound_eq_mul hN0] at hstep
  refine hstep.trans ?_
  have hrel : relMoebiusSharp N ≤ relMoebiusSharp Nmin :=
    relMoebiusSharp_antitone hNmin hNle
  have hrel0 : (0 : ℝ) ≤ relMoebiusSharp Nmin := relMoebiusSharp_nonneg (by linarith)
  have hrelN0 : (0 : ℝ) ≤ relMoebiusSharp N := relMoebiusSharp_nonneg hN0
  calc N * relMoebiusSharp N ≤ ((B₀ : ℝ) / (Q * (1 + η) ^ j)) * relMoebiusSharp Nmin :=
        mul_le_mul hNfl hrel hrelN0 (by positivity)
    _ = relMoebiusSharp Nmin * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) := by ring

end

end RHTower.Sieve
