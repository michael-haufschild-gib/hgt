import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortContinuousLimit

/-!
# Exact short Barban--Vehov main at the `49/100` schedule

The continuous endpoint error is bounded by `10/N²`; hence the literal harmonic-moment main has the
same exact limit as its continuous polynomial.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem fortyNine_short_scale_condition {N : ℕ} (hN : 8 ≤ N) :
    8 * (N ^ 49) ^ 2 ≤ N ^ 100 := by
  calc
    8 * (N ^ 49) ^ 2 = 8 * N ^ 98 := by ring
    _ ≤ N * N ^ 98 := Nat.mul_le_mul_right _ hN
    _ = N ^ 99 := by ring
    _ ≤ N ^ 99 * N := Nat.le_mul_of_pos_right _ (by omega)
    _ = N ^ 100 := by ring

private theorem log_pow_hundred_add_one_le_oneHundredOne_log
    {N : ℕ} (hN : 2 ≤ N) :
    Real.log ((N ^ 100 + 1 : ℕ) : ℝ) ≤ 101 * Real.log N := by
  have hpowPos : 0 < N ^ 100 := by positivity
  have hpowOne : 1 ≤ N ^ 100 := hpowPos
  have hle : N ^ 100 + 1 ≤ N ^ 101 := by
    calc
      N ^ 100 + 1 ≤ N ^ 100 + N ^ 100 := Nat.add_le_add_left hpowOne _
      _ = 2 * N ^ 100 := by ring
      _ ≤ N * N ^ 100 := Nat.mul_le_mul_right _ hN
      _ = N ^ 101 := by ring
  have hleft : (0 : ℝ) < ((N ^ 100 + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((N ^ 100 + 1 : ℕ) : ℝ) ≤ ((N ^ 101 : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hlog := Real.log_le_log hleft hcast
  rw [show ((N ^ 101 : ℕ) : ℝ) = (N : ℝ) ^ 101 by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hlog

private def fortyNineShortEndpointBound (N : ℕ) : ℝ :=
  ((((N ^ 49 : ℕ) : ℝ) * Real.log (N ^ 49 : ℕ)) ^ 2 *
          (1 / ((N ^ 100 : ℕ) : ℝ)) +
        2 * |(49 / 100 : ℝ) / (49 * Real.log N)| *
          ((((N ^ 49 : ℕ) : ℝ) * Real.log (N ^ 49 : ℕ)) ^ 2 *
            (2 * Real.log ((N ^ 100 + 1 : ℕ) : ℝ) / ((N ^ 100 : ℕ) : ℝ))) +
        ((49 / 100 : ℝ) / (49 * Real.log N)) ^ 2 *
          ((((N ^ 49 : ℕ) : ℝ) * Real.log (N ^ 49 : ℕ)) ^ 2 *
            (4 * Real.log ((N ^ 100 + 1 : ℕ) : ℝ) ^ 2 / ((N ^ 100 : ℕ) : ℝ)))) /
      Real.log (N ^ 49 : ℕ) ^ 2

private theorem fortyNineShortEndpointBound_le {N : ℕ} (hN : 8 ≤ N) :
    fortyNineShortEndpointBound N ≤ 10 / (N : ℝ) ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  let K := Real.log ((N ^ 100 + 1 : ℕ) : ℝ)
  let L := Real.log (N : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hN2)
  have hK0 : 0 ≤ K := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N ^ 100 + 1 by omega))
  have hK : K ≤ 101 * L := by
    simpa only [K, L] using log_pow_hundred_add_one_le_oneHundredOne_log hN2
  have hKsq : K ^ 2 ≤ (101 * L) ^ 2 := by nlinarith
  have hlinear : K / (25 * L) ≤ (101 / 25 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 25 * L)]
    nlinarith
  have hquad : K ^ 2 / (2500 * L ^ 2) ≤ (10201 / 2500 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 2500 * L ^ 2)]
    nlinarith
  have hbracket : 1 + K / (25 * L) + K ^ 2 / (2500 * L ^ 2) ≤ 10 := by
    linarith
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hlogN : Real.log (N : ℝ) ≠ 0 := by simpa only [L] using hL.ne'
  have hboundEq :
      fortyNineShortEndpointBound N =
        (1 / (N : ℝ) ^ 2) *
          (1 + K / (25 * L) + K ^ 2 / (2500 * L ^ 2)) := by
    rw [fortyNineShortEndpointBound,
      show Real.log (((N ^ 49 : ℕ) : ℝ)) = 49 * L by
        simp only [L, Nat.cast_pow, Real.log_pow]
        norm_num,
      show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
      show (((N ^ 100 : ℕ) : ℝ)) = (N : ℝ) ^ 100 by norm_num,
      abs_of_pos (div_pos (by norm_num) (mul_pos (by norm_num) hL))]
    dsimp only [K, L]
    field_simp [hNR, hlogN]
    ring
  rw [hboundEq]
  calc
    (1 / (N : ℝ) ^ 2) *
        (1 + K / (25 * L) + K ^ 2 / (2500 * L ^ 2)) ≤
      (1 / (N : ℝ) ^ 2) * 10 :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = 10 / (N : ℝ) ^ 2 := by ring

/-- Uniform endpoint-replacement rate at the exact natural-power schedule. -/
theorem abs_barbanVehovShortEnergyMain_sub_continuous_fortyNine_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovShortEnergyMain
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) -
      barbanVehovShortEnergyContinuous
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)| ≤
      10 / (N : ℝ) ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hM : 1 < N ^ 49 := by
    have hpow : N ≤ N ^ 49 := by
      calc
        N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hNpos 48)
        _ = N ^ 49 := by ring
    omega
  have hraw := abs_barbanVehovShortEnergyMain_sub_continuous_le
    ((49 / 100 : ℝ) / (49 * Real.log N)) hM
      (fortyNine_short_scale_condition hN)
  exact hraw.trans (by
    simpa only [fortyNineShortEndpointBound] using fortyNineShortEndpointBound_le hN)

private theorem tendsto_ten_div_nat_sq_zero :
    Tendsto (fun N : ℕ => (10 : ℝ) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  have hten : Tendsto (fun N : ℕ => (10 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmul := hten.mul hone
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hNR]

/-- Literal harmonic-moment short main at reciprocal `49/100` tuning. -/
theorem tendsto_barbanVehovShortEnergyMain_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      barbanVehovShortEnergyMain
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 (7782751 / 5880000 : ℝ)) := by
  let A : ℕ → ℝ := fun N =>
    barbanVehovShortEnergyMain
      ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)
  let C : ℕ → ℝ := fun N =>
    barbanVehovShortEnergyContinuous
      ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)
  have herr : Tendsto (fun N : ℕ => A N - C N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_ten_div_nat_sq_zero
    filter_upwards [eventually_ge_atTop 8] with N hN
    rw [Real.norm_eq_abs]
    simpa only [A, C] using
      abs_barbanVehovShortEnergyMain_sub_continuous_fortyNine_le hN
  have hc : Tendsto C atTop (𝓝 (7782751 / 5880000 : ℝ)) := by
    simpa only [C] using tendsto_barbanVehovShortEnergyContinuous_fortyNine_reciprocal
  have hadd := herr.add hc
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards with N
  dsimp only [A, C]
  ring

/-- Literal evaluated short lcm energy differs from its harmonic main by `O(N⁻²)`. -/
theorem abs_barbanVehovShortEnergyLcm_sub_main_fortyNine_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovShortEnergyLcm
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) -
      barbanVehovShortEnergyMain
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)| ≤
      10 / (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := by omega
  have hM : 1 < N ^ 49 := by
    have hpow : N ≤ N ^ 49 := by
      calc
        N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hNpos 48)
        _ = N ^ 49 := by ring
    omega
  have hraw := abs_barbanVehovShortEnergyLcm_sub_main_le
    ((49 / 100 : ℝ) / (49 * Real.log N)) hM
      (fortyNine_short_scale_condition hN)
  exact hraw.trans (by
    simpa only [fortyNineShortEndpointBound] using fortyNineShortEndpointBound_le hN)

/-- Actual evaluated short lcm detector at reciprocal `49/100` tuning. -/
theorem tendsto_barbanVehovShortEnergyLcm_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      barbanVehovShortEnergyLcm
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 (7782751 / 5880000 : ℝ)) := by
  let E : ℕ → ℝ := fun N =>
    barbanVehovShortEnergyLcm
      ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)
  let A : ℕ → ℝ := fun N =>
    barbanVehovShortEnergyMain
      ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)
  have herr : Tendsto (fun N : ℕ => E N - A N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_ten_div_nat_sq_zero
    filter_upwards [eventually_ge_atTop 8] with N hN
    rw [Real.norm_eq_abs]
    simpa only [E, A] using abs_barbanVehovShortEnergyLcm_sub_main_fortyNine_le hN
  have ha : Tendsto A atTop (𝓝 (7782751 / 5880000 : ℝ)) := by
    simpa only [A] using tendsto_barbanVehovShortEnergyMain_fortyNine_reciprocal
  have hadd := herr.add ha
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards with N
  dsimp only [E, A]
  ring

end

end RHTower.Sieve
