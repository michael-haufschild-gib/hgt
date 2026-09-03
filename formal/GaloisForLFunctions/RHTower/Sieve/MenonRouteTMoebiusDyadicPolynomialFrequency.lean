import GaloisForLFunctions.RHTower.Sieve.MenonRouteTMoebiusPolynomialFrequency
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusSharp
import GaloisForLFunctions.RHTower.Sieve.PolylogLimits

/-!
# Menon's medium Mobius atom on the polynomial frequency range

The polynomial-frequency sharp twisted Mertens estimate is transferred by Abel summation to the
literal truncated Mobius atom in a Heath--Brown dyadic box.  At every Perron abscissa `c >= 1`,
every fixed logarithmic power is saved uniformly for `|tau| <= N^24`, with exact Abel weight
`N^(1-c)` retained.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Menon's literal medium-Mobius estimate on the Perron half-plane: every fixed logarithmic
saving holds on sufficiently late dyadic blocks, uniformly through the full frequency range
`|tau| <= N^24`, and Abel summation retains the exact factor `N^(1-c)`. -/
theorem eventually_norm_LSeries_truncatedMoebius_dyadic_le_rpow_mul_log_rpow_neg_pow_twentyFour
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L : ℕ) (c tau : ℝ),
      1 ≤ c →
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        (((2 ^ q : ℕ) : ℝ)) ^ (1 - c) *
          (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
  obtain ⟨K, hK, hmainEventual⟩ :=
    exists_norm_sum_moebiusTwist_le_rate_pow_twentyFour
  rw [eventually_atTop] at hmainEventual
  obtain ⟨X0, hmain⟩ := hmainEventual
  have hdyadic : Tendsto (fun q : ℕ => (((2 ^ q : ℕ) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hdecayLimit : Tendsto (fun x : ℝ =>
      8 * K * ((Real.log x) ^ A *
        Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20))))) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_rpow_log_mul_exp_neg (c := A) (a := (1 : ℝ) / 20) (by norm_num)).const_mul
        (8 * K)
  have hreciprocalLimit : Tendsto (fun x : ℝ =>
      4 * ((Real.log x) ^ A * Real.exp (-((Real.log x) ^ (1 : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_rpow_log_mul_exp_neg (c := A) (a := (1 : ℝ)) (by norm_num)).const_mul 4
  have hdecay := hdecayLimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hreciprocal :=
    hreciprocalLimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hdyadic.eventually_ge_atTop X0,
    hdyadic.eventually hdecay, hdyadic.eventually hreciprocal,
    hdyadic.eventually_ge_atTop (2 : ℝ)] with q hX0 hdecayB hreciprocalB hB2
  intro L c tau hc hBL htau
  let Bn : ℕ := 2 ^ q
  let B : ℝ := (Bn : ℝ)
  have hB0 : (0 : ℝ) < B := by dsimp only [B, Bn]; positivity
  have hB1 : (1 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB2
  have hlogB0 : (0 : ℝ) < Real.log B := Real.log_pos hB1
  have hlogPow0 : (0 : ℝ) < (Real.log B) ^ A := Real.rpow_pos_of_pos hlogB0 _
  have hsharp : ∀ m : ℕ, Bn ≤ m →
      m ≤ min (2 ^ (q + 1)) (L + 1) →
      ‖∑ n ∈ Finset.range m, moebiusTwist tau n‖ ≤
        2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1 := by
    intro m hmB hmM
    have hmX0 : X0 ≤ (m : ℝ) := by
      have hBm : B ≤ (m : ℝ) := by
        dsimp only [B, Bn]
        exact_mod_cast hmB
      exact hX0.trans hBm
    have hm2Bn : m ≤ 2 * Bn := by
      calc
        m ≤ min (2 ^ (q + 1)) (L + 1) := hmM
        _ ≤ 2 ^ (q + 1) := min_le_left _ _
        _ = 2 * Bn := by simp only [Bn, pow_succ]; ring
    have hBm : B ≤ (m : ℝ) := by
      dsimp only [B, Bn]
      exact_mod_cast hmB
    have hm2B : (m : ℝ) ≤ 2 * B := by
      dsimp only [B, Bn]
      exact_mod_cast hm2Bn
    have hm0 : (0 : ℝ) < (m : ℝ) := hB0.trans_le hBm
    have hfreq : |tau| ≤ ((m : ℝ)) ^ (24 : ℕ) := by
      exact htau.trans ((pow_le_pow_left₀ hB0.le hBm) 24)
    have hraw := hmain (m : ℝ) hmX0 tau hfreq
    have hfloor : ⌊((m : ℝ))⌋₊ + 1 = m + 1 := by rw [Nat.floor_natCast]
    rw [hfloor] at hraw
    have hsum :
        ‖∑ n ∈ Finset.range m, moebiusTwist tau n‖ ≤
          K * (m : ℝ) * Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20))) + 1 := by
      calc
        ‖∑ n ∈ Finset.range m, moebiusTwist tau n‖ =
            ‖(∑ n ∈ Finset.range (m + 1), moebiusTwist tau n) - moebiusTwist tau m‖ := by
          rw [Finset.sum_range_succ, add_sub_cancel_right]
        _ ≤ ‖∑ n ∈ Finset.range (m + 1), moebiusTwist tau n‖ +
            ‖moebiusTwist tau m‖ := norm_sub_le _ _
        _ ≤ K * (m : ℝ) * Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20))) + 1 :=
          add_le_add hraw (norm_moebiusTwist_le_one tau m)
    have hlog : Real.log B ≤ Real.log (m : ℝ) := Real.log_le_log hB0 hBm
    have hlogBnonneg : (0 : ℝ) ≤ Real.log B := hlogB0.le
    have hpow : (Real.log B) ^ ((1 : ℝ) / 20) ≤
        (Real.log (m : ℝ)) ^ ((1 : ℝ) / 20) :=
      Real.rpow_le_rpow hlogBnonneg hlog (by norm_num)
    have hexp : Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20))) ≤
        Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) :=
      Real.exp_le_exp.2 (neg_le_neg hpow)
    have hrate :
        K * (m : ℝ) * Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20))) ≤
          2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) := by
      calc
        K * (m : ℝ) * Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20)))
            ≤ K * (2 * B) * Real.exp (-((Real.log (m : ℝ)) ^ ((1 : ℝ) / 20))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hm2B hK.le) (Real.exp_pos _).le
        _ ≤ K * (2 * B) * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = 2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) := by ring
    exact hsum.trans (by linarith)
  have hfactor := norm_LSeries_truncatedMoebius_dyadic_le_of_sharp_prefix
    (L := L) (q := q) (c := c) (τ := tau)
    (P := 2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1)
    (by simpa only [Bn] using hBL) (by linarith) hsharp
  have hdecayHalf :
      4 * K * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) ≤
        (1 / 2 : ℝ) * (Real.log B) ^ (-A) := by
    rw [Real.rpow_neg hlogB0.le]
    rw [show (1 / 2 : ℝ) * ((Real.log B) ^ A)⁻¹ =
      1 / (2 * (Real.log B) ^ A) by field_simp]
    rw [le_div_iff₀ (by positivity : 0 < 2 * (Real.log B) ^ A)]
    have hdecayB' : 8 * K * ((Real.log B) ^ A *
        Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20)))) < 1 := by
      simpa only [B, Bn] using hdecayB
    nlinarith
  have hreciprocalHalf : 2 / B ≤ (1 / 2 : ℝ) * (Real.log B) ^ (-A) := by
    have hexplog : Real.exp (-((Real.log B) ^ (1 : ℝ))) = 1 / B := by
      rw [Real.rpow_one, Real.exp_neg, Real.exp_log hB0]
      simp only [one_div]
    rw [Real.rpow_neg hlogB0.le]
    rw [show (1 / 2 : ℝ) * ((Real.log B) ^ A)⁻¹ =
      1 / (2 * (Real.log B) ^ A) by field_simp]
    rw [le_div_iff₀ (by positivity : 0 < 2 * (Real.log B) ^ A)]
    have hreciprocalB' : 4 * ((Real.log B) ^ A *
        Real.exp (-((Real.log B) ^ (1 : ℝ)))) < 1 := by
      simpa only [B, Bn] using hreciprocalB
    rw [hexplog] at hreciprocalB'
    calc
      2 / B * (2 * (Real.log B) ^ A) =
          4 * ((Real.log B) ^ A * (1 / B)) := by ring
      _ ≤ 1 := hreciprocalB'.le
  have hweight : B ^ (-(1 : ℝ)) = 1 / B := by
    rw [Real.rpow_neg_one]
    simp only [one_div]
  have hfinal :
      2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
          B ^ (-(1 : ℝ)) ≤
        (Real.log B) ^ (-A) := by
    rw [hweight]
    have hBne : B ≠ 0 := ne_of_gt hB0
    have hid :
        2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
            (1 / B) =
          4 * K * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 2 / B := by
      field_simp
      ring
    rw [hid]
    linarith
  have hfactor' :
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
          B ^ (-c) := by
    simpa [B, Bn] using hfactor
  have hfinal' :
      2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
          B ^ (-(1 : ℝ)) ≤
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
    simpa only [B, Bn] using hfinal
  have hscale0 : 0 ≤ B ^ (1 - c) := Real.rpow_nonneg hB0.le _
  calc
    ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
          B ^ (-c) := hfactor'
    _ = B ^ (1 - c) *
        (2 * (2 * K * B * Real.exp (-((Real.log B) ^ ((1 : ℝ) / 20))) + 1) *
          B ^ (-(1 : ℝ))) := by
      rw [show B ^ (-c) = B ^ (1 - c) * B ^ (-(1 : ℝ)) by
        rw [← Real.rpow_add hB0]
        congr 1
        ring]
      ring
    _ ≤ B ^ (1 - c) * (Real.log B) ^ (-A) :=
      mul_le_mul_of_nonneg_left hfinal hscale0
    _ = (((2 ^ q : ℕ) : ℝ)) ^ (1 - c) *
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
      simp only [B, Bn]

/-- Abscissa-one specialization of the full Perron-half-plane estimate. -/
theorem eventually_norm_LSeries_truncatedMoebius_dyadic_le_log_rpow_neg_pow_twentyFour
    (A : ℝ) :
    ∀ᶠ q : ℕ in atTop, ∀ (L : ℕ) (tau : ℝ),
      2 ^ q ≤ L →
      |tau| ≤ (((2 ^ q : ℕ) : ℝ)) ^ (24 : ℕ) →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((1 : ℂ) + (tau : ℝ) * Complex.I)‖ ≤
        (Real.log (((2 ^ q : ℕ) : ℝ))) ^ (-A) := by
  filter_upwards [
    eventually_norm_LSeries_truncatedMoebius_dyadic_le_rpow_mul_log_rpow_neg_pow_twentyFour A]
    with q hq
  intro L tau hqL htau
  simpa using hq L 1 tau (by norm_num) hqL htau

end

end RHTower.Sieve
