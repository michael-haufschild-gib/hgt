import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanVariesRegularly
import GaloisForLFunctions.RenormalizedIntersectionTheory.ThePositiveDivisorMeanControlsTheSignedPrimitive

/-!
# Recovering the signed mean from the positive divisor mean

The uniform lower bound on signed harmonic sums controls the negative prime-renewal
contribution. Positive divisor growth then turns the logarithmic error into a relative
error, even when the density of flipped primes tends to zero without a power rate.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

private theorem realLogHarmonicSum_log_nat (g : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    realLogHarmonicSum g (Real.log N) = gaugeHarmonicSum g N := by
  rw [realLogHarmonicSum, Real.exp_log (by exact_mod_cast hN)]
  simp

/-- The negative prime-renewal contribution costs only a logarithmic error, for every
prime pattern regardless of its density. -/
theorem exists_eventually_signedMean_le_positiveDivisorMean (P : Set ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      gaugeHarmonicSum (primeSetFlip P) N * Real.log N ≤
        2 * gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N +
          K * (1 + Real.log N) := by
  obtain ⟨K, hK, hrenewal⟩ := exists_abs_signed_flip_renewal_equation_le P
  let D := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  refine ⟨K + 8 + 2 * |D|, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hlog := Real.log_natCast_nonneg N
  have hmass : primeSetLogMass P N ≤ ∑ p ∈ Icc 1 N with p.Prime, Real.log p / p := by
    classical
    rw [primeSetLogMass, primeSetCutoff_eq_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
  have hmertens := (abs_le.mp (RHTower.Mertens.mertens_first_prime N hN)).2
  change (∑ p ∈ Icc 1 N with p.Prime, Real.log p / p) - Real.log N ≤ D at hmertens
  have hmean := (abs_le.mp (abs_positiveDivisorMean_sub_signedPolarMoment_le P N)).1
  have hnegative := neg_primeSetLogMass_le_flippedPrimeRenewalTerm P N
  have hsigned := (abs_le.mp (hrenewal N hN)).2
  have hDlog := mul_nonneg (abs_nonneg D) hlog
  nlinarith only [hmean, hnegative, hsigned, hmass, hmertens, le_abs_self D, hDlog, hlog]

private theorem tendsto_positiveDivisorMean_div_log_rpow_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : α < 2) :
    Tendsto (fun N : ℕ =>
      gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N / Real.log N ^ α) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_positive_divisor_harmonicMean_div_rpow_atTop P hP hα).comp hlog
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  change realLogHarmonicSum (signDivisorCount (primeSetFlip P)) (Real.log N) /
    Real.log N ^ α = _
  rw [realLogHarmonicSum_log_nat _ hN]

/-- A single positive-divisor ratio bounds every earlier signed harmonic mean. -/
theorem exists_eventually_uniform_signedMean_le_positiveDivisorMean (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
      gaugeHarmonicSum (primeSetFlip P) m ≤
        C * (gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N / Real.log N) := by
  let G := gaugeHarmonicSum (signDivisorCount (primeSetFlip P))
  obtain ⟨K, hK, hupper⟩ := exists_eventually_signedMean_le_positiveDivisorMean P
  obtain ⟨U, hU1, hcomp⟩ := exists_positive_divisor_harmonicMean_uniform_comparison P hP
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hupper.and ((hlog.eventually (eventually_ge_atTop U)).and
      (eventually_ge_atTop (1 : ℕ))))
  let C := 5 + 2 * K + Real.log M
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith only [hK, Real.log_natCast_nonneg M]
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ G N / Real.log N := by
    have h := tendsto_positiveDivisorMean_div_log_rpow_atTop P hP (by norm_num : (1 : ℝ) < 2)
    simpa only [Real.rpow_one] using h.eventually (eventually_ge_atTop (1 : ℝ))
  refine ⟨C, hC1, ?_⟩
  filter_upwards [eventually_ge_atTop M, hlarge] with N hMN hGN m hmN
  have hN := hM N hMN
  have hlogN : 0 < Real.log N := zero_lt_one.trans_le (hU1.trans hN.2.1)
  rcases le_or_gt M m with hMm | hmM
  · have hm := hM m hMm
    have hlogm1 : 1 ≤ Real.log m := hU1.trans hm.2.1
    have hlogm : 0 < Real.log m := zero_lt_one.trans_le hlogm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.2.2
    have hlogs : Real.log m ≤ Real.log N :=
      Real.log_le_log hm0 (by exact_mod_cast hmN)
    have hratio := hcomp (Real.log m) (Real.log N) hm.2.1 hlogs
    rw [realLogHarmonicSum_log_nat _ hm.2.2, realLogHarmonicSum_log_nat _ hN.2.2] at hratio
    have hsmall : gaugeHarmonicSum (primeSetFlip P) m ≤ 2 * (G m / Real.log m) + 2 * K := by
      have herror := mul_le_mul_of_nonneg_left
        (show 1 + Real.log m ≤ 2 * Real.log m by linarith only [hlogm1]) hK
      have hcancel : (2 * (G m / Real.log m) + 2 * K) * Real.log m =
          2 * G m + 2 * K * Real.log m := by field_simp [hlogm.ne']
      have hscaled : gaugeHarmonicSum (primeSetFlip P) m * Real.log m ≤
          (2 * (G m / Real.log m) + 2 * K) * Real.log m := by
        rw [hcancel]
        exact hm.1.trans (by nlinarith only [herror])
      exact le_of_mul_le_mul_left (a := Real.log m)
        (by simpa only [mul_comm] using hscaled) hlogm
    have hconst := mul_le_mul_of_nonneg_left hGN (show 0 ≤ 2 * K from mul_nonneg (by norm_num) hK)
    have hmargin := mul_nonneg (Real.log_natCast_nonneg M) (show 0 ≤ G N / Real.log N by linarith only [hGN])
    change G m / Real.log m ≤ 2 * (G N / Real.log N) at hratio
    change gaugeHarmonicSum (primeSetFlip P) m ≤ C * (G N / Real.log N)
    dsimp only [C]
    nlinarith only [hsmall, hratio, hconst, hmargin, hGN]
  · have hsmall : gaugeHarmonicSum (primeSetFlip P) m ≤ 1 + Real.log M := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [gaugeHarmonicSum, Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), sum_empty]
        linarith only [Real.log_natCast_nonneg M]
      · have habs := abs_gaugeHarmonicSum_le (primeSetFlip P) (abs_primeSetFlip_le P) m
        have hlogs := Real.log_le_log (by exact_mod_cast hm0 : (0 : ℝ) < m)
          (by exact_mod_cast hmM.le : (m : ℝ) ≤ M)
        linarith only [le_abs_self (gaugeHarmonicSum (primeSetFlip P) m), habs, hlogs]
    have hC : 1 + Real.log M ≤ C := by dsimp only [C]; linarith only [hK]
    exact hsmall.trans (hC.trans (le_mul_of_one_le_right (zero_le_one.trans hC1) hGN))

/-- At zero logarithmic prime density, the signed mean is asymptotic to twice the
positive divisor mean divided by the logarithmic horizon. -/
theorem tendsto_signedMean_mul_log_div_positiveDivisorMean (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (primeSetFlip P) N * Real.log N /
      gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N) atTop (𝓝 2) := by
  obtain ⟨C, hC1, hC⟩ := exists_eventually_uniform_signedMean_le_positiveDivisorMean P hP
  obtain ⟨K, hK, hKbound⟩ := exists_abs_signed_flip_renewal_equation_le P
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hGlim : Tendsto (fun N : ℕ =>
      gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N / Real.log N) atTop atTop := by
    simpa only [Real.rpow_one] using
      tendsto_positiveDivisorMean_div_log_rpow_atTop P hP (by norm_num : (1 : ℝ) < 2)
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hC, (Metric.tendsto_nhds.mp hP) (δ / (16 * C)) (by positivity),
    hGlim.eventually (eventually_ge_atTop (max 1 (8 * (K + 6) / δ))),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with N hCN hmass hGN hLN hN
  let L := Real.log N
  let G := gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N
  let S := gaugeHarmonicSum (primeSetFlip P) N
  let M := polarMoment (primeSetFlip P) N
  let A := primeSetLogMass P N
  let E := flippedPrimeRenewalTerm P N
  have hL : 0 < L := zero_lt_one.trans_le hLN
  have hV : 1 ≤ G / L := (le_max_left _ _).trans hGN
  have hG : 0 < G := hL.trans_le (by simpa only [one_mul] using (le_div_iff₀ hL).mp hV)
  have hA : 0 ≤ A := by
    unfold A primeSetLogMass
    exact sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
  have hEupper : E ≤ C * (G / L) * A := by
    calc
      E ≤ ∑ p ∈ primeSetCutoff P N, Real.log p / p * (C * (G / L)) := by
        apply sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_left (hCN (N / p) (Nat.div_le_self N p))
          (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _))
      _ = C * (G / L) * A := by
        rw [← sum_mul]
        change A * (C * (G / L)) = C * (G / L) * A
        ring
  have hEabs : |E| ≤ C * (G / L) * A := by
    have hnegative := neg_primeSetLogMass_le_flippedPrimeRenewalTerm P N
    change -A ≤ E at hnegative
    have hCV : 1 ≤ C * (G / L) := hC1.trans (le_mul_of_one_le_right hCpos.le hV)
    have hweight := mul_le_mul_of_nonneg_right hCV hA
    apply abs_le.mpr
    exact ⟨by nlinarith only [hnegative, hweight], hEupper⟩
  rw [Real.dist_eq, sub_zero] at hmass
  have hmass' : 8 * C * A ≤ δ * L := by
    have h := (div_lt_div_iff₀ (show 0 < 1 + L by linarith only [hLN])
      (show 0 < 16 * C by positivity)).mp ((le_abs_self _).trans_lt hmass)
    have hlogbound := mul_le_mul_of_nonneg_left
      (show 1 + L ≤ 2 * L by linarith only [hLN]) hδ.le
    change A * (16 * C) < δ * (1 + L) at h
    nlinarith only [h, hlogbound]
  have hLV : L * (G / L) = G := by field_simp [hL.ne']
  have hEsmall : 8 * |E| ≤ δ * G := by
    have h := mul_le_mul_of_nonneg_right hmass' (zero_le_one.trans hV)
    have heq : δ * L * (G / L) = δ * G := by rw [mul_assoc, hLV]
    rw [heq] at h
    nlinarith only [hEabs, h]
  have herrsmall : 4 * ((K + 6) * (1 + L)) ≤ δ * G := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hGN)
    have hweighted := mul_le_mul_of_nonneg_right h hL.le
    have herror := mul_le_mul_of_nonneg_left
      (show 1 + L ≤ 2 * L by linarith only [hLN]) (show 0 ≤ K + 6 by linarith only [hK])
    change 8 * (K + 6) * L ≤ (G / L * δ) * L at hweighted
    have heq : (G / L * δ) * L = δ * G := by field_simp [hL.ne']
    rw [heq] at hweighted
    nlinarith only [hweighted, herror]
  have hrenewal : |S * L - 2 * M + 2 * E| ≤ K * (1 + L) := hKbound N hN
  have hmean : |G - M| ≤ 3 + L := abs_positiveDivisorMean_sub_signedPolarMoment_le P N
  have hcombined : |S * L - 2 * G + 2 * E| ≤ (K + 6) * (1 + L) := by
    have htri := abs_add_le (S * L - 2 * M + 2 * E) (2 * (M - G))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm M G] at htri
    have heq : S * L - 2 * M + 2 * E + 2 * (M - G) = S * L - 2 * G + 2 * E := by ring
    rw [heq] at htri
    nlinarith only [hrenewal, hmean, htri, hLN]
  have herror : |S * L - 2 * G| ≤ δ / 2 * G := by
    have htri := abs_sub (S * L - 2 * G + 2 * E) (2 * E)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    have heq : S * L - 2 * G + 2 * E - 2 * E = S * L - 2 * G := by ring
    rw [heq] at htri
    nlinarith only [htri, hcombined, herrsmall, hEsmall]
  change dist (S * L / G) 2 < δ
  have heq : S * L / G - 2 = (S * L - 2 * G) / G := by field_simp [hG.ne']
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hG]
  exact ((div_le_iff₀ hG).mpr herror).trans_lt (by linarith only [hδ])

/-- Sparse prime flips have harmonic sums larger than every sublinear logarithmic
power, eventually and with an arbitrarily large coefficient. -/
theorem tendsto_sparse_signedMean_div_log_rpow_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {α : ℝ} (hα : α < 1) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (primeSetFlip P) N / Real.log N ^ α) atTop atTop := by
  have hpositive := tendsto_positiveDivisorMean_div_log_rpow_atTop P hP
    (show 1 + α < 2 by linarith only [hα])
  apply tendsto_atTop_mono' atTop ?_ hpositive
  have hratio := (Metric.tendsto_nhds.mp
    (tendsto_signedMean_mul_log_div_positiveDivisorMean P hP)) 1 (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio, hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with N hR hL1 hN
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hG := one_le_realLogHarmonicSum_signDivisorCount (primeSetFlip_isSignGauge P) hL.le
  rw [realLogHarmonicSum_log_nat _ hN] at hG
  have hG0 := zero_lt_one.trans_le hG
  rw [Real.dist_eq] at hR
  have hR1 : 1 ≤ gaugeHarmonicSum (primeSetFlip P) N * Real.log N /
      gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N := by
    have h := (abs_lt.mp hR).1
    linarith only [h]
  have hlower := (le_div_iff₀ hG0).mp hR1
  simp only [one_mul] at hlower
  calc
    gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N / Real.log N ^ (1 + α) =
        (gaugeHarmonicSum (signDivisorCount (primeSetFlip P)) N / Real.log N) /
          Real.log N ^ α := by rw [Real.rpow_add hL, Real.rpow_one, div_div]
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ hL).mpr hlower)
      (Real.rpow_nonneg hL.le _)

/-- Zero logarithmic prime density forces the signed harmonic mean to tend to positive
infinity, including prime patterns with zero Euler mass. -/
theorem tendsto_sparse_signedMean_atTop (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    Tendsto (gaugeHarmonicSum (primeSetFlip P)) atTop atTop := by
  simpa only [Real.rpow_zero, div_one] using
    tendsto_sparse_signedMean_div_log_rpow_atTop P hP (by norm_num : (0 : ℝ) < 1)

end GaloisForLFunctions.RenormalizedIntersectionTheory

