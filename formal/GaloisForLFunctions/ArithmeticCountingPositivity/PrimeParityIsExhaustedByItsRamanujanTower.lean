import GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicParitySpectralCoordinates
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival
import GaloisForLFunctions.RHTower.SummableDivisorHarmonicMean

/-!
# Prime parity is exhausted by its Ramanujan tower

Truncating the prime-power Ramanujan expansion restores parity exactly
outside one divisibility fibre. The harmonic count of that fibre gives an
exact squared error and a geometric bound uniform over all horizons.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The harmonic mean of a single-prime parity gauge. -/
def primeParityMean (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) + 1)

/-- The finite prime-power Ramanujan expansion of parity through conductor `p^K`. -/
def primeParityTowerProfile (p K n : ℕ) : ℝ :=
  primeParityMean p + ∑ k ∈ range K,
    2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) * sieveLagMultiplier (p ^ (k + 1)) n

/-- The tower profile on the same unit harmonic scale as the parity constraint. -/
def primeParityTowerVector (p K N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => primeParityTowerProfile p K n / Real.sqrt n /
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))

private theorem mean_pos {p : ℕ} (hp : p.Prime) : 0 < primeParityMean p := by
  have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_pos (sub_pos.mpr h) (by positivity)

private theorem mean_lt_one (p : ℕ) : primeParityMean p < 1 := by
  rw [primeParityMean, div_lt_one (by positivity : (0 : ℝ) < p + 1)]
  linarith

private theorem mean_shell {p : ℕ} (hp : p.Prime) :
    primeParityMean p + 2 * primeParityMean p / ((p : ℝ) - 1) = 1 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp.one_lt)).ne'
  have hp2 : (p : ℝ) + 1 ≠ 0 := by positivity
  rw [primeParityMean]
  field_simp [hp1, hp2]
  ring

private theorem mean_variance (p : ℕ) :
    1 - primeParityMean p ^ 2 = 4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2 := by
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  rw [primeParityMean]
  field_simp [hp1]
  ring

private theorem flip_prime_power {p : ℕ} (hp : p.Prime) (K : ℕ) :
    finiteFlip {p} (p ^ K) = (-1 : ℝ) ^ K := by
  simp only [finiteFlip, prod_singleton, hp.factorization_pow, Finsupp.single_eq_same]

private theorem towerProfile_succ (p K n : ℕ) :
    primeParityTowerProfile p (K + 1) n = primeParityTowerProfile p K n +
      2 * primeParityMean p * (-1 : ℝ) ^ (K + 1) * sieveLagMultiplier (p ^ (K + 1)) n := by
  rw [primeParityTowerProfile, primeParityTowerProfile, Finset.sum_range_succ]
  ring

/-- Only the deepest divisibility fibre remains unresolved by the finite tower. -/
theorem primeParityTowerProfile_value {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (K : ℕ) :
    primeParityTowerProfile p K n =
      if p ^ K ∣ n then primeParityMean p * (-1 : ℝ) ^ K else finiteFlip {p} n := by
  induction K with
  | zero => simp [primeParityTowerProfile]
  | succ K ih =>
      by_cases hnext : p ^ (K + 1) ∣ n
      · have hprev : p ^ K ∣ n := (pow_dvd_pow p (Nat.le_succ K)).trans hnext
        rw [towerProfile_succ, ih, if_pos hprev,
          sieveLagMultiplier_prime_pow_trichotomy p K n hp, if_pos hnext,
          if_pos hnext, pow_succ]
        ring
      · by_cases hprev : p ^ K ∣ n
        · have hq : ¬ p ∣ n / p ^ K := by
            rintro ⟨r, hr⟩
            apply hnext
            refine ⟨r, ?_⟩
            calc
              n = p ^ K * (n / p ^ K) := (Nat.mul_div_cancel' hprev).symm
              _ = p ^ (K + 1) * r := by rw [hr, pow_succ]; ring
          have hflip : finiteFlip {p} n = (-1 : ℝ) ^ K := by
            rw [(finiteFlip_isSignGauge {p}).of_dvd (pow_ne_zero _ hp.ne_zero) hn.ne' hprev,
              flip_prime_power hp K,
              finiteFlip_eq_one_of_coprime (by simpa only [mem_singleton, forall_eq] using hq),
              mul_one]
          rw [towerProfile_succ, ih, if_pos hprev,
            sieveLagMultiplier_prime_pow_trichotomy p K n hp, if_neg hnext,
            if_pos hprev, if_neg hnext, hflip, pow_succ]
          calc
            _ = (-1 : ℝ) ^ K *
                (primeParityMean p + 2 * primeParityMean p / ((p : ℝ) - 1)) := by ring
            _ = _ := by rw [mean_shell hp, mul_one]
        · rw [towerProfile_succ, ih, if_neg hprev,
            sieveLagMultiplier_prime_pow_trichotomy p K n hp, if_neg hnext,
            if_neg hprev, if_neg hnext, mul_zero, add_zero]

private theorem euclidean_sum_apply {N : ℕ} (S : Finset ℕ)
    (f : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N)) (n : PrimeHorizonIndex N) :
    (∑ k ∈ S, f k) n = ∑ k ∈ S, f k n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih => simp only [sum_insert hk, PiLp.add_apply, ih]

private theorem scaled_ramanujan_apply {m N : ℕ} (hm : 0 < m) (hN : 1 ≤ N)
    (a : ℝ) (n : PrimeHorizonIndex N) :
    ((a / Real.sqrt (m.totient : ℝ)) • harmonicRamanujanHorizonVector m N) n =
      a * sieveLagMultiplier m n / Real.sqrt n /
        Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hsφ := (Real.sqrt_pos.mpr hφ).ne'
  have hH := (Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)).ne'
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.property).1
  have hsn := (Real.sqrt_pos.mpr hn).ne'
  change (a / Real.sqrt (m.totient : ℝ)) *
      ((Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))⁻¹ * ramanujanPoleProfile m n) = _
  rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm,
    ramanujanLagCoefficient_eq_totient_mul]
  field_simp [hsφ, hH, hsn]
  rw [Real.sq_sqrt hφ.le]

/-- The counting profile is a literal finite sum of the normalized arithmetic modes. -/
theorem primeParityTowerVector_eq_ramanujan {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) (K : ℕ) :
    primeParityTowerVector p K N =
      primeParityMean p • harmonicRamanujanHorizonVector 1 N +
        ∑ k ∈ range K,
          (2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) /
            Real.sqrt ((p ^ (k + 1)).totient : ℝ)) •
              harmonicRamanujanHorizonVector (p ^ (k + 1)) N := by
  ext n
  rw [PiLp.add_apply, euclidean_sum_apply]
  have hground := scaled_ramanujan_apply (by norm_num : 0 < 1) hN (primeParityMean p) n
  have hone : sieveLagMultiplier 1 (n : ℕ) = 1 := sieveLagMultiplier_of_dvd one_ne_zero (one_dvd _)
  simp only [Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one, hone, mul_one] at hground
  rw [hground]
  simp_rw [scaled_ramanujan_apply (pow_pos hp.pos _) hN]
  change (primeParityMean p + ∑ k ∈ range K,
    2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) * sieveLagMultiplier (p ^ (k + 1)) n) /
      Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) = _
  simp only [add_div, sum_div]

private theorem neg_one_pow_sq (K : ℕ) : ((-1 : ℝ) ^ K) ^ 2 = 1 := by
  rw [sq, ← mul_pow]
  norm_num

/-- The entire approximation error is an exact harmonic count on one fibre. -/
theorem primeParityTower_error_sq_eq {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) (K : ℕ) :
    ‖primeParityHorizonVector p N - primeParityTowerVector p K N‖ ^ 2 =
      ((1 + primeParityMean p ^ 2) * gaugeHarmonicSum (fun _ => 1) (N / p ^ K) -
        2 * primeParityMean p * gaugeHarmonicSum (finiteFlip {p}) (N / p ^ K)) /
          ((p : ℝ) ^ K * gaugeHarmonicSum (fun _ => 1) N) := by
  have hH := gaugeHarmonicSum_one_pos hN
  have hnorm : ‖primeParityHorizonVector p N - primeParityTowerVector p K N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, (finiteFlip {p} n - primeParityTowerProfile p K n) ^ 2 / n) /
        gaugeHarmonicSum (fun _ => 1) N := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ n : PrimeHorizonIndex N,
      (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) -
        primeParityTowerProfile p K n / Real.sqrt n /
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2) = _
    rw [sum_coe_sort (Icc 1 N) (fun n =>
      (finiteFlip {p} n / Real.sqrt n / Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) -
        primeParityTowerProfile p K n / Real.sqrt n /
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N)) ^ 2), sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [← sub_div, ← sub_div, div_pow, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hH.le]
  have hsupport :
      (∑ n ∈ Icc 1 N, (finiteFlip {p} n - primeParityTowerProfile p K n) ^ 2 / n) =
      ∑ n ∈ (Icc 1 N).filter (p ^ K ∣ ·),
        (finiteFlip {p} n - primeParityMean p * (-1 : ℝ) ^ K) ^ 2 / n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    rw [primeParityTowerProfile_value hp (mem_Icc.mp hn).1 K]
    by_cases hd : p ^ K ∣ n
    · simp only [if_pos hd]
    · simp only [if_neg hd, sub_self]
      norm_num
  have hterm (n : ℕ) :
      (finiteFlip {p} n - primeParityMean p * (-1 : ℝ) ^ K) ^ 2 / n =
        (1 + primeParityMean p ^ 2) * (1 / (n : ℝ)) -
          2 * primeParityMean p * (-1 : ℝ) ^ K * (finiteFlip {p} n / n) := by
    have hf : finiteFlip {p} n ^ 2 = 1 := by rw [sq, singleFlip_mul_self]
    calc
      _ = (finiteFlip {p} n ^ 2 + primeParityMean p ^ 2 * ((-1 : ℝ) ^ K) ^ 2 -
          2 * primeParityMean p * (-1 : ℝ) ^ K * finiteFlip {p} n) / n := by ring
      _ = _ := by rw [hf, neg_one_pow_sq]; ring
  rw [hnorm, hsupport, sum_congr rfl (fun n _ => hterm n), sum_sub_distrib,
    ← mul_sum, ← mul_sum, harmonicMass_multiples (pow_pos hp.pos _),
    gaugeHarmonicSum_multiples (finiteFlip {p}) (finiteFlip_isSignGauge {p}) (pow_pos hp.pos _),
    flip_prime_power hp K, Nat.cast_pow]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0, hH.ne']
  rw [neg_one_pow_sq, mul_one]

private theorem mean_mul_harmonic_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    primeParityMean p * gaugeHarmonicSum (fun _ => 1) N ≤
      gaugeHarmonicSum (finiteFlip {p}) N := by
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  rw [primeParityMean, div_mul_eq_mul_div, div_le_iff₀ hp1]
  linarith only [(prime_parity_boundary_bounds hp N).1]

/-- The geometric error bound is uniform over the whole positive integer horizon. -/
theorem primeParityTower_error_sq_le {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) (K : ℕ) :
    ‖primeParityHorizonVector p N - primeParityTowerVector p K N‖ ^ 2 ≤
      (4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2) / (p : ℝ) ^ K := by
  have hH := gaugeHarmonicSum_one_pos hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : 0 < (p : ℝ) ^ K := pow_pos hp0 K
  have hc := mean_pos hp
  have hc1 := mean_lt_one p
  have hv : 0 ≤ 1 - primeParityMean p ^ 2 := by nlinarith only [hc, hc1]
  have hm : gaugeHarmonicSum (fun _ => 1) (N / p ^ K) ≤
      gaugeHarmonicSum (fun _ => 1) N := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (Nat.div_le_self N (p ^ K))⟩
    · intro n _ _
      positivity
  have hpay := mul_le_mul_of_nonneg_left (mean_mul_harmonic_le hp (N / p ^ K))
    (show 0 ≤ 2 * primeParityMean p by positivity)
  have hmass := mul_le_mul_of_nonneg_left hm hv
  rw [primeParityTower_error_sq_eq hp hN, ← mean_variance p,
    div_le_iff₀ (mul_pos hd hH)]
  have he : ((1 - primeParityMean p ^ 2) / (p : ℝ) ^ K) *
      ((p : ℝ) ^ K * gaugeHarmonicSum (fun _ => 1) N) =
      (1 - primeParityMean p ^ 2) * gaugeHarmonicSum (fun _ => 1) N := by
    field_simp [hd.ne']
  rw [he]
  nlinarith only [hpay, hmass]

private theorem harmonicMass_eq_harmonic (N : ℕ) :
    gaugeHarmonicSum (fun _ => 1) N = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [gaugeHarmonicSum, one_div]

private theorem harmonicMass_decimation_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 1) := by
  have hnum : Tendsto (fun N : ℕ => gaugeHarmonicSum (fun _ => 1) (N / d) / Real.log N)
      atTop (𝓝 1) := by
    simpa only [harmonicMass_eq_harmonic] using _root_.RHTower.tendsto_harmonic_natDiv_div_log hd
  have h := hnum.div tendsto_harmonicMass_div_log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hH := (gaugeHarmonicSum_one_pos (show 1 ≤ N by omega)).ne'
  change (gaugeHarmonicSum (fun _ => 1) (N / d) / Real.log N) /
    (gaugeHarmonicSum (fun _ => 1) N / Real.log N) =
      gaugeHarmonicSum (fun _ => 1) (N / d) / gaugeHarmonicSum (fun _ => 1) N
  field_simp [hlog, hH]

/-- The uniform error constant is attained in the harmonic horizon limit. -/
theorem tendsto_primeParityTower_error_sq {p : ℕ} (hp : p.Prime) (K : ℕ) :
    Tendsto (fun N : ℕ => ‖primeParityHorizonVector p N - primeParityTowerVector p K N‖ ^ 2)
      atTop (𝓝 ((4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2) / (p : ℝ) ^ K)) := by
  have hH := harmonicMass_decimation_tendsto (pow_pos hp.pos K)
  have hS := primeParity_decimation_tendsto hp (pow_pos hp.pos K)
  change Tendsto (fun N : ℕ => gaugeHarmonicSum (finiteFlip {p}) (N / p ^ K) /
    gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 (primeParityMean p)) at hS
  have h := ((hH.const_mul (1 + primeParityMean p ^ 2)).sub
    (hS.const_mul (2 * primeParityMean p))).div_const ((p : ℝ) ^ K)
  have hvalue : ((1 + primeParityMean p ^ 2) * 1 -
      2 * primeParityMean p * primeParityMean p) / (p : ℝ) ^ K =
      (4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2) / (p : ℝ) ^ K := by
    rw [← mean_variance p]
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [primeParityTower_error_sq_eq hp hN]
  ring

/-- The squared Ramanujan coefficients have exactly the same geometric remainder. -/
theorem primeParityTower_coefficient_mass {p : ℕ} (hp : p.Prime) (K : ℕ) :
    primeParityMean p ^ 2 + ∑ k ∈ range K,
        (2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) /
          Real.sqrt ((p ^ (k + 1)).totient : ℝ)) ^ 2 =
      1 - (4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2) / (p : ℝ) ^ K := by
  have hcoeff (k : ℕ) :
      (2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) /
        Real.sqrt ((p ^ (k + 1)).totient : ℝ)) ^ 2 =
      4 * primeParityMean p ^ 2 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
    rw [div_pow, mul_pow, mul_pow, neg_one_pow_sq,
      Real.sq_sqrt (Nat.cast_nonneg _), Nat.totient_prime_pow_succ hp,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
    norm_num
  induction K with
  | zero =>
      simp only [range_zero, sum_empty, add_zero, pow_zero, div_one]
      linarith only [mean_variance p]
  | succ K ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih, hcoeff K, pow_succ]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp.one_lt)).ne'
      have hp2 : (p : ℝ) + 1 ≠ 0 := by positivity
      rw [primeParityMean]
      field_simp [hp0, hp1, hp2]
      ring

private theorem tendsto_tower_tail {p : ℕ} (hp : p.Prime) :
    Tendsto (fun K : ℕ => (4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2) / (p : ℝ) ^ K)
      atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (1 : ℝ) / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := (div_lt_one (by positivity)).mpr hp1
  simpa only [div_pow, one_pow, mul_zero, mul_one_div] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (4 * (p : ℝ) / ((p : ℝ) + 1) ^ 2)

/-- The prime-power coefficients exhaust the full unit spectral mass. -/
theorem tendsto_primeParityTower_coefficient_mass {p : ℕ} (hp : p.Prime) :
    Tendsto (fun K : ℕ => primeParityMean p ^ 2 + ∑ k ∈ range K,
      (2 * primeParityMean p * (-1 : ℝ) ^ (k + 1) /
        Real.sqrt ((p ^ (k + 1)).totient : ℝ)) ^ 2) atTop (𝓝 1) := by
  simpa only [primeParityTower_coefficient_mass hp, sub_zero] using
    tendsto_const_nhds.sub (tendsto_tower_tail hp)

/-- Prime-power arithmetic modes exhaust parity uniformly in the integer horizon. -/
theorem primeParityTower_uniform_exhaustion {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ N : ℕ, 1 ≤ N →
      ‖primeParityHorizonVector p N - primeParityTowerVector p K N‖ ^ 2 < ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_tower_tail hp).eventually (gt_mem_nhds hε))
  exact ⟨K, fun N hN => (primeParityTower_error_sq_le hp hN K).trans_lt (hK K le_rfl)⟩

end GaloisForLFunctions.ArithmeticCountingPositivity
