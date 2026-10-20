import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeInheritanceAndSelbergDerivative
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DownwardBuchstabL2TelescopeAndSawtoothCoupling
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedPronicMultiplicativityAndRoutePMBridge
import GaloisForLFunctions.BiScaleUncertainty.KerPCenteredSieveAndFirstSecondMomentReciprocity
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSecondMoment
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanWeights
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff

/-!
# Damped prime horizons: slope reversal and a diverging crossover

For the damped weight `c_ε(d) = μ(d) d^{-ε}` the prime horizon step `p = N + 1` of the prefix
energy is, with `B = ⌊M/p⌋` and `r = p^{-ε}`,

`E_p(M) - E_{p-1}(M) = r² B - 2 r Σ_{d<p} c_ε(d) ⌊B/d⌋ = r B λ_ε(p) + O(r p)`,

with the **damped prime slope** `λ_ε(p) = p^{-ε} - 2 Σ_{d<p} μ(d) d^{-1-ε}`; at `ε = 0` it is the
Buchstab slope `λ(p) = 1 - 2 m(p-1)`.

* **Reversal.** For every fixed `ε > 0`, every large prime horizon strictly *lowers* the energy at
  every trans-horizon prefix `M ≥ p`. Completing the floor sum to horizon `B` turns it into the
  damped divisor sum `Σ_{j≤B} τ_ε(j) ≥ κ_ε B` (its mean `1/ζ(1+ε)` is positive), while the omitted
  divisors `d ≥ p` cost at most `B (1+ε)/ε · p^{-ε}`; both are uniform in `B`, and the injection
  `r² B` is `o(r B)`.
* **Small damping.** At `ε = 0` large primes inject energy (`λ(p) → 1`). The slope moves by at most
  `ε log p (2p - 1)`, so every prime with `λ(p) > 0` still injects at large prefixes for all
  `ε ≤ λ(p)/(2 log p (2p - 1))`.
* **Crossover.** Hence the dissipation threshold `P(ε)` beyond which all prime horizons dissipate
  exists for every `ε > 0` but diverges as `ε → 0`: no threshold is uniform in the damping.
  The Möbius horizon picture is the `ε → 0` limit only on bounded horizon ranges.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The damped prime step in floor form -/

theorem pmPowerDampedRealWeight_prime {p : ℕ} (hp : p.Prime) (ε : ℝ) :
    pmPowerDampedRealWeight ε p = -((p : ℝ) ^ (-ε)) := by
  unfold pmPowerDampedRealWeight
  simp [moebiusReal, ArithmeticFunction.moebius_apply_prime hp]

theorem abs_pmPowerDampedRealWeight_le {ε : ℝ} (d : ℕ) :
    |pmPowerDampedRealWeight ε d| ≤ (d : ℝ) ^ (-ε) := by
  unfold pmPowerDampedRealWeight moebiusReal
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have h : |((μ d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) h

theorem abs_pmPowerDampedRealWeight_le_one {ε : ℝ} (hε : 0 ≤ ε) (d : ℕ) :
    |pmPowerDampedRealWeight ε d| ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [pmPowerDampedRealWeight, moebiusReal]
  · exact (abs_pmPowerDampedRealWeight_le d).trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith))

/-- A sieve prefix sum is a floor sum: `Σ_{j≤B} s_{N,c}(j) = Σ_{d≤N} c(d) ⌊B/d⌋`. -/
theorem sum_sieveSeq_eq_sum_floor (N B : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ Icc 1 B, sieveSeq N c j) = ∑ d ∈ Icc 1 N, c d * ((B / d : ℕ) : ℝ) := by
  have h := sum_sieveSeq_mul_eq_sum_floor_gcd N 1 B c
  simp only [one_mul, Nat.gcd_one_right, Nat.div_one] at h
  exact h

/-- **Prime step, floor form.** `E_p(M) - E_{p-1}(M) = r² B - 2 r Σ_{d<p} c_ε(d) ⌊B/d⌋`. -/
theorem pmPowerDamped_prime_horizon_step_eq_floor {N : ℕ} (hp : (N + 1).Prime) (ε : ℝ) (M : ℕ) :
    sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
        sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) =
      (((N + 1 : ℕ) : ℝ) ^ (-ε)) ^ 2 * ((M / (N + 1) : ℕ) : ℝ) -
        2 * ((N + 1 : ℕ) : ℝ) ^ (-ε) *
          ∑ d ∈ Icc 1 N, pmPowerDampedRealWeight ε d * ((M / (N + 1) / d : ℕ) : ℝ) := by
  rw [sieveL2PrefixEnergy_prime_horizon_sub_eq hp M, pmPowerDampedRealWeight_prime hp,
    sum_sieveSeq_eq_sum_floor]
  ring

/-- Past the prefix, the damped floor sum is the damped divisor sum `Σ_{j≤B} τ_ε(j)`. -/
theorem sum_floor_pmPowerDamped_eq_divisorSum {K B : ℕ} (hBK : B ≤ K) (ε : ℝ) :
    ∑ d ∈ Icc 1 K, pmPowerDampedRealWeight ε d * ((B / d : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 B, pmPowerDampedDivisorCoeff ε j := by
  rw [← sum_sieveSeq_eq_sum_floor]
  exact sum_congr rfl fun j hj => sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff
    (mem_Icc.mp hj).1 ((mem_Icc.mp hj).2.trans hBK)

private theorem sum_Icc_one_split (f : ℕ → ℝ) {N K : ℕ} (hNK : N ≤ K) :
    ∑ d ∈ Icc 1 K, f d = ∑ d ∈ Icc 1 N, f d + ∑ d ∈ Icc (N + 1) K, f d := by
  have h1 (a : ℕ) : Icc 1 a = Ioc 0 a := by ext d; simp only [mem_Icc, mem_Ioc]; omega
  have h2 : Icc (N + 1) K = Ioc N K := by ext d; simp only [mem_Icc, mem_Ioc]; omega
  rw [h1, h1, h2, sum_Ioc_consecutive f (Nat.zero_le N) hNK]

/-- The divisors omitted below the prefix cost at most `B (1+ε)/ε (N+1)^{-ε}`, uniformly in `B`. -/
theorem abs_sum_floor_pmPowerDamped_tail_le {ε : ℝ} (hε : 0 < ε) (N K B : ℕ) :
    |∑ d ∈ Icc (N + 1) K, pmPowerDampedRealWeight ε d * ((B / d : ℕ) : ℝ)| ≤
      B * ((1 + ε) / ε * ((N + 1 : ℕ) : ℝ) ^ (-ε)) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ d ∈ Icc (N + 1) K,
      |pmPowerDampedRealWeight ε d * ((B / d : ℕ) : ℝ)| ≤ B * (d : ℝ) ^ (-(1 + ε)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := (mem_Icc.mp hd).1; omega)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (B / d))]
    have hfl : ((B / d : ℕ) : ℝ) ≤ B / d := Nat.cast_div_le
    have hpow : (d : ℝ) ^ (-(1 + ε)) = (d : ℝ) ^ (-ε) / d := by
      rw [show -(1 + ε) = -ε + -1 by ring, Real.rpow_add hd0, Real.rpow_neg_one, div_eq_mul_inv]
    rw [hpow]
    calc |pmPowerDampedRealWeight ε d| * ((B / d : ℕ) : ℝ)
        ≤ (d : ℝ) ^ (-ε) * (B / d) :=
          mul_le_mul (abs_pmPowerDampedRealWeight_le d) hfl (Nat.cast_nonneg _)
            (Real.rpow_nonneg hd0.le _)
      _ = B * ((d : ℝ) ^ (-ε) / d) := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  have h := sum_rpow_neg_tail_le (c := 1 + ε) (by linarith) (R := N + 1) (N := K) (by omega)
  rw [show (1 : ℝ) - (1 + ε) = -ε by ring, show (1 + ε - 1 : ℝ) = ε by ring] at h
  exact h

/-- The damped divisor sum grows at least linearly: `Σ_{j≤B} τ_ε(j) ≥ κ B` for some `κ > 0`. -/
theorem exists_pos_linear_le_pmPowerDampedDivisorSum {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, κ * B ≤ ∑ j ∈ Icc 1 B, pmPowerDampedDivisorCoeff ε j := by
  set ρ := (pmPowerDampedDivisorDensity ε).re
  have hρ : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  obtain ⟨X, hX⟩ := eventually_atTop.mp ((tendsto_pmPowerDampedDivisorSum_div_real hε).eventually
    (eventually_gt_nhds (show ρ / 2 < ρ by linarith)))
  set X₁ := max X 1
  have hX₁ : 0 < X₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨min (ρ / 2) (1 / X₁), lt_min (by linarith) (by positivity), fun B => ?_⟩
  have hnn : ∀ j ∈ Icc 1 B, 0 ≤ pmPowerDampedDivisorCoeff ε j :=
    fun j _ => pmPowerDampedDivisorCoeff_nonneg hε.le j
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  by_cases hBX : X₁ ≤ (B : ℝ)
  · have h := hX B (le_trans (le_max_left _ _) hBX)
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    unfold pmPowerDampedDivisorSum at h
    rw [Nat.floor_natCast, lt_div_iff₀ hB0] at h
    calc min (ρ / 2) (1 / X₁) * B ≤ ρ / 2 * B :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hB0.le
      _ ≤ _ := h.le
  · push Not at hBX
    have h1 : (1 : ℝ) ≤ ∑ j ∈ Icc 1 B, pmPowerDampedDivisorCoeff ε j := by
      have := single_le_sum hnn (show 1 ∈ Icc 1 B from mem_Icc.mpr ⟨le_refl 1, hB⟩)
      rwa [pmPowerDampedDivisorCoeff_one] at this
    calc min (ρ / 2) (1 / X₁) * B ≤ 1 / X₁ * B :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg B)
      _ ≤ 1 / X₁ * X₁ := mul_le_mul_of_nonneg_left hBX.le (by positivity)
      _ = 1 := by field_simp
      _ ≤ _ := h1

/-! ### Reversal: at fixed damping every large prime horizon dissipates -/

/-- **Damped prime horizons dissipate.** For every `ε > 0`, every large prime `p` and every
prefix `M ≥ p`, adding the horizon `p` strictly lowers the damped prefix energy. -/
theorem eventually_pmPowerDamped_prime_horizon_step_neg {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ M : ℕ, p ≤ M →
      sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) <
        sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) := by
  obtain ⟨κ, hκ, hT⟩ := exists_pos_linear_le_pmPowerDampedDivisorSum hε
  set C := (1 + ε) / ε
  have hC : 0 < C := by positivity
  have hr : Tendsto (fun p : ℕ => (p : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [hr.eventually (eventually_lt_nhds (show (0 : ℝ) < 2 * κ / (1 + 2 * C) by
    positivity)), eventually_ge_atTop 2] with p hsmall hp2 hp M hM
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by omega⟩
  rw [show N + 1 - 1 = N by omega]
  set B := M / (N + 1)
  have hB : 1 ≤ B := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  set r := ((N + 1 : ℕ) : ℝ) ^ (-ε)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hstep := pmPowerDamped_prime_horizon_step_eq_floor hp ε M
  set F := ∑ d ∈ Icc 1 N, pmPowerDampedRealWeight ε d * ((B / d : ℕ) : ℝ)
  -- complete the floor sum to horizon `N + B`, where it is the damped divisor sum
  have hsplit := sum_Icc_one_split (fun d => pmPowerDampedRealWeight ε d * ((B / d : ℕ) : ℝ))
    (show N ≤ N + B by omega)
  rw [sum_floor_pmPowerDamped_eq_divisorSum (show B ≤ N + B by omega)] at hsplit
  have htail := abs_sum_floor_pmPowerDamped_tail_le hε N (N + B) B
  have hF : B * (κ - C * r) ≤ F := by
    have := hT B
    have := (abs_le.mp htail).2
    nlinarith
  have hsmall' : (1 + 2 * C) * r < 2 * κ := by
    rw [lt_div_iff₀ (by positivity)] at hsmall; linarith
  have : sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
      sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) < 0 := by
    rw [hstep]
    have h2 : r * B * ((1 + 2 * C) * r - 2 * κ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hr0 hB0) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hF (show 0 ≤ 2 * r by positivity)]
  linarith

/-! ### Small damping: injection persists near the Möbius limit -/

/-- The **damped prime slope** `λ_ε(p) = p^{-ε} - 2 Σ_{d<p} μ(d) d^{-1-ε}`. -/
def dampedPrimeSlope (ε : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-ε) - 2 * finiteHarmonicSum (p - 1) (pmPowerDampedRealWeight ε)

/-- At zero damping the damped prime slope is the Buchstab slope. -/
theorem dampedPrimeSlope_zero {p : ℕ} (hp : p.Prime) : dampedPrimeSlope 0 p = buchstabSlope p := by
  rw [buchstabSlope_prime hp]
  unfold dampedPrimeSlope
  have hw : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d; simp [pmPowerDampedRealWeight]
  rw [hw]
  simp

/-- **Slope law.** At a prime horizon `p`, `|E_p(M) - E_{p-1}(M) - p^{-ε} B λ_ε(p)| ≤ 2 p^{-ε}(p-1)`
for every prefix `M` and every `ε ≥ 0`. -/
theorem abs_pmPowerDamped_prime_step_sub_slope_le {N : ℕ} (hp : (N + 1).Prime) {ε : ℝ}
    (hε : 0 ≤ ε) (M : ℕ) :
    |sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
        sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) -
        ((N + 1 : ℕ) : ℝ) ^ (-ε) * ((M / (N + 1) : ℕ) : ℝ) * dampedPrimeSlope ε (N + 1)| ≤
      2 * ((N + 1 : ℕ) : ℝ) ^ (-ε) * N := by
  rw [sieveL2PrefixEnergy_prime_horizon_sub_eq_sawtooth hp M, pmPowerDampedRealWeight_prime hp]
  unfold dampedPrimeSlope
  rw [show N + 1 - 1 = N by omega]
  set r := ((N + 1 : ℕ) : ℝ) ^ (-ε)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfr := abs_sievedFractSum_le_sum_abs N (pmPowerDampedRealWeight ε) (M / (N + 1))
  have hsum : ∑ d ∈ Icc 1 N, |pmPowerDampedRealWeight ε d| ≤ N := by
    calc ∑ d ∈ Icc 1 N, |pmPowerDampedRealWeight ε d| ≤ ∑ _d ∈ Icc 1 N, (1 : ℝ) :=
          sum_le_sum fun d _ => abs_pmPowerDampedRealWeight_le_one hε d
      _ = N := by simp
  have hid : ((M / (N + 1) : ℕ) : ℝ) * ((-r) ^ 2 + 2 * -r *
      finiteHarmonicSum N (pmPowerDampedRealWeight ε)) -
      2 * -r * sievedFractSum N (pmPowerDampedRealWeight ε) (M / (N + 1)) -
      r * ((M / (N + 1) : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (-ε) -
        2 * finiteHarmonicSum N (pmPowerDampedRealWeight ε)) =
      2 * r * sievedFractSum N (pmPowerDampedRealWeight ε) (M / (N + 1)) := by ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_left (hfr.trans hsum) (by positivity)

/-- `1 - x^{-ε} ≤ ε log x` for `x ≥ 1`. -/
private theorem one_sub_rpow_neg_le {x : ℝ} (ε : ℝ) (hx : 1 ≤ x) :
    1 - x ^ (-ε) ≤ ε * Real.log x := by
  rw [Real.rpow_def_of_pos (by linarith)]
  have := Real.add_one_le_exp (Real.log x * -ε)
  linarith

/-- **Damping moves the prime slope by at most `ε log p (2p - 1)`.** -/
theorem buchstabSlope_sub_le_dampedPrimeSlope {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 ≤ ε) :
    buchstabSlope p - ε * (Real.log p * (2 * p - 1)) ≤ dampedPrimeSlope ε p := by
  rw [← dampedPrimeSlope_zero hp]
  unfold dampedPrimeSlope finiteHarmonicSum
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have htop := one_sub_rpow_neg_le ε hp1
  -- each harmonic term moves by at most `ε log p`
  have hterm : ∀ d ∈ Icc 1 (p - 1),
      pmPowerDampedRealWeight ε d / d - pmPowerDampedRealWeight 0 d / d ≤ ε * Real.log p := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
    have hdp : (d : ℝ) ≤ p := by
      have := (mem_Icc.mp hd).2; exact_mod_cast (show d ≤ p by omega)
    have hdiff : pmPowerDampedRealWeight ε d / d - pmPowerDampedRealWeight 0 d / d =
        moebiusReal d * ((d : ℝ) ^ (-ε) - 1) / d := by
      unfold pmPowerDampedRealWeight; simp; ring
    rw [hdiff]
    have hμ : |moebiusReal d| ≤ 1 := by unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hgap : |(d : ℝ) ^ (-ε) - 1| ≤ ε * Real.log p := by
      rw [abs_sub_comm, abs_of_nonneg (by
        linarith [Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith : -ε ≤ 0)])]
      exact (one_sub_rpow_neg_le ε hd1).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hdp) hε)
    calc moebiusReal d * ((d : ℝ) ^ (-ε) - 1) / d ≤ |moebiusReal d * ((d : ℝ) ^ (-ε) - 1) / d| :=
          le_abs_self _
      _ = |moebiusReal d| * |(d : ℝ) ^ (-ε) - 1| / d := by
          rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d)]
      _ ≤ 1 * (ε * Real.log p) / 1 := by
          apply div_le_div₀ (by positivity) (mul_le_mul hμ hgap (abs_nonneg _) zero_le_one)
            zero_lt_one hd1
      _ = ε * Real.log p := by ring
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard : ((p - 1 + 1 - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [show p - 1 + 1 - 1 = p - 1 by omega, Nat.cast_sub hp.one_le, Nat.cast_one]
  rw [hcard] at hsum
  rw [neg_zero, Real.rpow_zero]
  nlinarith

/-- **Injection at small damping.** If the Buchstab slope `λ(p)` of a prime is positive, then for
every damping `0 ≤ ε` with `ε log p (2p-1) ≤ λ(p)/2` the horizon `p` strictly raises the damped
prefix energy at every prefix with `⌊M/p⌋ λ(p) > 4(p-1)`. -/
theorem pmPowerDamped_prime_horizon_step_pos {p : ℕ} (hp : p.Prime) (hlam : 0 < buchstabSlope p)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε * (Real.log p * (2 * p - 1)) ≤ buchstabSlope p / 2)
    {M : ℕ} (hM : 4 * ((p : ℝ) - 1) < ((M / p : ℕ) : ℝ) * buchstabSlope p) :
    sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) <
      sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) := by
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by have := hp.one_le; omega⟩
  rw [show N + 1 - 1 = N by omega]
  have hslope := buchstabSlope_sub_le_dampedPrimeSlope hp hε0
  have hlaw := abs_pmPowerDamped_prime_step_sub_slope_le hp hε0 M
  set r := ((N + 1 : ℕ) : ℝ) ^ (-ε)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  set B : ℝ := ((M / (N + 1) : ℕ) : ℝ)
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hN : ((N + 1 : ℕ) : ℝ) - 1 = N := by push_cast; ring
  rw [hN] at hM
  have hlamε : buchstabSlope (N + 1) / 2 ≤ dampedPrimeSlope ε (N + 1) := by linarith
  have hgain : 2 * N < B * dampedPrimeSlope ε (N + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlamε hB0]
  have hlo := (abs_le.mp hlaw).1
  have : 0 < sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
      sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) := by
    nlinarith [mul_lt_mul_of_pos_left hgain hr0]
  linarith

/-! ### The crossover diverges as the damping vanishes -/

/-- **Divergent crossover.** For every `P` there is `ε₀ > 0` such that every damping
`0 ≤ ε ≤ ε₀` has a prime horizon `p ≥ P` that strictly raises the energy at some prefix `M ≥ p`. -/
theorem exists_injecting_prime_horizon_of_small_damping (P : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∃ p M : ℕ, P ≤ p ∧ p.Prime ∧ p ≤ M ∧
      sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) <
        sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (tendsto_finiteHarmonicSum_moebiusReal_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (tendsto_finiteHarmonicSum_moebiusReal_zero.eventually
    (eventually_gt_nhds (show (-1 / 4 : ℝ) < 0 by norm_num)))
  obtain ⟨p, hpP, hp⟩ := Nat.exists_infinite_primes (P + N₀ + N₁ + 3)
  have hlam : 1 / 2 < buchstabSlope p := by
    rw [buchstabSlope_prime hp]
    have := hN₀ (p - 1) (by omega)
    linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  set D := Real.log p * (2 * p - 1)
  have hD : 0 < D := mul_pos hlog (by linarith)
  refine ⟨buchstabSlope p / 2 / D, by positivity, fun ε hε0 hε => ?_⟩
  set K := ⌈4 * ((p : ℝ) - 1) / buchstabSlope p⌉₊ + 1
  have hK : 4 * ((p : ℝ) - 1) < (K : ℝ) * buchstabSlope p := by
    have h1 := Nat.le_ceil (4 * ((p : ℝ) - 1) / buchstabSlope p)
    have h2 : 4 * ((p : ℝ) - 1) / buchstabSlope p < K := by
      simp only [K]; push_cast; linarith
    rwa [div_lt_iff₀ (by linarith)] at h2
  refine ⟨p, p * K, by omega, hp, Nat.le_mul_of_pos_right p (by omega), ?_⟩
  apply pmPowerDamped_prime_horizon_step_pos hp (by linarith) hε0
  · rwa [le_div_iff₀ hD] at hε
  · rwa [Nat.mul_div_cancel_left K hp.pos]

/-- **No damping-uniform dissipation threshold.** There is no `P` such that, for every damping
`0 < ε ≤ 1`, every prime horizon `p ≥ P` lowers the energy at every prefix `M ≥ p`. -/
theorem not_exists_uniform_pmPowerDamped_dissipation_threshold :
    ¬ ∃ P : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ p : ℕ, P ≤ p → p.Prime → ∀ M : ℕ, p ≤ M →
      sieveL2PrefixEnergy p M (pmPowerDampedRealWeight ε) <
        sieveL2PrefixEnergy (p - 1) M (pmPowerDampedRealWeight ε) := by
  rintro ⟨P, hP⟩
  obtain ⟨ε₀, hε₀, h⟩ := exists_injecting_prime_horizon_of_small_damping P
  obtain ⟨p, M, hPp, hp, hpM, hlt⟩ := h (min ε₀ 1) (le_min hε₀.le zero_le_one) (min_le_left _ _)
  have := hP (min ε₀ 1) (lt_min hε₀ one_pos) (min_le_right _ _) p hPp hp M hpM
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
