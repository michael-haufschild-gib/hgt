import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsEulerProductHarmonicMean
import GaloisForLFunctions.ArithmeticCountingPositivity.ConductorMassBoundsGapLossAndProbePrecision

/-!
# Infinite prime counts have zero or unit conductor mass

Every fixed conductor sees only finitely many prime signs. Finite-cutoff
mass bounds therefore control the full nonnegative conductor series when
the Euler density is positive. Its normalized mass is exactly one; when
the density vanishes, every fixed normalized coefficient is zero. Exact
divisibility counts identify these coefficients as actual harmonic
Ramanujan means for arbitrary infinite prime patterns.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.BezoutValuationIncidence

open private primeSetCutoff_mono primeSetHarmonicDensity_le_cutoff
  const_div_harmonic_tendsto_zero from
  GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternHasItsEulerProductHarmonicMean
open private primeSetCutoff_prime primeSetFlip_sign from
  GaloisForLFunctions.ArithmeticCountingPositivity.DivisibilityCountsControlInfinitePrimeFlips
open private signed_harmonic_shell_le from
  GaloisForLFunctions.ArithmeticCountingPositivity.PrimeStrippingHasAnAdditiveHarmonicError
open private harmonicMass_shell from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity

/-- The literal Möbius divisor transform of an arbitrary prime-sign pattern. -/
def primeSetMobius (P : Set ℕ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, moebiusReal (m / d) * primeSetFlip P d

/-- Unnormalized squared conductor weight for an arbitrary prime pattern. -/
def primeSetSpectralWeight (P : Set ℕ) (m : ℕ) : ℝ :=
  primeSetMobius P m ^ 2 / (m.totient : ℝ)

/-- The harmonic Ramanujan coefficient of an arbitrary prime pattern. -/
def primeSetConductorCoefficient (P : Set ℕ) (m : ℕ) : ℝ :=
  primeSetHarmonicDensity P * primeSetMobius P m / Real.sqrt (m.totient : ℝ)

/-- A fixed conductor transform stabilizes once the prime cutoff reaches it. -/
theorem primeSetMobius_eq_finiteCutoff (P : Set ℕ) {m Q : ℕ} (hmQ : m ≤ Q) :
    primeSetMobius P m = finiteFlipMobius (primeSetCutoff P Q) m := by
  rw [primeSetMobius, finiteFlipMobius_eq_divisor_sum]
  apply sum_congr rfl
  intro d hd
  have hd' := Nat.mem_divisors.mp hd
  have hdm : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hd'.2) hd'.1
  rw [primeSetFlip_eq_finiteFlip_of_le P (hdm.trans hmQ)]

private theorem primeSetSpectralWeight_eq_finiteCutoff (P : Set ℕ) {m Q : ℕ} (hmQ : m ≤ Q) :
    primeSetSpectralWeight P m = finiteFlipSpectralWeight (primeSetCutoff P Q) m := by
  rw [primeSetSpectralWeight, primeSetMobius_eq_finiteCutoff P hmQ]
  rfl

private theorem primeSetSpectralWeight_nonneg (P : Set ℕ) (m : ℕ) :
    0 ≤ primeSetSpectralWeight P m := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem finite_weight_le_primeSet_weight (P : Set ℕ) (Q m : ℕ) :
    finiteFlipSpectralWeight (primeSetCutoff P Q) m ≤ primeSetSpectralWeight P m := by
  calc
    _ ≤ finiteFlipSpectralWeight (primeSetCutoff P (max Q m)) m :=
      finiteFlipSpectralWeight_mono (primeSetCutoff_mono P (le_max_left Q m)) m
    _ = _ := (primeSetSpectralWeight_eq_finiteCutoff P (le_max_right Q m)).symm

private theorem finiteCutoffMass_le_total (P : Set ℕ) (hs : Summable (primeSetSpectralWeight P))
    (Q : ℕ) : 1 / finiteFlipHarmonicDensity (primeSetCutoff P Q) ^ 2 ≤
      ∑' m : ℕ, primeSetSpectralWeight P m := by
  have hf := hasSum_finiteFlipSpectralWeight (primeSetCutoff P Q) (primeSetCutoff_prime P Q)
  rw [← hf.tsum_eq]
  exact Summable.tsum_mono hf.summable hs (finite_weight_le_primeSet_weight P Q)

/-- Squaring the coefficient removes the totient square root, including
the zero conductor where both sides vanish. -/
theorem primeSetConductorCoefficient_sq (P : Set ℕ) (m : ℕ) :
    primeSetConductorCoefficient P m ^ 2 =
      primeSetHarmonicDensity P ^ 2 * primeSetSpectralWeight P m := by
  rw [primeSetConductorCoefficient, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    primeSetSpectralWeight]
  ring

private theorem positive_density_weight_hasSum (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) :
    HasSum (primeSetSpectralWeight P) (1 / primeSetHarmonicDensity P ^ 2) := by
  -- Every finite conductor packet fits inside one finite-prime mass bound.
  have hpartial (N : ℕ) :
      (∑ m ∈ range N, primeSetSpectralWeight P m) ≤ 1 / primeSetHarmonicDensity P ^ 2 := by
    have hf := hasSum_finiteFlipSpectralWeight (primeSetCutoff P N) (primeSetCutoff_prime P N)
    have hcN := finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P N)
    have hle := primeSetHarmonicDensity_le_cutoff P N
    have hsq : primeSetHarmonicDensity P ^ 2 ≤
        finiteFlipHarmonicDensity (primeSetCutoff P N) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hcN.le hc.le)]
    calc
      _ = ∑ m ∈ range N, finiteFlipSpectralWeight (primeSetCutoff P N) m := by
        apply sum_congr rfl
        intro m hm
        exact primeSetSpectralWeight_eq_finiteCutoff P (Nat.le_of_lt (mem_range.mp hm))
      _ ≤ ∑' m : ℕ, finiteFlipSpectralWeight (primeSetCutoff P N) m :=
        hf.summable.sum_le_tsum (range N)
          (fun m _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      _ = 1 / finiteFlipHarmonicDensity (primeSetCutoff P N) ^ 2 := hf.tsum_eq
      _ ≤ _ := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hcN) (sq_pos_of_pos hc)]
        simpa only [one_mul] using hsq
  have hs := summable_of_sum_range_le (primeSetSpectralWeight_nonneg P) hpartial
  have hu : (∑' m : ℕ, primeSetSpectralWeight P m) ≤ 1 / primeSetHarmonicDensity P ^ 2 :=
    le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall hpartial)
  -- Finite-prime total masses give the reverse inequality in the cutoff limit.
  have hcut := finiteCutoffMass_le_total P hs
  have hlim : Tendsto (fun Q => 1 / finiteFlipHarmonicDensity (primeSetCutoff P Q) ^ 2)
      atTop (𝓝 (1 / primeSetHarmonicDensity P ^ 2)) :=
    tendsto_const_nhds.div ((tendsto_primeSetCutoff_density P).pow 2) (pow_ne_zero 2 hc.ne')
  have hl := le_of_tendsto hlim (Eventually.of_forall hcut)
  have he : (∑' m : ℕ, primeSetSpectralWeight P m) = 1 / primeSetHarmonicDensity P ^ 2 :=
    le_antisymm hu hl
  exact he ▸ hs.hasSum

/-- The unnormalized conductor series is summable exactly at positive
Euler density. A zero product forces its finite-prime masses to diverge. -/
theorem summable_primeSetSpectralWeight_iff (P : Set ℕ) :
    Summable (primeSetSpectralWeight P) ↔ 0 < primeSetHarmonicDensity P := by
  constructor
  · intro hs
    by_contra hn
    have hz : primeSetHarmonicDensity P = 0 :=
      le_antisymm (le_of_not_gt hn) (primeSetHarmonicDensity_bounds P).1
    have hb (Q : ℕ) : (1 : ℝ) ≤
        (∑' m : ℕ, primeSetSpectralWeight P m) *
          finiteFlipHarmonicDensity (primeSetCutoff P Q) ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos (finiteFlipHarmonicDensity_pos (primeSetCutoff_prime P Q)))).mp
        (finiteCutoffMass_le_total P hs Q)
    have hlim := ((tendsto_primeSetCutoff_density P).pow 2).const_mul
      (∑' m : ℕ, primeSetSpectralWeight P m)
    have hbad := ge_of_tendsto hlim (Eventually.of_forall hb)
    rw [hz, pow_two, zero_mul, mul_zero] at hbad
    norm_num at hbad
  · intro hc
    exact (positive_density_weight_hasSum P hc).summable

/-- The total squared conductor mass is exactly one at positive Euler
density, and exactly zero at vanishing density. -/
theorem hasSum_primeSetConductorCoefficient_sq (P : Set ℕ) :
    HasSum (fun m : ℕ => primeSetConductorCoefficient P m ^ 2)
      (if primeSetHarmonicDensity P = 0 then 0 else 1) := by
  classical
  by_cases hc : primeSetHarmonicDensity P = 0
  · rw [if_pos hc]
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro m
    rw [primeSetConductorCoefficient, hc, zero_mul, zero_div, pow_two, zero_mul]
  · rw [if_neg hc]
    have hcpos : 0 < primeSetHarmonicDensity P :=
      lt_of_le_of_ne (primeSetHarmonicDensity_bounds P).1 (Ne.symm hc)
    have h := (positive_density_weight_hasSum P hcpos).mul_left (primeSetHarmonicDensity P ^ 2)
    have hs : HasSum (fun m : ℕ => primeSetHarmonicDensity P ^ 2 * primeSetSpectralWeight P m) 1 := by
      simpa only [mul_one_div, div_self (pow_ne_zero 2 hc)] using h
    exact hs.congr_fun (primeSetConductorCoefficient_sq P)

/-- The literal mixed harmonic count with a Ramanujan conductor. -/
def primeSetRamanujanSum (P : Set ℕ) (m N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, primeSetFlip P n * ramanujanLagCoefficient m n / n

/-- Divisibility incidence expresses the mixed count as decimated signed
harmonic sums, retaining the complete Möbius coefficient. -/
theorem primeSetRamanujanSum_eq (P : Set ℕ) (m N : ℕ) :
    primeSetRamanujanSum P m N =
      ∑ d ∈ m.divisors, moebiusReal (m / d) * primeSetFlip P d *
        gaugeHarmonicSum (primeSetFlip P) (N / d) := by
  unfold primeSetRamanujanSum ramanujanLagCoefficient
  simp_rw [mul_sum, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have he : (∑ n ∈ Icc 1 N, primeSetFlip P n *
      (moebiusReal (m / d) * (if d ∣ n then (d : ℝ) else 0)) / n) =
      moebiusReal (m / d) *
        ∑ n ∈ Icc 1 N, primeSetFlip P n * (if d ∣ n then (d : ℝ) else 0) / n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [he, gaugeHarmonicSum_divisibility (primeSetFlip P)
    (primeSetFlip_sign P) (Nat.pos_of_mem_divisors hd)]
  ring

private theorem primeSet_decimation_tendsto (P : Set ℕ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (primeSetFlip P) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 (primeSetHarmonicDensity P)) := by
  have hmain := primeSetFlip_harmonicCorrelation_tendsto P
  have herr := const_div_harmonic_tendsto_zero (1 + Real.log d)
  have hl : Tendsto (fun N => harmonicCorrelation (primeSetFlip P) N -
      (1 + Real.log d) / gaugeHarmonicSum (fun _ => 1) N)
        atTop (𝓝 (primeSetHarmonicDensity P)) := by
    simpa only [sub_zero] using hmain.sub herr
  have hu : Tendsto (fun N => harmonicCorrelation (primeSetFlip P) N +
      (1 + Real.log d) / gaugeHarmonicSum (fun _ => 1) N)
        atTop (𝓝 (primeSetHarmonicDensity P)) := by
    simpa only [add_zero] using hmain.add herr
  have hb : ∀ᶠ N : ℕ in atTop,
      harmonicCorrelation (primeSetFlip P) N -
          (1 + Real.log d) / gaugeHarmonicSum (fun _ => 1) N ≤
        gaugeHarmonicSum (primeSetFlip P) (N / d) / gaugeHarmonicSum (fun _ => 1) N ∧
      gaugeHarmonicSum (primeSetFlip P) (N / d) / gaugeHarmonicSum (fun _ => 1) N ≤
        harmonicCorrelation (primeSetFlip P) N +
          (1 + Real.log d) / gaugeHarmonicSum (fun _ => 1) N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hH := gaugeHarmonicSum_one_pos hN
    have hshell := (signed_harmonic_shell_le (primeSetFlip P) (primeSetFlip_sign P)
      (Nat.div_le_self N d)).trans (harmonicMass_shell hd N).2
    have hpaid := div_le_div_of_nonneg_right hshell hH.le
    have he : (gaugeHarmonicSum (primeSetFlip P) N -
        gaugeHarmonicSum (primeSetFlip P) (N / d)) / gaugeHarmonicSum (fun _ => 1) N =
        harmonicCorrelation (primeSetFlip P) N -
          gaugeHarmonicSum (primeSetFlip P) (N / d) / gaugeHarmonicSum (fun _ => 1) N := by
      rw [harmonicCorrelation, sub_div]
    have hbound : |harmonicCorrelation (primeSetFlip P) N -
        gaugeHarmonicSum (primeSetFlip P) (N / d) / gaugeHarmonicSum (fun _ => 1) N| ≤
          (1 + Real.log d) / gaugeHarmonicSum (fun _ => 1) N := by
      rw [← he, abs_div, abs_of_pos hH]
      exact hpaid
    obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
    constructor <;> linarith only [hlo, hhi]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- The actual harmonic Ramanujan mean is the Euler density times the
literal Möbius transform, for every prime pattern and conductor. -/
theorem primeSetRamanujanSum_tendsto (P : Set ℕ) (m : ℕ) :
    Tendsto (fun N : ℕ => primeSetRamanujanSum P m N / gaugeHarmonicSum (fun _ => 1) N)
      atTop (𝓝 (primeSetHarmonicDensity P * primeSetMobius P m)) := by
  have hlim := tendsto_finsetSum m.divisors (fun d hd =>
    (primeSet_decimation_tendsto P (Nat.pos_of_mem_divisors hd)).const_mul
      (moebiusReal (m / d) * primeSetFlip P d))
  simpa only [primeSetRamanujanSum_eq, sum_div, mul_div_assoc, ← sum_mul,
    mul_comm (primeSetHarmonicDensity P), primeSetMobius] using hlim

end GaloisForLFunctions.ArithmeticCountingPositivity
