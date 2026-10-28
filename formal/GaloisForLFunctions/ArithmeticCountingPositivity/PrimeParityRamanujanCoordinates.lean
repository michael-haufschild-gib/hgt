import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityPairing
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# Harmonic Ramanujan coordinates of prime parity

Divisibility incidence expresses the mixed harmonic count as a finite Mobius
sum of decimated parity counts. Their bounded boundary errors determine its
limit. Every nontrivial conductor coprime to the flipped prime has zero limit.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.BezoutValuationIncidence

/-- Multiplicativity retains the exact harmonic count on a divisibility fibre. -/
theorem gaugeHarmonicSum_multiples (ω : ℕ → ℝ) (hω : IsSignGauge ω)
    {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), ω n / n) =
      ω d / d * gaugeHarmonicSum ω (N / d) := by
  rw [filter_dvd_Icc_eq_image hd,
    sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h),
    gaugeHarmonicSum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [hω.mul hd.ne' (Nat.ne_of_gt (mem_Icc.mp hn).1), Nat.cast_mul]
  ring

/-- The divisor weight cancels the harmonic cost of entering its fibre. -/
theorem gaugeHarmonicSum_divisibility (ω : ℕ → ℝ) (hω : IsSignGauge ω)
    {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ω n * (if d ∣ n then (d : ℝ) else 0) / n) =
      ω d * gaugeHarmonicSum ω (N / d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = (d : ℝ) * ∑ n ∈ (Icc 1 N).filter (d ∣ ·), ω n / n := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    _ = _ := by
      rw [gaugeHarmonicSum_multiples ω hω hd]
      field_simp [hdR]

/-- The signed harmonic pairing with an unnormalized Ramanujan conductor. -/
def primeParityRamanujanSum (p m N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, finiteFlip {p} n * ramanujanLagCoefficient m n / n

/-- Mobius inversion turns the mixed count into exact decimated parity counts. -/
theorem primeParityRamanujanSum_eq (p m N : ℕ) :
    primeParityRamanujanSum p m N =
      ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d *
        gaugeHarmonicSum (finiteFlip {p}) (N / d) := by
  unfold primeParityRamanujanSum ramanujanLagCoefficient
  simp_rw [mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have he : (∑ n ∈ Icc 1 N, finiteFlip {p} n *
      (moebiusReal (m / d) * (if d ∣ n then (d : ℝ) else 0)) / n) =
      moebiusReal (m / d) *
        ∑ n ∈ Icc 1 N, finiteFlip {p} n * (if d ∣ n then (d : ℝ) else 0) / n := by
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [he, gaugeHarmonicSum_divisibility (finiteFlip {p})
    (finiteFlip_isSignGauge {p}) (Nat.pos_of_mem_divisors hd)]
  ring

/-- A fixed decimation changes the parity mean by a bounded boundary error. -/
theorem primeParity_decimation_error {p d : ℕ} (hp : p.Prime) (hd : 0 < d) (N : ℕ) :
    |gaugeHarmonicSum (finiteFlip {p}) (N / d) -
        ((p : ℝ) - 1) / ((p : ℝ) + 1) * gaugeHarmonicSum (fun _ => 1) N| ≤
      2 * (1 + Real.log p) / ((p : ℝ) + 1) +
        ((p : ℝ) - 1) / ((p : ℝ) + 1) * (1 + Real.log d) := by
  let c := ((p : ℝ) - 1) / ((p : ℝ) + 1)
  let K := 2 * (1 + Real.log p) / ((p : ℝ) + 1)
  have hp1 : 0 < (p : ℝ) + 1 := by positivity
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hpR) hp1.le
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (by norm_num) (by positivity : 0 ≤ 1 + Real.log p)) hp1.le
  have hboundary := prime_parity_boundary_bounds hp (N / d)
  have he : gaugeHarmonicSum (finiteFlip {p}) (N / d) -
      c * gaugeHarmonicSum (fun _ => 1) (N / d) =
      (((p : ℝ) + 1) * gaugeHarmonicSum (finiteFlip {p}) (N / d) -
        ((p : ℝ) - 1) * gaugeHarmonicSum (fun _ => 1) (N / d)) / ((p : ℝ) + 1) := by
    dsimp only [c]
    field_simp [hp1.ne']
  have he0 : 0 ≤ gaugeHarmonicSum (finiteFlip {p}) (N / d) -
      c * gaugeHarmonicSum (fun _ => 1) (N / d) := by
    rw [he]
    exact div_nonneg hboundary.1 hp1.le
  have heK : gaugeHarmonicSum (finiteFlip {p}) (N / d) -
      c * gaugeHarmonicSum (fun _ => 1) (N / d) ≤ K := by
    rw [he]
    exact div_le_div_of_nonneg_right hboundary.2 hp1.le
  have hmono : gaugeHarmonicSum (fun _ => 1) (N / d) ≤
      gaugeHarmonicSum (fun _ => 1) N := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (Nat.div_le_self N d)⟩
    · intro n _ _
      positivity
  have htail := roughHarmonic_sub_div_le 0 N hd
  simp only [roughHarmonic, roughInterval_zero] at htail
  change gaugeHarmonicSum (fun _ => 1) N -
    gaugeHarmonicSum (fun _ => 1) (N / d) ≤ 1 + Real.log d at htail
  have hcost := mul_le_mul_of_nonneg_left htail hc
  have hcost0 : 0 ≤ c * (1 + Real.log d) := by positivity
  have hmonoc := mul_le_mul_of_nonneg_left hmono hc
  change |gaugeHarmonicSum (finiteFlip {p}) (N / d) -
    c * gaugeHarmonicSum (fun _ => 1) N| ≤ K + c * (1 + Real.log d)
  rw [abs_le]
  constructor
  · nlinarith only [he0, hcost, hK]
  · linarith only [heK, hmonoc, hcost0]

/-- Decimation by a fixed positive integer preserves the normalized parity mean. -/
theorem primeParity_decimation_tendsto {p d : ℕ} (hp : p.Prime) (hd : 0 < d) :
    Tendsto (fun N : ℕ => gaugeHarmonicSum (finiteFlip {p}) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N) atTop
      (𝓝 (((p : ℝ) - 1) / ((p : ℝ) + 1))) := by
  let c := ((p : ℝ) - 1) / ((p : ℝ) + 1)
  let C := 2 * (1 + Real.log p) / ((p : ℝ) + 1) + c * (1 + Real.log d)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (C / ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hH := gaugeHarmonicSum_one_pos hN1
  have hlarge : C / ε < gaugeHarmonicSum (fun _ => 1) N :=
    (hN₀ N ((le_max_right _ _).trans hN)).trans_le (log_le_gaugeHarmonicSum_one hN1)
  have hsmall : C / gaugeHarmonicSum (fun _ => 1) N < ε := by
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hH]
    nlinarith only [hlarge]
  have he : gaugeHarmonicSum (finiteFlip {p}) (N / d) /
      gaugeHarmonicSum (fun _ => 1) N - c =
      (gaugeHarmonicSum (finiteFlip {p}) (N / d) -
        c * gaugeHarmonicSum (fun _ => 1) N) / gaugeHarmonicSum (fun _ => 1) N := by
    field_simp [hH.ne']
  rw [Real.dist_eq]
  change |gaugeHarmonicSum (finiteFlip {p}) (N / d) /
    gaugeHarmonicSum (fun _ => 1) N - c| < ε
  rw [he, abs_div, abs_of_pos hH]
  exact (div_le_div_of_nonneg_right (primeParity_decimation_error hp hd N) hH.le).trans_lt hsmall

/-- The exact harmonic Ramanujan coordinate is the finite Mobius transform of parity. -/
theorem primeParityRamanujanSum_tendsto {p : ℕ} (hp : p.Prime) (m : ℕ) :
    Tendsto (fun N : ℕ => primeParityRamanujanSum p m N /
      gaugeHarmonicSum (fun _ => 1) N) atTop
      (𝓝 (((p : ℝ) - 1) / ((p : ℝ) + 1) *
        ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d)) := by
  have hlim := tendsto_finsetSum m.divisors (fun d hd =>
    (primeParity_decimation_tendsto hp (Nat.pos_of_mem_divisors hd)).const_mul
      (moebiusReal (m / d) * finiteFlip {p} d))
  simpa only [primeParityRamanujanSum_eq, sum_div, mul_div_assoc, ← sum_mul,
    mul_comm (((p : ℝ) - 1) / ((p : ℝ) + 1))] using hlim

/-- A prime flip has no nontrivial coprime conductor coordinate in harmonic mean. -/
theorem primeParityRamanujanSum_tendsto_zero {p m : ℕ} (hp : p.Prime)
    (hm : 2 ≤ m) (hpm : ¬ p ∣ m) :
    Tendsto (fun N : ℕ => primeParityRamanujanSum p m N /
      gaugeHarmonicSum (fun _ => 1) N) atTop (𝓝 0) := by
  have hflip : ∀ d ∈ m.divisors, finiteFlip {p} d = 1 := by
    intro d hd
    apply finiteFlip_eq_one_of_coprime
    simpa only [mem_singleton, forall_eq] using
      (show ¬ p ∣ d from fun hpd => hpm (hpd.trans (Nat.dvd_of_mem_divisors hd)))
  have hsum : (∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip {p} d) = 0 := by
    calc
      _ = ∑ d ∈ m.divisors, moebiusReal (m / d) :=
        sum_congr rfl fun d hd => by rw [hflip d hd, mul_one]
      _ = ∑ d ∈ m.divisors, moebiusReal d := Nat.sum_div_divisors m moebiusReal
      _ = 0 := by
        have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
          (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
        simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
          ArithmeticFunction.intCoe_apply, moebiusReal,
          if_neg (by omega : m ≠ 1)] using h
  simpa only [hsum, mul_zero] using primeParityRamanujanSum_tendsto hp m

end GaloisForLFunctions.ArithmeticCountingPositivity
