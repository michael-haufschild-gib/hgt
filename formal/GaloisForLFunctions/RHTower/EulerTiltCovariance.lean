import GaloisForLFunctions.RHTower.MertensLogSquareSum
import GaloisForLFunctions.RHTower.EulerTiltMeanEnergy
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence

/-!
# Euler-edge covariance sums

The Bernoulli variance weight of the Euler tilt is `w_p = p^{-σ}/(1+p^{-σ})²`.  Because
`w_p = p^{-1}(1 + O(δ log p + p^{-1}))`, the occupancy variance, the parity–energy covariance and
the energy variance are the prime harmonic sums `∑ 1/p`, `∑ log p/p` and `∑ (log p)²/p` up to
absolutely convergent corrections and one tilt correction.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Convergent tail constants -/

theorem logSqSquareTail_summable :
    Summable (fun n : ℕ => Real.log n ^ 2 / (n : ℝ) ^ (2 : ℝ)) := by
  have hcomp : Summable (fun n : ℕ => 16 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left _
  refine hcomp.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
      positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlog := Mertens.log_le_rpow hn0 (show (0 : ℝ) < 1 / 4 by norm_num)
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have hsq : Real.log n ^ 2 ≤ 16 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        have hrp : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (n : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hn0.le]
          norm_num
        have hbase : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
          have h4 : (1 : ℝ) / (1 / 4) = 4 := by norm_num
          rw [h4] at hlog
          exact hlog
        nlinarith [hbase, hlog0, Real.rpow_nonneg hn0.le ((1 : ℝ) / 4), hrp]
      have hn2 : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hn0 _
      rw [div_le_iff₀ hn2]
      have hval : 16 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) * (n : ℝ) ^ (2 : ℝ)
          = 16 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [one_div, ← Real.rpow_neg hn0.le, mul_assoc, ← Real.rpow_add hn0]
        norm_num
      rw [hval]
      exact hsq

/-- The convergent tail `∑ (log n)²/n²`. -/
def logSqSquareTailConst : ℝ := ∑' n : ℕ, Real.log n ^ 2 / (n : ℝ) ^ (2 : ℝ)

theorem logSqSquareTail_nonneg (n : ℕ) : 0 ≤ Real.log n ^ 2 / (n : ℝ) ^ (2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    positivity

theorem sum_logSq_div_sq_le (s : Finset ℕ) :
    ∑ n ∈ s, Real.log n ^ 2 / (n : ℝ) ^ (2 : ℝ) ≤ logSqSquareTailConst :=
  Summable.sum_le_tsum s (fun n _ => logSqSquareTail_nonneg n) logSqSquareTail_summable

theorem invSquareTail_summable : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) :=
  Real.summable_one_div_nat_rpow.mpr (by norm_num)

/-- The convergent tail `∑ 1/n²`. -/
def invSquareTailConst : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 : ℝ)

theorem invSquareTail_nonneg (n : ℕ) : 0 ≤ 1 / (n : ℝ) ^ (2 : ℝ) := by positivity

theorem sum_inv_rpow_two_le (s : Finset ℕ) :
    ∑ n ∈ s, 1 / (n : ℝ) ^ (2 : ℝ) ≤ invSquareTailConst :=
  Summable.sum_le_tsum s (fun n _ => invSquareTail_nonneg n) invSquareTail_summable

/-! ## The Bernoulli variance weight -/

/-- The Bernoulli variance weight `w_p = p^{-σ}/(1+p^{-σ})²`. -/
def eulerTiltWeight (σ : ℝ) (p : ℕ) : ℝ := (p : ℝ) ^ (-σ) / (1 + (p : ℝ) ^ (-σ)) ^ 2

/-- **The variance weight is the prime reciprocal up to a tilt and a square correction.** -/
theorem abs_eulerTiltWeight_sub_inv_le {δ : ℝ} (hδ : 0 ≤ δ) {p : ℕ} (hp : p.Prime) :
    |eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹|
      ≤ δ * (Real.log p / (p : ℝ)) + 3 * (1 / (p : ℝ) ^ (2 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set t : ℝ := (p : ℝ) ^ (-(1 + δ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have htle : t ≤ (p : ℝ) ^ (-(1 : ℝ)) := by
    rw [ht]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hinv : (p : ℝ) ^ (-(1 : ℝ)) = ((p : ℝ))⁻¹ := by
    rw [Real.rpow_neg_one]
  have htsmall : t ≤ ((p : ℝ))⁻¹ := by rwa [hinv] at htle
  have hthalf : t ≤ 1 / 2 := by
    have hinv2 : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  -- the tilt factor
  have hfactor : t = ((p : ℝ))⁻¹ * (p : ℝ) ^ (-δ) := by
    rw [ht, ← hinv, ← Real.rpow_add hp0]
    congr 1
    ring
  have htilt : 1 - (p : ℝ) ^ (-δ) ≤ δ * Real.log p := by
    have hexp : (p : ℝ) ^ (-δ) = Real.exp (-(δ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]
      congr 1
      ring
    have h := Real.add_one_le_exp (-(δ * Real.log p))
    rw [hexp]
    linarith
  have htiltpos : (p : ℝ) ^ (-δ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
      (show -δ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  -- assemble
  have hden : (0 : ℝ) < (1 + t) ^ 2 := by positivity
  have hval : eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹
      = ((p : ℝ))⁻¹ * (((p : ℝ) ^ (-δ) - (1 + t) ^ 2) / (1 + t) ^ 2) := by
    rw [eulerTiltWeight, ← ht, hfactor]
    field_simp
  rw [hval, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((p : ℝ))⁻¹)]
  have hnum : |((p : ℝ) ^ (-δ) - (1 + t) ^ 2) / (1 + t) ^ 2| ≤ δ * Real.log p + 3 * t := by
    have hsplit : |(p : ℝ) ^ (-δ) - (1 + t) ^ 2| ≤ δ * Real.log p + 3 * t := by
      have h1 : (1 + t) ^ 2 - (p : ℝ) ^ (-δ) ≤ 3 * t + δ * Real.log p := by
        nlinarith [htilt, hthalf, ht0]
      have h2 : (p : ℝ) ^ (-δ) - (1 + t) ^ 2 ≤ 0 := by nlinarith [htiltpos, ht0]
      rw [abs_le]
      constructor <;> nlinarith [h1, h2, ht0, hthalf]
    have hone : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith [ht0]
    rw [abs_div, abs_of_pos hden]
    rw [div_le_iff₀ hden]
    nlinarith [hsplit, hone, abs_nonneg ((p : ℝ) ^ (-δ) - (1 + t) ^ 2)]
  have hstep : ((p : ℝ))⁻¹ * |((p : ℝ) ^ (-δ) - (1 + t) ^ 2) / (1 + t) ^ 2|
      ≤ ((p : ℝ))⁻¹ * (δ * Real.log p + 3 * t) :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  refine le_trans hstep ?_
  have hsq : ((p : ℝ))⁻¹ * t ≤ 1 / (p : ℝ) ^ (2 : ℝ) := by
    have hle : ((p : ℝ))⁻¹ * t ≤ ((p : ℝ))⁻¹ * ((p : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left htsmall (by positivity)
    have hval2 : ((p : ℝ))⁻¹ * ((p : ℝ))⁻¹ = 1 / (p : ℝ) ^ (2 : ℝ) := by
      rw [one_div, ← Real.rpow_neg hp0.le, ← hinv, ← Real.rpow_add hp0]
      norm_num
    linarith [hle, hval2]
  have hlogterm : ((p : ℝ))⁻¹ * (δ * Real.log p) = δ * (Real.log p / (p : ℝ)) := by
    field_simp
  nlinarith [hsq, hlogterm, hlog, hδ]

/-! ## The three covariance sums -/

/-- The occupancy variance `Var N = ∑_{p ≤ Y} w_p`. -/
def eulerTiltMass (σ Y : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊Y⌋₊, eulerTiltWeight σ p

/-- The parity–energy covariance `Cov(N, E) = ∑_{p ≤ Y} w_p log p`. -/
def eulerTiltCovariance (σ Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, eulerTiltWeight σ p * Real.log p

/-- The energy variance `Var E = ∑_{p ≤ Y} w_p (log p)²`. -/
def eulerTiltEnergyVariance (σ Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, eulerTiltWeight σ p * Real.log p ^ 2

/-- The prime log-square sum over all primes up to the cutoff. -/
def primeLogSqSumLE (Y : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p ^ 2 / (p : ℝ)

theorem primeLogSqSumLE_nonneg (Y : ℝ) : 0 ≤ primeLogSqSumLE Y := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  positivity

theorem log_le_log_of_mem_primesLE {Y : ℝ} (hY : 2 ≤ Y) {p : ℕ}
    (hp : p ∈ Nat.primesLE ⌊Y⌋₊) : Real.log p ≤ Real.log Y := by
  have hprime := Nat.prime_of_mem_primesLE hp
  have hple : p ≤ ⌊Y⌋₊ := (Nat.mem_primesLE.mp hp).1
  have hpY : (p : ℝ) ≤ Y := by
    have h1 : ((p : ℕ) : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hple
    exact le_trans h1 (Nat.floor_le (by linarith))
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  exact Real.log_le_log hp0 hpY

theorem sum_primesLE_log_div_eq (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / (p : ℝ) = mertensPrimeWeightSum N := by
  rw [mertensPrimeWeightSum_eq, Nat.primesLE, Nat.primesBelow, Finset.sum_filter,
    Finset.sum_filter]
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- **The occupancy variance is the prime reciprocal sum.** -/
theorem abs_eulerTiltMass_sub_mertensS_le {δ Y : ℝ} (hδ : 0 ≤ δ) :
    |eulerTiltMass (1 + δ) Y - Sieve.mertensS ⌊Y⌋₊|
      ≤ δ * mertensPrimeWeightSum ⌊Y⌋₊ + 3 * invSquareTailConst := by
  have hdiff : eulerTiltMass (1 + δ) Y - Sieve.mertensS ⌊Y⌋₊
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹) := by
    rw [eulerTiltMass, Sieve.mertensS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [one_div]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      |eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹|
        ≤ δ * (Real.log p / (p : ℝ)) + 3 * (1 / (p : ℝ) ^ (2 : ℝ)) :=
    fun p hp => abs_eulerTiltWeight_sub_inv_le hδ (Nat.prime_of_mem_primesLE hp)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / (p : ℝ) = mertensPrimeWeightSum ⌊Y⌋₊ :=
    sum_primesLE_log_div_eq _
  have h2 : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, 1 / (p : ℝ) ^ (2 : ℝ) ≤ invSquareTailConst :=
    sum_inv_rpow_two_le _
  have hmass : 0 ≤ mertensPrimeWeightSum ⌊Y⌋₊ := mertensPrimeWeightSum_nonneg _
  rw [h1]
  nlinarith [h2, hδ, hmass]

/-- **The parity–energy covariance is the prime log-density sum.** -/
theorem abs_eulerTiltCovariance_sub_le {δ Y : ℝ} (hδ : 0 ≤ δ) :
    |eulerTiltCovariance (1 + δ) Y - mertensPrimeWeightSum ⌊Y⌋₊|
      ≤ δ * primeLogSqSumLE Y + 3 * logSquareTailConst := by
  have hdiff : eulerTiltCovariance (1 + δ) Y - mertensPrimeWeightSum ⌊Y⌋₊
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        (eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹) * Real.log p := by
    rw [eulerTiltCovariance, ← sum_primesLE_log_div_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    field_simp
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      |(eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹) * Real.log p|
        ≤ δ * (Real.log p ^ 2 / (p : ℝ)) + 3 * (Real.log p / (p : ℝ) ^ (2 : ℝ)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hbase := abs_eulerTiltWeight_sub_inv_le hδ hprime
    rw [abs_mul, abs_of_nonneg hlog]
    have hstep := mul_le_mul_of_nonneg_right hbase hlog
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / (p : ℝ) ^ (2 : ℝ) ≤ logSquareTailConst :=
    sum_log_div_sq_le _
  have hpos : 0 ≤ primeLogSqSumLE Y := primeLogSqSumLE_nonneg Y
  have hval : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p ^ 2 / (p : ℝ) = primeLogSqSumLE Y := rfl
  rw [hval]
  nlinarith [h2, hδ, hpos]

/-- **The energy variance is the prime log-square sum.** -/
theorem abs_eulerTiltEnergyVariance_sub_le {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : 2 ≤ Y) :
    |eulerTiltEnergyVariance (1 + δ) Y - primeLogSqSumLE Y|
      ≤ δ * Real.log Y * primeLogSqSumLE Y + 3 * logSqSquareTailConst := by
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hdiff : eulerTiltEnergyVariance (1 + δ) Y - primeLogSqSumLE Y
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        (eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹) * Real.log p ^ 2 := by
    rw [eulerTiltEnergyVariance, primeLogSqSumLE, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    field_simp
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      |(eulerTiltWeight (1 + δ) p - ((p : ℝ))⁻¹) * Real.log p ^ 2|
        ≤ δ * Real.log Y * (Real.log p ^ 2 / (p : ℝ))
          + 3 * (Real.log p ^ 2 / (p : ℝ) ^ (2 : ℝ)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogle : Real.log p ≤ Real.log Y := log_le_log_of_mem_primesLE hY hp
    have hbase := abs_eulerTiltWeight_sub_inv_le hδ hprime
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log p ^ 2)]
    have hstep := mul_le_mul_of_nonneg_right hbase (by positivity : (0 : ℝ) ≤ Real.log p ^ 2)
    refine le_trans hstep ?_
    have hval : (δ * (Real.log p / (p : ℝ)) + 3 * (1 / (p : ℝ) ^ (2 : ℝ))) * Real.log p ^ 2
        = δ * Real.log p * (Real.log p ^ 2 / (p : ℝ))
          + 3 * (Real.log p ^ 2 / (p : ℝ) ^ (2 : ℝ)) := by
      field_simp
    rw [hval]
    have hmul : δ * Real.log p * (Real.log p ^ 2 / (p : ℝ))
        ≤ δ * Real.log Y * (Real.log p ^ 2 / (p : ℝ)) := by
      have hcoef : δ * Real.log p ≤ δ * Real.log Y := mul_le_mul_of_nonneg_left hlogle hδ
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p ^ 2 / (p : ℝ) ^ (2 : ℝ) ≤ logSqSquareTailConst :=
    sum_logSq_div_sq_le _
  have hpos : 0 ≤ primeLogSqSumLE Y := primeLogSqSumLE_nonneg Y
  have hval : ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p ^ 2 / (p : ℝ) = primeLogSqSumLE Y := rfl
  rw [hval]
  nlinarith [h2, hδ, hpos, hlogY]

/-! ## The Euler-edge asymptotics -/

/-- The floor does not move the double logarithm by more than one. -/
theorem abs_logLog_floor_sub_le {Y : ℝ} (hY : Real.exp 2 ≤ Y) :
    |Sieve.logLog ⌊Y⌋₊ - Real.log (Real.log Y)| ≤ 1 := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hfloor6 : (6 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Y))
    exact_mod_cast h
  have hfloorle : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hfloorge : Y - 1 ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one Y
    linarith
  have hflog0 : 0 < Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hYlog : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y :=
    Real.log_le_log (by linarith) hfloorle
  have hYlog2 : (2 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos 2) hY
    rwa [Real.log_exp] at h
  -- the gap between the two logarithms
  have hgap : Real.log Y - Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ 1 := by
    have hratio : (0 : ℝ) < Y / ((⌊Y⌋₊ : ℕ) : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (by linarith) (by linarith)] at h
    have hquot : Y / ((⌊Y⌋₊ : ℕ) : ℝ) - 1 ≤ 1 := by
      rw [div_sub_one (by linarith), div_le_one (by linarith)]
      linarith
    linarith
  have hlogYpos : 0 < Real.log Y := by linarith
  -- compare the double logarithms
  have hupper : Sieve.logLog ⌊Y⌋₊ ≤ Real.log (Real.log Y) := by
    rw [Sieve.logLog]
    exact Real.log_le_log hflog0 hYlog
  have hlower : Real.log (Real.log Y) - Sieve.logLog ⌊Y⌋₊ ≤ 1 := by
    rw [Sieve.logLog]
    have hratio : (0 : ℝ) < Real.log Y / Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (by linarith) (by linarith)] at h
    have hquot : Real.log Y / Real.log ((⌊Y⌋₊ : ℕ) : ℝ) - 1 ≤ 1 := by
      rw [div_sub_one (by linarith), div_le_one (by linarith)]
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The constant of the Euler-edge occupancy law. -/
def eulerTiltMassConst : ℝ :=
  |Sieve.meisselMertensConst| + (2 * Sieve.mertensFirstConst + 1 / 2) + 1
    + 3 * invSquareTailConst

/-- **(11a) The occupancy variance is `log log Y + O(1)`**, with an explicit tilt correction. -/
theorem abs_eulerTiltMass_sub_logLog_le {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : Real.exp 2 ≤ Y) :
    |eulerTiltMass (1 + δ) Y - Real.log (Real.log Y)|
      ≤ eulerTiltMassConst + δ * (Real.log Y + (mertensPrimeWindowBound + 1)) := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hY7 : (7 : ℝ) < Y := lt_of_lt_of_le hexp2 hY
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ Y))
  have hflog : (0 : ℝ) < Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h6 : (6 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
      have h : (6 : ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Y))
      exact_mod_cast h
    exact Real.log_pos (by linarith)
  have hmass := abs_eulerTiltMass_sub_mertensS_le (δ := δ) (Y := Y) hδ
  have hmertens := Sieve.abs_mertensS_sub_logLog_sub_const_le hfloor2
  have hfloorlog := abs_logLog_floor_sub_le hY
  have hweight := abs_mertensPrimeWeightSum_floor_sub_log_le hY2
  have hlogone : (1 : ℝ) ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    have h6 : (6 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by
      have h : (6 : ℕ) ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Y))
      exact_mod_cast h
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ ((⌊Y⌋₊ : ℕ) : ℝ) by
      have hexp1 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith)
    rwa [Real.log_exp] at h
  have hdiv : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊Y⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have hnum : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
      have := Sieve.mertensFirstConst_nonneg
      linarith
    rw [div_le_iff₀ hflog]
    nlinarith [hnum, hlogone]
  have hb1 := abs_le.mp hmass
  have hb2 := abs_le.mp hmertens
  have hb3 := abs_le.mp hfloorlog
  have hb4 := abs_le.mp hweight
  have hmeissel : |Sieve.meisselMertensConst| = |Sieve.meisselMertensConst| := rfl
  have hmabs : Sieve.meisselMertensConst ≤ |Sieve.meisselMertensConst| := le_abs_self _
  have hmabs' : -|Sieve.meisselMertensConst| ≤ Sieve.meisselMertensConst := neg_abs_le _
  have hinv : 0 ≤ invSquareTailConst := by
    rw [invSquareTailConst]
    exact tsum_nonneg invSquareTail_nonneg
  rw [eulerTiltMassConst, abs_le]
  constructor
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2, hdiv, hmabs, hmabs',
      hδ, hinv]
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2, hdiv, hmabs, hmabs',
      hδ, hinv]

/-- The prime log-square sum over all primes, in terms of the window sum. -/
theorem primeLogSqSumLE_eq {Y : ℝ} (hY : 2 ≤ Y) :
    primeLogSqSumLE Y = Real.log 2 ^ 2 / 2 + primeLogSqSumIoc Y := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have h := sum_primesLE_eq_add_sum_Ioc
    (fun p : ℕ => Real.log p ^ 2 / (p : ℝ)) hfloor
  rw [primeLogSqSumLE, h, primeLogSqSumIoc]
  norm_num

/-- **Mertens' second moment over all primes.** -/
theorem abs_primeLogSqSumLE_sub_le {Y : ℝ} (hY : 2 ≤ Y) :
    |primeLogSqSumLE Y - Real.log Y ^ 2 / 2|
      ≤ mertensLogSqConst * (1 + Real.log Y) + Real.log 2 ^ 2 / 2 := by
  have hsplit := primeLogSqSumLE_eq hY
  have hwindow := abs_primeLogSqSumIoc_sub_le hY
  have hlog2 : (0 : ℝ) ≤ Real.log 2 ^ 2 / 2 := by positivity
  have hb := abs_le.mp hwindow
  rw [hsplit, abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- **(11b) The parity–energy covariance is `log Y + O(1 + δ (log Y)²)`.** -/
theorem abs_eulerTiltCovariance_sub_log_le {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : 2 ≤ Y) :
    |eulerTiltCovariance (1 + δ) Y - Real.log Y|
      ≤ (mertensPrimeWindowBound + 1) + 3 * logSquareTailConst
        + δ * (Real.log Y ^ 2 / 2 + mertensLogSqConst * (1 + Real.log Y)
          + Real.log 2 ^ 2 / 2) := by
  have hcov := abs_eulerTiltCovariance_sub_le (δ := δ) (Y := Y) hδ
  have hweight := abs_mertensPrimeWeightSum_floor_sub_log_le hY
  have hsq := abs_primeLogSqSumLE_sub_le hY
  have hb1 := abs_le.mp hcov
  have hb2 := abs_le.mp hweight
  have hb3 := abs_le.mp hsq
  rw [abs_le]
  constructor
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hδ]
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hδ]

/-- **(11c) The energy variance is `(log Y)²/2 + O(log Y + δ (log Y)³)`.** -/
theorem abs_eulerTiltEnergyVariance_sub_logSq_le {δ Y : ℝ} (hδ : 0 ≤ δ) (hY : 2 ≤ Y) :
    |eulerTiltEnergyVariance (1 + δ) Y - Real.log Y ^ 2 / 2|
      ≤ mertensLogSqConst * (1 + Real.log Y) + Real.log 2 ^ 2 / 2
        + 3 * logSqSquareTailConst
        + δ * Real.log Y * (Real.log Y ^ 2 / 2 + mertensLogSqConst * (1 + Real.log Y)
          + Real.log 2 ^ 2 / 2) := by
  have hvar := abs_eulerTiltEnergyVariance_sub_le (δ := δ) (Y := Y) hδ hY
  have hsq := abs_primeLogSqSumLE_sub_le hY
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hb1 := abs_le.mp hvar
  have hb2 := abs_le.mp hsq
  have hprod : δ * Real.log Y * primeLogSqSumLE Y
      ≤ δ * Real.log Y * (Real.log Y ^ 2 / 2 + mertensLogSqConst * (1 + Real.log Y)
        + Real.log 2 ^ 2 / 2) := by
    have hle : primeLogSqSumLE Y ≤ Real.log Y ^ 2 / 2 + mertensLogSqConst * (1 + Real.log Y)
        + Real.log 2 ^ 2 / 2 := by linarith [hb2.2]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  rw [abs_le]
  constructor
  · linarith [hb1.1, hb1.2, hb2.1, hb2.2, hprod]
  · linarith [hb1.1, hb1.2, hb2.1, hb2.2, hprod]

end

end RHTower
