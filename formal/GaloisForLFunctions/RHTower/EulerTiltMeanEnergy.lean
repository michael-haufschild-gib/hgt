import GaloisForLFunctions.RHTower.TiltedPrimeLogSum
import GaloisForLFunctions.RHTower.RouteESaddlePntTransport
import GaloisForLFunctions.RHTower.SpurCumulantBounds

/-!
# The Bernoulli mean energy of the Euler tilt

For a prime cutoff `Y` and a tilt `σ = 1 + δ` the Bernoulli mean energy of the source-faithful
Euler tilt is

```text
μ(σ, Y) = ∑_{p ≤ Y} p^{-σ} log p / (1 + p^{-σ}).
```

The Euler denominators cost only an absolutely convergent correction, so the tilted prime sum
controls the mean energy, and the elementary Taylor expansion of `(1 - Y^{-δ})/δ` gives the exact
cofactor law

```text
μ(1 + δ, Y) = log Y - δ (log Y)² / 2 + O(δ² (log Y)³ + 1),
```

uniformly for `δ ∈ (0, 1]`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## The convergent prime-power correction -/

/-- The absolutely convergent tail constant `∑_n log n / n²`. -/
def logSquareTailConst : ℝ := ∑' n : ℕ, Real.log n / (n : ℝ) ^ (2 : ℝ)

theorem logSquareTail_summable : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ (2 : ℝ)) :=
  Mertens.summable_log_div_rpow (by norm_num)

theorem logSquareTail_nonneg (n : ℕ) : 0 ≤ Real.log n / (n : ℝ) ^ (2 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    positivity

theorem logSquareTailConst_nonneg : 0 ≤ logSquareTailConst :=
  tsum_nonneg logSquareTail_nonneg

theorem sum_log_div_sq_le (s : Finset ℕ) :
    ∑ n ∈ s, Real.log n / (n : ℝ) ^ (2 : ℝ) ≤ logSquareTailConst :=
  Summable.sum_le_tsum s (fun n _ => logSquareTail_nonneg n) logSquareTail_summable

/-! ## The mean energy -/

/-- The Bernoulli mean energy of the Euler tilt at abscissa `σ` and cutoff `Y`. -/
def eulerTiltMeanEnergy (σ Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-σ) * Real.log p / (1 + (p : ℝ) ^ (-σ))

/-- The tilted prime logarithm sum over all primes up to the cutoff. -/
def tiltedPrimeLogSumLE (δ Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-δ - 1) * Real.log p

theorem tiltedPrimeLogSumLE_eq {δ Y : ℝ} (hY : 2 ≤ Y) :
    tiltedPrimeLogSumLE δ Y
      = (2 : ℝ) ^ (-δ - 1) * Real.log 2 + tiltedPrimeLogSum δ Y := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have h := sum_primesLE_eq_add_sum_Ioc
    (fun p : ℕ => (p : ℝ) ^ (-δ - 1) * Real.log p) hfloor
  rw [tiltedPrimeLogSumLE, h, tiltedPrimeLogSum, primeRpowLogSumIoc]
  norm_num

/-- **The Euler denominators cost one absolutely convergent constant.** -/
theorem abs_eulerTiltMeanEnergy_sub_le {δ Y : ℝ} (hδ : 0 ≤ δ) :
    |eulerTiltMeanEnergy (1 + δ) Y - tiltedPrimeLogSumLE δ Y| ≤ logSquareTailConst := by
  have hdiff : eulerTiltMeanEnergy (1 + δ) Y - tiltedPrimeLogSumLE δ Y
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        ((p : ℝ) ^ (-(1 + δ)) * Real.log p / (1 + (p : ℝ) ^ (-(1 + δ)))
          - (p : ℝ) ^ (-δ - 1) * Real.log p) := by
    rw [eulerTiltMeanEnergy, tiltedPrimeLogSumLE, ← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
    (sum_log_div_sq_le (Nat.primesLE ⌊Y⌋₊))
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hexp : (-(1 + δ) : ℝ) = -δ - 1 := by ring
  rw [hexp]
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-δ - 1) := Real.rpow_pos_of_pos hp0 _
  have hden : (0 : ℝ) < 1 + (p : ℝ) ^ (-δ - 1) := by linarith
  have hval : (p : ℝ) ^ (-δ - 1) * Real.log p / (1 + (p : ℝ) ^ (-δ - 1))
      - (p : ℝ) ^ (-δ - 1) * Real.log p
      = -(((p : ℝ) ^ (-δ - 1)) ^ 2 * Real.log p / (1 + (p : ℝ) ^ (-δ - 1))) := by
    field_simp
    ring
  rw [hval, abs_neg, abs_of_nonneg (by positivity)]
  -- the squared tilt is below the square weight
  have hsq : ((p : ℝ) ^ (-δ - 1)) ^ 2 ≤ ((p : ℝ) ^ (2 : ℝ))⁻¹ := by
    have hmul : ((p : ℝ) ^ (-δ - 1)) ^ 2 = (p : ℝ) ^ (2 * (-δ - 1)) := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (-δ - 1)) 2, ← Real.rpow_mul hp0.le]
      norm_num
      ring_nf
    rw [hmul, ← Real.rpow_neg hp0.le]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    linarith
  have hA : (0 : ℝ) ≤ ((p : ℝ) ^ (-δ - 1)) ^ 2 * Real.log p := by positivity
  have hstep : ((p : ℝ) ^ (-δ - 1)) ^ 2 * Real.log p / (1 + (p : ℝ) ^ (-δ - 1))
      ≤ ((p : ℝ) ^ (-δ - 1)) ^ 2 * Real.log p := by
    rw [div_le_iff₀ hden]
    nlinarith [hA, hrp]
  refine le_trans hstep ?_
  rw [div_eq_inv_mul, ← Real.rpow_neg hp0.le]
  have hle : ((p : ℝ) ^ (-δ - 1)) ^ 2 * Real.log p ≤ (p : ℝ) ^ (-(2 : ℝ)) * Real.log p := by
    have h := hsq
    rw [← Real.rpow_neg hp0.le] at h
    exact mul_le_mul_of_nonneg_right h hlog
  exact hle

/-! ## The Taylor expansion of the tilted main term -/

/-- **The cubic Taylor bound for the tilted main term.**  This is the corpus truncation bound
`|exp(-y) - Σ_{p<P} (-y)^p/p!| ≤ y^P/P!` at `P = 3`. -/
theorem abs_exp_neg_sub_quadratic_le {y : ℝ} (hy : 0 ≤ y) :
    |Real.exp (-y) - (1 - y + y ^ 2 / 2)| ≤ y ^ 3 / 6 := by
  have h := expNegTruncError_le_pow_div_factorial 3 hy
  rw [expNegTruncError] at h
  have hpoly : (expNegTruncPoly 3).eval y = 1 - y + y ^ 2 / 2 := by
    simp [expNegTruncPoly, Finset.sum_range_succ]
    ring
  rw [hpoly] at h
  norm_num at h
  exact h

/-! ## The cofactor law -/

/-- The uniform constant of the mean-energy cofactor law. -/
def eulerTiltEnergyConst : ℝ :=
  tiltedPrimeLogSumConst + logSquareTailConst + Real.log 2

theorem abs_main_sub_expansion_le {δ Y : ℝ} (hδ0 : 0 < δ) (hY : 2 ≤ Y) :
    |(1 - Y ^ (-δ)) / δ - (Real.log Y - δ * Real.log Y ^ 2 / 2)|
      ≤ δ ^ 2 * Real.log Y ^ 3 / 6 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hy : 0 ≤ δ * Real.log Y := by positivity
  have hrp : Y ^ (-δ) = Real.exp (-(δ * Real.log Y)) := by
    rw [Real.rpow_def_of_pos hY0]
    congr 1
    ring
  have htaylor := abs_exp_neg_sub_quadratic_le hy
  have hval : (1 - Y ^ (-δ)) / δ - (Real.log Y - δ * Real.log Y ^ 2 / 2)
      = -((Real.exp (-(δ * Real.log Y))
          - (1 - δ * Real.log Y + (δ * Real.log Y) ^ 2 / 2)) / δ) := by
    rw [hrp]
    field_simp
    ring
  rw [hval, abs_neg, abs_div, abs_of_pos hδ0, div_le_iff₀ hδ0]
  have hcube : (δ * Real.log Y) ^ 3 / 6 = δ ^ 2 * Real.log Y ^ 3 / 6 * δ := by ring
  rw [← hcube]
  exact htaylor

/-- **The cofactor law of the Bernoulli mean energy.**  Uniformly in the tilt `δ ∈ (0,1]`,
`μ(1+δ, Y) = log Y - δ (log Y)²/2 + O(δ² (log Y)³ + 1)`. -/
theorem abs_eulerTiltMeanEnergy_sub_expansion_le {δ Y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hY : 2 ≤ Y) :
    |eulerTiltMeanEnergy (1 + δ) Y - (Real.log Y - δ * Real.log Y ^ 2 / 2)|
      ≤ eulerTiltEnergyConst + δ ^ 2 * Real.log Y ^ 3 / 6 := by
  have hdenom := abs_eulerTiltMeanEnergy_sub_le (δ := δ) (Y := Y) hδ0.le
  have hsplit := tiltedPrimeLogSumLE_eq (δ := δ) hY
  have htilt := abs_tiltedPrimeLogSum_sub_le hδ0 hδ1 hY
  have hmain := abs_main_sub_expansion_le hδ0 hY
  have hbase : |(2 : ℝ) ^ (-δ - 1) * Real.log 2| ≤ Real.log 2 := by
    have hrp : (2 : ℝ) ^ (-δ - 1) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show -δ - 1 ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h
    have hrp0 : (0 : ℝ) < (2 : ℝ) ^ (-δ - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [abs_mul, abs_of_pos hrp0, abs_of_nonneg hlog2]
    nlinarith [hrp, hrp0, hlog2]
  have hchain : eulerTiltMeanEnergy (1 + δ) Y - (Real.log Y - δ * Real.log Y ^ 2 / 2)
      = (eulerTiltMeanEnergy (1 + δ) Y - tiltedPrimeLogSumLE δ Y)
        + (2 : ℝ) ^ (-δ - 1) * Real.log 2
        + (tiltedPrimeLogSum δ Y - (1 - Y ^ (-δ)) / δ)
        + ((1 - Y ^ (-δ)) / δ - (Real.log Y - δ * Real.log Y ^ 2 / 2)) := by
    rw [hsplit]
    ring
  rw [hchain, eulerTiltEnergyConst]
  have h1 := abs_le.mp hdenom
  have h2 := abs_le.mp hbase
  have h3 := abs_le.mp htilt
  have h4 := abs_le.mp hmain
  rw [abs_le]
  constructor
  · linarith [h1.1, h2.1, h3.1, h4.1]
  · linarith [h1.2, h2.2, h3.2, h4.2]

end

end RHTower
