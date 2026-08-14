import GaloisForLFunctions.RHTower.PrimeWindowLawNoLog
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Prime-number-theorem transport of the physical Euler saddle

The positive squared Euler law `∏_{p ≤ Y}(1 + p^{-σ})²` is a Bernoulli product whose logarithmic
centre and variance are prime sums.  For `1/2 ≤ σ < 1` and `a = 1 - σ`, Abel summation against
the Chebyshev function gives

```text
∑_{p ≤ Y} p^{-σ} log p       = (Y^a/a)(1 + o(1)),
∑_{p ≤ Y} p^{-2σ} log p      = O(log Y)                     (Mertens' first theorem),
Λ_{σ,Y} = 2∑_{p≤Y} q_p log p = (2/a) Y^a (1 + o(1)),
Var_{σ,Y}                    = (2/a) Y^a log Y (1 + o(1)),
```

with `q_p = p^{-σ}/(1 + p^{-σ})`.  The denominator corrections are controlled by
`p^{-2σ} ≤ p^{-1}` for `σ ≥ 1/2`, so Mertens' first theorem bounds them by `log Y + log 4`, which
is negligible against `Y^a`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Sums over all primes below a bound -/

/-- Splitting a prime sum into its first term and the window `(2, N]`. -/
theorem sum_primesLE_eq_add_sum_Ioc (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, f p
      = f 2 + ∑ k ∈ Finset.Ioc 2 N, (if k.Prime then f k else 0) := by
  classical
  have hfilter : ∑ p ∈ Nat.primesLE N, f p
      = ∑ k ∈ Finset.range (N + 1), (if k.Prime then f k else 0) := by
    rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  have hset : Finset.Ico 3 (N + 1) = Finset.Ioc 2 N := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hsplit := Finset.sum_Ico_consecutive
    (fun k : ℕ => (if k.Prime then f k else 0)) (show 0 ≤ 3 by omega)
    (show 3 ≤ N + 1 by omega)
  rw [hfilter, Finset.range_eq_Ico, ← hsplit, hset]
  congr 1
  have h3 : Finset.Ico 0 3 = ({0, 1, 2} : Finset ℕ) := by decide
  rw [h3]
  norm_num [Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]

/-- The prime power–logarithm sum over all primes below `Y`. -/
def primeRpowLogSumLE (a Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1) * Real.log p

theorem primeRpowLogSumLE_eq_add {a Y : ℝ} (hY : 2 ≤ Y) :
    primeRpowLogSumLE a Y = (2 : ℝ) ^ (a - 1) * Real.log 2 + primeRpowLogSumIoc a Y := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  rw [primeRpowLogSumLE, sum_primesLE_eq_add_sum_Ioc _ hfloor, primeRpowLogSumIoc]
  norm_num

/-- **The prime power–logarithm sum over all primes below `Y`.** -/
theorem tendsto_primeRpowLogSumLE {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun Y : ℝ => primeRpowLogSumLE a Y / Y ^ a) atTop (nhds (1 / a)) := by
  have hconst : Tendsto (fun Y : ℝ => (2 : ℝ) ^ (a - 1) * Real.log 2 / Y ^ a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
  have h := hconst.add (tendsto_primeRpowLogSumIoc ha0)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  rw [primeRpowLogSumLE_eq_add hY, add_div]

/-! ## The Mertens deficit of the Euler tilt -/

/-- The second-order Euler deficit `∑_{p ≤ Y} p^{-2σ} log p / (1 + p^{-σ})`. -/
def eulerTiltDeficit (σ Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-2 * σ) * Real.log p / (1 + (p : ℝ) ^ (-σ))

theorem eulerTiltDeficit_nonneg (σ : ℝ) (Y : ℝ) : 0 ≤ eulerTiltDeficit σ Y := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  have h1 : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) := Real.rpow_nonneg hp0.le _
  have h2 : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) := by
    have : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    linarith
  exact div_nonneg (mul_nonneg h1 hlog) h2.le

theorem eulerTiltDeficit_le {σ Y : ℝ} (hσ : 1 / 2 ≤ σ) (hY : 2 ≤ Y) :
    eulerTiltDeficit σ Y ≤ Real.log ⌊Y⌋₊ + Real.log 4 := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  refine le_trans (Finset.sum_le_sum ?_) (Sieve.mertensFirst_upper (by omega : 1 ≤ ⌊Y⌋₊))
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
  have hdenom : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) := by
    have : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    linarith
  have hone : (1 : ℝ) ≤ 1 + (p : ℝ) ^ (-σ) := by
    have : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
    linarith
  have hexp : (p : ℝ) ^ (-2 * σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hinv : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ)⁻¹ := by
    rw [Real.rpow_neg hp0.le, Real.rpow_one]
  calc (p : ℝ) ^ (-2 * σ) * Real.log p / (1 + (p : ℝ) ^ (-σ))
      ≤ (p : ℝ) ^ (-2 * σ) * Real.log p / 1 := by
        apply div_le_div_of_nonneg_left _ (by norm_num) hone
        exact mul_nonneg (Real.rpow_nonneg hp0.le _) hlog
    _ = (p : ℝ) ^ (-2 * σ) * Real.log p := by ring
    _ ≤ (p : ℝ)⁻¹ * Real.log p := by
        rw [← hinv]
        exact mul_le_mul_of_nonneg_right hexp hlog
    _ = Real.log p / (p : ℝ) := by
        rw [inv_mul_eq_div]

/-- **The Euler tilt deficit is negligible.** -/
theorem tendsto_eulerTiltDeficit {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun Y : ℝ => eulerTiltDeficit σ Y / Y ^ (1 - σ)) atTop (nhds 0) := by
  have ha0 : (0 : ℝ) < 1 - σ := by linarith
  have hmajor : Tendsto (fun Y : ℝ => (Real.log Y + Real.log 4) / Y ^ (1 - σ)) atTop (nhds 0) := by
    have hlog : Tendsto (fun Y : ℝ => Real.log Y / Y ^ (1 - σ)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
    have hconst : Tendsto (fun Y : ℝ => Real.log 4 / Y ^ (1 - σ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
    have h := hlog.add hconst
    rw [add_zero] at h
    refine h.congr fun Y => ?_
    rw [add_div]
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact div_nonneg (eulerTiltDeficit_nonneg σ Y) (Real.rpow_pos_of_pos hY _).le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hYa : (0 : ℝ) < Y ^ (1 - σ) := Real.rpow_pos_of_pos hY0 _
    have hfloorle : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le hY0.le
    have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
    have hfloorpos : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by
      have : (0 : ℕ) < ⌊Y⌋₊ := by omega
      exact_mod_cast this
    have hlogle : Real.log ⌊Y⌋₊ ≤ Real.log Y := Real.log_le_log hfloorpos hfloorle
    have hnum : eulerTiltDeficit σ Y ≤ Real.log Y + Real.log 4 :=
      le_trans (eulerTiltDeficit_le hσ hY) (by linarith)
    exact div_le_div_of_nonneg_right hnum hYa.le

/-! ## The physical saddle centre -/

/-- The logarithmic centre `Λ_{σ,Y} = 2∑_{p ≤ Y} q_p log p` of the positive squared Euler law. -/
def saddleLogCenter (σ Y : ℝ) : ℝ :=
  2 * ∑ p ∈ Nat.primesLE ⌊Y⌋₊, ((p : ℝ) ^ (-σ) / (1 + (p : ℝ) ^ (-σ))) * Real.log p

theorem saddleLogCenter_eq (σ Y : ℝ) :
    saddleLogCenter σ Y = 2 * (primeRpowLogSumLE (1 - σ) Y - eulerTiltDeficit σ Y) := by
  rw [saddleLogCenter, primeRpowLogSumLE, eulerTiltDeficit, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hu : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
  have hdenom : (1 : ℝ) + (p : ℝ) ^ (-σ) ≠ 0 := by linarith
  have hsq : (p : ℝ) ^ (-2 * σ) = (p : ℝ) ^ (-σ) * (p : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hexp : (p : ℝ) ^ (1 - σ - 1) = (p : ℝ) ^ (-σ) := by
    congr 1
    ring
  rw [hexp, hsq]
  field_simp
  ring

/-- **The physical saddle centre.**  `Λ_{σ,Y} = (2/a) Y^a (1 + o(1))` with `a = 1 - σ`. -/
theorem tendsto_saddleLogCenter {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun Y : ℝ => saddleLogCenter σ Y / Y ^ (1 - σ)) atTop (nhds (2 / (1 - σ))) := by
  have ha0 : (0 : ℝ) < 1 - σ := by linarith
  have h1 := tendsto_primeRpowLogSumLE ha0
  have h2 := tendsto_eulerTiltDeficit hσ hσ1
  have h := (h1.sub h2).const_mul (2 : ℝ)
  rw [sub_zero] at h
  have hval : (2 : ℝ) * (1 / (1 - σ)) = 2 / (1 - σ) := by ring
  rw [hval] at h
  refine h.congr fun Y => ?_
  rw [saddleLogCenter_eq]
  ring

/-! ## The physical saddle variance -/

/-- The prime power–squared-logarithm sum over all primes below `Y`. -/
def primeRpowLogSqSumLE (a Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1) * (Real.log p) ^ 2

theorem primeRpowLogSqSumLE_eq_add {a Y : ℝ} (hY : 2 ≤ Y) :
    primeRpowLogSqSumLE a Y
      = (2 : ℝ) ^ (a - 1) * (Real.log 2) ^ 2
        + (Real.log Y * primeWindowSum a 0 Y - primeWindowSum a 1 Y) := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  rw [primeRpowLogSqSumLE, sum_primesLE_eq_add_sum_Ioc _ hfloor]
  congr 1
  rw [primeWindowSum, primeWindowSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp, if_pos hp]
    ring
  · rw [if_neg hp, if_neg hp, if_neg hp]
    ring

/-- **The prime power–squared-logarithm sum.** -/
theorem tendsto_primeRpowLogSqSumLE {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun Y : ℝ => primeRpowLogSqSumLE a Y / (Y ^ a * Real.log Y)) atTop
      (nhds (1 / a)) := by
  have hS0 := tendsto_primeWindowSum ha0 0
  have hS1 := tendsto_primeWindowSum ha0 1
  have hconst : Tendsto
      (fun Y : ℝ => (2 : ℝ) ^ (a - 1) * (Real.log 2) ^ 2 / (Y ^ a * Real.log Y)) atTop
      (nhds 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact Filter.Tendsto.atTop_mul_atTop₀ (tendsto_rpow_atTop ha0) Real.tendsto_log_atTop
  have hinvlog : Tendsto (fun Y : ℝ => (Real.log Y)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hS1' : Tendsto (fun Y : ℝ => (primeWindowSum a 1 Y / Y ^ a) * (Real.log Y)⁻¹) atTop
      (nhds 0) := by
    have h := hS1.mul hinvlog
    rwa [mul_zero] at h
  have hsum := (hconst.add hS0).sub hS1'
  rw [zero_add, sub_zero] at hsum
  have hconst0 : (Nat.factorial 0 : ℝ) / a ^ (0 + 1) = 1 / a := by
    simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  rw [hconst0] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
  have hlogY : (0 : ℝ) < Real.log Y := Real.log_pos (by linarith)
  rw [primeRpowLogSqSumLE_eq_add hY]
  field_simp
  ring

end

end RHTower
