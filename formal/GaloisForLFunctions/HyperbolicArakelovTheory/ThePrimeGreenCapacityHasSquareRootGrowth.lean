import GaloisForLFunctions.HyperbolicArakelovTheory.TheArithmeticMassClockOfThePrimeGreenKernel
import GaloisForLFunctions.RHTower.RouteESaddlePntTransport

/-!
# The spatial growth of prime Green capacity

The capacity through degree `N` is `4 √N + o(√N)`. Its difference from
twice the weighted prime sum `Σ log(p)/√p` is nonnegative and at most
`8 (log N + log 4)`. Weighted prime-number asymptotics therefore determine
the exact coefficient of the arithmetic clock's spatial horizon.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
open _root_.RHTower

private theorem capacity_excess_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ capacity p - 2 * (Real.log p / Real.sqrt p) ∧
      capacity p - 2 * (Real.log p / Real.sqrt p) ≤ 8 * (Real.log p / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs2 := Real.sq_sqrt hp0.le
  have hs : 4 / 3 ≤ Real.sqrt p := by nlinarith only [hp2, hs0, hs2]
  have hs1 : 0 < Real.sqrt p - 1 := by linarith only [hs]
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp2])
  have he : capacity p - 2 * (Real.log p / Real.sqrt p) =
      2 * Real.log p / (Real.sqrt p * (Real.sqrt p - 1)) := by
    rw [capacity]
    field_simp
    ring
  have hden : (p : ℝ) / 4 ≤ Real.sqrt p * (Real.sqrt p - 1) := by
    nlinarith only [hs2, mul_nonneg hs0.le (sub_nonneg.mpr hs)]
  have hb : 2 * Real.log p / (Real.sqrt p * (Real.sqrt p - 1)) ≤ 8 * (Real.log p / p) := by
    rw [show 8 * (Real.log p / p) = (8 * Real.log p) / p by ring,
      div_le_div_iff₀ (mul_pos hs0 hs1) hp0]
    nlinarith only [mul_le_mul_of_nonneg_left hden hl]
  rw [he]
  exact ⟨div_nonneg (by positivity) (mul_pos hs0 hs1).le, hb⟩

theorem cumulativeCapacity_succ_eq_prime_sum (N : ℕ) :
    cumulativeCapacity (N + 1) = ∑ p ∈ Nat.primesLE N, capacity p := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  rfl

private theorem half_power_weight (p : ℕ) :
    (p : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log p = Real.log p / Real.sqrt p := by
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by ring,
    Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow]
  ring

/-- All higher prime-ladder repetitions add only logarithmic mass to the square-root term. -/
theorem cumulativeCapacity_excess_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ cumulativeCapacity (N + 1) - 2 * primeRpowLogSumLE (1 / 2) N ∧
      cumulativeCapacity (N + 1) - 2 * primeRpowLogSumLE (1 / 2) N ≤
        8 * (Real.log N + Real.log 4) := by
  have he : cumulativeCapacity (N + 1) - 2 * primeRpowLogSumLE (1 / 2) N =
      ∑ p ∈ Nat.primesLE N, (capacity p - 2 * (Real.log p / Real.sqrt p)) := by
    rw [cumulativeCapacity_succ_eq_prime_sum, primeRpowLogSumLE, Nat.floor_natCast,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [half_power_weight]
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun p hp => (capacity_excess_prime (Nat.prime_of_mem_primesLE hp)).1
  · calc
      _ ≤ ∑ p ∈ Nat.primesLE N, 8 * (Real.log p / p) :=
        Finset.sum_le_sum fun p hp => (capacity_excess_prime (Nat.prime_of_mem_primesLE hp)).2
      _ = 8 * ∑ p ∈ Nat.primesLE N, Real.log p / p := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Sieve.mertensFirst_upper hN) (by norm_num)

private theorem sqrt_nat_atTop :
    Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_half_power_prime_sum :
    Tendsto (fun N : ℕ => primeRpowLogSumLE (1 / 2) N / Real.sqrt N) atTop (𝓝 2) := by
  have h : Tendsto (fun N : ℕ => primeRpowLogSumLE (1 / 2) N / (N : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 ((1 : ℝ) / (1 / 2))) :=
    (tendsto_primeRpowLogSumLE (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  simpa only [← Real.sqrt_eq_rpow, show (1 : ℝ) / (1 / 2) = 2 by norm_num] using h

theorem tendsto_cumulativeCapacity_excess_div_sqrt :
    Tendsto (fun N : ℕ =>
      (cumulativeCapacity (N + 1) - 2 * primeRpowLogSumLE (1 / 2) N) / Real.sqrt N)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop
    simpa only [← Real.sqrt_eq_rpow] using h
  have hconst : Tendsto (fun N : ℕ => Real.log 4 / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop sqrt_nat_atTop
  have hmajor : Tendsto (fun N : ℕ => 8 * ((Real.log N + Real.log 4) / Real.sqrt N))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero, add_div] using (hlog.add hconst).const_mul 8
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact div_nonneg (cumulativeCapacity_excess_bounds hN).1 (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (cumulativeCapacity_excess_bounds hN).2 (Real.sqrt_nonneg _)

/-- The exact coefficient of the arithmetic clock's square-root spatial growth is four. -/
theorem tendsto_cumulativeCapacity_div_sqrt :
    Tendsto (fun N : ℕ => cumulativeCapacity (N + 1) / Real.sqrt N) atTop (𝓝 4) := by
  have h := (tendsto_half_power_prime_sum.const_mul 2).add
    tendsto_cumulativeCapacity_excess_div_sqrt
  norm_num at h
  apply h.congr
  intro N
  ring

#print axioms cumulativeCapacity_excess_bounds
#print axioms tendsto_cumulativeCapacity_div_sqrt

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension
