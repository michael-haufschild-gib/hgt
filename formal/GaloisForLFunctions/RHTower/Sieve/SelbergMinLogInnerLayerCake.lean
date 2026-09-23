import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogThresholdNatRatio
import GaloisForLFunctions.RHTower.Sieve.FiniteMinPowerLayerCake
import GaloisForLFunctions.RHTower.Sieve.SelbergMinLogMonomial

/-!
# Layer cake for the inner minimum-logarithmic Selberg kernels

After diagonalizing the principal Selberg coefficient, the remaining pair of Möbius variables
contains a power of the minimum of two logarithms.  The generic theorem below factors that pair
through any supplied threshold-kernel identities.  Its three corollaries use the corpus's exact
shifted linear and quadratic Möbius kernels.
-/

open ArithmeticFunction Finset MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- A minimum-logarithmic Möbius pair factors through its two threshold kernels. -/
theorem selbergMoebiusPair_minLog_eq_layerCake_of_threshold
    (N q r i j k : ℕ) (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hqN : q ≤ N)
    (Kq Kr : ℝ → ℝ)
    (hKq : ∀ t : ℝ, 0 ≤ t →
      (∑ u ∈ Finset.Icc 1 (N / q),
        selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ i *
          (if t ≤ Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) = Kq t)
    (hKr : ∀ t : ℝ, 0 ≤ t →
      (∑ v ∈ Finset.Icc 1 (N / r),
        selbergMoebiusReciprocalCoeff v *
          Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ)) ^ j *
          (if t ≤ Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) = Kr t) :
    (∑ u ∈ Finset.Icc 1 (N / q), ∑ v ∈ Finset.Icc 1 (N / r),
      let A := Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
      let B := Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
      selbergMoebiusReciprocalPair u v *
        (A ^ i * B ^ j * min A B ^ (k + 1))) =
      ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / (q : ℝ)),
        ((k : ℝ) + 1) * t ^ k * Kq t * Kr t := by
  let S := Finset.Icc 1 (N / q)
  let T := Finset.Icc 1 (N / r)
  let A : ℕ → ℝ := fun u =>
    Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
  let B : ℕ → ℝ := fun v =>
    Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
  let L : ℝ := Real.log ((N : ℝ) / (q : ℝ))
  have hA0 : ∀ u ∈ S, 0 ≤ A u := by
    intro u hu
    exact Real.log_nonneg (one_le_selbergScaledArgument hq le_rfl hu)
  have hB0 : ∀ v ∈ T, 0 ≤ B v := by
    intro v hv
    exact Real.log_nonneg (one_le_selbergScaledArgument hr le_rfl hv)
  have hAL : ∀ u ∈ S, A u ≤ L := by
    intro u hu
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hden : (q : ℝ) ≤ ((q * u : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_right q hu1
    have hratio : (N : ℝ) / ((q * u : ℕ) : ℝ) ≤
        (N : ℝ) / (q : ℝ) := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hqR hden
    exact Real.log_le_log (by positivity) hratio
  have hlayer := finite_sum_min_pow_succ_eq_layerCake_le
    S T selbergMoebiusReciprocalCoeff selbergMoebiusReciprocalCoeff
      A B i j k L hA0 hAL hB0
  calc
    (∑ u ∈ Finset.Icc 1 (N / q), ∑ v ∈ Finset.Icc 1 (N / r),
      let A := Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
      let B := Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
      selbergMoebiusReciprocalPair u v *
        (A ^ i * B ^ j * min A B ^ (k + 1))) =
      ∑ u ∈ S, ∑ v ∈ T,
        selbergMoebiusReciprocalCoeff u *
          selbergMoebiusReciprocalCoeff v *
          A u ^ i * B v ^ j * min (A u) (B v) ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        rw [selbergMoebiusReciprocalPair]
        dsimp only [S, T, A, B]
        ring
    _ = ∫ t in (0 : ℝ)..L,
        ((k : ℝ) + 1) * t ^ k *
          (∑ u ∈ S, selbergMoebiusReciprocalCoeff u * A u ^ i *
            (if t ≤ A u then (1 : ℝ) else 0)) *
          (∑ v ∈ T, selbergMoebiusReciprocalCoeff v * B v ^ j *
            (if t ≤ B v then (1 : ℝ) else 0)) := hlayer
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t htmem
      have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div (by positivity)).mpr
        (by exact_mod_cast hqN))
      rw [Set.uIcc_of_le hL0] at htmem
      have ht0 : 0 ≤ t := htmem.1
      have hleft :
          (∑ u ∈ S, selbergMoebiusReciprocalCoeff u * A u ^ i *
            (if t ≤ A u then (1 : ℝ) else 0)) = Kq t := by
        simpa only [S, A] using hKq t ht0
      have hright :
          (∑ v ∈ T, selbergMoebiusReciprocalCoeff v * B v ^ j *
            (if t ≤ B v then (1 : ℝ) else 0)) = Kr t := by
        simpa only [T, B] using hKr t ht0
      change
        (((k : ℝ) + 1) * t ^ k *
          (∑ u ∈ S, selbergMoebiusReciprocalCoeff u * A u ^ i *
            (if t ≤ A u then (1 : ℝ) else 0))) *
          (∑ v ∈ T, selbergMoebiusReciprocalCoeff v * B v ^ j *
            (if t ≤ B v then (1 : ℝ) else 0)) =
          ((k : ℝ) + 1) * t ^ k * Kq t * Kr t
      rw [hleft, hright]

/-- Exact layer-cake model for a linear/linear Möbius pair and a positive minimum power. -/
theorem selbergMoebiusPair_minLogOneOne_eq_layerCake
    (N q r k : ℕ) (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hqN : q ≤ N) :
    (∑ u ∈ Finset.Icc 1 (N / q), ∑ v ∈ Finset.Icc 1 (N / r),
      let A := Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
      let B := Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
      selbergMoebiusReciprocalPair u v *
        (A * B * min A B ^ (k + 1))) =
      ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / (q : ℝ)),
        ((k : ℝ) + 1) * t ^ k *
          moebiusShiftedLogKernelReal t
            (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) *
          moebiusShiftedLogKernelReal t
            (((N : ℝ) / (r : ℝ)) * Real.exp (-t)) := by
  have h := selbergMoebiusPair_minLog_eq_layerCake_of_threshold
    N q r 1 1 k hN hq hr hqN
    (fun t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N q hN hq t ht)
    (fun t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N r hN hr t ht)
  simpa only [pow_one] using h

/-- Exact layer-cake model for a linear/quadratic Möbius pair and a positive minimum power. -/
theorem selbergMoebiusPair_minLogOneTwo_eq_layerCake
    (N q r k : ℕ) (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hqN : q ≤ N) :
    (∑ u ∈ Finset.Icc 1 (N / q), ∑ v ∈ Finset.Icc 1 (N / r),
      let A := Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
      let B := Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
      selbergMoebiusReciprocalPair u v *
        (A * B ^ (2 : ℕ) * min A B ^ (k + 1))) =
      ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / (q : ℝ)),
        ((k : ℝ) + 1) * t ^ k *
          moebiusShiftedLogKernelReal t
            (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) *
          moebiusShiftedLogSqKernelReal t
            (((N : ℝ) / (r : ℝ)) * Real.exp (-t)) := by
  have h := selbergMoebiusPair_minLog_eq_layerCake_of_threshold
    N q r 1 2 k hN hq hr hqN
    (fun t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun t => moebiusShiftedLogSqKernelReal t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N q hN hq t ht)
    (fun t ht => by simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N r hN hr t ht)
  simpa only [pow_one] using h

/-- Exact layer-cake model for a quadratic/quadratic Möbius pair and a positive minimum power. -/
theorem selbergMoebiusPair_minLogTwoTwo_eq_layerCake
    (N q r k : ℕ) (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hqN : q ≤ N) :
    (∑ u ∈ Finset.Icc 1 (N / q), ∑ v ∈ Finset.Icc 1 (N / r),
      let A := Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))
      let B := Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ))
      selbergMoebiusReciprocalPair u v *
        (A ^ (2 : ℕ) * B ^ (2 : ℕ) * min A B ^ (k + 1))) =
      ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / (q : ℝ)),
        ((k : ℝ) + 1) * t ^ k *
          moebiusShiftedLogSqKernelReal t
            (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) *
          moebiusShiftedLogSqKernelReal t
            (((N : ℝ) / (r : ℝ)) * Real.exp (-t)) := by
  apply selbergMoebiusPair_minLog_eq_layerCake_of_threshold N q r 2 2 k hN hq hr hqN
  · intro t ht
    simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N q hN hq t ht
  · intro t ht
    simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N r hN hr t ht

end

end RHTower.Sieve
