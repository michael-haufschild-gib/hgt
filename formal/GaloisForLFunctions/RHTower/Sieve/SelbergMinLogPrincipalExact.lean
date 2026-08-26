import GaloisForLFunctions.RHTower.Sieve.SelbergMinLogInnerLayerCake
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic

/-!
# Exact principal models for minimum-logarithmic Selberg forms

The principal coefficient first expands into a diagonal reciprocal coefficient convolved with a
Möbius pair.  Arbitrary-kernel diagonal collapse and the inner layer-cake identities turn this
into a single common-diagonal sum of one-dimensional integrals.
-/

open ArithmeticFunction Finset MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Generic principal minimum-logarithmic model from two exact threshold-kernel interfaces. -/
theorem selbergPrincipalMinLogMonomial_eq_layerCake_of_threshold
    (i j k a b N : ℕ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (Kq Kr : ℕ → ℝ → ℝ)
    (hKq : ∀ q : ℕ, 0 < q → ∀ t : ℝ, 0 ≤ t →
      (∑ u ∈ Finset.Icc 1 (N / q),
        selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ i *
          (if t ≤ Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) = Kq q t)
    (hKr : ∀ r : ℕ, 0 < r → ∀ t : ℝ, 0 ≤ t →
      (∑ v ∈ Finset.Icc 1 (N / r),
        selbergMoebiusReciprocalCoeff v *
          Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ)) ^ j *
          (if t ≤ Real.log ((N : ℝ) / ((r * v : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) = Kr r t) :
    selbergPrincipalMinLogMonomialModel i j (k + 1) a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b), (1 / (d : ℝ)) *
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k * Kq (a * d) t * Kr (b * d) t := by
  rw [selbergPrincipalMinLogMonomialModel, selbergPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ j *
              min (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)))
                (Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ))) ^ (k + 1))) =
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k * Kq (a * d) t * Kr (b * e) t := by
    intro d hd e he
    have hadN : a * d ≤ N := by
      simpa [Nat.mul_comm] using
        ((Nat.le_div_iff_mul_le ha).mp (Finset.mem_Icc.mp hd).2)
    have hi := selbergMoebiusPair_minLog_eq_layerCake_of_threshold
      N (a * d) (b * e) i j k hN
        (Nat.mul_pos ha (Finset.mem_Icc.mp hd).1)
        (Nat.mul_pos hb (Finset.mem_Icc.mp he).1) hadN
        (Kq (a * d)) (Kr (b * e))
        (hKq (a * d) (Nat.mul_pos ha (Finset.mem_Icc.mp hd).1))
        (hKr (b * e) (Nat.mul_pos hb (Finset.mem_Icc.mp he).1))
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_assoc] using hi
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalReciprocalCoeff_double_sum_mul_eq,
    min_natDiv_eq_natDiv_max N a b ha hb]

/-- Exact principal layer-cake model for the `(1,1,k+1)` minimum monomial. -/
theorem selbergPrincipalMinLogOneOne_eq_layerCake
    (k a b N : ℕ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) :
    selbergPrincipalMinLogMonomialModel 1 1 (k + 1) a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b), (1 / (d : ℝ)) *
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k *
            moebiusShiftedLogKernelReal t
              (((N : ℝ) / ((a * d : ℕ) : ℝ)) * Real.exp (-t)) *
            moebiusShiftedLogKernelReal t
              (((N : ℝ) / ((b * d : ℕ) : ℝ)) * Real.exp (-t)) := by
  have h := selbergPrincipalMinLogMonomial_eq_layerCake_of_threshold
    1 1 k a b N hN ha hb
    (fun q t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun r t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun q hq t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N q hN hq t ht)
    (fun r hr t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N r hN hr t ht)
  simpa only [pow_one] using h

/-- Exact principal layer-cake model for the `(1,2,k+1)` minimum monomial. -/
theorem selbergPrincipalMinLogOneTwo_eq_layerCake
    (k a b N : ℕ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) :
    selbergPrincipalMinLogMonomialModel 1 2 (k + 1) a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b), (1 / (d : ℝ)) *
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k *
            moebiusShiftedLogKernelReal t
              (((N : ℝ) / ((a * d : ℕ) : ℝ)) * Real.exp (-t)) *
            moebiusShiftedLogSqKernelReal t
              (((N : ℝ) / ((b * d : ℕ) : ℝ)) * Real.exp (-t)) := by
  have h := selbergPrincipalMinLogMonomial_eq_layerCake_of_threshold
    1 2 k a b N hN ha hb
    (fun q t => moebiusShiftedLogKernelReal t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun r t => moebiusShiftedLogSqKernelReal t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun q hq t ht => by simpa only [pow_one, mul_assoc] using
      sum_moebius_log_threshold_nat_ratio_eq_shifted N q hN hq t ht)
    (fun r hr t ht => by simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N r hN hr t ht)
  simpa only [pow_one] using h

/-- Exact principal layer-cake model for the `(2,2,k+1)` minimum monomial. -/
theorem selbergPrincipalMinLogTwoTwo_eq_layerCake
    (k a b N : ℕ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) :
    selbergPrincipalMinLogMonomialModel 2 2 (k + 1) a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b), (1 / (d : ℝ)) *
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k *
            moebiusShiftedLogSqKernelReal t
              (((N : ℝ) / ((a * d : ℕ) : ℝ)) * Real.exp (-t)) *
            moebiusShiftedLogSqKernelReal t
              (((N : ℝ) / ((b * d : ℕ) : ℝ)) * Real.exp (-t)) := by
  exact selbergPrincipalMinLogMonomial_eq_layerCake_of_threshold
    2 2 k a b N hN ha hb
    (fun q t => moebiusShiftedLogSqKernelReal t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun r t => moebiusShiftedLogSqKernelReal t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun q hq t ht => by simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N q hN hq t ht)
    (fun r hr t ht => by simpa only [mul_assoc] using
      sum_moebius_log_sq_threshold_nat_ratio_eq_shifted N r hN hr t ht)

end

end RHTower.Sieve
