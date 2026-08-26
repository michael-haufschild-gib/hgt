import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogPowerThreshold
import GaloisForLFunctions.RHTower.Sieve.SelbergMinLogPrincipalExact

/-!
# Arbitrary-power principal minimum-logarithmic Selberg forms

The generic shifted threshold identity instantiates the exact layer-cake decomposition for every
pair of logarithmic powers.  This single theorem contains all minimum-log monomials occurring in
the differentiated included and omitted Barban--Vehov boundaries.
-/

open ArithmeticFunction Finset MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Exact layer-cake model for arbitrary logarithmic powers on both Möbius legs. -/
theorem selbergPrincipalMinLogMonomial_eq_logPowerLayerCake
    (i j k a b N : ℕ) (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) :
    selbergPrincipalMinLogMonomialModel i j (k + 1) a b N =
      ∑ d ∈ Finset.Icc 1 (N / max a b), (1 / (d : ℝ)) *
        ∫ t in (0 : ℝ)..Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)),
          ((k : ℝ) + 1) * t ^ k *
            moebiusShiftedLogPowerKernelReal i t
              (((N : ℝ) / ((a * d : ℕ) : ℝ)) * Real.exp (-t)) *
            moebiusShiftedLogPowerKernelReal j t
              (((N : ℝ) / ((b * d : ℕ) : ℝ)) * Real.exp (-t)) := by
  exact selbergPrincipalMinLogMonomial_eq_layerCake_of_threshold
    i j k a b N hN ha hb
    (fun q t => moebiusShiftedLogPowerKernelReal i t
      (((N : ℝ) / (q : ℝ)) * Real.exp (-t)))
    (fun r t => moebiusShiftedLogPowerKernelReal j t
      (((N : ℝ) / (r : ℝ)) * Real.exp (-t)))
    (fun q hq t ht => by simpa only [mul_assoc] using
      sum_moebius_log_pow_threshold_nat_ratio_eq_shifted i N q hN hq t ht)
    (fun r hr t ht => by simpa only [mul_assoc] using
      sum_moebius_log_pow_threshold_nat_ratio_eq_shifted j N r hN hr t ht)

end

end RHTower.Sieve
