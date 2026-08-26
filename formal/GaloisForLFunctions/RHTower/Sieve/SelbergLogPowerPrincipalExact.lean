import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerRealCutoff

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

theorem moebiusLogPowerKernelReal_nat_ratio
    (p N q : ℕ) (hq : 0 < q) :
    moebiusLogPowerKernelReal p ((N : ℝ) / (q : ℝ)) =
      ∑ u ∈ Finset.Icc 1 (N / q),
        selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ p := by
  rw [moebiusLogPowerKernelReal, Nat.floor_div_natCast, Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro u hu
  rw [selbergMoebiusReciprocalCoeff]
  congr 1
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
  push_cast
  field_simp [hqR, huR]

/-- Principal rectangular Selberg model for an arbitrary pair of logarithmic powers. -/
def selbergPrincipalScaledLogPowerModel
    (i j a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    moebiusLogPowerKernelReal i ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      moebiusLogPowerKernelReal j ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
        (d : ℝ)

/-- The arbitrary logarithmic monomial of the principal Selberg coefficient collapses exactly
to the corresponding one-dimensional rectangular model. -/
theorem selbergPrincipalCoeff_weighted_logPower_eq_scaledModel
    (i j a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergPrincipalCoeff r s *
        (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ i *
          Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ j)) =
      selbergPrincipalScaledLogPowerModel i j a b N := by
  rw [selbergPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ j)) =
        moebiusLogPowerKernelReal i ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
          moebiusLogPowerKernelReal j ((N : ℝ) / ((b * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ j)) =
          (∑ r ∈ Finset.Icc 1 (N / a / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((a * d) * r : ℕ) : ℝ)) ^ i) *
          (∑ s ∈ Finset.Icc 1 (N / b / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((b * e) * s : ℕ) : ℝ)) ^ j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [selbergMoebiusReciprocalPair]
        simp only [Nat.mul_assoc]
        ring
      _ = _ := by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
          ← moebiusLogPowerKernelReal_nat_ratio i N (a * d) (Nat.mul_pos ha
            (Finset.mem_Icc.mp hd).1),
          ← moebiusLogPowerKernelReal_nat_ratio j N (b * e) (Nat.mul_pos hb
            (Finset.mem_Icc.mp he).1)]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalReciprocalCoeff_double_sum_eq,
    min_natDiv_eq_natDiv_max N a b ha hb]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end


end RHTower.Sieve
