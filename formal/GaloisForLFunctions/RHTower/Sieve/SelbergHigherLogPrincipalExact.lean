import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

theorem moebiusDoubleLogKernelReal_nat_ratio (N q : ℕ) (hq : 0 < q) :
    moebiusDoubleLogKernelReal ((N : ℝ) / (q : ℝ)) =
      ∑ u ∈ Finset.Icc 1 (N / q),
        selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ 2 := by
  rw [moebiusDoubleLogKernelReal, Nat.floor_div_natCast, Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro u hu
  rw [selbergMoebiusReciprocalCoeff]
  congr 1
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
  push_cast
  field_simp [hqR, huR]

/-- Principal `(log, log²)` rectangular model after fixed dilation. -/
def selbergPrincipalScaledMixedModel (a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
        (d : ℝ)

/-- Principal `(log², log²)` rectangular model after fixed dilation. -/
def selbergPrincipalScaledQuadraticModel (a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
        (d : ℝ)

theorem selbergPrincipalCoeff_weighted_one_two_eq_scaledMixedModel
    (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergPrincipalCoeff r s *
        (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) *
          Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ 2)) =
      selbergPrincipalScaledMixedModel a b N := by
  rw [selbergPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ 2)) =
        coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
          moebiusDoubleLogKernelReal ((N : ℝ) / ((b * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ 2)) =
          (∑ r ∈ Finset.Icc 1 (N / a / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((a * d) * r : ℕ) : ℝ))) *
          (∑ s ∈ Finset.Icc 1 (N / b / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((b * e) * s : ℕ) : ℝ)) ^ 2) := by
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
          ← coprimeLogMoebius_one_nat_ratio N (a * d) (Nat.mul_pos ha
            (Finset.mem_Icc.mp hd).1),
          ← moebiusDoubleLogKernelReal_nat_ratio N (b * e) (Nat.mul_pos hb
            (Finset.mem_Icc.mp he).1)]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalReciprocalCoeff_double_sum_eq,
    min_natDiv_eq_natDiv_max N a b ha hb]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem selbergPrincipalCoeff_weighted_two_two_eq_scaledQuadraticModel
    (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergPrincipalCoeff r s *
        (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ 2 *
          Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ 2)) =
      selbergPrincipalScaledQuadraticModel a b N := by
  rw [selbergPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ 2)) =
        moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
          moebiusDoubleLogKernelReal ((N : ℝ) / ((b * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ 2 *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ 2)) =
          (∑ r ∈ Finset.Icc 1 (N / a / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((a * d) * r : ℕ) : ℝ)) ^ 2) *
          (∑ s ∈ Finset.Icc 1 (N / b / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((b * e) * s : ℕ) : ℝ)) ^ 2) := by
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
          ← moebiusDoubleLogKernelReal_nat_ratio N (a * d) (Nat.mul_pos ha
            (Finset.mem_Icc.mp hd).1),
          ← moebiusDoubleLogKernelReal_nat_ratio N (b * e) (Nat.mul_pos hb
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
