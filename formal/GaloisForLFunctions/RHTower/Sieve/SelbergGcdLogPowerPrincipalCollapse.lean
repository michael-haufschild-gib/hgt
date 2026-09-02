import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPrincipalCollapse

/-!
# Principal Selberg coefficients with arbitrary gcd-logarithmic power

The origin-based Barban--Vehov short energy contains the three weights
`log (m,n)^a`, `a = 1,2,3`.  The existing principal collapse treats only
`a = 1`.  This file builds the exponent-uniform coefficient

`diag(log(d)^a / d) * (mu/d tensor mu/d)`

and collapses every rectangular logarithmic moment to one diagonal sum.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Reciprocal diagonal coefficient weighted by an arbitrary logarithmic power. -/
def selbergDiagonalLogPowerReciprocalCoeff (a m n : ℕ) : ℝ :=
  if m = n then Real.log (m : ℝ) ^ a / (m : ℝ) else 0

@[simp] theorem selbergDiagonalLogPowerReciprocalCoeff_one (a : ℕ) :
    selbergDiagonalLogPowerReciprocalCoeff a 1 1 = if a = 0 then 1 else 0 := by
  cases a <;> simp [selbergDiagonalLogPowerReciprocalCoeff]

theorem selbergDiagonalLogPowerReciprocalCoeff_one_eq
    (m n : ℕ) :
    selbergDiagonalLogPowerReciprocalCoeff 1 m n =
      selbergDiagonalLogReciprocalCoeff m n := by
  rw [selbergDiagonalLogPowerReciprocalCoeff,
    selbergDiagonalLogReciprocalCoeff]
  split_ifs <;> ring

/-- A rectangular double sum against the logarithmic-power diagonal collapses to its diagonal. -/
theorem selbergDiagonalLogPowerReciprocalCoeff_double_sum_mul_eq
    (a : ℕ) {X Y : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogPowerReciprocalCoeff a d e * F d e) =
      ∑ d ∈ Finset.Icc 1 (min X Y),
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * F d d := by
  have hinner : ∀ d ∈ Finset.Icc 1 X,
      (∑ e ∈ Finset.Icc 1 Y,
        selbergDiagonalLogPowerReciprocalCoeff a d e * F d e) =
      if d ∈ Finset.Icc 1 Y then
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * F d d else 0 := by
    intro d hd
    by_cases hdY : d ∈ Finset.Icc 1 Y
    · rw [if_pos hdY, Finset.sum_eq_single_of_mem d hdY]
      · rw [selbergDiagonalLogPowerReciprocalCoeff, if_pos rfl]
      · intro e he hed
        rw [selbergDiagonalLogPowerReciprocalCoeff,
          if_neg (Ne.symm hed), zero_mul]
    · rw [if_neg hdY]
      apply Finset.sum_eq_zero
      intro e he
      rw [selbergDiagonalLogPowerReciprocalCoeff]
      split_ifs with hde
      · subst e
        exact (hdY he).elim
      · ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Product-kernel specialization of the logarithmic-power diagonal collapse. -/
theorem selbergDiagonalLogPowerReciprocalCoeff_double_sum_eq
    (a : ℕ) {X Y : ℕ} (h k : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogPowerReciprocalCoeff a d e * (h d * k e)) =
      ∑ d ∈ Finset.Icc 1 (min X Y),
        (Real.log (d : ℝ) ^ a / (d : ℝ)) * (h d * k d) := by
  simpa using selbergDiagonalLogPowerReciprocalCoeff_double_sum_mul_eq
    a (X := X) (Y := Y) (fun d e => h d * k e)

/-- Principal Euler coefficient carrying `log(gcd)^a`. -/
def selbergGcdLogPowerPrincipalCoeff (a : ℕ) : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution
    (selbergDiagonalLogPowerReciprocalCoeff a)
    selbergMoebiusReciprocalPair

theorem selbergGcdLogPowerPrincipalCoeff_one_eq :
    selbergGcdLogPowerPrincipalCoeff 1 = selbergGcdLogPrincipalCoeff := by
  unfold selbergGcdLogPowerPrincipalCoeff selbergGcdLogPrincipalCoeff
  rw [show selbergDiagonalLogPowerReciprocalCoeff 1 =
      selbergDiagonalLogReciprocalCoeff by
    funext m n
    exact selbergDiagonalLogPowerReciprocalCoeff_one_eq m n]

/-- Rectangular model after collapsing the principal `log(gcd)^a` coefficient. -/
def selbergGcdLogPowerPrincipalScaledModel
    (a i j A B N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max A B),
    Real.log (d : ℝ) ^ a *
      (moebiusLogPowerKernelReal i ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
        moebiusLogPowerKernelReal j ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
      (d : ℝ)

/-- The principal `log(gcd)^a` coefficient collapses to one weighted harmonic model. -/
theorem selbergGcdLogPowerPrincipalCoeff_weighted_logPower_eq_scaledModel
    (a i j A B N : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (∑ r ∈ Finset.Icc 1 (N / A), ∑ s ∈ Finset.Icc 1 (N / B),
      selbergGcdLogPowerPrincipalCoeff a r s *
        (Real.log ((N : ℝ) / ((A * r : ℕ) : ℝ)) ^ i *
          Real.log ((N : ℝ) / ((B * s : ℕ) : ℝ)) ^ j)) =
      selbergGcdLogPowerPrincipalScaledModel a i j A B N := by
  rw [selbergGcdLogPowerPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / A), ∀ e ∈ Finset.Icc 1 (N / B),
      (∑ r ∈ Finset.Icc 1 (N / A / d),
        ∑ s ∈ Finset.Icc 1 (N / B / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((A * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((B * (e * s) : ℕ) : ℝ)) ^ j)) =
        moebiusLogPowerKernelReal i ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
          moebiusLogPowerKernelReal j ((N : ℝ) / ((B * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / A / d),
        ∑ s ∈ Finset.Icc 1 (N / B / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((A * (d * r) : ℕ) : ℝ)) ^ i *
              Real.log ((N : ℝ) / ((B * (e * s) : ℕ) : ℝ)) ^ j)) =
          (∑ r ∈ Finset.Icc 1 (N / A / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((A * d) * r : ℕ) : ℝ)) ^ i) *
          (∑ s ∈ Finset.Icc 1 (N / B / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((B * e) * s : ℕ) : ℝ)) ^ j) := by
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
          ← moebiusLogPowerKernelReal_nat_ratio i N (A * d)
            (Nat.mul_pos hA (Finset.mem_Icc.mp hd).1),
          ← moebiusLogPowerKernelReal_nat_ratio j N (B * e)
            (Nat.mul_pos hB (Finset.mem_Icc.mp he).1)]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalLogPowerReciprocalCoeff_double_sum_eq,
    min_natDiv_eq_natDiv_max N A B hA hB,
    selbergGcdLogPowerPrincipalScaledModel]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end

end RHTower.Sieve
