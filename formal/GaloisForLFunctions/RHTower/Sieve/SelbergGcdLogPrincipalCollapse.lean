import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogHarmonicMain
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerPrincipalExact

/-!
# The gcd-logarithmic principal coefficient and its rectangular collapse

Differentiating the two-parameter Selberg family `c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)` at `s = 1`
replaces the reciprocal diagonal weight `1/d` of the principal Euler factor by `log d / d`.  This
file fixes the resulting principal coefficient

`𝒫^{log} = diag(log d / d) ∗ (μ/·) ⊗ (μ/·)`

and proves that its weighted double sum collapses to the one-dimensional model
`∑_{d ≤ N/max(a,b)} (log d / d)·K_i(N/(ad))·K_j(N/(bd))`, exactly as the ordinary principal
coefficient collapses to `∑_d K_i K_j / d`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Logarithmically weighted reciprocal diagonal coefficient. -/
def selbergDiagonalLogReciprocalCoeff (m n : ℕ) : ℝ :=
  if m = n then Real.log (m : ℝ) / (m : ℝ) else 0

/-- A double sum against the logarithmic diagonal coefficient collapses to its diagonal. -/
theorem selbergDiagonalLogReciprocalCoeff_double_sum_mul_eq
    {X Y : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogReciprocalCoeff d e * F d e) =
      ∑ d ∈ Finset.Icc 1 (min X Y), (Real.log (d : ℝ) / (d : ℝ)) * F d d := by
  have hinner : ∀ d ∈ Finset.Icc 1 X,
      (∑ e ∈ Finset.Icc 1 Y,
        selbergDiagonalLogReciprocalCoeff d e * F d e) =
      if d ∈ Finset.Icc 1 Y then (Real.log (d : ℝ) / (d : ℝ)) * F d d else 0 := by
    intro d hd
    by_cases hdY : d ∈ Finset.Icc 1 Y
    · rw [if_pos hdY, Finset.sum_eq_single_of_mem d hdY]
      · rw [selbergDiagonalLogReciprocalCoeff, if_pos rfl]
      · intro e he hed
        rw [selbergDiagonalLogReciprocalCoeff, if_neg (Ne.symm hed), zero_mul]
    · rw [if_neg hdY]
      apply Finset.sum_eq_zero
      intro e he
      rw [selbergDiagonalLogReciprocalCoeff]
      split_ifs with hde
      · subst e
        exact (hdY he).elim
      · ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Product-kernel specialization of the logarithmic diagonal collapse. -/
theorem selbergDiagonalLogReciprocalCoeff_double_sum_eq
    {X Y : ℕ} (h k : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalLogReciprocalCoeff d e * (h d * k e)) =
      ∑ d ∈ Finset.Icc 1 (min X Y), (Real.log (d : ℝ) / (d : ℝ)) * (h d * k d) := by
  simpa using selbergDiagonalLogReciprocalCoeff_double_sum_mul_eq (X := X) (Y := Y)
    (fun d e => h d * k e)

/-- The gcd-logarithmic principal coefficient. -/
def selbergGcdLogPrincipalCoeff : ℕ → ℕ → ℝ :=
  bivariateDirichletConvolution selbergDiagonalLogReciprocalCoeff
    selbergMoebiusReciprocalPair

/-- Principal rectangular model for the gcd-logarithmic diagonal weight. -/
def selbergGcdLogPrincipalScaledLogPowerModel (i j a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    Real.log (d : ℝ) *
      (moebiusLogPowerKernelReal i ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
        moebiusLogPowerKernelReal j ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
      (d : ℝ)

/-- **The gcd-logarithmic principal coefficient collapses to the logarithmically weighted
one-dimensional model.** -/
theorem selbergGcdLogPrincipalCoeff_weighted_logPower_eq_scaledModel
    (i j a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergGcdLogPrincipalCoeff r s *
        (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) ^ i *
          Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)) ^ j)) =
      selbergGcdLogPrincipalScaledLogPowerModel i j a b N := by
  rw [selbergGcdLogPrincipalCoeff,
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
  rw [selbergDiagonalLogReciprocalCoeff_double_sum_eq,
    min_natDiv_eq_natDiv_max N a b ha hb,
    selbergGcdLogPrincipalScaledLogPowerModel]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end

end RHTower.Sieve
