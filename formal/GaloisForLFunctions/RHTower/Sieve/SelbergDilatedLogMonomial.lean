import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerGeneralAsymptotic

/-!
# Dilated original Selberg log-monomials

The gcd-logarithmic Selberg family is reached by peeling one prime out of `log (m,n)`, which
replaces the truncation `N` by `N/p` and forces the *dilated* original form

`Ŝ(i,j,a,b,N) = ∑_{m ≤ N/a, n ≤ N/b} c(m,n)·log(N/(am))^i·log(N/(bn))^j`.

This file introduces it, gives its exact Euler-correction decomposition, and extracts the uniform
principal envelope that the whole comparison argument runs on.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- **Uniform envelope for the principal rectangular model at every pair of dilations.** -/
theorem exists_abs_selbergPrincipalScaledLogPowerModel_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b →
      |selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N| ≤
        M * Real.log N ^ (q + r + 1) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow q
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  refine ⟨2 * DA * DB, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN a b ha hb
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hratioTwo : (harmonic N : ℝ) / Real.log N < 2 := by
    rw [Real.dist_eq] at hnearN
    have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
        |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
    linarith
  have hmodel : |selbergPrincipalScaledLogPowerModel
      (q + 1) (r + 1) a b N| ≤
      DA * DB * Real.log N ^ (q + r) * (harmonic N : ℝ) := by
    rw [selbergPrincipalScaledLogPowerModel]
    calc
      |∑ d ∈ Finset.Icc 1 (N / max a b),
        moebiusLogPowerKernelReal (q + 1)
              ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal (r + 1)
              ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
            (d : ℝ)| ≤
          ∑ d ∈ Finset.Icc 1 (N / max a b),
            |moebiusLogPowerKernelReal (q + 1)
                  ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1)
                  ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
                (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 (N / max a b),
          DA * DB * Real.log N ^ (q + r) * (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
        let YA : ℝ := (N : ℝ) / ((a * d : ℕ) : ℝ)
        let YB : ℝ := (N : ℝ) / ((b * d : ℕ) : ℝ)
        have hYAone : (1 : ℝ) ≤ YA :=
          one_le_selbergScaledArgument ha (le_max_left a b) hd
        have hYBone : (1 : ℝ) ≤ YB :=
          one_le_selbergScaledArgument hb (le_max_right a b) hd
        have hYAle : YA ≤ (N : ℝ) := selbergScaledArgument_le_natCast ha hdpos
        have hYBle : YB ≤ (N : ℝ) := selbergScaledArgument_le_natCast hb hdpos
        have hlogYA0 : 0 ≤ Real.log YA := Real.log_nonneg hYAone
        have hlogYB0 : 0 ≤ Real.log YB := Real.log_nonneg hYBone
        have hlogYA : Real.log YA ≤ Real.log N :=
          Real.log_le_log (by positivity) hYAle
        have hlogYB : Real.log YB ≤ Real.log N :=
          Real.log_le_log (by positivity) hYBle
        have hQA := hDAbound YA hYAone
        have hQB := hDBbound YB hYBone
        have hQAN : |moebiusLogPowerKernelReal (q + 1) YA| ≤
            DA * Real.log N ^ q :=
          hQA.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hlogYA0 hlogYA q) hDA)
        have hQBN : |moebiusLogPowerKernelReal (r + 1) YB| ≤
            DB * Real.log N ^ r :=
          hQB.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hlogYB0 hlogYB r) hDB)
        rw [abs_div, abs_mul, abs_of_pos hdR]
        have hprod := mul_le_mul hQAN hQBN
          (abs_nonneg (moebiusLogPowerKernelReal (r + 1) YB))
          (mul_nonneg hDA (pow_nonneg hlogpos.le q))
        have hcore :
            |moebiusLogPowerKernelReal (q + 1) YA| *
                |moebiusLogPowerKernelReal (r + 1) YB| ≤
              DA * DB * Real.log N ^ (q + r) := by
          calc
            _ ≤ (DA * Real.log N ^ q) * (DB * Real.log N ^ r) := hprod
            _ = DA * DB * Real.log N ^ (q + r) := by
              rw [pow_add]
              ring
        simpa [YA, YB, div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_right hcore
            (by positivity : 0 ≤ 1 / (d : ℝ))
      _ = DA * DB * Real.log N ^ (q + r) *
          (harmonic (N / max a b) : ℝ) := by
        rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
      _ ≤ DA * DB * Real.log N ^ (q + r) * (harmonic N : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (RHTower.harmonic_cast_mono (Nat.div_le_self N (max a b)))
          (by positivity)
  have hstep : DA * DB * Real.log N ^ (q + r) * (harmonic N : ℝ) ≤
      2 * DA * DB * Real.log N ^ (q + r + 1) := by
    have hharm : (harmonic N : ℝ) ≤ 2 * Real.log N := by
      have := (div_lt_iff₀ hlogpos).mp hratioTwo
      linarith
    have hpow : (0 : ℝ) ≤ Real.log N ^ (q + r) := pow_nonneg hlogpos.le _
    calc
      DA * DB * Real.log N ^ (q + r) * (harmonic N : ℝ)
          ≤ DA * DB * Real.log N ^ (q + r) * (2 * Real.log N) := by
            exact mul_le_mul_of_nonneg_left hharm (by positivity)
      _ = 2 * DA * DB * Real.log N ^ (q + r + 1) := by
            rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
            ring
  exact hmodel.trans hstep

/-- Dilated original Selberg log-monomial. -/
def selbergOriginalDilatedLogMonomial (i j a b N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (N / a), ∑ n ∈ Finset.Icc 1 (N / b),
    selbergOriginalCoeff m n *
      (Real.log ((N : ℝ) / ((a * m : ℕ) : ℝ)) ^ i *
        Real.log ((N : ℝ) / ((b * n : ℕ) : ℝ)) ^ j)

/-- Undilated specialization. -/
theorem selbergOriginalDilatedLogMonomial_one_one (i j N : ℕ) :
    selbergOriginalDilatedLogMonomial i j 1 1 N =
      selbergOriginalLogMonomial i j N := by
  rw [selbergOriginalDilatedLogMonomial, selbergOriginalLogMonomial,
    Finset.sum_product]
  simp only [Nat.div_one, Nat.one_mul]

/-- **Exact Euler-correction decomposition of the dilated form.** -/
theorem selbergOriginalDilatedLogMonomial_eq_correction_scaled
    (i j : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    selbergOriginalDilatedLogMonomial i j a b N =
      ∑ d ∈ Finset.Icc 1 (N / a), ∑ e ∈ Finset.Icc 1 (N / b),
        selbergEulerCorrectionCoeff d e *
          selbergPrincipalScaledLogPowerModel i j (a * d) (b * e) N := by
  rw [selbergOriginalDilatedLogMonomial]
  calc
    (∑ m ∈ Finset.Icc 1 (N / a), ∑ n ∈ Finset.Icc 1 (N / b),
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / ((a * m : ℕ) : ℝ)) ^ i *
          Real.log ((N : ℝ) / ((b * n : ℕ) : ℝ)) ^ j)) =
      ∑ m ∈ Finset.Icc 1 (N / a), ∑ n ∈ Finset.Icc 1 (N / b),
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
          (Real.log ((N : ℝ) / ((a * m : ℕ) : ℝ)) ^ i *
            Real.log ((N : ℝ) / ((b * n : ℕ) : ℝ)) ^ j) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ d ∈ Finset.Icc 1 (N / a), ∑ e ∈ Finset.Icc 1 (N / b),
        selbergEulerCorrectionCoeff d e *
          (∑ r ∈ Finset.Icc 1 (N / a / d), ∑ s ∈ Finset.Icc 1 (N / b / e),
            selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) ^ i *
                Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)) ^ j)) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ (N / a) (N / b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
        ← selbergPrincipalCoeff_weighted_logPower_eq_scaledModel i j (a * d) (b * e) N
          (Nat.mul_pos ha (Finset.mem_Icc.mp hd).1)
          (Nat.mul_pos hb (Finset.mem_Icc.mp he).1)]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [Nat.mul_assoc, Nat.mul_assoc]

end

end RHTower.Sieve
