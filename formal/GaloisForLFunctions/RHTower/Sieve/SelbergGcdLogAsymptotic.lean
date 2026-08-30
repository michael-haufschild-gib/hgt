import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionLogSummable
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogGlobalIdentity
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogHarmonicReplacement
import GaloisForLFunctions.RHTower.Sieve.SelbergDilatedLogMonomialAsymptotic

/-!
# The gcd-logarithmic Selberg log-monomial asymptotic

`∑_{m,n ≤ N} μ(m)μ(n)(m,n)/(mn)·log(N/m)^i·log(N/n)^j·log(m,n) ~ (i·j/((i+j−1)(i+j)))·(log N)^{i+j}`.

The global identity of `SelbergGcdLogGlobalIdentity` splits the coefficient into
`corr^{log} ∗ 𝒫 + corr ∗ 𝒫^{log}`.  The first piece is `O((log N)^{i+j−1})` by the uniform
principal envelope and `‖corr^{log}‖₁ < ∞`; the second carries the main term through the same
dominated-convergence layer used for the pure-log family.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- **Uniform envelope for the gcd-logarithmic principal model.** -/
theorem exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b →
      |selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N| ≤
        M * Real.log N ^ (q + r + 2) := by
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
  have hharm : (harmonic N : ℝ) ≤ 2 * Real.log N := by
    have := (div_lt_iff₀ hlogpos).mp hratioTwo
    linarith
  rw [selbergGcdLogPrincipalScaledLogPowerModel]
  calc
    |∑ d ∈ Finset.Icc 1 (N / max a b),
        Real.log (d : ℝ) *
          (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
          (d : ℝ)|
        ≤ ∑ d ∈ Finset.Icc 1 (N / max a b),
            |Real.log (d : ℝ) *
              (moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
              (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / max a b),
        DA * DB * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hdN : d ≤ N := le_trans (Finset.mem_Icc.mp hd).2 (Nat.div_le_self N (max a b))
      have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hdpos)
      have hlogdN : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by positivity) hdNR
      have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((a * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument ha (le_max_left a b) hd
      have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((b * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument hb (le_max_right a b) hd
      have hYAle : (N : ℝ) / ((a * d : ℕ) : ℝ) ≤ (N : ℝ) :=
        selbergScaledArgument_le_natCast ha hdpos
      have hYBle : (N : ℝ) / ((b * d : ℕ) : ℝ) ≤ (N : ℝ) :=
        selbergScaledArgument_le_natCast hb hdpos
      have hLA0 : 0 ≤ Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) := Real.log_nonneg hYAone
      have hLB0 : 0 ≤ Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) := Real.log_nonneg hYBone
      have hLAle : Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ≤ Real.log N :=
        Real.log_le_log (by positivity) hYAle
      have hLBle : Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ≤ Real.log N :=
        Real.log_le_log (by positivity) hYBle
      have hQA : |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ))| ≤
          DA * Real.log N ^ q :=
        (hDAbound _ hYAone).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hLA0 hLAle q) hDA)
      have hQB : |moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))| ≤
          DB * Real.log N ^ r :=
        (hDBbound _ hYBone).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hLB0 hLBle r) hDB)
      rw [abs_div, abs_of_pos hdR, abs_mul, abs_of_nonneg hlogd0, abs_mul]
      rw [div_le_iff₀ hdR]
      have hcore : |moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ))| *
          |moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))| ≤
          DA * DB * Real.log N ^ (q + r) := by
        calc
          _ ≤ (DA * Real.log N ^ q) * (DB * Real.log N ^ r) :=
            mul_le_mul hQA hQB (abs_nonneg _) (by positivity)
          _ = DA * DB * Real.log N ^ (q + r) := by rw [pow_add]; ring
      have hprod : Real.log (d : ℝ) *
          (|moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ))| *
            |moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))|) ≤
          Real.log N * (DA * DB * Real.log N ^ (q + r)) :=
        mul_le_mul hlogdN hcore (by positivity) hlogpos.le
      have hfac : Real.log N * (DA * DB * Real.log N ^ (q + r)) =
          DA * DB * Real.log N ^ (q + r + 1) := by
        rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
        ring
      rw [hfac] at hprod
      calc
        Real.log (d : ℝ) *
            (|moebiusLogPowerKernelReal (q + 1) ((N : ℝ) / ((a * d : ℕ) : ℝ))| *
              |moebiusLogPowerKernelReal (r + 1) ((N : ℝ) / ((b * d : ℕ) : ℝ))|)
            ≤ DA * DB * Real.log N ^ (q + r + 1) := hprod
        _ = DA * DB * Real.log N ^ (q + r + 1) * (1 / (d : ℝ)) * (d : ℝ) := by
            field_simp
    _ = DA * DB * Real.log N ^ (q + r + 1) * (harmonic (N / max a b) : ℝ) := by
      rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
    _ ≤ DA * DB * Real.log N ^ (q + r + 1) * (harmonic N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (RHTower.harmonic_cast_mono (Nat.div_le_self N (max a b)))
        (by positivity)
    _ ≤ DA * DB * Real.log N ^ (q + r + 1) * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = 2 * DA * DB * Real.log N ^ (q + r + 2) := by
      rw [show q + r + 2 = (q + r + 1) + 1 by omega, pow_succ]
      ring

/-- **Exact splitting of the gcd-logarithmic monomial into the two correction sums.** -/
theorem selbergOriginalGcdLogMonomial_eq_correction_split (i j N : ℕ) :
    selbergOriginalGcdLogMonomial i j N =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogCoeff d e *
          selbergPrincipalScaledLogPowerModel i j d e N) +
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff d e *
          selbergGcdLogPrincipalScaledLogPowerModel i j d e N) := by
  rw [selbergOriginalGcdLogMonomial]
  have hcoef : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N,
      selbergOriginalGcdLogCoeff m n *
          (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j) =
        bivariateDirichletConvolution selbergEulerCorrectionLogCoeff
            selbergPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j) +
          bivariateDirichletConvolution selbergEulerCorrectionCoeff
            selbergGcdLogPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j) := by
    intro m hm n hn
    rw [selbergOriginalGcdLogCoeff_eq_convolution_sum
      (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1]
    ring
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => hcoef m hm n hn))]
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [selbergPrincipalCoeff_weighted_logPower_eq_scaledModel i j d e N
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1]
  · rw [sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [selbergGcdLogPrincipalCoeff_weighted_logPower_eq_scaledModel i j d e N
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1]

/-- Normalized main-term correction convolution. -/
def selbergGcdCorrectionScaledTerm (q r N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) mn.1 mn.2 N /
        Real.log N ^ (q + r + 2))
  else 0

theorem tsum_selbergGcdCorrectionScaledTerm (q r N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergGcdCorrectionScaledTerm q r N mn) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff d e *
          (selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N /
            Real.log N ^ (q + r + 2)) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp [selbergGcdCorrectionScaledTerm, hd, he]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergGcdCorrectionScaledTerm, if_neg hmn]

theorem exists_eventually_norm_selbergGcdCorrectionScaledTerm_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
      ‖selbergGcdCorrectionScaledTerm q r N mn‖ ≤
        M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  obtain ⟨M, hM, hMbound⟩ :=
    exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le q r
  refine ⟨M, hM, ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2 mn
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  rw [selbergGcdCorrectionScaledTerm]
  split_ifs with hab
  · obtain ⟨hdMem, heMem⟩ := hab
    have hd : 0 < mn.1 := (Finset.mem_Icc.mp hdMem).1
    have he : 0 < mn.2 := (Finset.mem_Icc.mp heMem).1
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos hlogpos (q + r + 2))]
    have hscaled :
        |selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) mn.1 mn.2 N| /
            Real.log N ^ (q + r + 2) ≤ M := by
      rw [div_le_iff₀ (pow_pos hlogpos (q + r + 2))]
      exact hN mn.1 mn.2 hd he
    calc |selbergEulerCorrectionCoeff mn.1 mn.2| *
          (|selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1) mn.1 mn.2 N| /
            Real.log N ^ (q + r + 2))
        ≤ |selbergEulerCorrectionCoeff mn.1 mn.2| * M :=
          mul_le_mul_of_nonneg_left hscaled (abs_nonneg _)
      _ = M * |selbergEulerCorrectionCoeff mn.1 mn.2| := mul_comm _ _
  · simp
    positivity

theorem tendsto_selbergGcdCorrectionScaledTerm (q r : ℕ) (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergGcdCorrectionScaledTerm q r N mn)
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)) *
        selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨d, e⟩
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [selbergGcdCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  rcases e.eq_zero_or_pos with rfl | he
  · simp [selbergGcdCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergGcdLogPrincipalScaledLogPowerModel_div_log_pow q r hd he).const_mul
      (selbergEulerCorrectionCoeff d e)
  simpa only [mul_comm] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max d e)] with N hN
    rw [selbergGcdCorrectionScaledTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨hd, (le_max_left d e).trans hN⟩,
      Finset.mem_Icc.mpr ⟨he, (le_max_right d e).trans hN⟩⟩)

theorem tendsto_tsum_selbergGcdCorrectionScaledTerm (q r : ℕ) :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ, selbergGcdCorrectionScaledTerm q r N mn)
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)))) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergGcdCorrectionScaledTerm_le q r
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) :=
    summable_abs_selbergEulerCorrectionCoeff.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    (tendsto_selbergGcdCorrectionScaledTerm q r) hdomEventually
  rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff, mul_one] at hconv
  exact hconv

/-- The differentiated-correction error term is `O((log N)^{q+r+1})`. -/
theorem exists_abs_gcdLogErrorTerm_le (q r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      |∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N| ≤
        K * Real.log N ^ (q + r + 1) := by
  obtain ⟨M, hM, hMbound⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  have habs := summable_abs_selbergEulerCorrectionLogCoeff
  have hSnn : 0 ≤ ∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2| :=
    tsum_nonneg fun _ => abs_nonneg _
  refine ⟨M * (∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2|),
    mul_nonneg hM hSnn, ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hpow : (0 : ℝ) ≤ Real.log N ^ (q + r + 1) := pow_nonneg hlogpos.le _
  have hterm : ∀ d ∈ Finset.Icc 1 N, ∀ e ∈ Finset.Icc 1 N,
      |selbergEulerCorrectionLogCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N| ≤
        |selbergEulerCorrectionLogCoeff d e| * (M * Real.log N ^ (q + r + 1)) := by
    intro d hd e he
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (hN d e (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1) (abs_nonneg _)
  calc
    |∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N|
        ≤ ∑ d ∈ Finset.Icc 1 N, |∑ e ∈ Finset.Icc 1 N,
            selbergEulerCorrectionLogCoeff d e *
              selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          |selbergEulerCorrectionLogCoeff d e| * (M * Real.log N ^ (q + r + 1)) := by
          refine Finset.sum_le_sum ?_
          intro d hd
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (hterm d hd))
    _ = (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
            |selbergEulerCorrectionLogCoeff p.1 p.2|) *
          (M * Real.log N ^ (q + r + 1)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => (Finset.sum_mul _ _ _).symm
    _ ≤ (∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2|) *
          (M * Real.log N ^ (q + r + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Summable.sum_le_tsum _ (fun _ _ => abs_nonneg _) habs
    _ = M * (∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2|) *
          Real.log N ^ (q + r + 1) := by ring

theorem tendsto_gcdLogErrorTerm_div (q r : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N) /
        Real.log N ^ (q + r + 2)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hKbound⟩ := exists_abs_gcdLogErrorTerm_le q r
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => K / Real.log N) atTop (𝓝 0) :=
    hlogTop.const_div_atTop K
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hKbound, eventually_ge_atTop 2] with N hN hN2
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlogpos (q + r + 2))]
  rw [div_le_div_iff₀ (pow_pos hlogpos (q + r + 2)) hlogpos]
  have hstep : |∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      selbergEulerCorrectionLogCoeff d e *
        selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) d e N| *
      Real.log N ≤ (K * Real.log N ^ (q + r + 1)) * Real.log N :=
    mul_le_mul_of_nonneg_right hN hlogpos.le
  refine hstep.trans_eq ?_
  rw [show q + r + 2 = (q + r + 1) + 1 by omega, pow_succ]
  ring

/-- **The gcd-logarithmic Selberg log-monomial asymptotic.** -/
theorem tendsto_selbergOriginalGcdLogMonomial_succ_succ_div_log_pow (q r : ℕ) :
    Tendsto (fun N : ℕ =>
      selbergOriginalGcdLogMonomial (q + 1) (r + 1) N /
        Real.log N ^ (q + r + 2))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)))) := by
  have herr := tendsto_gcdLogErrorTerm_div q r
  have hmain := tendsto_tsum_selbergGcdCorrectionScaledTerm q r
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [tsum_selbergGcdCorrectionScaledTerm,
    selbergOriginalGcdLogMonomial_eq_correction_split, add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- **Graham's Selberg diagonal with a gcd-logarithmic weight, at every pair of positive
powers.** -/
theorem tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Tendsto (fun N : ℕ =>
      selbergOriginalGcdLogMonomial i j N / Real.log N ^ (i + j))
      atTop (𝓝 (((i : ℝ) * (j : ℝ)) /
        (((i : ℝ) + (j : ℝ) - 1) * ((i : ℝ) + (j : ℝ))))) := by
  obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  have hexp : q + 1 + (r + 1) = q + r + 2 := by omega
  rw [hexp]
  have hval : (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)) /
      ((((q + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) - 1) *
        (((q + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ))) =
      (((q : ℝ) + 1) * ((r : ℝ) + 1)) /
        (((q : ℝ) + (r : ℝ) + 1) * ((q : ℝ) + (r : ℝ) + 2)) := by
    push_cast
    ring_nf
  rw [hval]
  exact tendsto_selbergOriginalGcdLogMonomial_succ_succ_div_log_pow q r

end

end RHTower.Sieve
