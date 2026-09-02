import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionHigherLogSummable
import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogAsymptotic

/-!
# Higher gcd-logarithmic Selberg asymptotics

The all-order Euler-jet identity and absolute correction summability imply, for every fixed
`a`, the origin-based Selberg energy law

`Σ μ(m)μ(n) gcd(m,n)/(mn) log(gcd(m,n))^a log(N/m) log(N/n)
  ~ log(N)^(a+1)/(a+1)`.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Literal origin-based Selberg monomial with an arbitrary power of `log gcd`. -/
def selbergOriginalGcdLogPowerMonomial (a N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ a *
      (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)))

/-- Uniform envelope for every principal `log(gcd)^a` model used by the origin-based energy. -/
theorem exists_abs_selbergGcdLogPowerPrincipalScaledModel_one_one_le (a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ A B : ℕ, 0 < A → 0 < B →
      |selbergGcdLogPowerPrincipalScaledModel a 1 1 A B N| ≤
        M * Real.log N ^ (a + 1) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow 0
  refine ⟨2 * DA * DB, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN A B hA hB
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hratioTwo : (harmonic N : ℝ) / Real.log N < 2 := by
    rw [Real.dist_eq] at hnearN
    have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
        |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
    linarith
  have hharm : (harmonic N : ℝ) ≤ 2 * Real.log N := by
    have := (div_lt_iff₀ hlogpos).mp hratioTwo
    linarith
  rw [selbergGcdLogPowerPrincipalScaledModel]
  calc
    |∑ d ∈ Finset.Icc 1 (N / max A B),
        Real.log (d : ℝ) ^ a *
          (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
          (d : ℝ)| ≤
      ∑ d ∈ Finset.Icc 1 (N / max A B),
        |Real.log (d : ℝ) ^ a *
          (moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))) /
          (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / max A B),
        DA * DB * Real.log N ^ a * (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hdN : d ≤ N :=
        le_trans (Finset.mem_Icc.mp hd).2 (Nat.div_le_self N (max A B))
      have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hdpos)
      have hlogdN : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by positivity) hdNR
      have hYAone : (1 : ℝ) ≤ (N : ℝ) / ((A * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument hA (le_max_left A B) hd
      have hYBone : (1 : ℝ) ≤ (N : ℝ) / ((B * d : ℕ) : ℝ) :=
        one_le_selbergScaledArgument hB (le_max_right A B) hd
      have hQA : |moebiusLogPowerKernelReal 1
          ((N : ℝ) / ((A * d : ℕ) : ℝ))| ≤ DA := by
        simpa using hDAbound _ hYAone
      have hQB : |moebiusLogPowerKernelReal 1
          ((N : ℝ) / ((B * d : ℕ) : ℝ))| ≤ DB := by
        simpa using hDBbound _ hYBone
      rw [abs_div, abs_of_pos hdR, abs_mul, abs_pow, abs_of_nonneg hlogd0, abs_mul]
      rw [div_le_iff₀ hdR]
      have hlogpow : Real.log (d : ℝ) ^ a ≤ Real.log N ^ a :=
        pow_le_pow_left₀ hlogd0 hlogdN a
      have hkernel :
          |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ))| *
            |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))| ≤
          DA * DB := mul_le_mul hQA hQB (abs_nonneg _) hDA
      calc
        Real.log (d : ℝ) ^ a *
            (|moebiusLogPowerKernelReal 1 ((N : ℝ) / ((A * d : ℕ) : ℝ))| *
              |moebiusLogPowerKernelReal 1 ((N : ℝ) / ((B * d : ℕ) : ℝ))|) ≤
          Real.log N ^ a * (DA * DB) :=
            mul_le_mul hlogpow hkernel (by positivity) (pow_nonneg hlogpos.le a)
        _ = DA * DB * Real.log N ^ a * (1 / (d : ℝ)) * (d : ℝ) := by
          field_simp
    _ = DA * DB * Real.log N ^ a * (harmonic (N / max A B) : ℝ) := by
      rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
    _ ≤ DA * DB * Real.log N ^ a * (harmonic N : ℝ) :=
      mul_le_mul_of_nonneg_left
        (RHTower.harmonic_cast_mono (Nat.div_le_self N (max A B))) (by positivity)
    _ ≤ DA * DB * Real.log N ^ a * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = 2 * DA * DB * Real.log N ^ (a + 1) := by
      rw [pow_succ]
      ring

/-- Exact all-order correction split of the origin-based gcd-logarithmic monomial. -/
theorem selbergOriginalGcdLogPowerMonomial_eq_correction_sum (a N : ℕ) :
    selbergOriginalGcdLogPowerMonomial a N =
      ∑ l ∈ Finset.range (a + 1), (a.choose l : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N := by
  rw [selbergOriginalGcdLogPowerMonomial]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ) ^ a *
          (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)))) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ∑ l ∈ Finset.range (a + 1),
          (a.choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (a - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergOriginalCoeff_mul_log_gcd_pow_eq_correction_convolution_principal]
      rw [Finset.sum_mul]
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ l ∈ Finset.range (a + 1),
        ∑ n ∈ Finset.Icc 1 N,
          (a.choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (a - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ l ∈ Finset.range (a + 1), ∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N,
          (a.choose l : ℝ) *
            bivariateDirichletConvolution
              (selbergEulerCorrectionLogPowerCoeff l)
              (selbergGcdLogPowerPrincipalCoeff (a - l)) m n *
            (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      calc
        (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (a.choose l : ℝ) *
              bivariateDirichletConvolution
                (selbergEulerCorrectionLogPowerCoeff l)
                (selbergGcdLogPowerPrincipalCoeff (a - l)) m n *
              (Real.log ((N : ℝ) / (m : ℝ)) *
                Real.log ((N : ℝ) / (n : ℝ)))) =
          (a.choose l : ℝ) *
            (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              bivariateDirichletConvolution
                (selbergEulerCorrectionLogPowerCoeff l)
                (selbergGcdLogPowerPrincipalCoeff (a - l)) m n *
              (Real.log ((N : ℝ) / (m : ℝ)) *
                Real.log ((N : ℝ) / (n : ℝ)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = _ := by
          apply congrArg (fun x : ℝ => (a.choose l : ℝ) * x)
          rw [sum_Icc_bivariateDirichletConvolution_mul
            (selbergEulerCorrectionLogPowerCoeff l)
            (selbergGcdLogPowerPrincipalCoeff (a - l)) _ N N]
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          apply congrArg (fun x : ℝ => selbergEulerCorrectionLogPowerCoeff l d e * x)
          simpa using
            (selbergGcdLogPowerPrincipalCoeff_weighted_logPower_eq_scaledModel
              (a - l) 1 1 d e N (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1)

/-- One normalized correction order in the higher gcd-logarithmic decomposition. -/
def selbergGcdLogPowerCorrectionScaledTerm
    (a l N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2 *
      (selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 mn.1 mn.2 N /
        Real.log N ^ (a + 1))
  else 0

theorem tsum_selbergGcdLogPowerCorrectionScaledTerm (a l N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergGcdLogPowerCorrectionScaledTerm a l N mn) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        selbergEulerCorrectionLogPowerCoeff l d e *
          (selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N /
            Real.log N ^ (a + 1)) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp [selbergGcdLogPowerCorrectionScaledTerm, hd, he]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergGcdLogPowerCorrectionScaledTerm, if_neg hmn]

private theorem tendsto_log_nat_pow_atTop {l : ℕ} (hl : 0 < l) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ l) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨r, rfl⟩ : ∃ r, l = r + 1 := ⟨l - 1, by omega⟩
  refine Filter.tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  rw [pow_succ]
  simpa [mul_comm] using
    (le_mul_of_one_le_right (le_trans zero_le_one hN) (one_le_pow₀ hN))

theorem exists_eventually_norm_selbergGcdLogPowerCorrectionScaledTerm_le
    (a l : ℕ) (hl : l ≤ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
      ‖selbergGcdLogPowerCorrectionScaledTerm a l N mn‖ ≤
        D * |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| := by
  obtain ⟨M, hM, hMbound⟩ :=
    exists_abs_selbergGcdLogPowerPrincipalScaledModel_one_one_le (a - l)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨M / Real.log (2 : ℝ) ^ l, div_nonneg hM (pow_nonneg hlogTwo.le l), ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2 mn
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
  have hpowTwoLe : Real.log (2 : ℝ) ^ l ≤ Real.log (N : ℝ) ^ l :=
    pow_le_pow_left₀ hlogTwo.le hlogTwoLe l
  rw [selbergGcdLogPowerCorrectionScaledTerm]
  split_ifs with hmem
  · obtain ⟨hm, hn⟩ := hmem
    have hmpos : 0 < mn.1 := (Finset.mem_Icc.mp hm).1
    have hnpos : 0 < mn.2 := (Finset.mem_Icc.mp hn).1
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos hlogpos (a + 1))]
    have hmodel := hN mn.1 mn.2 hmpos hnpos
    have hexp : a + 1 = (a - l + 1) + l := by omega
    have hratio :
        |selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 mn.1 mn.2 N| /
            Real.log N ^ (a + 1) ≤
          M / Real.log (2 : ℝ) ^ l := by
      calc
        |selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 mn.1 mn.2 N| /
              Real.log N ^ (a + 1) ≤
            (M * Real.log N ^ (a - l + 1)) /
              Real.log N ^ (a + 1) :=
          div_le_div_of_nonneg_right hmodel (pow_nonneg hlogpos.le _)
        _ = M / Real.log N ^ l := by
          rw [hexp, pow_add]
          field_simp
          rw [pow_add, pow_succ]
          ring
        _ ≤ M / Real.log (2 : ℝ) ^ l := by
          rw [div_le_div_iff₀ (pow_pos hlogpos l) (pow_pos hlogTwo l)]
          exact mul_le_mul_of_nonneg_left hpowTwoLe hM
    calc
      |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| *
          (|selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 mn.1 mn.2 N| /
            Real.log N ^ (a + 1)) ≤
        |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| *
          (M / Real.log (2 : ℝ) ^ l) :=
        mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
      _ = (M / Real.log (2 : ℝ) ^ l) *
          |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2| := mul_comm _ _
  · simp
    exact mul_nonneg (div_nonneg hM (pow_nonneg hlogTwo.le l)) (abs_nonneg _)

theorem tendsto_selbergGcdLogPowerCorrectionScaledTerm
    (a l : ℕ) (hl : l ≤ a) (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergGcdLogPowerCorrectionScaledTerm a l N mn)
      atTop (𝓝 (if l = 0 then
        (1 / ((a : ℝ) + 1)) * selbergEulerCorrectionCoeff mn.1 mn.2 else 0)) := by
  rcases mn with ⟨d, e⟩
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [selbergGcdLogPowerCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  rcases e.eq_zero_or_pos with rfl | he
  · simp [selbergGcdLogPowerCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  by_cases hl0 : l = 0
  · subst l
    simp only [if_true]
    have hmain :=
      (tendsto_selbergGcdLogPowerPrincipalScaledModel_one_one_div_log_pow
        a hd he).const_mul (selbergEulerCorrectionCoeff d e)
    simpa only [selbergEulerCorrectionLogPowerCoeff_zero, mul_comm] using
      hmain.congr' (by
        filter_upwards [eventually_ge_atTop (max d e)] with N hN
        have hmem : d ∈ Finset.Icc 1 N ∧ e ∈ Finset.Icc 1 N :=
          ⟨Finset.mem_Icc.mpr ⟨hd, (le_max_left d e).trans hN⟩,
            Finset.mem_Icc.mpr ⟨he, (le_max_right d e).trans hN⟩⟩
        rw [selbergGcdLogPowerCorrectionScaledTerm, if_pos hmem]
        simp [selbergEulerCorrectionLogPowerCoeff_zero])
  · rw [if_neg hl0]
    obtain ⟨M, hM, hMbound⟩ :=
      exists_abs_selbergGcdLogPowerPrincipalScaledModel_one_one_le (a - l)
    have hlogPow := tendsto_log_nat_pow_atTop (Nat.pos_of_ne_zero hl0)
    have hmaj : Tendsto (fun N : ℕ =>
        (|selbergEulerCorrectionLogPowerCoeff l d e| * M) /
          Real.log N ^ l) atTop (𝓝 0) :=
      hlogPow.const_div_atTop (|selbergEulerCorrectionLogPowerCoeff l d e| * M)
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hMbound, eventually_ge_atTop (max (max d e) 2)] with N hN hNlarge
    have hdN : d ≤ N := (le_max_left d e).trans
      ((le_max_left (max d e) 2).trans hNlarge)
    have heN : e ≤ N := (le_max_right d e).trans
      ((le_max_left (max d e) 2).trans hNlarge)
    have hN2 : 2 ≤ N := (le_max_right (max d e) 2).trans hNlarge
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    rw [selbergGcdLogPowerCorrectionScaledTerm,
      if_pos ⟨Finset.mem_Icc.mpr ⟨hd, hdN⟩, Finset.mem_Icc.mpr ⟨he, heN⟩⟩,
      Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos hlogpos (a + 1))]
    have hmodel := hN d e hd he
    have hexp : a + 1 = (a - l + 1) + l := by omega
    calc
      |selbergEulerCorrectionLogPowerCoeff l d e| *
          (|selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N| /
            Real.log N ^ (a + 1)) ≤
        |selbergEulerCorrectionLogPowerCoeff l d e| *
          ((M * Real.log N ^ (a - l + 1)) / Real.log N ^ (a + 1)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hmodel (pow_nonneg hlogpos.le _)) (abs_nonneg _)
      _ = (|selbergEulerCorrectionLogPowerCoeff l d e| * M) /
          Real.log N ^ l := by
        rw [hexp, pow_add]
        field_simp
        rw [pow_add, pow_succ]
        ring

theorem tendsto_tsum_selbergGcdLogPowerCorrectionScaledTerm
    (a l : ℕ) (hl : l ≤ a) :
    Tendsto (fun N : ℕ =>
      ∑' mn : ℕ × ℕ, selbergGcdLogPowerCorrectionScaledTerm a l N mn)
      atTop (𝓝 (if l = 0 then 1 / ((a : ℝ) + 1) else 0)) := by
  obtain ⟨D, hD, hdomEventually⟩ :=
    exists_eventually_norm_selbergGcdLogPowerCorrectionScaledTerm_le a l hl
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      D * |selbergEulerCorrectionLogPowerCoeff l mn.1 mn.2|) :=
    (summable_abs_selbergEulerCorrectionLogPowerCoeff l).mul_left D
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    (tendsto_selbergGcdLogPowerCorrectionScaledTerm a l hl) hdomEventually
  by_cases hl0 : l = 0
  · subst l
    simp only [if_true] at hconv ⊢
    rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff, mul_one] at hconv
    exact hconv
  · simp only [if_neg hl0] at hconv ⊢
    simpa using hconv

/-- **Origin-based Selberg energy with every fixed power of `log gcd`.** -/
theorem tendsto_selbergOriginalGcdLogPowerMonomial_div_log_pow (a : ℕ) :
    Tendsto (fun N : ℕ =>
      selbergOriginalGcdLogPowerMonomial a N / Real.log N ^ (a + 1))
      atTop (𝓝 (1 / ((a : ℝ) + 1))) := by
  have hterms : ∀ l ∈ Finset.range (a + 1),
      Tendsto (fun N : ℕ => (a.choose l : ℝ) *
        ∑' mn : ℕ × ℕ, selbergGcdLogPowerCorrectionScaledTerm a l N mn)
        atTop (𝓝 ((a.choose l : ℝ) *
          (if l = 0 then 1 / ((a : ℝ) + 1) else 0))) := by
    intro l hl
    exact (tendsto_tsum_selbergGcdLogPowerCorrectionScaledTerm a l (by simpa using hl)).const_mul _
  have hsum := tendsto_finsetSum (Finset.range (a + 1)) hterms
  have hlimit :
      (∑ l ∈ Finset.range (a + 1), (a.choose l : ℝ) *
        (if l = 0 then 1 / ((a : ℝ) + 1) else 0)) =
        1 / ((a : ℝ) + 1) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro l hl hl0
      simp [hl0]
    · simp
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [] with N
  rw [selbergOriginalGcdLogPowerMonomial_eq_correction_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l hl
  rw [tsum_selbergGcdLogPowerCorrectionScaledTerm]
  calc
    (a.choose l : ℝ) *
        (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            (selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N /
              Real.log N ^ (a + 1))) =
      (a.choose l : ℝ) *
        ((∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N) /
          Real.log N ^ (a + 1)) := by
      apply congrArg (fun x : ℝ => (a.choose l : ℝ) * x)
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = ((a.choose l : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          selbergEulerCorrectionLogPowerCoeff l d e *
            selbergGcdLogPowerPrincipalScaledModel (a - l) 1 1 d e N) /
        Real.log N ^ (a + 1) := by ring

end

end RHTower.Sieve
