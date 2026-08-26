import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerPrincipalAsymptotics

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Correction-weighted arbitrary positive log-power model, zero off the truncation square. -/
def selbergCorrectionScaledLogPowerTerm
    (q r N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) mn.1 mn.2 N /
        Real.log N ^ (q + r + 1))
  else 0

/-- All positive log-power correction terms admit one summable coefficient majorant. -/
theorem exists_eventually_norm_selbergCorrectionScaledLogPowerTerm_le
    (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
        ‖selbergCorrectionScaledLogPowerTerm q r N mn‖ ≤
          M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow q
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  refine ⟨2 * DA * DB, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN mn
  rcases mn with ⟨a, b⟩
  rw [selbergCorrectionScaledLogPowerTerm]
  split_ifs with hab
  · obtain ⟨haMem, hbMem⟩ := hab
    have ha : 0 < a := (Finset.mem_Icc.mp haMem).1
    have hb : 0 < b := (Finset.mem_Icc.mp hbMem).1
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
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos hlogpos (q + r + 1))]
    have hscaled :
        |selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N| /
            Real.log N ^ (q + r + 1) ≤ 2 * DA * DB := by
      calc
        |selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N| /
              Real.log N ^ (q + r + 1) ≤
            (DA * DB * Real.log N ^ (q + r) * (harmonic N : ℝ)) /
              Real.log N ^ (q + r + 1) :=
          div_le_div_of_nonneg_right hmodel
            (pow_pos hlogpos (q + r + 1)).le
        _ = DA * DB * ((harmonic N : ℝ) / Real.log N) := by
          rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
          field_simp [hlogpos.ne']
        _ ≤ 2 * DA * DB := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left hratioTwo.le (mul_nonneg hDA hDB)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hscaled
        (abs_nonneg (selbergEulerCorrectionCoeff a b))
  · simp
    positivity

theorem tsum_selbergCorrectionScaledLogPowerTerm
    (q r N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergCorrectionScaledLogPowerTerm q r N mn) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N /
            Real.log N ^ (q + r + 1)) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp [selbergCorrectionScaledLogPowerTerm, ha, hb]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergCorrectionScaledLogPowerTerm, if_neg hmn]

theorem tendsto_selbergCorrectionScaledLogPowerTerm_zero_three
    (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledLogPowerTerm 0 3 N mn)
      atTop (𝓝 (selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledLogPowerModel_one_four_div_log_fourth_one
      ha hb).const_mul (selbergEulerCorrectionCoeff a b)
  simpa only [mul_one] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledLogPowerTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

theorem tendsto_selbergCorrectionScaledLogPowerTerm_one_two
    (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledLogPowerTerm 1 2 N mn)
      atTop (𝓝 ((3 / 2 : ℝ) * selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledLogPowerTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledLogPowerModel_two_three_div_log_fourth_three_halves
      ha hb).const_mul (selbergEulerCorrectionCoeff a b)
  simpa only [mul_comm] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledLogPowerTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

theorem tendsto_tsum_selbergCorrectionScaledLogPowerTerm_zero_three_one :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledLogPowerTerm 0 3 N mn) atTop (𝓝 1) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionScaledLogPowerTerm_le 0 3
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    tendsto_selbergCorrectionScaledLogPowerTerm_zero_three hdomEventually
  rw [tsum_selbergEulerCorrectionCoeff] at hconv
  exact hconv

theorem tendsto_tsum_selbergCorrectionScaledLogPowerTerm_one_two_three_halves :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledLogPowerTerm 1 2 N mn)
      atTop (𝓝 (3 / 2 : ℝ)) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionScaledLogPowerTerm_le 1 2
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    tendsto_selbergCorrectionScaledLogPowerTerm_one_two hdomEventually
  rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff] at hconv
  norm_num at hconv ⊢
  exact hconv

end

end RHTower.Sieve
