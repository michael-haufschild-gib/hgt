import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogPrincipalAsymptotics

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Correction-weighted `(log, log²)` principal model, zero outside the truncation square. -/
def selbergCorrectionScaledMixedTerm (N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergPrincipalScaledMixedModel mn.1 mn.2 N / Real.log N ^ 2)
  else 0

theorem tendsto_selbergCorrectionScaledMixedTerm (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledMixedTerm N mn) atTop
      (𝓝 (selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledMixedTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledMixedTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledMixedModel_div_log_sq_one ha hb).const_mul
      (selbergEulerCorrectionCoeff a b)
  simpa only [mul_one] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledMixedTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

theorem exists_eventually_norm_selbergCorrectionScaledMixedTerm_le :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
        ‖selbergCorrectionScaledMixedTerm N mn‖ ≤
          M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  let C : ℝ := 6 + |Real.eulerMascheroniConstant|
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg Real.eulerMascheroniConstant]
  obtain ⟨D, hD, hDbound⟩ :=
    exists_abs_moebiusDoubleLogKernelReal_le_const_mul_log
  refine ⟨2 * C * D, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN mn
  rcases mn with ⟨a, b⟩
  rw [selbergCorrectionScaledMixedTerm]
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
    have hmodel : |selbergPrincipalScaledMixedModel a b N| ≤
        C * D * Real.log N * (harmonic N : ℝ) := by
      rw [selbergPrincipalScaledMixedModel]
      calc
        |∑ d ∈ Finset.Icc 1 (N / max a b),
          coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
              (d : ℝ)| ≤
            ∑ d ∈ Finset.Icc 1 (N / max a b),
              |coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
                  (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / max a b),
            C * D * Real.log N * (1 / (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
          have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
          let Y : ℝ := (N : ℝ) / ((b * d : ℕ) : ℝ)
          have hYone : (1 : ℝ) ≤ Y :=
            one_le_selbergScaledArgument hb (le_max_right a b) hd
          have hYle : Y ≤ (N : ℝ) := selbergScaledArgument_le_natCast hb hdpos
          have hlogY : Real.log Y ≤ Real.log N :=
            Real.log_le_log (by positivity) hYle
          have hA := abs_coprimeLogMoebius_one_le
            ((N : ℝ) / ((a * d : ℕ) : ℝ))
          change |coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ))| ≤ C at hA
          have hQ : |moebiusDoubleLogKernelReal Y| ≤ D * Real.log Y :=
            hDbound Y hYone
          rw [abs_div, abs_mul, abs_of_pos hdR]
          have hprod := mul_le_mul hA hQ
            (abs_nonneg (moebiusDoubleLogKernelReal Y)) hC
          have hlogscaled : C * (D * Real.log Y) ≤ C * D * Real.log N := by
            calc
              C * (D * Real.log Y) = (C * D) * Real.log Y := by ring
              _ ≤ (C * D) * Real.log N :=
                mul_le_mul_of_nonneg_left hlogY (mul_nonneg hC hD)
              _ = C * D * Real.log N := by ring
          have hcore := hprod.trans hlogscaled
          simpa [Y, div_eq_mul_inv, mul_assoc] using
            mul_le_mul_of_nonneg_right hcore (by positivity : 0 ≤ 1 / (d : ℝ))
        _ = C * D * Real.log N * (harmonic (N / max a b) : ℝ) := by
          rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
        _ ≤ C * D * Real.log N * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (RHTower.harmonic_cast_mono (Nat.div_le_self N (max a b))) (by positivity)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (pow_pos hlogpos 2)]
    have hscaled : |selbergPrincipalScaledMixedModel a b N| / Real.log N ^ 2 ≤
        2 * C * D := by
      calc
        |selbergPrincipalScaledMixedModel a b N| / Real.log N ^ 2 ≤
            (C * D * Real.log N * (harmonic N : ℝ)) / Real.log N ^ 2 :=
          div_le_div_of_nonneg_right hmodel (pow_pos hlogpos 2).le
        _ = C * D * ((harmonic N : ℝ) / Real.log N) := by
          field_simp [hlogpos.ne']
        _ ≤ 2 * C * D := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left hratioTwo.le (mul_nonneg hC hD)
    simpa [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hscaled
      (abs_nonneg (selbergEulerCorrectionCoeff a b))
  · simp
    positivity

theorem tsum_selbergCorrectionScaledMixedTerm (N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergCorrectionScaledMixedTerm N mn) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (selbergPrincipalScaledMixedModel a b N / Real.log N ^ 2) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp [selbergCorrectionScaledMixedTerm, ha, hb]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergCorrectionScaledMixedTerm, if_neg hmn]

theorem tendsto_tsum_selbergCorrectionScaledMixedTerm_one :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledMixedTerm N mn) atTop (𝓝 1) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionScaledMixedTerm_le
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    tendsto_selbergCorrectionScaledMixedTerm hdomEventually
  rw [tsum_selbergEulerCorrectionCoeff] at hconv
  exact hconv

/-- Correction-weighted `(log², log²)` principal model, zero outside the truncation square. -/
def selbergCorrectionScaledQuadraticTerm (N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergPrincipalScaledQuadraticModel mn.1 mn.2 N / Real.log N ^ 3)
  else 0

theorem tendsto_selbergCorrectionScaledQuadraticTerm (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledQuadraticTerm N mn) atTop
      (𝓝 ((4 / 3 : ℝ) * selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledQuadraticTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledQuadraticTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledQuadraticModel_div_log_cube_four_thirds ha hb).const_mul
      (selbergEulerCorrectionCoeff a b)
  simpa only [mul_comm] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledQuadraticTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

theorem exists_eventually_norm_selbergCorrectionScaledQuadraticTerm_le :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
        ‖selbergCorrectionScaledQuadraticTerm N mn‖ ≤
          M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  obtain ⟨D, hD, hDbound⟩ :=
    exists_abs_moebiusDoubleLogKernelReal_le_const_mul_log
  refine ⟨2 * D ^ 2, by positivity, ?_⟩
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN mn
  rcases mn with ⟨a, b⟩
  rw [selbergCorrectionScaledQuadraticTerm]
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
    have hmodel : |selbergPrincipalScaledQuadraticModel a b N| ≤
        D ^ 2 * Real.log N ^ 2 * (harmonic N : ℝ) := by
      rw [selbergPrincipalScaledQuadraticModel]
      calc
        |∑ d ∈ Finset.Icc 1 (N / max a b),
          moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
              (d : ℝ)| ≤
            ∑ d ∈ Finset.Icc 1 (N / max a b),
              |moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
                  (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / max a b),
            D ^ 2 * Real.log N ^ 2 * (1 / (d : ℝ)) := by
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
          have hlogYA : Real.log YA ≤ Real.log N :=
            Real.log_le_log (by positivity) hYAle
          have hlogYB : Real.log YB ≤ Real.log N :=
            Real.log_le_log (by positivity) hYBle
          have hQA : |moebiusDoubleLogKernelReal YA| ≤ D * Real.log YA :=
            hDbound YA hYAone
          have hQB : |moebiusDoubleLogKernelReal YB| ≤ D * Real.log YB :=
            hDbound YB hYBone
          have hDYA : D * Real.log YA ≤ D * Real.log N :=
            mul_le_mul_of_nonneg_left hlogYA hD
          have hDYB : D * Real.log YB ≤ D * Real.log N :=
            mul_le_mul_of_nonneg_left hlogYB hD
          rw [abs_div, abs_mul, abs_of_pos hdR]
          have hprod := mul_le_mul (hQA.trans hDYA) (hQB.trans hDYB)
            (abs_nonneg (moebiusDoubleLogKernelReal YB)) (by positivity : 0 ≤ D * Real.log N)
          have hcore :
              |moebiusDoubleLogKernelReal YA| * |moebiusDoubleLogKernelReal YB| ≤
                D ^ 2 * Real.log N ^ 2 := by
            calc
              _ ≤ (D * Real.log N) * (D * Real.log N) := hprod
              _ = D ^ 2 * Real.log N ^ 2 := by ring
          simpa [YA, YB, div_eq_mul_inv, mul_assoc] using
            mul_le_mul_of_nonneg_right hcore (by positivity : 0 ≤ 1 / (d : ℝ))
        _ = D ^ 2 * Real.log N ^ 2 * (harmonic (N / max a b) : ℝ) := by
          rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
        _ ≤ D ^ 2 * Real.log N ^ 2 * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (RHTower.harmonic_cast_mono (Nat.div_le_self N (max a b))) (by positivity)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (pow_pos hlogpos 3)]
    have hscaled : |selbergPrincipalScaledQuadraticModel a b N| / Real.log N ^ 3 ≤
        2 * D ^ 2 := by
      calc
        |selbergPrincipalScaledQuadraticModel a b N| / Real.log N ^ 3 ≤
            (D ^ 2 * Real.log N ^ 2 * (harmonic N : ℝ)) / Real.log N ^ 3 :=
          div_le_div_of_nonneg_right hmodel (pow_pos hlogpos 3).le
        _ = D ^ 2 * ((harmonic N : ℝ) / Real.log N) := by
          field_simp [hlogpos.ne']
        _ ≤ 2 * D ^ 2 := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_left hratioTwo.le (sq_nonneg D)
    simpa [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hscaled
      (abs_nonneg (selbergEulerCorrectionCoeff a b))
  · simp
    positivity

theorem tsum_selbergCorrectionScaledQuadraticTerm (N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergCorrectionScaledQuadraticTerm N mn) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (selbergPrincipalScaledQuadraticModel a b N / Real.log N ^ 3) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp [selbergCorrectionScaledQuadraticTerm, ha, hb]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergCorrectionScaledQuadraticTerm, if_neg hmn]

theorem tendsto_tsum_selbergCorrectionScaledQuadraticTerm_four_thirds :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledQuadraticTerm N mn) atTop (𝓝 (4 / 3 : ℝ)) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionScaledQuadraticTerm_le
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    tendsto_selbergCorrectionScaledQuadraticTerm hdomEventually
  rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff] at hconv
  norm_num at hconv ⊢
  exact hconv

end

end RHTower.Sieve
