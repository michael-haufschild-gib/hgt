import GaloisForLFunctions.RHTower.Sieve.SelbergScaledArgumentBounds
import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogHarmonicModels

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Every fixed `(log, log²)` principal dilation has leading coefficient one. -/
theorem tendsto_selbergPrincipalScaledMixedModel_div_log_sq_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergPrincipalScaledMixedModel a b N / Real.log N ^ (2 : ℕ))
      atTop (𝓝 1) := by
  let C : ℝ := 6 + |Real.eulerMascheroniConstant|
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg Real.eulerMascheroniConstant]
  obtain ⟨D, hD, hDbound⟩ :=
    exists_abs_moebiusDoubleLogKernelReal_le_const_mul_log
  let B : ℝ := C * D + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have herr : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 (N / c),
        (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
          2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
          (d : ℝ)) / Real.log N ^ (2 : ℕ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let η : ℝ := δ / (C + 2)
    have hη : 0 < η := by dsimp [η]; positivity
    have hAnear : ∀ᶠ Y : ℝ in atTop,
        |coprimeLogMoebius 1 Y - 1| < η := by
      exact tendsto_coprimeLogMoebius_one.eventually (Metric.ball_mem_nhds 1 hη)
    rw [eventually_atTop] at hAnear
    obtain ⟨KA, hKA⟩ := hAnear
    have hQnear : ∀ᶠ Y : ℝ in atTop,
        |moebiusDoubleLogKernelReal Y / Real.log Y - 2| < η := by
      exact tendsto_moebiusDoubleLogKernelReal_div_log_two.eventually
        (Metric.ball_mem_nhds 2 hη)
    rw [eventually_atTop] at hQnear
    obtain ⟨KQ, hKQ⟩ := hQnear
    let K : ℝ := max (max KA KQ) 2
    have hKAge : KA ≤ K := le_trans (le_max_left KA KQ) (le_max_left _ _)
    have hKQge : KQ ≤ K := le_trans (le_max_right KA KQ) (le_max_left _ _)
    have hKtwo : (2 : ℝ) ≤ K := le_max_right _ _
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKtwo
    have hfull : ∀ᶠ N : ℕ in atTop,
        dist ((harmonic (N / c) : ℝ) / Real.log N) 1 < 1 :=
      hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
    rw [eventually_atTop] at hfull
    obtain ⟨Nfull, hNfull⟩ := hfull
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlarge : ∀ᶠ N : ℕ in atTop,
        4 * B * K * (c : ℝ) / ε < Real.log N :=
      hlog.eventually_gt_atTop (4 * B * K * (c : ℝ) / ε)
    rw [eventually_atTop] at hlarge
    obtain ⟨Nlarge, hNlarge⟩ := hlarge
    refine ⟨max (max Nfull Nlarge) 2, ?_⟩
    intro N hN
    have hNfull' : Nfull ≤ N := (le_max_left Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hNlarge' : Nlarge ≤ N := (le_max_right Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hN2 : 2 ≤ N := (le_max_right (max Nfull Nlarge) 2).trans hN
    have hNpos : 0 < N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hratioTwo : (harmonic (N / c) : ℝ) / Real.log N < 2 := by
      have hfullN := hNfull N hNfull'
      rw [Real.dist_eq] at hfullN
      have hself : (harmonic (N / c) : ℝ) / Real.log N - 1 ≤
          |(harmonic (N / c) : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
        |(coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
            (d : ℝ)| ≤
          δ * Real.log N * (1 / (d : ℝ)) +
            B * Real.log N * (K * (c : ℝ) / (N : ℝ)) := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      let YA : ℝ := (N : ℝ) / ((a * d : ℕ) : ℝ)
      let YQ : ℝ := (N : ℝ) / ((b * d : ℕ) : ℝ)
      let A : ℝ := coprimeLogMoebius 1 YA
      let Q : ℝ := moebiusDoubleLogKernelReal YQ
      let L : ℝ := Real.log YQ
      have hYAone : (1 : ℝ) ≤ YA := by
        exact one_le_selbergScaledArgument ha (le_max_left a b) hd
      have hYQone : (1 : ℝ) ≤ YQ := by
        exact one_le_selbergScaledArgument hb (le_max_right a b) hd
      have hYQle : YQ ≤ (N : ℝ) := selbergScaledArgument_le_natCast hb hdpos
      have hLnonneg : 0 ≤ L := Real.log_nonneg hYQone
      have hLle : L ≤ Real.log N := Real.log_le_log (by positivity) hYQle
      have hA : |A| ≤ C := abs_coprimeLogMoebius_one_le _
      have hQ : |Q| ≤ D * L := hDbound YQ hYQone
      have hglobal : |A * Q - 2 * L| ≤ B * Real.log N := by
        calc
          |A * Q - 2 * L| ≤ |A * Q| + |2 * L| := abs_sub _ _
          _ = |A| * |Q| + 2 * L := by
            rw [abs_mul, abs_mul, abs_of_nonneg hLnonneg]
            norm_num
          _ ≤ C * (D * L) + 2 * L := by
            have hmul := mul_le_mul hA hQ (abs_nonneg Q) (by positivity : 0 ≤ C)
            nlinarith
          _ = B * L := by dsimp [B]; ring
          _ ≤ B * Real.log N := mul_le_mul_of_nonneg_left hLle hB
      by_cases hya : K ≤ YA
      · by_cases hyq : K ≤ YQ
        · have hAn : |A - 1| < η := hKA _ (hKAge.trans hya)
          have hQn : |Q / L - 2| < η := hKQ _ (hKQge.trans hyq)
          have hYQtwo : 2 ≤ YQ := hKtwo.trans hyq
          have hLpos : 0 < L := Real.log_pos (by linarith)
          have hQdiff : |Q - 2 * L| ≤ η * L := by
            have heq : Q - 2 * L = (Q / L - 2) * L := by
              field_simp [hLpos.ne']
            rw [heq, abs_mul, abs_of_pos hLpos]
            exact (mul_le_mul_of_nonneg_right hQn.le hLpos.le)
          have hprod : |A * Q - 2 * L| ≤ δ * Real.log N := by
            have hsplit : A * Q - 2 * L =
                A * (Q - 2 * L) + 2 * L * (A - 1) := by ring
            rw [hsplit]
            calc
              |A * (Q - 2 * L) + 2 * L * (A - 1)| ≤
                  |A| * |Q - 2 * L| + 2 * L * |A - 1| := by
                have hadd := abs_add_le (A * (Q - 2 * L)) (2 * L * (A - 1))
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hLnonneg,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hadd
                simpa [mul_assoc] using hadd
              _ ≤ C * (η * L) + 2 * L * η := by
                have hleft := mul_le_mul hA hQdiff
                  (abs_nonneg (Q - 2 * L)) (by positivity : 0 ≤ C)
                have hright : 2 * L * |A - 1| ≤ 2 * L * η :=
                  mul_le_mul_of_nonneg_left hAn.le
                    (mul_nonneg (by norm_num) hLnonneg)
                exact add_le_add hleft hright
              _ = δ * L := by
                dsimp [η]
                field_simp
              _ ≤ δ * Real.log N := mul_le_mul_of_nonneg_left hLle hδ.le
          rw [abs_div, abs_of_pos hdR]
          calc
            |A * Q - 2 * L| / (d : ℝ) ≤
                δ * Real.log N * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ _ := le_add_of_nonneg_right (by positivity)
        · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
            inv_natCast_le_scaled_of_argument_lt hKpos hNpos hb
              (le_max_right a b) hdpos (not_le.mp hyq)
          rw [abs_div, abs_of_pos hdR]
          calc
            |A * Q - 2 * L| / (d : ℝ) ≤
                B * Real.log N * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ B * Real.log N * (K * (c : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ ≤ _ := le_add_of_nonneg_left (by positivity)
      · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
          inv_natCast_le_scaled_of_argument_lt hKpos hNpos ha
            (le_max_left a b) hdpos (not_le.mp hya)
        rw [abs_div, abs_of_pos hdR]
        calc
          |A * Q - 2 * L| / (d : ℝ) ≤
              B * Real.log N * (1 / (d : ℝ)) := by
            have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
            simpa [div_eq_mul_inv, mul_assoc] using this
          _ ≤ B * Real.log N * (K * (c : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
    have habssum :
        |∑ d ∈ Finset.Icc 1 (N / c),
          (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
            (d : ℝ)| ≤
          δ * Real.log N * (harmonic (N / c) : ℝ) +
            B * Real.log N * K * (c : ℝ) := by
      calc
        |∑ d ∈ Finset.Icc 1 (N / c),
          (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
            (d : ℝ)| ≤
          ∑ d ∈ Finset.Icc 1 (N / c),
            |(coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
              (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            (δ * Real.log N * (1 / (d : ℝ)) +
              B * Real.log N * (K * (c : ℝ) / (N : ℝ))) :=
          Finset.sum_le_sum hterm
        _ ≤ δ * Real.log N * (harmonic (N / c) : ℝ) +
            B * Real.log N * K * (c : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            sum_Icc_one_div_eq_harmonic]
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [Nat.add_sub_cancel]
          have hqle : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.div_le_self N c
          have htailnonneg :
              0 ≤ B * Real.log N * (K * (c : ℝ) / (N : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hqle htailnonneg
          have heq : (N : ℝ) *
              (B * Real.log N * (K * (c : ℝ) / (N : ℝ))) =
              B * Real.log N * K * (c : ℝ) := by
            field_simp [hNR.ne']
          nlinarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (pow_pos hlogpos 2)]
    calc
      |∑ d ∈ Finset.Icc 1 (N / c),
        (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
          2 * Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ))) /
          (d : ℝ)| / Real.log N ^ (2 : ℕ) ≤
          (δ * Real.log N * (harmonic (N / c) : ℝ) +
            B * Real.log N * K * (c : ℝ)) / Real.log N ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right habssum (pow_pos hlogpos 2).le
      _ = δ * ((harmonic (N / c) : ℝ) / Real.log N) +
          B * K * (c : ℝ) / Real.log N := by field_simp [hlogpos.ne']
      _ < ε := by
        have htail : B * K * (c : ℝ) / Real.log N < ε / 4 := by
          have hlargeN := hNlarge N hNlarge'
          have hBKc : 0 ≤ B * K * (c : ℝ) := by positivity
          apply (div_lt_iff₀ hlogpos).2
          have hscaled := (div_lt_iff₀ hε).mp hlargeN
          nlinarith
        have hhead : δ * ((harmonic (N / c) : ℝ) / Real.log N) < ε / 4 := by
          dsimp [δ]
          nlinarith
        linarith
  have hmain := tendsto_selbergMixedHarmonicMain_div_log_sq_one hb hc
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergPrincipalScaledMixedModel, selbergMixedHarmonicMain,
    show max a b = c by rfl]
  field_simp [hlogne]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Every fixed `(log², log²)` principal dilation has leading coefficient `4/3`. -/
theorem tendsto_selbergPrincipalScaledQuadraticModel_div_log_cube_four_thirds
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergPrincipalScaledQuadraticModel a b N / Real.log N ^ (3 : ℕ))
      atTop (𝓝 (4 / 3 : ℝ)) := by
  obtain ⟨D, hD, hDbound⟩ :=
    exists_abs_moebiusDoubleLogKernelReal_le_const_mul_log
  let B : ℝ := D ^ (2 : ℕ) + 4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have herr : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 (N / c),
        (moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
          4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
          (d : ℝ)) / Real.log N ^ (3 : ℕ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let η : ℝ := δ / (D + 2)
    have hη : 0 < η := by dsimp [η]; positivity
    have hQnear : ∀ᶠ Y : ℝ in atTop,
        |moebiusDoubleLogKernelReal Y / Real.log Y - 2| < η := by
      exact tendsto_moebiusDoubleLogKernelReal_div_log_two.eventually
        (Metric.ball_mem_nhds 2 hη)
    rw [eventually_atTop] at hQnear
    obtain ⟨KQ, hKQ⟩ := hQnear
    let K : ℝ := max KQ 2
    have hKQge : KQ ≤ K := le_max_left _ _
    have hKtwo : (2 : ℝ) ≤ K := le_max_right _ _
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hKtwo
    have hfull : ∀ᶠ N : ℕ in atTop,
        dist ((harmonic (N / c) : ℝ) / Real.log N) 1 < 1 :=
      hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
    rw [eventually_atTop] at hfull
    obtain ⟨Nfull, hNfull⟩ := hfull
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlarge : ∀ᶠ N : ℕ in atTop,
        4 * B * K * (c : ℝ) / ε < Real.log N :=
      hlog.eventually_gt_atTop (4 * B * K * (c : ℝ) / ε)
    rw [eventually_atTop] at hlarge
    obtain ⟨Nlarge, hNlarge⟩ := hlarge
    refine ⟨max (max Nfull Nlarge) 2, ?_⟩
    intro N hN
    have hNfull' : Nfull ≤ N := (le_max_left Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hNlarge' : Nlarge ≤ N := (le_max_right Nfull Nlarge).trans
      ((le_max_left (max Nfull Nlarge) 2).trans hN)
    have hN2 : 2 ≤ N := (le_max_right (max Nfull Nlarge) 2).trans hN
    have hNpos : 0 < N := by omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hratioTwo : (harmonic (N / c) : ℝ) / Real.log N < 2 := by
      have hfullN := hNfull N hNfull'
      rw [Real.dist_eq] at hfullN
      have hself : (harmonic (N / c) : ℝ) / Real.log N - 1 ≤
          |(harmonic (N / c) : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
        |(moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
            (d : ℝ)| ≤
          δ * Real.log N ^ (2 : ℕ) * (1 / (d : ℝ)) +
            B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ)) := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      let YA : ℝ := (N : ℝ) / ((a * d : ℕ) : ℝ)
      let YB : ℝ := (N : ℝ) / ((b * d : ℕ) : ℝ)
      let QA : ℝ := moebiusDoubleLogKernelReal YA
      let QB : ℝ := moebiusDoubleLogKernelReal YB
      let LA : ℝ := Real.log YA
      let LB : ℝ := Real.log YB
      have hYAone : (1 : ℝ) ≤ YA := by
        exact one_le_selbergScaledArgument ha (le_max_left a b) hd
      have hYBone : (1 : ℝ) ≤ YB := by
        exact one_le_selbergScaledArgument hb (le_max_right a b) hd
      have hYAle : YA ≤ (N : ℝ) := selbergScaledArgument_le_natCast ha hdpos
      have hYBle : YB ≤ (N : ℝ) := selbergScaledArgument_le_natCast hb hdpos
      have hLAnonneg : 0 ≤ LA := Real.log_nonneg hYAone
      have hLBnonneg : 0 ≤ LB := Real.log_nonneg hYBone
      have hLAle : LA ≤ Real.log N := Real.log_le_log (by positivity) hYAle
      have hLBle : LB ≤ Real.log N := Real.log_le_log (by positivity) hYBle
      have hlogprod : LA * LB ≤ Real.log N ^ (2 : ℕ) := by
        have := mul_le_mul hLAle hLBle hLBnonneg hlogpos.le
        nlinarith
      have hQA : |QA| ≤ D * LA := hDbound YA hYAone
      have hQB : |QB| ≤ D * LB := hDbound YB hYBone
      have hglobal : |QA * QB - 4 * (LA * LB)| ≤ B * Real.log N ^ (2 : ℕ) := by
        calc
          |QA * QB - 4 * (LA * LB)| ≤ |QA * QB| + |4 * (LA * LB)| :=
            abs_sub _ _
          _ = |QA| * |QB| + 4 * (LA * LB) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hLAnonneg,
              abs_of_nonneg hLBnonneg]
            norm_num
          _ ≤ (D * LA) * (D * LB) + 4 * (LA * LB) := by
            have hmul := mul_le_mul hQA hQB (abs_nonneg QB)
              (mul_nonneg hD hLAnonneg)
            nlinarith
          _ = B * (LA * LB) := by dsimp [B]; ring
          _ ≤ B * Real.log N ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hlogprod hB
      by_cases hya : K ≤ YA
      · by_cases hyb : K ≤ YB
        · have hQAn : |QA / LA - 2| < η := hKQ _ (hKQge.trans hya)
          have hQBn : |QB / LB - 2| < η := hKQ _ (hKQge.trans hyb)
          have hYAtwo : 2 ≤ YA := hKtwo.trans hya
          have hYBtwo : 2 ≤ YB := hKtwo.trans hyb
          have hLApos : 0 < LA := Real.log_pos (by linarith)
          have hLBpos : 0 < LB := Real.log_pos (by linarith)
          have hPAbound : |QA / LA| ≤ D := by
            rw [abs_div, abs_of_pos hLApos]
            exact (div_le_iff₀ hLApos).2 hQA
          have hnorm : |(QA / LA) * (QB / LB) - 4| ≤ δ := by
            have hsplit : (QA / LA) * (QB / LB) - 4 =
                (QA / LA) * (QB / LB - 2) + 2 * (QA / LA - 2) := by ring
            rw [hsplit]
            calc
              |(QA / LA) * (QB / LB - 2) + 2 * (QA / LA - 2)| ≤
                  |QA / LA| * |QB / LB - 2| + 2 * |QA / LA - 2| := by
                have hadd := abs_add_le
                  ((QA / LA) * (QB / LB - 2)) (2 * (QA / LA - 2))
                rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hadd
                simpa using hadd
              _ ≤ D * η + 2 * η := by
                have hleft := mul_le_mul hPAbound hQBn.le
                  (abs_nonneg (QB / LB - 2)) hD
                have hright : 2 * |QA / LA - 2| ≤ 2 * η :=
                  mul_le_mul_of_nonneg_left hQAn.le (by norm_num)
                exact add_le_add hleft hright
              _ = δ := by
                dsimp [η]
                field_simp
          have hprod : |QA * QB - 4 * (LA * LB)| ≤ δ * Real.log N ^ (2 : ℕ) := by
            have heq : QA * QB - 4 * (LA * LB) =
                ((QA / LA) * (QB / LB) - 4) * (LA * LB) := by
              field_simp [hLApos.ne', hLBpos.ne']
            rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hLAnonneg hLBnonneg)]
            exact (mul_le_mul hnorm hlogprod
              (mul_nonneg hLAnonneg hLBnonneg) hδ.le)
          rw [abs_div, abs_of_pos hdR]
          calc
            |QA * QB - 4 * (LA * LB)| / (d : ℝ) ≤
                δ * Real.log N ^ (2 : ℕ) * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ _ := le_add_of_nonneg_right (by positivity)
        · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
            inv_natCast_le_scaled_of_argument_lt hKpos hNpos hb
              (le_max_right a b) hdpos (not_le.mp hyb)
          rw [abs_div, abs_of_pos hdR]
          calc
            |QA * QB - 4 * (LA * LB)| / (d : ℝ) ≤
                B * Real.log N ^ (2 : ℕ) * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ ≤ _ := le_add_of_nonneg_left (by positivity)
      · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
          inv_natCast_le_scaled_of_argument_lt hKpos hNpos ha
            (le_max_left a b) hdpos (not_le.mp hya)
        rw [abs_div, abs_of_pos hdR]
        calc
          |QA * QB - 4 * (LA * LB)| / (d : ℝ) ≤
              B * Real.log N ^ (2 : ℕ) * (1 / (d : ℝ)) := by
            have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
            simpa [div_eq_mul_inv, mul_assoc] using this
          _ ≤ B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
    have habssum :
        |∑ d ∈ Finset.Icc 1 (N / c),
          (moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
            (d : ℝ)| ≤
          δ * Real.log N ^ (2 : ℕ) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (2 : ℕ) * K * (c : ℝ) := by
      calc
        |∑ d ∈ Finset.Icc 1 (N / c),
          (moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
            (d : ℝ)| ≤
          ∑ d ∈ Finset.Icc 1 (N / c),
            |(moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
              (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            (δ * Real.log N ^ (2 : ℕ) * (1 / (d : ℝ)) +
              B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ))) :=
          Finset.sum_le_sum hterm
        _ ≤ δ * Real.log N ^ (2 : ℕ) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (2 : ℕ) * K * (c : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            sum_Icc_one_div_eq_harmonic]
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [Nat.add_sub_cancel]
          have hqle : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.div_le_self N c
          have htailnonneg :
              0 ≤ B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hqle htailnonneg
          have heq : (N : ℝ) *
              (B * Real.log N ^ (2 : ℕ) * (K * (c : ℝ) / (N : ℝ))) =
              B * Real.log N ^ (2 : ℕ) * K * (c : ℝ) := by
            field_simp [hNR.ne']
          nlinarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (pow_pos hlogpos 3)]
    calc
      |∑ d ∈ Finset.Icc 1 (N / c),
        (moebiusDoubleLogKernelReal ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusDoubleLogKernelReal ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
          4 * (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)))) /
          (d : ℝ)| / Real.log N ^ (3 : ℕ) ≤
          (δ * Real.log N ^ (2 : ℕ) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (2 : ℕ) * K * (c : ℝ)) / Real.log N ^ (3 : ℕ) :=
        div_le_div_of_nonneg_right habssum (pow_pos hlogpos 3).le
      _ = δ * ((harmonic (N / c) : ℝ) / Real.log N) +
          B * K * (c : ℝ) / Real.log N := by field_simp [hlogpos.ne']
      _ < ε := by
        have htail : B * K * (c : ℝ) / Real.log N < ε / 4 := by
          have hlargeN := hNlarge N hNlarge'
          have hBKc : 0 ≤ B * K * (c : ℝ) := by positivity
          apply (div_lt_iff₀ hlogpos).2
          have hscaled := (div_lt_iff₀ hε).mp hlargeN
          nlinarith
        have hhead : δ * ((harmonic (N / c) : ℝ) / Real.log N) < ε / 4 := by
          dsimp [δ]
          nlinarith
        linarith
  have hmain := tendsto_selbergQuadraticHarmonicMain_div_log_cube_four_thirds ha hb hc
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergPrincipalScaledQuadraticModel, selbergQuadraticHarmonicMain,
    show max a b = c by rfl]
  field_simp [hlogne]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end

end RHTower.Sieve
