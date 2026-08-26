import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerHomogeneousBound
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerPrincipalExact
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerHarmonicModels
import GaloisForLFunctions.RHTower.Sieve.SelbergScaledArgumentBounds

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Harmonic leading model for two arbitrary positive logarithmic Möbius kernels. -/
def selbergLogPowerHarmonicMain
    (q r a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    (((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
      Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
      Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r) / (d : ℝ)

/-- Uniform harmonic replacement for every fixed pair of positive logarithmic powers. -/
theorem tendsto_selbergPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      (selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) a b N -
        selbergLogPowerHarmonicMain q r a b N) /
          Real.log N ^ (q + r + 1)) atTop (𝓝 0) := by
  obtain ⟨DA, hDA, hDAbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow q
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  let cq : ℝ := ((q + 1 : ℕ) : ℝ)
  let cr : ℝ := ((r + 1 : ℕ) : ℝ)
  have hcq : 0 ≤ cq := by dsimp [cq]; positivity
  have hcr : 0 ≤ cr := by dsimp [cr]; positivity
  have hcrpos : 0 < cr := by dsimp [cr]; positivity
  let B : ℝ := DA * DB + cq * cr
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have herr : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 (N / c),
        (moebiusLogPowerKernelReal (q + 1)
              ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            moebiusLogPowerKernelReal (r + 1)
              ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
          cq * cr *
            (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
              Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
          (d : ℝ)) / Real.log N ^ (q + r + 1)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let η : ℝ := δ / (DA + cr)
    have hdenpos : 0 < DA + cr := add_pos_of_nonneg_of_pos hDA hcrpos
    have hη : 0 < η := by dsimp [η]; positivity
    have hAnear : ∀ᶠ Y : ℝ in atTop,
        |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q - cq| < η := by
      exact tendsto_moebiusLogPowerKernelReal_div_log_pow q |>.eventually
        (Metric.ball_mem_nhds cq hη)
    rw [eventually_atTop] at hAnear
    obtain ⟨KA, hKA⟩ := hAnear
    have hBnear : ∀ᶠ Y : ℝ in atTop,
        |moebiusLogPowerKernelReal (r + 1) Y / Real.log Y ^ r - cr| < η := by
      exact tendsto_moebiusLogPowerKernelReal_div_log_pow r |>.eventually
        (Metric.ball_mem_nhds cr hη)
    rw [eventually_atTop] at hBnear
    obtain ⟨KB, hKB⟩ := hBnear
    let K : ℝ := max (max KA KB) 2
    have hKAge : KA ≤ K := le_trans (le_max_left KA KB) (le_max_left _ _)
    have hKBge : KB ≤ K := le_trans (le_max_right KA KB) (le_max_left _ _)
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
        |(moebiusLogPowerKernelReal (q + 1)
                ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1)
                ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            cq * cr *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
            (d : ℝ)| ≤
          δ * Real.log N ^ (q + r) * (1 / (d : ℝ)) +
            B * Real.log N ^ (q + r) * (K * (c : ℝ) / (N : ℝ)) := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      let YA : ℝ := (N : ℝ) / ((a * d : ℕ) : ℝ)
      let YB : ℝ := (N : ℝ) / ((b * d : ℕ) : ℝ)
      let QA : ℝ := moebiusLogPowerKernelReal (q + 1) YA
      let QB : ℝ := moebiusLogPowerKernelReal (r + 1) YB
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
      have hLApow : LA ^ q ≤ Real.log N ^ q :=
        pow_le_pow_left₀ hLAnonneg hLAle q
      have hLBpow : LB ^ r ≤ Real.log N ^ r :=
        pow_le_pow_left₀ hLBnonneg hLBle r
      have hlogprod : LA ^ q * LB ^ r ≤ Real.log N ^ (q + r) := by
        calc
          LA ^ q * LB ^ r ≤ Real.log N ^ q * Real.log N ^ r :=
            mul_le_mul hLApow hLBpow (pow_nonneg hLBnonneg r)
              (pow_nonneg hlogpos.le q)
          _ = Real.log N ^ (q + r) := (pow_add _ _ _).symm
      have hQA : |QA| ≤ DA * LA ^ q := hDAbound YA hYAone
      have hQB : |QB| ≤ DB * LB ^ r := hDBbound YB hYBone
      have hglobal :
          |QA * QB - cq * cr * (LA ^ q * LB ^ r)| ≤
            B * Real.log N ^ (q + r) := by
        calc
          |QA * QB - cq * cr * (LA ^ q * LB ^ r)| ≤
              |QA * QB| + |cq * cr * (LA ^ q * LB ^ r)| := abs_sub _ _
          _ = |QA| * |QB| + cq * cr * (LA ^ q * LB ^ r) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul,
              abs_of_nonneg hcq, abs_of_nonneg hcr,
              abs_of_nonneg (pow_nonneg hLAnonneg q),
              abs_of_nonneg (pow_nonneg hLBnonneg r)]
          _ ≤ (DA * LA ^ q) * (DB * LB ^ r) +
              cq * cr * (LA ^ q * LB ^ r) := by
            exact add_le_add
              (mul_le_mul hQA hQB (abs_nonneg QB)
                (mul_nonneg hDA (pow_nonneg hLAnonneg q))) le_rfl
          _ = B * (LA ^ q * LB ^ r) := by dsimp [B]; ring
          _ ≤ B * Real.log N ^ (q + r) :=
            mul_le_mul_of_nonneg_left hlogprod hB
      by_cases hya : K ≤ YA
      · by_cases hyb : K ≤ YB
        · have hQAn : |QA / LA ^ q - cq| < η := hKA _ (hKAge.trans hya)
          have hQBn : |QB / LB ^ r - cr| < η := hKB _ (hKBge.trans hyb)
          have hYAtwo : 2 ≤ YA := hKtwo.trans hya
          have hYBtwo : 2 ≤ YB := hKtwo.trans hyb
          have hLApos : 0 < LA := Real.log_pos (by linarith)
          have hLBpos : 0 < LB := Real.log_pos (by linarith)
          have hPAbound : |QA / LA ^ q| ≤ DA := by
            rw [abs_div, abs_of_pos (pow_pos hLApos q)]
            exact (div_le_iff₀ (pow_pos hLApos q)).2 hQA
          have hnorm : |(QA / LA ^ q) * (QB / LB ^ r) - cq * cr| ≤ δ := by
            have hsplit : (QA / LA ^ q) * (QB / LB ^ r) - cq * cr =
                (QA / LA ^ q) * (QB / LB ^ r - cr) +
                  cr * (QA / LA ^ q - cq) := by ring
            rw [hsplit]
            calc
              |(QA / LA ^ q) * (QB / LB ^ r - cr) +
                  cr * (QA / LA ^ q - cq)| ≤
                |QA / LA ^ q| * |QB / LB ^ r - cr| +
                  cr * |QA / LA ^ q - cq| := by
                have hadd := abs_add_le
                  ((QA / LA ^ q) * (QB / LB ^ r - cr))
                  (cr * (QA / LA ^ q - cq))
                rw [abs_mul, abs_mul, abs_of_nonneg hcr] at hadd
                simpa using hadd
              _ ≤ DA * η + cr * η := by
                exact add_le_add
                  (mul_le_mul hPAbound hQBn.le (abs_nonneg _) hDA)
                  (mul_le_mul_of_nonneg_left hQAn.le hcr)
              _ = δ := by
                dsimp [η]
                field_simp [hdenpos.ne']
          have hprod : |QA * QB - cq * cr * (LA ^ q * LB ^ r)| ≤
              δ * Real.log N ^ (q + r) := by
            have heq : QA * QB - cq * cr * (LA ^ q * LB ^ r) =
                ((QA / LA ^ q) * (QB / LB ^ r) - cq * cr) *
                  (LA ^ q * LB ^ r) := by
              field_simp [hLApos.ne', hLBpos.ne']
            rw [heq, abs_mul,
              abs_of_nonneg (mul_nonneg (pow_nonneg hLAnonneg q)
                (pow_nonneg hLBnonneg r))]
            exact mul_le_mul hnorm hlogprod
              (mul_nonneg (pow_nonneg hLAnonneg q) (pow_nonneg hLBnonneg r)) hδ.le
          rw [abs_div, abs_of_pos hdR]
          calc
            |QA * QB - cq * cr * (LA ^ q * LB ^ r)| / (d : ℝ) ≤
                δ * Real.log N ^ (q + r) * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hprod
                (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ _ := le_add_of_nonneg_right (by positivity)
        · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
            inv_natCast_le_scaled_of_argument_lt hKpos hNpos hb
              (le_max_right a b) hdpos (not_le.mp hyb)
          rw [abs_div, abs_of_pos hdR]
          calc
            |QA * QB - cq * cr * (LA ^ q * LB ^ r)| / (d : ℝ) ≤
                B * Real.log N ^ (q + r) * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hglobal
                (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv, mul_assoc] using this
            _ ≤ B * Real.log N ^ (q + r) * (K * (c : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ ≤ _ := le_add_of_nonneg_left (by positivity)
      · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) :=
          inv_natCast_le_scaled_of_argument_lt hKpos hNpos ha
            (le_max_left a b) hdpos (not_le.mp hya)
        rw [abs_div, abs_of_pos hdR]
        calc
          |QA * QB - cq * cr * (LA ^ q * LB ^ r)| / (d : ℝ) ≤
              B * Real.log N ^ (q + r) * (1 / (d : ℝ)) := by
            have := mul_le_mul_of_nonneg_right hglobal
              (by positivity : 0 ≤ 1 / (d : ℝ))
            simpa [div_eq_mul_inv, mul_assoc] using this
          _ ≤ B * Real.log N ^ (q + r) * (K * (c : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
    have habssum :
        |∑ d ∈ Finset.Icc 1 (N / c),
          (moebiusLogPowerKernelReal (q + 1)
                  ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1)
                  ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
              (d : ℝ)| ≤
          δ * Real.log N ^ (q + r) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (q + r) * K * (c : ℝ) := by
      calc
        |∑ d ∈ Finset.Icc 1 (N / c),
          (moebiusLogPowerKernelReal (q + 1)
                  ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                moebiusLogPowerKernelReal (r + 1)
                  ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
              cq * cr *
                (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                  Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
              (d : ℝ)| ≤
          ∑ d ∈ Finset.Icc 1 (N / c),
            |(moebiusLogPowerKernelReal (q + 1)
                    ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                  moebiusLogPowerKernelReal (r + 1)
                    ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
                cq * cr *
                  (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                    Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
                (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            (δ * Real.log N ^ (q + r) * (1 / (d : ℝ)) +
              B * Real.log N ^ (q + r) * (K * (c : ℝ) / (N : ℝ))) :=
          Finset.sum_le_sum hterm
        _ ≤ δ * Real.log N ^ (q + r) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (q + r) * K * (c : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            sum_Icc_one_div_eq_harmonic]
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [Nat.add_sub_cancel]
          have hqle : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.div_le_self N c
          have htailnonneg :
              0 ≤ B * Real.log N ^ (q + r) *
                (K * (c : ℝ) / (N : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hqle htailnonneg
          have heq : (N : ℝ) *
              (B * Real.log N ^ (q + r) * (K * (c : ℝ) / (N : ℝ))) =
              B * Real.log N ^ (q + r) * K * (c : ℝ) := by
            field_simp [hNR.ne']
          nlinarith
    rw [Real.dist_eq, sub_zero, abs_div,
      abs_of_pos (pow_pos hlogpos (q + r + 1))]
    calc
      |∑ d ∈ Finset.Icc 1 (N / c),
        (moebiusLogPowerKernelReal (q + 1)
                ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              moebiusLogPowerKernelReal (r + 1)
                ((N : ℝ) / ((b * d : ℕ) : ℝ)) -
            cq * cr *
              (Real.log ((N : ℝ) / ((a * d : ℕ) : ℝ)) ^ q *
                Real.log ((N : ℝ) / ((b * d : ℕ) : ℝ)) ^ r)) /
            (d : ℝ)| / Real.log N ^ (q + r + 1) ≤
          (δ * Real.log N ^ (q + r) * (harmonic (N / c) : ℝ) +
            B * Real.log N ^ (q + r) * K * (c : ℝ)) /
              Real.log N ^ (q + r + 1) :=
        div_le_div_of_nonneg_right habssum
          (pow_pos hlogpos (q + r + 1)).le
      _ = δ * ((harmonic (N / c) : ℝ) / Real.log N) +
          B * K * (c : ℝ) / Real.log N := by
        rw [show q + r + 1 = (q + r) + 1 by omega, pow_succ]
        field_simp [hlogpos.ne']
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
  simpa only [cq, cr] using herr.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogne : Real.log N ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    rw [selbergPrincipalScaledLogPowerModel, selbergLogPowerHarmonicMain,
      show max a b = c by rfl]
    field_simp [hlogne]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring)

theorem selbergLogPowerHarmonicMain_zero_three_eq_oneFour
    (a b N : ℕ) :
    selbergLogPowerHarmonicMain 0 3 a b N =
      selbergOneFourHarmonicMain b (max a b) N := by
  rw [selbergLogPowerHarmonicMain, selbergOneFourHarmonicMain]
  apply Finset.sum_congr rfl
  intro d hd
  norm_num

theorem selbergLogPowerHarmonicMain_one_two_eq_twoThree
    (a b N : ℕ) :
    selbergLogPowerHarmonicMain 1 2 a b N =
      selbergTwoThreeHarmonicMain a b (max a b) N := by
  rw [selbergLogPowerHarmonicMain, selbergTwoThreeHarmonicMain]
  apply Finset.sum_congr rfl
  intro d hd
  norm_num
  ring

/-- Every fixed `(log, log⁴)` principal dilation has leading coefficient one. -/
theorem tendsto_selbergPrincipalScaledLogPowerModel_one_four_div_log_fourth_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergPrincipalScaledLogPowerModel 1 4 a b N / Real.log N ^ 4)
      atTop (𝓝 1) := by
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have herr :=
    tendsto_selbergPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero
      0 3 ha hb
  norm_num at herr
  have hmain := tendsto_selbergOneFourHarmonicMain_div_log_fourth_one hb hc
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergLogPowerHarmonicMain_zero_three_eq_oneFour,
    show max a b = c by rfl]
  field_simp [hlogne]
  ring

/-- Every fixed `(log², log³)` principal dilation has leading coefficient `3/2`. -/
theorem tendsto_selbergPrincipalScaledLogPowerModel_two_three_div_log_fourth_three_halves
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergPrincipalScaledLogPowerModel 2 3 a b N / Real.log N ^ 4)
      atTop (𝓝 (3 / 2 : ℝ)) := by
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have herr :=
    tendsto_selbergPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero
      1 2 ha hb
  norm_num at herr
  have hmain :=
    tendsto_selbergTwoThreeHarmonicMain_div_log_fourth_three_halves ha hb hc
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergLogPowerHarmonicMain_one_two_eq_twoThree,
    show max a b = c by rfl]
  field_simp [hlogne]
  ring

end

end RHTower.Sieve
