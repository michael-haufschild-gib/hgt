import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCoefficientIdentity
import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalHarmonicModel
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalLowerAsymptotic

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

theorem coprimeLogMoebius_one_nat_ratio (N q : ℕ) (hq : 0 < q) :
    coprimeLogMoebius 1 ((N : ℝ) / (q : ℝ)) =
      ∑ u ∈ Finset.Icc 1 (N / q),
        selbergMoebiusReciprocalCoeff u *
          Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) := by
  rw [coprimeLogMoebius, Nat.floor_div_natCast, Nat.floor_natCast]
  rw [Finset.filter_true_of_mem (fun u _ => Nat.coprime_one_left u)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [selbergMoebiusReciprocalCoeff]
  congr 1
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
  push_cast
  field_simp [hqR, huR]

/-- Principal rectangular model after fixed dilation in both variables. -/
def selbergPrincipalScaledModel (a b N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (N / max a b),
    coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
      coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
        (d : ℝ)

/-- A double sum against the diagonal reciprocal coefficient collapses to its common diagonal. -/
theorem selbergDiagonalReciprocalCoeff_double_sum_eq {X Y : ℕ} (h k : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
      selbergDiagonalReciprocalCoeff d e * (h d * k e)) =
      ∑ d ∈ Finset.Icc 1 (min X Y), (1 / (d : ℝ)) * (h d * k d) := by
  have hinner : ∀ d ∈ Finset.Icc 1 X,
      (∑ e ∈ Finset.Icc 1 Y,
        selbergDiagonalReciprocalCoeff d e * (h d * k e)) =
      if d ∈ Finset.Icc 1 Y then (1 / (d : ℝ)) * (h d * k d) else 0 := by
    intro d hd
    by_cases hdY : d ∈ Finset.Icc 1 Y
    · rw [if_pos hdY, Finset.sum_eq_single_of_mem d hdY]
      · rw [selbergDiagonalReciprocalCoeff, if_pos rfl,
          reciprocalNatArithmetic_apply (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)]
      · intro e he hed
        rw [selbergDiagonalReciprocalCoeff, if_neg (Ne.symm hed), zero_mul]
    · rw [if_neg hdY]
      apply Finset.sum_eq_zero
      intro e he
      rw [selbergDiagonalReciprocalCoeff]
      split_ifs with hde
      · subst e
        exact (hdY he).elim
      · ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The common truncation of two positive dilations is division by their maximum. -/
theorem min_natDiv_eq_natDiv_max (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    min (N / a) (N / b) = N / max a b := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, min_eq_right (Nat.div_le_div_left hab ha)]
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba, min_eq_left (Nat.div_le_div_left hba hb)]

theorem selbergPrincipalCoeff_weighted_eq_scaledModel
    (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
      selbergPrincipalCoeff r s *
        (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) *
          Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)))) =
      selbergPrincipalScaledModel a b N := by
  rw [selbergPrincipalCoeff,
    sum_Icc_bivariateDirichletConvolution_mul]
  have hinner : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)))) =
        coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
          coprimeLogMoebius 1 ((N : ℝ) / ((b * e : ℕ) : ℝ)) := by
    intro d hd e he
    calc
      (∑ r ∈ Finset.Icc 1 (N / a / d),
        ∑ s ∈ Finset.Icc 1 (N / b / e),
          selbergMoebiusReciprocalPair r s *
            (Real.log ((N : ℝ) / ((a * (d * r) : ℕ) : ℝ)) *
              Real.log ((N : ℝ) / ((b * (e * s) : ℕ) : ℝ)))) =
          (∑ r ∈ Finset.Icc 1 (N / a / d),
            selbergMoebiusReciprocalCoeff r *
              Real.log ((N : ℝ) / (((a * d) * r : ℕ) : ℝ))) *
          (∑ s ∈ Finset.Icc 1 (N / b / e),
            selbergMoebiusReciprocalCoeff s *
              Real.log ((N : ℝ) / (((b * e) * s : ℕ) : ℝ))) := by
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
          ← coprimeLogMoebius_one_nat_ratio N (b * e) (Nat.mul_pos hb
            (Finset.mem_Icc.mp he).1)]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl
    (fun e he => by rw [hinner d hd e he]))]
  rw [selbergDiagonalReciprocalCoeff_double_sum_eq]
  rw [min_natDiv_eq_natDiv_max N a b ha hb]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Every fixed rectangular dilation of the principal kernel has residue one. -/
theorem tendsto_selbergPrincipalScaledModel_div_log_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ => selbergPrincipalScaledModel a b N / Real.log N)
      atTop (𝓝 1) := by
  let C : ℝ := 6 + |Real.eulerMascheroniConstant|
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg Real.eulerMascheroniConstant]
  let c : ℕ := max a b
  have hc : 0 < c := lt_of_lt_of_le ha (le_max_left a b)
  have hratio := RHTower.tendsto_harmonic_natDiv_div_log (d := c) hc
  have herr : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 (N / c),
        (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
          (d : ℝ)) / Real.log N) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 8
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let η : ℝ := δ / (C + 1)
    have hη : 0 < η := by dsimp [η]; positivity
    have hnear : ∀ᶠ Y : ℝ in atTop,
        |coprimeLogMoebius 1 Y - 1| < η := by
      have hlim := tendsto_coprimeLogMoebius_one
      exact hlim.eventually (Metric.ball_mem_nhds 1 hη)
    rw [eventually_atTop] at hnear
    obtain ⟨K₀, hK₀⟩ := hnear
    let K : ℝ := max K₀ 1
    have hK₀K : K₀ ≤ K := le_max_left _ _
    have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hfull : ∀ᶠ N : ℕ in atTop,
        dist ((harmonic (N / c) : ℝ) / Real.log N) 1 < 1 :=
      hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
    rw [eventually_atTop] at hfull
    obtain ⟨Nfull, hNfull⟩ := hfull
    let B : ℝ := C ^ 2 + 1
    have hB : 0 ≤ B := by dsimp [B]; positivity
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
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
    have hratioTwo : (harmonic (N / c) : ℝ) / Real.log N < 2 := by
      have hfullN := hNfull N hNfull'
      rw [Real.dist_eq] at hfullN
      have hself : (harmonic (N / c) : ℝ) / Real.log N - 1 ≤
          |(harmonic (N / c) : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    have hterm : ∀ d ∈ Finset.Icc 1 (N / c),
        |(coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
            (d : ℝ)| ≤
          δ * (1 / (d : ℝ)) + B * (K * (c : ℝ) / (N : ℝ)) := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      let A : ℝ := coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ))
      let D : ℝ := coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ))
      have hA : |A| ≤ C := abs_coprimeLogMoebius_one_le _
      have hD : |D| ≤ C := abs_coprimeLogMoebius_one_le _
      have hglobal : |A * D - 1| ≤ B := by
        calc
          |A * D - 1| ≤ |A * D| + |(1 : ℝ)| := abs_sub (A * D) 1
          _ = |A| * |D| + 1 := by rw [abs_mul, abs_one]
          _ ≤ C * C + 1 := by nlinarith [abs_nonneg A, abs_nonneg D]
          _ = B := by dsimp [B]; ring
      by_cases hqa : K ≤ (N : ℝ) / ((a * d : ℕ) : ℝ)
      · by_cases hqb : K ≤ (N : ℝ) / ((b * d : ℕ) : ℝ)
        · have hAn : |A - 1| < η := hK₀ _ (hK₀K.trans hqa)
          have hDn : |D - 1| < η := hK₀ _ (hK₀K.trans hqb)
          have hprod : |A * D - 1| ≤ δ := by
            calc
              |A * D - 1| = |A * (D - 1) + (A - 1)| := by congr 1; ring
              _ ≤ |A| * |D - 1| + |A - 1| := by
                simpa [abs_mul] using abs_add_le (A * (D - 1)) (A - 1)
              _ ≤ C * η + η := by
                nlinarith [abs_nonneg A, abs_nonneg (D - 1), abs_nonneg (A - 1)]
              _ = δ := by dsimp [η]; field_simp
          rw [abs_div, abs_of_pos hdR]
          have := div_le_div_of_nonneg_right hprod (le_of_lt hdR)
          calc
            |A * D - 1| / (d : ℝ) ≤ δ / (d : ℝ) := this
            _ = δ * (1 / (d : ℝ)) := by ring
            _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hB (by positivity))
        · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
            have hbd : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_right a b
            have hlt : (N : ℝ) < K * (b : ℝ) * (d : ℝ) := by
              have habd : (0 : ℝ) < ((b * d : ℕ) : ℝ) := by positivity
              have := (not_le.mp hqb)
              rw [div_lt_iff₀ habd] at this
              push_cast at this
              nlinarith
            apply (le_div_iff₀ hNR).2
            rw [one_div, inv_mul_eq_div]
            apply (div_le_iff₀ hdR).2
            exact hlt.le.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbd hKpos.le) hdR.le)
          rw [abs_div, abs_of_pos hdR]
          calc
            |A * D - 1| / (d : ℝ) ≤ B * (1 / (d : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
              simpa [div_eq_mul_inv] using this
            _ ≤ B * (K * (c : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hfrac hB
            _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδ.le (by positivity))
      · have hfrac : 1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
          have had : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast le_max_left a b
          have hlt : (N : ℝ) < K * (a : ℝ) * (d : ℝ) := by
            have haad : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by positivity
            have := (not_le.mp hqa)
            rw [div_lt_iff₀ haad] at this
            push_cast at this
            nlinarith
          apply (le_div_iff₀ hNR).2
          rw [one_div, inv_mul_eq_div]
          apply (div_le_iff₀ hdR).2
          exact hlt.le.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left had hKpos.le) hdR.le)
        rw [abs_div, abs_of_pos hdR]
        calc
          |A * D - 1| / (d : ℝ) ≤ B * (1 / (d : ℝ)) := by
            have := mul_le_mul_of_nonneg_right hglobal (by positivity : 0 ≤ 1 / (d : ℝ))
            simpa [div_eq_mul_inv] using this
          _ ≤ B * (K * (c : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hfrac hB
          _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδ.le (by positivity))
    have habssum :
        |∑ d ∈ Finset.Icc 1 (N / c),
          (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
            (d : ℝ)| ≤
          δ * (harmonic (N / c) : ℝ) + B * K * (c : ℝ) := by
      calc
        |∑ d ∈ Finset.Icc 1 (N / c),
          (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
              coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
            (d : ℝ)| ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            |(coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
              (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / c),
            (δ * (1 / (d : ℝ)) + B * (K * (c : ℝ) / (N : ℝ))) :=
          Finset.sum_le_sum hterm
        _ ≤ δ * (harmonic (N / c) : ℝ) + B * K * (c : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            sum_Icc_one_div_eq_harmonic]
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp only [Nat.add_sub_cancel]
          have hqle : ((N / c : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast Nat.div_le_self N c
          have htailnonneg : 0 ≤ B * (K * (c : ℝ) / (N : ℝ)) := by positivity
          have hmul := mul_le_mul_of_nonneg_right hqle htailnonneg
          have heq : (N : ℝ) * (B * (K * (c : ℝ) / (N : ℝ))) =
              B * K * (c : ℝ) := by
            field_simp [hNR.ne']
          nlinarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlogpos]
    calc
      |∑ d ∈ Finset.Icc 1 (N / c),
        (coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) - 1) /
          (d : ℝ)| / Real.log N ≤
          (δ * (harmonic (N / c) : ℝ) + B * K * (c : ℝ)) /
            Real.log N := div_le_div_of_nonneg_right habssum hlogpos.le
      _ = δ * ((harmonic (N / c) : ℝ) / Real.log N) +
          B * K * (c : ℝ) / Real.log N := by ring
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
  have hmain : Tendsto (fun N : ℕ =>
      (harmonic (N / c) : ℝ) / Real.log N) atTop (𝓝 1) := hratio
  have hadd := herr.add hmain
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [selbergPrincipalScaledModel, show max a b = c by rfl,
    ← sum_Icc_one_div_eq_harmonic]
  field_simp [hlogne]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Correction-weighted principal model, zero-extended off the positive truncation square. -/
def selbergCorrectionScaledTerm (N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergPrincipalScaledModel mn.1 mn.2 N / Real.log N)
  else 0

theorem tendsto_selbergCorrectionScaledTerm (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionScaledTerm N mn) atTop
      (𝓝 (selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨a, b⟩
  rcases a.eq_zero_or_pos with rfl | ha
  · simp [selbergCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  rcases b.eq_zero_or_pos with rfl | hb
  · simp [selbergCorrectionScaledTerm, selbergEulerCorrectionCoeff]
  have hmain := (tendsto_selbergPrincipalScaledModel_div_log_one ha hb).const_mul
    (selbergEulerCorrectionCoeff a b)
  simpa only [mul_one] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (max a b)] with N hN
    rw [selbergCorrectionScaledTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left a b).trans hN⟩,
      Finset.mem_Icc.mpr ⟨hb, (le_max_right a b).trans hN⟩⟩)

theorem eventually_norm_selbergCorrectionScaledTerm_le :
    ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
      ‖selbergCorrectionScaledTerm N mn‖ ≤
        2 * (6 + |Real.eulerMascheroniConstant|) ^ 2 *
          |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  let C : ℝ := 6 + |Real.eulerMascheroniConstant|
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [abs_nonneg Real.eulerMascheroniConstant]
  have hratio := GaloisForLFunctions.tendsto_harmonic_div_log
  have hnear : ∀ᶠ N : ℕ in atTop,
      dist ((harmonic N : ℝ) / Real.log N) 1 < 1 :=
    hratio.eventually (Metric.ball_mem_nhds 1 zero_lt_one)
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnearN hN mn
  rcases mn with ⟨a, b⟩
  rw [selbergCorrectionScaledTerm]
  split_ifs with hab
  · obtain ⟨ha, hb⟩ := hab
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hharmonic : (0 : ℝ) ≤ (harmonic N : ℝ) := by
      simpa using RHTower.harmonic_cast_mono (m := 0) (n := N) (Nat.zero_le N)
    have hratioNonneg : 0 ≤ (harmonic N : ℝ) / Real.log N := by positivity
    have hratioTwo : (harmonic N : ℝ) / Real.log N < 2 := by
      rw [Real.dist_eq] at hnearN
      have hself : (harmonic N : ℝ) / Real.log N - 1 ≤
          |(harmonic N : ℝ) / Real.log N - 1| := le_abs_self _
      linarith
    have hmodel : |selbergPrincipalScaledModel a b N| ≤
        C ^ 2 * (harmonic N : ℝ) := by
      rw [selbergPrincipalScaledModel]
      calc
        |∑ d ∈ Finset.Icc 1 (N / max a b),
          coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
            coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
              (d : ℝ)| ≤
            ∑ d ∈ Finset.Icc 1 (N / max a b),
              |coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ)) *
                coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ)) /
                  (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N / max a b), C ^ 2 * (1 / (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdR : (0 : ℝ) < (d : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hd).1
          rw [abs_div, abs_mul, abs_of_pos hdR]
          have hA := abs_coprimeLogMoebius_one_le
            ((N : ℝ) / ((a * d : ℕ) : ℝ))
          have hB := abs_coprimeLogMoebius_one_le
            ((N : ℝ) / ((b * d : ℕ) : ℝ))
          change |coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ))| ≤ C at hA
          change |coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ))| ≤ C at hB
          change _ ≤ C ^ 2 * (1 / (d : ℝ))
          have hprod :
              |coprimeLogMoebius 1 ((N : ℝ) / ((a * d : ℕ) : ℝ))| *
                |coprimeLogMoebius 1 ((N : ℝ) / ((b * d : ℕ) : ℝ))| ≤ C ^ 2 := by
            have hp := mul_le_mul hA hB
              (abs_nonneg (coprimeLogMoebius 1
                ((N : ℝ) / ((b * d : ℕ) : ℝ)))) hC
            simpa [pow_two] using hp
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hprod (by positivity : 0 ≤ 1 / (d : ℝ))
        _ = C ^ 2 * (harmonic (N / max a b) : ℝ) := by
          rw [← Finset.mul_sum, sum_Icc_one_div_eq_harmonic]
        _ ≤ C ^ 2 * (harmonic N : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (RHTower.harmonic_cast_mono (Nat.div_le_self N (max a b))) (sq_nonneg C)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hlogpos]
    have hscaled : |selbergPrincipalScaledModel a b N| / Real.log N ≤
        2 * C ^ 2 := by
      calc
        |selbergPrincipalScaledModel a b N| / Real.log N ≤
            C ^ 2 * (harmonic N : ℝ) / Real.log N :=
          div_le_div_of_nonneg_right hmodel hlogpos.le
        _ = C ^ 2 * ((harmonic N : ℝ) / Real.log N) := by ring
        _ ≤ 2 * C ^ 2 := by nlinarith [sq_nonneg C]
    dsimp [C] at hscaled ⊢
    simpa [mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hscaled
        (abs_nonneg (selbergEulerCorrectionCoeff a b))
  · simp
    positivity

theorem tsum_selbergCorrectionScaledTerm (N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergCorrectionScaledTerm N mn) =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (selbergPrincipalScaledModel a b N / Real.log N) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp [selbergCorrectionScaledTerm, ha, hb]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergCorrectionScaledTerm, if_neg hmn]

theorem tendsto_tsum_selbergCorrectionScaledTerm_one :
    Tendsto (fun N : ℕ => ∑' mn : ℕ × ℕ,
      selbergCorrectionScaledTerm N mn) atTop (𝓝 1) := by
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      2 * (6 + |Real.eulerMascheroniConstant|) ^ 2 *
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left _
  have hdom := tendsto_tsum_of_dominated_convergence hsumAbs
    tendsto_selbergCorrectionScaledTerm
    eventually_norm_selbergCorrectionScaledTerm_le
  rw [tsum_selbergEulerCorrectionCoeff] at hdom
  exact hdom

/-- Original Möbius/gcd logarithmic quadratic form. -/
def selbergOriginalLogQuadratic (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalCoeff m n *
      (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)))

theorem selbergOriginalLogQuadratic_eq_correction_scaled (N : ℕ) :
    selbergOriginalLogQuadratic N =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b * selbergPrincipalScaledModel a b N := by
  rw [selbergOriginalLogQuadratic]
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      selbergOriginalCoeff m n *
        (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ)))) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergPrincipalCoeff m n *
            (Real.log ((N : ℝ) / (m : ℝ)) * Real.log ((N : ℝ) / (n : ℝ))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [selbergEulerCorrection_convolution_principal]
    _ = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        selbergEulerCorrectionCoeff a b *
          (∑ r ∈ Finset.Icc 1 (N / a), ∑ s ∈ Finset.Icc 1 (N / b),
            selbergPrincipalCoeff r s *
              (Real.log ((N : ℝ) / ((a * r : ℕ) : ℝ)) *
                Real.log ((N : ℝ) / ((b * s : ℕ) : ℝ)))) :=
      sum_Icc_bivariateDirichletConvolution_mul _ _ _ N N
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [selbergPrincipalCoeff_weighted_eq_scaledModel a b N
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1]

theorem selbergOriginalLogQuadratic_div_log_eq_tsum
    {N : ℕ} (hN : 2 ≤ N) :
    selbergOriginalLogQuadratic N / Real.log N =
      ∑' mn : ℕ × ℕ, selbergCorrectionScaledTerm N mn := by
  rw [tsum_selbergCorrectionScaledTerm,
    selbergOriginalLogQuadratic_eq_correction_scaled]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp [hlog]

theorem tendsto_selbergOriginalLogQuadratic_div_log_one :
    Tendsto (fun N : ℕ => selbergOriginalLogQuadratic N / Real.log N)
      atTop (𝓝 1) := by
  refine tendsto_tsum_selbergCorrectionScaledTerm_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (selbergOriginalLogQuadratic_div_log_eq_tsum hN).symm

theorem barbanVehovSelbergDiagonal_eq_originalLogQuadratic (N : ℕ) :
    barbanVehovSelbergDiagonal N = selbergOriginalLogQuadratic N := by
  let S := Finset.Icc 1 N
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hbi : S.biUnion Nat.divisors = S := by
    ext e
    constructor
    · intro he
      obtain ⟨m, hm, hem⟩ := Finset.mem_biUnion.mp he
      obtain ⟨hedvd, hm0⟩ := Nat.mem_divisors.mp hem
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd (hSpos m hm)
      have hemle : e ≤ m := Nat.le_of_dvd (hSpos m hm) hedvd
      exact Finset.mem_Icc.mpr ⟨hepos, hemle.trans (Finset.mem_Icc.mp hm).2⟩
    · intro he
      exact Finset.mem_biUnion.mpr ⟨e, he,
        Nat.mem_divisors.mpr ⟨dvd_rfl, (Nat.ne_of_gt (Finset.mem_Icc.mp he).1)⟩⟩
  calc
    barbanVehovSelbergDiagonal N =
        ∑ e ∈ S.biUnion Nat.divisors, (Nat.totient e : ℝ) *
          (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2 := by
      rw [barbanVehovSelbergDiagonal]
      change (∑ e ∈ S, (Nat.totient e : ℝ) *
        (∑ m ∈ S.filter (fun m => e ∣ m), barbanVehovWeight N m / (m : ℝ)) ^ 2) = _
      rw [hbi]
    _ = ∑ p ∈ S ×ˢ S,
        barbanVehovWeight N p.1 * barbanVehovWeight N p.2 /
          (Nat.lcm p.1 p.2 : ℝ) :=
      (sum_div_lcm_eq_totient_diagonal S hSpos (barbanVehovWeight N)).symm
    _ = selbergOriginalLogQuadratic N := by
      rw [Finset.sum_product, selbergOriginalLogQuadratic]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [barbanVehovWeight, if_pos (Finset.mem_Icc.mp hm).2,
        barbanVehovWeight, if_pos (Finset.mem_Icc.mp hn).2,
        selbergOriginalCoeff]
      have hmR : (m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      have hlcm : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero
        (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      have hlcmR : (Nat.lcm m n : ℝ) ≠ 0 := by exact_mod_cast hlcm
      have hgcdlcm : (Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ) =
          (m : ℝ) * (n : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm m n
      push_cast
      field_simp [hmR, hnR, hlcmR]
      calc
        (((μ m : ℤ) : ℝ) * (m : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
            ((μ n : ℤ) : ℝ) * (n : ℝ) * Real.log ((N : ℝ) / (n : ℝ))) =
            (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
              ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ))) *
                ((m : ℝ) * (n : ℝ)) := by ring
        _ = (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
              ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ))) *
                ((Nat.gcd m n : ℝ) * (Nat.lcm m n : ℝ)) := by rw [hgcdlcm]
        _ = (((μ m : ℤ) : ℝ) * Real.log ((N : ℝ) / (m : ℝ)) *
              ((μ n : ℤ) : ℝ) * Real.log ((N : ℝ) / (n : ℝ))) *
                (Nat.lcm m n : ℝ) * (Nat.gcd m n : ℝ) := by ring

/-- Matching sharp upper half of Graham's Selberg diagonal. -/
theorem tendsto_barbanVehovSelbergDiagonal_div_log_one :
    Tendsto (fun N : ℕ => barbanVehovSelbergDiagonal N / Real.log N)
      atTop (𝓝 1) := by
  simpa only [barbanVehovSelbergDiagonal_eq_originalLogQuadratic] using
    tendsto_selbergOriginalLogQuadratic_div_log_one

end

end RHTower.Sieve
