/-
# The Levinson mollified budget on any abscissa `1/4 ≤ σ₀ < 2`

The corpus budget `exists_levinson_mollified_budget_le` is stated for `σ₀ < 1/2`; its proof only
uses `σ₀ < 15/2`. This is the same proof with the hypothesis widened, for right-shifted lines.
-/
import GaloisForLFunctions.RHTower.MollifiedDetectorFarRightEdge
import GaloisForLFunctions.RHTower.LevinsonWeightedHorizontalEdge
import GaloisForLFunctions.RHTower.EntireDirichletPolynomialHorizontalEdge
import GaloisForLFunctions.RHTower.LevinsonLeftEdgeJensen
import GaloisForLFunctions.RHTower.LevinsonMollifiedEdges
import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

theorem exists_levinson_mollified_budget_le_wide :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite →
        (∃ t ∈ Set.Ioo T₁ T₂,
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
        weightedLittlewoodBoundary
            (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)) σ₀ (15 / 2) T₁ T₂
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨KG, hKG, hGhoriz⟩ := exists_horizontal_weighted_levinsonG_bound
  set α : ℝ := Real.log 2 with hα
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 22 * Real.exp (-α * (15 / 2)) / α) with hCfar
  set Cfar' : ℝ := 2 * ((2 * 22 * Real.exp α) * Real.exp (-α * (15 / 2)) / α) with hCfar'
  have hCfar0 : 0 < Cfar := by rw [hCfar]; positivity
  have hCfar'0 : 0 < Cfar' := by rw [hCfar']; positivity
  set Kpsi : ℝ := 2 * (15 / 2 : ℝ) * Real.pi / Real.log (8 / (15 / 4 : ℝ)) with hKpsi
  have hlog2pos : 0 < Real.log (8 / (15 / 4 : ℝ)) := Real.log_pos (by norm_num)
  have hKpsi0 : 0 < Kpsi := by rw [hKpsi]; positivity
  refine ⟨Cfar + (15 / 2) * Cfar' + 2 * (2 * (15 / 2 : ℝ) *
      ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) + 1,
    2 * KG + 2 * Kpsi + 1, by positivity, by positivity, ?_⟩
  intro lam hlam b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hfin hex hMsq
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hlamC : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  have hT2 : (20 : ℝ) ≤ T₂ := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hne1' : ∀ (c t : ℝ), 20 ≤ t → ((c : ℂ) + (t : ℂ) * I) ≠ 1 := hne1
  -- ## the left edge
  have hleft : (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) := by
    have hana : ∀ t ∈ uIcc T₁ T₂,
        AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((σ₀ : ℂ) + (t : ℂ) * I) := by
      intro t ht
      rw [huIcct] at ht
      exact analyticAt_levinsonMollifiedDetector _ b hs (hne1' σ₀ t (by linarith [ht.1]))
    have hJ := integral_log_norm_le_of_meanSquare hT hana hfin hex hMsq
    linarith
  -- ## the far-right edges
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re →
      AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) z := by
    intro z hz
    refine analyticAt_levinsonMollifiedDetector _ b hs ?_
    intro hEq
    rw [hEq, Complex.one_re] at hz
    linarith
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖
        ≤ 22 * Real.exp (-α * z.re) := fun z hz =>
    norm_levinsonMollifiedDetector_sub_one_le_exp hlamC b hs h1 hb1 hbn (le_of_lt hz)
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖ ≤ 1 / 2 := fun z hz =>
    norm_levinsonMollifiedDetector_sub_one_le_half hlamC b hs h1 hb1 hbn (le_of_lt hz)
  have hfarlog : |∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  -- ## the horizontal edges
  have hhoriz : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), edPoly b s ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
          (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
            ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ KG * Real.log T + (Kpsi * Real.log Mb
            + 2 * (15 / 2 : ℝ) *
              ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) := by
    intro T hT20 hGne hPne
    have hGana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      analyticAt_levinsonG _ (hne1 x T hT20)
    have hPana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (edPoly b s) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      (analyticOnNhd_edPoly b hs) _ (Set.mem_univ _)
    have hGi : IntervalIntegrable
        (fun x : ℝ => (x - σ₀) *
          (logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im)
        volume σ₀ (15 / 2 : ℝ) :=
      (continuousOn_weighted_im_logDeriv_horizontal hGana
        (fun x hx => hGne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hPi : IntervalIntegrable
        (fun x : ℝ => (x - σ₀) * (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im)
        volume σ₀ (15 / 2 : ℝ) :=
      (continuousOn_weighted_im_logDeriv_horizontal hPana
        (fun x hx => hPne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hsplit : (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)).im)
        = (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im)
          + ∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im := by
      rw [← intervalIntegral.integral_add hGi hPi]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [huIccx] at hx
      have hld : logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)
          = logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)
            + logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I) :=
        logDeriv_mul _ (hGne x hx) (hPne x hx)
          (analyticAt_levinsonG _ (hne1 x T hT20)).differentiableAt
          (differentiable_edPoly b hs _)
      rw [hld, Complex.add_im]
      ring
    rw [hsplit]
    have hGbound := hGhoriz lam hlam T (by linarith) σ₀ (15 / 2 : ℝ) hσ₀ hσ₀15 le_rfl hGne
    have hPbound := abs_integral_weighted_im_logDeriv_edPoly_le b hs hbreal T
      (c := σ₀) (e := (15 / 2 : ℝ)) (r := (15 / 4 : ℝ)) (m := (5 / 16 : ℝ)) (Mb := Mb)
      hσ₀15 (by norm_num) (by norm_num) (by linarith) (by norm_num) hPne (by norm_num) hMb1
      (norm_edPolyTrace_centre_ge b hs h1 hb1 hbn hbreal T) hmass
    have hlogsplit : Real.log (Mb / (5 / 16 : ℝ)) = Real.log Mb + Real.log (16 / 5 : ℝ) := by
      rw [Real.log_div (by linarith) (by norm_num)]
      rw [show (16 / 5 : ℝ) = ((5 / 16 : ℝ))⁻¹ by norm_num, Real.log_inv]
      ring
    rw [hlogsplit] at hPbound
    have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
    have hwidth : (15 / 2 : ℝ) - σ₀ ≤ 15 / 2 := by linarith
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hPfinal : |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ Kpsi * Real.log Mb
          + 2 * (15 / 2 : ℝ) *
            ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi) := by
      refine le_trans hPbound ?_
      have hlog165 : (0 : ℝ) ≤ Real.log (16 / 5 : ℝ) := Real.log_nonneg (by norm_num)
      have hq : (0 : ℝ) ≤ (Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) := div_nonneg (by linarith) hlog2pos.le
      have hnn : (0 : ℝ) ≤ ((Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi :=
        mul_nonneg (by linarith) Real.pi_pos.le
      have hexpand : 2 * ((15 / 2 : ℝ) - σ₀) *
          (((Real.log Mb + Real.log (16 / 5 : ℝ)) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)
          ≤ 2 * (15 / 2 : ℝ) *
            (((Real.log Mb + Real.log (16 / 5 : ℝ)) / Real.log (8 / (15 / 4 : ℝ)) + 1)
              * Real.pi) := mul_le_mul_of_nonneg_right (by linarith) hnn
      refine le_trans hexpand ?_
      rw [hKpsi]
      have hdiv : (Real.log Mb + Real.log (16 / 5 : ℝ)) / Real.log (8 / (15 / 4 : ℝ))
          = Real.log Mb / Real.log (8 / (15 / 4 : ℝ))
            + Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) := by ring
      rw [hdiv]
      have hval : 2 * (15 / 2 : ℝ) *
          ((Real.log Mb / Real.log (8 / (15 / 4 : ℝ))
            + Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)
          = (2 * (15 / 2 : ℝ) * Real.pi / Real.log (8 / (15 / 4 : ℝ))) * Real.log Mb
            + 2 * (15 / 2 : ℝ) *
              ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi) := by
        field_simp
        ring
      rw [hval]
    refine le_trans (abs_add_le _ _) ?_
    linarith [hGbound, hPfinal]
  have hH1 := hhoriz T₁ h20 hG1 hP1
  have hH2 := hhoriz T₂ (by linarith) hG2 hP2
  -- ## assembly
  have hlogT1 : Real.log T₁ ≤ Real.log T₂ :=
    Real.log_le_log (by linarith) hT.le
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  have hσ₀pos : (0 : ℝ) < 15 / 2 - σ₀ := by linarith
  unfold weightedLittlewoodBoundary
  have hR : ((15 / 2 : ℝ) - σ₀) * (∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) ≤ (15 / 2 : ℝ) * Cfar' := by
    have habs := le_abs_self (∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
    have hstep1 : ((15 / 2 : ℝ) - σ₀) * (∫ t in T₁..T₂,
        (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
        ≤ ((15 / 2 : ℝ) - σ₀) * Cfar' :=
      mul_le_mul_of_nonneg_left (le_trans habs hfarld) hσ₀pos.le
    have hstep2 : ((15 / 2 : ℝ) - σ₀) * Cfar' ≤ (15 / 2 : ℝ) * Cfar' :=
      mul_le_mul_of_nonneg_right (by linarith) hCfar'0.le
    linarith
  have hL1 : -(∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Cfar := by
    have habs := neg_abs_le (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
    linarith [hfarlog, habs]
  have hHa := le_abs_self (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
      ((x : ℂ) + (T₁ : ℂ) * I)).im)
  have hHb := neg_abs_le (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
      ((x : ℂ) + (T₂ : ℂ) * I)).im)
  have hKbound : KG * Real.log T₁ + KG * Real.log T₂ + 2 * Kpsi * Real.log Mb
      ≤ (2 * KG + 2 * Kpsi + 1) * (Real.log T₂ + Real.log Mb) := by
    have hstep : KG * Real.log T₁ ≤ KG * Real.log T₂ :=
      mul_le_mul_of_nonneg_left hlogT1 hKG.le
    nlinarith [hlogT2, hlogMb, hKG.le, hKpsi0.le]
  linarith [hleft, hL1, hR, hH1, hH2, hHa, hHb, hKbound]


end RHTower
