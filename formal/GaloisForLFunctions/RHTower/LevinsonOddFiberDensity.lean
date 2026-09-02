import GaloisForLFunctions.RHTower.LevinsonOddFiberFinal
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge
import GaloisForLFunctions.RHTower.LevinsonDensityScale

/-!
# From Levinson's window count to a positive proportion

The window inequality bounds an *absolute* count on one window.  Turning it into a proportion needs
three asymptotic ingredients, all owned by the corpus: the Riemann–Siegel phase asymptotic
`θ(T) ~ ½ T log T`, the Riemann–von Mangoldt asymptotic `N(T) ~ (1/2π) T log T`, and monotonicity of
the odd-fibre census.  This file assembles them.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

noncomputable section

namespace RHTower

/-- The odd-fibre census is monotone. -/
theorem xiOddFiberCount_mono : Monotone xiOddFiberCount := by
  classical
  intro T U hTU
  refine Finset.card_le_card ?_
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  obtain ⟨hmem, hprop⟩ := hz
  refine ⟨?_, hprop⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_stripFinsetPos.mp hmem
  exact mem_stripFinsetPos.mpr ⟨h1, h2, h3, le_trans h4 hTU, h5⟩

/-- The Riemann–Siegel phase advance over a window anchored near `20` is `(½ − ε)·T log T`. -/
theorem eventually_phase_advance_ge (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ T₁ ∈ Set.Icc (20 : ℝ) 21,
      (1 / 2 - ε) * (T * Real.log T) ≤ gammaHardyTheta T - gammaHardyTheta T₁ := by
  obtain ⟨Cθ, hCθ⟩ : ∃ C : ℝ, ∀ t ∈ Set.Icc (20 : ℝ) 21, |gammaHardyTheta t| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (20 : ℝ)) (b := 21)).exists_bound_of_continuousOn
      (differentiable_gammaHardyTheta.continuous.continuousOn)
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg _) (hCθ 20 (by norm_num))
  have hmain : Tendsto (fun t : ℝ => (gammaHardyTheta t - gammaHardyThetaMain t) / t)
      atTop (nhds 0) := gammaHardyTheta_sub_main_div_tendsto_zero
  have habs : ∀ᶠ t in atTop, |(gammaHardyTheta t - gammaHardyThetaMain t) / t| < ε / 4 := by
    have hz := NormedAddGroup.tendsto_nhds_zero.mp hmain (ε / 4) (by linarith)
    simpa [Real.norm_eq_abs, abs_div] using hz
  filter_upwards [habs, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (Real.exp (4 * (Cθ + 1) / ε)),
    eventually_ge_atTop (Real.exp (4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε)),
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (3 : ℝ)]
    with T hTabs hT0 hTexp hTexp2 hT1 hT3 T₁ hT₁
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos hT1
  have hdiff : |gammaHardyTheta T - gammaHardyThetaMain T| ≤ (ε / 4) * T := by
    have h := le_of_lt hTabs
    rw [abs_div, abs_of_pos hT0] at h
    rw [div_le_iff₀ hT0] at h
    linarith [h]
  have hmainval : gammaHardyThetaMain T
      = T / 2 * Real.log (T / (2 * Real.pi)) - T / 2 := rfl
  have hlogsplit : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) := by
    rw [Real.log_div (ne_of_gt hT0) (by positivity)]
  have hlow : gammaHardyThetaMain T
      = (1 / 2) * (T * Real.log T) - T * (Real.log (2 * Real.pi) / 2 + 1 / 2) := by
    rw [hmainval, hlogsplit]
    ring
  have hlogge : 4 * (Cθ + 1) / ε ≤ Real.log T := by
    rw [← Real.log_exp (4 * (Cθ + 1) / ε)]
    exact Real.log_le_log (Real.exp_pos _) hTexp
  have hlogge2 : 4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε ≤ Real.log T := by
    rw [← Real.log_exp (4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε)]
    exact Real.log_le_log (Real.exp_pos _) hTexp2
  have hmul1 : 4 * (Cθ + 1) ≤ ε * Real.log T := by
    rw [div_le_iff₀ hε] at hlogge
    linarith
  have hmul2 : 4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) ≤ ε * Real.log T := by
    rw [div_le_iff₀ hε] at hlogge2
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTge : (1 : ℝ) ≤ T := by linarith
  have hTlog : Real.log T ≤ T * Real.log T := by nlinarith [hlogT, hTge]
  have hCbound : Cθ ≤ (ε / 4) * (T * Real.log T) := by
    have hstep : (ε / 4) * Real.log T ≤ (ε / 4) * (T * Real.log T) := by
      nlinarith [hTlog, hε]
    linarith [hmul1, hstep]
  have hlinbound : T * (Real.log (2 * Real.pi) / 2 + 1 / 2)
      ≤ (ε / 4) * (T * Real.log T) := by
    nlinarith [hmul2, hT0]
  have hTbound : (ε / 4) * T ≤ (ε / 4) * (T * Real.log T) := by
    nlinarith [hT0, hε, hlog1]
  have habs1 := abs_le.mp hdiff
  have hθ₁ := abs_le.mp (hCθ T₁ hT₁)
  linarith [habs1.1, hθ₁.2, hlow, hCbound, hlinbound, hTbound]


/-- **The Levinson mollified mean-square gate.**  For every `ε > 0` and every sufficiently large
`U` there is an admissible Levinson window `[T₁,T₂] ⊆ [20, U]` with `T₂` within `1` of `U`, and a
real mollifier of unit head and bounded coefficients, on which the mean square of `(ζ+λζ′)·Ψ` at
the Levinson abscissa `σ₀ = ½ − R/log T₂` is at most `(c+ε)·(T₂−T₁)`. -/
def LevinsonMeanSquareGate (R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (T₁ T₂ σ₀ lam Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    T₁ ∈ Set.Icc (20 : ℝ) 21 ∧ T₂ ∈ Set.Ioc (U - 1) U ∧
    lam < 0 ∧ |lam| ≤ 1 ∧
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log T₂ ∧
    1 / 4 ≤ σ₀ ∧ σ₀ < 1 / 2 ∧ (1 / 2 - σ₀) * Real.log T₂ = R ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∫ t in T₁..T₂, ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (c + ε) * (T₂ - T₁)

/-- Sign-correct Levinson gate.  The polar argument uses exactly nonvanishing of `lam` and
positivity of the detector weight on the selected window; it does not require a negative shift. -/
def LevinsonMeanSquareGateOfYPos (R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (T₁ T₂ σ₀ lam Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    T₁ ∈ Set.Icc (20 : ℝ) 21 ∧ T₂ ∈ Set.Ioc (U - 1) U ∧
    lam ≠ 0 ∧ |lam| ≤ 1 ∧
    (∀ u ∈ Set.Icc T₁ T₂, (0 : ℝ) < (levinsonY (lam : ℂ) (linePt u)).re) ∧
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log T₂ ∧
    1 / 4 ≤ σ₀ ∧ σ₀ < 1 / 2 ∧ (1 / 2 - σ₀) * Real.log T₂ = R ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∫ t in T₁..T₂, ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (c + ε) * (T₂ - T₁)

/-- The legacy negative-shift gate supplies the exact positive detector-weight interface. -/
theorem levinsonMeanSquareGateOfYPos_of_gate {R c : ℝ}
    (hgate : LevinsonMeanSquareGate R c) : LevinsonMeanSquareGateOfYPos R c := by
  intro ε hε
  filter_upwards [hgate ε hε] with U hU
  obtain ⟨T₁, T₂, σ₀, lam, Mb, b, N, hT₁, hT₂, hlam0, hlam1, hN, hb1, hbn,
    hbreal, hMb1, hmass, hlogMb, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
  refine ⟨T₁, T₂, σ₀, lam, Mb, b, N, hT₁, hT₂, ne_of_lt hlam0, hlam1, ?_, hN,
    hb1, hbn, hbreal, hMb1, hmass, hlogMb, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩
  intro u hu
  rw [levinsonY_line_eq, Complex.ofReal_re]
  have hdig := log_pi_lt_re_digamma_quarter (le_trans hT₁.1 hu.1)
  have hmul : lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
      + ((u / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hlam0.le (sub_nonneg.mpr hdig.le)
  linarith

/-- Monotonicity of `Real.log` on nonnegative arguments, with the junk value at `0` absorbed. -/
theorem log_le_log_of_nonneg_of_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0, Real.log_zero]
    exact Real.log_nonneg hy
  · exact Real.log_le_log hx0 hxy



private theorem levinson_coef_bound {δ η : ℝ} (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hη0 : 0 < η)
    (hηsmall : η ≤ 1 / 60) :
    Real.pi * ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) ≤ (1 / 3 + δ) / 2 + 5 * η := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : Real.pi * (1 / (2 * Real.pi) + η) = 1 / 2 + Real.pi * η := by
    rw [mul_add]
    congr 1
    field_simp
  have hexp : Real.pi * ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η))
      = ((1 / 3 + δ) * (1 + η)) * (1 / 2 + Real.pi * η) := by
    rw [← hpi2]; ring
  rw [hexp]
  have hA : (1 / 3 + δ : ℝ) ≤ 2 / 3 := by linarith
  have hA0 : (0 : ℝ) ≤ 1 / 3 + δ := by linarith
  have h1e : (1 : ℝ) + η ≤ 61 / 60 := by linarith
  have hP0 : (0 : ℝ) ≤ (1 / 3 + δ) * (1 + η) := by positivity
  have hP1 : (1 / 3 + δ) * (1 + η) ≤ (2 / 3) * (61 / 60 : ℝ) :=
    mul_le_mul hA h1e (by linarith) (by norm_num)
  have hPle : (1 / 3 + δ) * (1 + η) ≤ (1 / 3 + δ) + (2 / 3) * η := by nlinarith [hA, hη0]
  have hstep2 : Real.pi * η ≤ 4 * η := mul_le_mul_of_nonneg_right Real.pi_le_four hη0.le
  have hpe : (0 : ℝ) ≤ Real.pi * η := by positivity
  have hb2 : ((1 / 3 + δ) * (1 + η)) * (Real.pi * η)
      ≤ ((2 / 3) * (61 / 60 : ℝ)) * (4 * η) := mul_le_mul hP1 hstep2 hpe (by norm_num)
  have hsplit : ((1 / 3 + δ) * (1 + η)) * (1 / 2 + Real.pi * η)
      = ((1 / 3 + δ) * (1 + η)) / 2 + ((1 / 3 + δ) * (1 + η)) * (Real.pi * η) := by ring
  rw [hsplit]
  linarith [hPle, hb2, hη0]


private theorem levinson_budget_scalar {η R c C K T₁ T₂ Λ S LM LMb σ₀ : ℝ}
    (hη0 : 0 < η) (hR : 0 < R) (hlogc : 0 ≤ Real.log c)
    (hΛ0 : 0 < Λ) (hS : S = T₂ * Λ) (hT₁T₂ : T₁ < T₂) (hT₁0 : 0 < T₁)
    (hK : 0 < K) (hσ₀ : (1 / 2 - σ₀) * Λ = R) (hσ₀b : σ₀ < 1 / 2)
    (hLM : LM ≤ Real.log c + R * η) (hLMb : LMb ≤ 5 * Λ) (hlogT₂ : Real.log T₂ = Λ) :
    ((T₂ - T₁) / 2 * LM + C + K * (Real.log T₂ + LMb)) / (1 / 2 - σ₀)
      ≤ (S / (2 * R)) * Real.log c + (S / 2) * η + (C / R) * Λ + (6 * K / R) * Λ ^ 2 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hL0 : (0 : ℝ) < T₂ - T₁ := by linarith
  have hLT : T₂ - T₁ ≤ T₂ := by linarith
  have hwidthpos : (0 : ℝ) < 1 / 2 - σ₀ := by linarith
  have hinvR : (1 : ℝ) / (1 / 2 - σ₀) = Λ / R := by
    rw [div_eq_div_iff (ne_of_gt hwidthpos) (ne_of_gt hR)]
    linarith [hσ₀]
  have hnum : (T₂ - T₁) / 2 * LM + C + K * (Real.log T₂ + LMb)
      ≤ (T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ := by
    have h1 : (T₂ - T₁) / 2 * LM ≤ (T₂ - T₁) / 2 * (Real.log c + R * η) :=
      mul_le_mul_of_nonneg_left hLM (by linarith)
    have h2 : K * (Real.log T₂ + LMb) ≤ 6 * K * Λ := by
      rw [hlogT₂]
      nlinarith [hK, hLMb]
    linarith
  have hdiv : ((T₂ - T₁) / 2 * LM + C + K * (Real.log T₂ + LMb)) / (1 / 2 - σ₀)
      ≤ ((T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ) / (1 / 2 - σ₀) := by
    gcongr
  refine le_trans hdiv ?_
  have hrw : ((T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ) / (1 / 2 - σ₀)
      = ((T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ) * (Λ / R) := by
    rw [div_eq_mul_one_div, hinvR]
  rw [hrw]
  have hR1 : R * η * (Λ / R) = η * Λ := by field_simp
  have hexpand : ((T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ) * (Λ / R)
      = ((T₂ - T₁) * Λ / (2 * R)) * Real.log c + ((T₂ - T₁) * Λ / 2) * η
        + (C / R) * Λ + (6 * K / R) * Λ ^ 2 := by
    have hsplit : ((T₂ - T₁) / 2 * (Real.log c + R * η) + C + 6 * K * Λ) * (Λ / R)
        = ((T₂ - T₁) / 2 * Real.log c) * (Λ / R) + ((T₂ - T₁) / 2) * (R * η * (Λ / R))
          + C * (Λ / R) + 6 * K * Λ * (Λ / R) := by ring
    rw [hsplit, hR1]
    ring
  rw [hexpand]
  have hle : (T₂ - T₁) * Λ ≤ S := by
    rw [hS]
    have := mul_le_mul_of_nonneg_right hLT hΛ0.le
    linarith
  have hb1 : ((T₂ - T₁) * Λ / (2 * R)) * Real.log c ≤ (S / (2 * R)) * Real.log c := by
    have hd : (T₂ - T₁) * Λ / (2 * R) ≤ S / (2 * R) := by gcongr
    exact mul_le_mul_of_nonneg_right hd hlogc
  have hb2 : ((T₂ - T₁) * Λ / 2) * η ≤ (S / 2) * η := by
    have hd : (T₂ - T₁) * Λ / 2 ≤ S / 2 := by linarith
    exact mul_le_mul_of_nonneg_right hd hη0.le
  linarith

private theorem levinson_window_scalar
    {δ η R c cw C K T₁ T₂ Λ S NU mR LM LMb Θ σ₀ : ℝ}
    (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hη0 : 0 < η) (hηsmall : η ≤ 1 / 60)
    (hR : 0 < R) (hlogc : 0 ≤ Real.log c)
    (hbracket : (1 / 3 + δ) + 20 * η ≤ 1 - Real.log c / R)
    (hΛ1 : 1 ≤ Λ) (hS : S = T₂ * Λ)
    (hT₁20 : 20 ≤ T₁) (hT₁21 : T₁ ≤ 21) (hT₁T₂ : T₁ < T₂)
    (hcw : 0 < cw) (hK : 0 < K)
    (hσ₀ : (1 / 2 - σ₀) * Λ = R) (hσ₀b : σ₀ < 1 / 2)
    (_hNU0 : 0 ≤ NU)
    (hxS : (1 / 3 + δ) * NU ≤ ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S)
    (hmR : mR ≤ (1 / 3 + δ) * NU + 1)
    (hLM : LM ≤ Real.log c + R * η) (hLMb : LMb ≤ 5 * Λ)
    (hΘ : (1 / 2 - η) * S ≤ Θ)
    (hlower : 4 * Real.pi + cw * Real.log 21 + (cw + C / R) * Λ + (6 * K / R) * Λ ^ 2
      + (6 / 400) * T₂ ≤ η * S)
    (hlogT₂ : Real.log T₂ = Λ) :
    (mR + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2) + cw * Real.log T₁
      + cw * Real.log T₂
      + ((T₂ - T₁) / 2 * LM + C + K * (Real.log T₂ + LMb)) / (1 / 2 - σ₀) ≤ Θ := by
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  have hT₂0 : (0 : ℝ) < T₂ := by linarith
  have hS0 : (0 : ℝ) < S := by rw [hS]; positivity
  have hL0 : (0 : ℝ) < T₂ - T₁ := by linarith
  have hLT : T₂ - T₁ ≤ T₂ := by linarith
  have hbud := levinson_budget_scalar (η := η) (R := R) (c := c) (C := C) (K := K)
    (T₁ := T₁) (T₂ := T₂) (Λ := Λ) (S := S) (LM := LM) (LMb := LMb) (σ₀ := σ₀)
    hη0 hR hlogc hΛ0 hS hT₁T₂ (by linarith) hK hσ₀ hσ₀b hLM hLMb hlogT₂
  have hcoef := levinson_coef_bound hδ0 hδ3 hη0 hηsmall
  have hmπ : (mR + 2) * Real.pi + Real.pi
      ≤ ((1 / 3 + δ) / 2 + 5 * η) * S + 4 * Real.pi := by
    have hxπ : ((1 / 3 + δ) * NU) * Real.pi
        ≤ (((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S) * Real.pi :=
      mul_le_mul_of_nonneg_right hxS hπ0.le
    have hrw : (((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S) * Real.pi
        = (Real.pi * ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η))) * S := by ring
    rw [hrw] at hxπ
    have h2 : ((1 / 3 + δ) * NU) * Real.pi ≤ ((1 / 3 + δ) / 2 + 5 * η) * S :=
      le_trans hxπ (mul_le_mul_of_nonneg_right hcoef hS0.le)
    have h1 : mR * Real.pi ≤ ((1 / 3 + δ) * NU + 1) * Real.pi :=
      mul_le_mul_of_nonneg_right hmR hπ0.le
    linarith [h1, h2]
  have hT₁log : cw * Real.log T₁ ≤ cw * Real.log 21 :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hT₁21) hcw.le
  have hT₁sq : (T₂ - T₁) * (6 / T₁ ^ 2) ≤ (6 / 400) * T₂ := by
    have hsq : (400 : ℝ) ≤ T₁ ^ 2 := by nlinarith [hT₁20]
    have h1 : (6 : ℝ) / T₁ ^ 2 ≤ 6 / 400 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
    have hstep : (T₂ - T₁) * (6 / T₁ ^ 2) ≤ (T₂ - T₁) * (6 / 400) :=
      mul_le_mul_of_nonneg_left h1 hL0.le
    have hstep2 : (T₂ - T₁) * (6 / 400 : ℝ) ≤ T₂ * (6 / 400) :=
      mul_le_mul_of_nonneg_right hLT (by norm_num)
    linarith
  have hbr2 : (1 / 3 + δ) / 2 + Real.log c / (2 * R) + 7 * η + η / 2 ≤ 1 / 2 - η := by
    have hlogdiv : Real.log c / (2 * R) = (Real.log c / R) / 2 := by ring
    rw [hlogdiv]
    linarith [hbracket]
  have hbr := mul_le_mul_of_nonneg_right hbr2 hS0.le
  have hexp : ((1 / 3 + δ) / 2 + Real.log c / (2 * R) + 7 * η + η / 2) * S
      = ((1 / 3 + δ) / 2) * S + (S / (2 * R)) * Real.log c + 7 * (η * S) + (S / 2) * η := by
    ring
  rw [hexp] at hbr
  have hexp2 : (cw + C / R) * Λ = cw * Λ + (C / R) * Λ := by ring
  rw [hexp2] at hlower
  have hexpm : ((1 / 3 + δ) / 2 + 5 * η) * S = ((1 / 3 + δ) / 2) * S + 5 * (η * S) := by ring
  rw [hexpm] at hmπ
  have hηS : (0 : ℝ) ≤ η * S := by positivity
  rw [hlogT₂] at hbud ⊢
  linarith [hmπ, hbud, hT₁log, hT₁sq, hΘ, hbr, hlower, hηS]

set_option maxHeartbeats 1000000 in
/-- **Levinson's positive proportion from the mean-square gate.**  If the mollified mean square is
eventually at most `c` and Levinson's margin `1 − log c/R` exceeds `1/3`, then the odd-fibre census
eventually exceeds that proportion of the whole census. -/
theorem eventually_oddFiber_ge_of_gate_of_Y_pos {R c δ : ℝ}
    (hR : 0 < R) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hmargin : 1 / 3 + 2 * δ < 1 - Real.log c / R)
    (hgate : LevinsonMeanSquareGateOfYPos R c) :
    ∀ᶠ U in atTop, (1 / 3 + δ) * (xiPosZeroCount U : ℝ) ≤ (xiOddFiberCount U : ℝ) := by
  classical
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hc0 : (0 : ℝ) < c := by linarith
  have hlogc : (0 : ℝ) ≤ Real.log c := Real.log_nonneg hc
  set κ : ℝ := 1 - Real.log c / R with hκ
  have hκ1 : κ ≤ 1 := by
    rw [hκ]
    have : (0 : ℝ) ≤ Real.log c / R := by positivity
    linarith
  set η : ℝ := (κ - 1 / 3 - 2 * δ) / 40 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hηsmall : η ≤ 1 / 60 := by rw [hηdef]; linarith
  have hδ3 : δ < 1 / 3 := by linarith
  -- the gate parameter
  set εg : ℝ := min 1 (c * R * η) with hεgdef
  have hεg0 : 0 < εg := by
    rw [hεgdef]
    exact lt_min (by norm_num) (by positivity)
  have hεgle : εg ≤ c * R * η := min_le_right _ _
  have hloggate : Real.log (c + εg) ≤ Real.log c + R * η := by
    have hsplit : Real.log (c + εg) - Real.log c = Real.log ((c + εg) / c) := by
      rw [Real.log_div (by linarith) (ne_of_gt hc0)]
    have hle : Real.log ((c + εg) / c) ≤ (c + εg) / c - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hval : (c + εg) / c - 1 = εg / c := by
      field_simp
      ring
    have hquot : εg / c ≤ R * η := by
      rw [div_le_iff₀ hc0]
      nlinarith [hεgle]
    rw [hval] at hle
    linarith
  have hcεg : (1 : ℝ) ≤ c + εg := by linarith
  -- the window capstone and the eventual facts
  obtain ⟨cw, C, K, hcw, hC, hK, hcap⟩ :=
    exists_le_xiOddFiberCount_of_mollified_meanSquare_of_Y_pos
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (eventually_phase_advance_ge η hη0)
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp (eventually_scale_shift hη0)
  obtain ⟨A₃, hA₃⟩ := eventually_atTop.mp
    (eventually_lower_order_le (a := 4 * Real.pi + cw * Real.log 21) (b := cw + C / R)
      (d := 6 * K / R) (e := 6 / 400) (by positivity) (by positivity) hη0)
  obtain ⟨A₄, hA₄, hA₄close⟩ := exists_xiZeroCount_close η hη0
  filter_upwards [hgate εg hεg0, eventually_ge_atTop (A₁ + 1), eventually_ge_atTop (A₂ + 1),
    eventually_ge_atTop (A₃ + 1), eventually_ge_atTop A₄, eventually_ge_atTop (100 : ℝ)]
    with U hUgate hU1 hU2 hU3 hU4 hU100
  obtain ⟨T₁, T₂, σ₀, lam, Mb, b, N, hT₁, hT₂, hlam0, hlam1, hY, hN, hb1, hbn,
    hbreal, hMb1, hmass, hlogMb, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hUgate
  set Msq : ℝ := (c + εg) * (T₂ - T₁) with hMsqdef
  have hT₂U : T₂ ≤ U := hT₂.2
  have hT₂gt : U - 1 < T₂ := hT₂.1
  have hT₂big : (99 : ℝ) < T₂ := by linarith
  have hT₂A₁ : A₁ ≤ T₂ := by linarith
  have hT₂A₂ : A₂ ≤ T₂ := by linarith
  have hT₂A₃ : A₃ ≤ T₂ := by linarith
  have hT₂0 : (0 : ℝ) < T₂ := by linarith
  clear_value Msq
  set Λ : ℝ := Real.log T₂ with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    rw [hΛdef, Real.le_log_iff_exp_le hT₂0]
    have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hΛ0 : (0 : ℝ) < Λ := by linarith
  clear_value Λ
  set S : ℝ := T₂ * Λ with hSdef
  have hS0 : (0 : ℝ) < S := by rw [hSdef]; positivity
  clear_value S
  have hT₁20 : (20 : ℝ) ≤ T₁ := hT₁.1
  have hT₁21 : T₁ ≤ 21 := hT₁.2
  have hL0 : (0 : ℝ) < T₂ - T₁ := by linarith
  have hLT : T₂ - T₁ ≤ T₂ := by linarith
  have hUpos : (0 : ℝ) < U := by linarith
  set NU : ℝ := (xiPosZeroCount U : ℝ) with hNUdef
  have hNU0 : (0 : ℝ) ≤ NU := by rw [hNUdef]; positivity
  clear_value NU
  have hNU : NU ≤ (1 / (2 * Real.pi) + η) * (U * Real.log U) := by
    have hclose := hA₄close U (by linarith)
    have heq : NU = (xiZeroCount U : ℝ) := by
      rw [hNUdef]
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (xiPosZeroCount_eq_xiZeroCount hUpos.le)
    rw [heq]
    have habs := abs_le.mp hclose
    have hlogU : (0 : ℝ) ≤ Real.log U := Real.log_nonneg (by linarith)
    nlinarith [habs.2, hlogU, hUpos]
  have hUS : U * Real.log U ≤ (1 + η) * S := by
    rw [hSdef, hΛdef]
    exact hA₂ T₂ hT₂A₂ U ⟨hT₂U, by linarith⟩
  set x : ℝ := (1 / 3 + δ) * NU with hxdef
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; positivity
  clear_value x
  set m : ℕ := ⌊x⌋₊ + 1 with hmdef
  have hxm : x < (m : ℝ) := by
    rw [hmdef]; push_cast; exact Nat.lt_floor_add_one x
  have hmx : (m : ℝ) ≤ x + 1 := by
    rw [hmdef]; push_cast
    have hfl := Nat.floor_le hx0
    linarith
  clear_value m
  -- the count `x` against the scale
  have hcoefnn : (0 : ℝ) ≤ 1 / (2 * Real.pi) + η := by positivity
  have hxS : x ≤ ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S := by
    have hstep : NU ≤ ((1 / (2 * Real.pi) + η) * (1 + η)) * S := by
      have h1 : (1 / (2 * Real.pi) + η) * (U * Real.log U)
          ≤ (1 / (2 * Real.pi) + η) * ((1 + η) * S) :=
        mul_le_mul_of_nonneg_left hUS hcoefnn
      calc NU ≤ (1 / (2 * Real.pi) + η) * (U * Real.log U) := hNU
        _ ≤ (1 / (2 * Real.pi) + η) * ((1 + η) * S) := h1
        _ = ((1 / (2 * Real.pi) + η) * (1 + η)) * S := by ring
    have hpos : (0 : ℝ) ≤ 1 / 3 + δ := by linarith
    calc x = (1 / 3 + δ) * NU := hxdef
      _ ≤ (1 / 3 + δ) * (((1 / (2 * Real.pi) + η) * (1 + η)) * S) :=
          mul_le_mul_of_nonneg_left hstep hpos
      _ = ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S := by ring
  -- the mean-square input in logarithmic form
  have hlogratio : Real.log (Msq / (T₂ - T₁)) ≤ Real.log c + R * η := by
    have hquot : Msq / (T₂ - T₁) = c + εg := by
      rw [hMsqdef, mul_div_assoc, div_self (ne_of_gt hL0), mul_one]
    rw [hquot]
    exact hloggate
  have hbracketkey : (1 / 3 + δ) + 20 * η ≤ 1 - Real.log c / R := by
    rw [← hκ, hηdef]; linarith
  have hlower : 4 * Real.pi + cw * Real.log 21 + (cw + C / R) * Λ + (6 * K / R) * Λ ^ 2
      + (6 / 400) * T₂ ≤ η * S := by
    have h := hA₃ T₂ hT₂A₃
    rw [hSdef, hΛdef]
    exact h
  have hphase : (1 / 2 - η) * S ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁ := by
    have h := hA₁ T₂ hT₂A₁ T₁ hT₁
    rw [hSdef, hΛdef]
    exact h
  have hσ₀scale : (1 / 2 - σ₀) * Λ = R := hσ₀R
  have hxS' : (1 / 3 + δ) * NU ≤ ((1 / 3 + δ) * (1 / (2 * Real.pi) + η) * (1 + η)) * S := by
    rw [← hxdef]; exact hxS
  have hmx' : (m : ℝ) ≤ (1 / 3 + δ) * NU + 1 := by
    rw [← hxdef]; exact hmx
  have hwin := levinson_window_scalar (δ := δ) (η := η) (R := R) (c := c) (cw := cw) (C := C)
    (K := K) (T₁ := T₁) (T₂ := T₂) (Λ := Λ) (S := S) (NU := NU) (mR := (m : ℝ))
    (LM := Real.log (Msq / (T₂ - T₁))) (LMb := Real.log Mb)
    (Θ := gammaHardyTheta T₂ - gammaHardyTheta T₁) (σ₀ := σ₀)
    hδ hδ3 hη0 hηsmall hR hlogc hbracketkey hΛ1 hSdef hT₁20 hT₁21 (by linarith)
    hcw hK hσ₀scale hσ₀b hNU0 hxS' hmx' hlogratio hlogMb hphase hlower hΛdef.symm
  have hcount := hcap lam hlam0 hlam1 b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀a hσ₀b hT₁20 (by linarith) hY hG1 hG2 hP1 hP2 hMsq m hwin
  have hmono := xiOddFiberCount_mono hT₂U
  have hfinN : (m : ℝ) ≤ (xiOddFiberCount U : ℝ) := by
    have hle : m ≤ xiOddFiberCount U := le_trans hcount hmono
    exact_mod_cast hle
  rw [hxdef] at hxm
  linarith [hxm, hfinN]

/-- Legacy negative-shift specialization of Levinson's positive-proportion theorem. -/
theorem eventually_oddFiber_ge_of_gate {R c δ : ℝ}
    (hR : 0 < R) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hmargin : 1 / 3 + 2 * δ < 1 - Real.log c / R)
    (hgate : LevinsonMeanSquareGate R c) :
    ∀ᶠ U in atTop, (1 / 3 + δ) * (xiPosZeroCount U : ℝ) ≤ (xiOddFiberCount U : ℝ) :=
  eventually_oddFiber_ge_of_gate_of_Y_pos hR hc hδ hmargin
    (levinsonMeanSquareGateOfYPos_of_gate hgate)

end RHTower

end
