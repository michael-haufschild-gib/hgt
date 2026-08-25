import GaloisForLFunctions.RHTower.ZetaChiDisplacedCriticalRatioOscillatoryIntegral

/-!
# Displaced chi oscillation on dyadic subintervals

The stationary critical-line phase and its slowly varying displaced amplitude retain the full
dyadic cancellation bound on every subinterval of the block.  This is the form needed when the
moving logarithmic chi slope is frozen separately on short windows.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Uniform stationary-phase bound on every subinterval of a fixed dyadic block. -/
theorem norm_integral_zetaChi_line_mul_exp_subinterval_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    (ω : ℝ) :
    ‖∫ t in a..b,
        zetaChi (linePt t) * Complex.exp ((((ω * t : ℝ) : ℂ)) * I)‖ ≤
      6 / Real.sqrt (1 / (100 * T)) := by
  have hTpos : 0 < T := by linarith
  have hlam : 0 < 1 / (100 * T) := by positivity
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChi_line_mul_exp_eq_exp_twistPhase ω t)]
  apply norm_integral_cexp_secondDeriv_neg hab hlam
      (g' := fun t => ω - 2 * gammaHardyPhaseRate t)
      (g'' := fun t => -2 * deriv gammaHardyPhaseRate t)
  · intro t ht
    exact hasDerivAt_zetaChiCriticalTwistPhase ω t
  · intro t ht
    exact hasDerivAt_zetaChiCriticalTwistRate ω t
  · have hc : Continuous (fun t : ℝ =>
        -(2 * deriv gammaHardyPhaseRate t)) :=
      (continuous_const.mul continuous_deriv_gammaHardyPhaseRate).neg
    simpa only [neg_mul] using hc.continuousOn
  · intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      rwa [Set.uIcc_of_le hab] at ht
    have htT : T ≤ t := ha.trans htIcc.1
    have htpos : 0 < t := hTpos.trans_le htT
    have hcurv := deriv_gammaHardyPhaseRate_lower_bound (hT.trans htT)
    have htTop : t ≤ 2 * T := htIcc.2.trans hb
    have haux : 1 ≤ 2 * T / t := by
      exact (le_div_iff₀ htpos).2 (by simpa using htTop)
    have heq : 2 * (1 / (100 * t)) * (100 * T) = 2 * T / t := by
      field_simp [htpos.ne', hTpos.ne']
    have hfrac : 1 / (100 * T) ≤ 2 * (1 / (100 * t)) := by
      rw [div_le_iff₀ (by positivity : 0 < 100 * T)]
      rw [heq]
      exact haux
    have : 1 / (100 * T) ≤ 2 * deriv gammaHardyPhaseRate t :=
      hfrac.trans (mul_le_mul_of_nonneg_left hcurv (by norm_num))
    linarith

/-- Abel summation with stationary critical-line cancellation on any dyadic subinterval. -/
theorem norm_integral_complexAmplitude_mul_zetaChi_line_mul_exp_subinterval_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    (ω : ℝ) {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume a b) :
    ‖∫ x in a..b,
        u x * (zetaChi (linePt x) *
          Complex.exp (((ω * x : ℝ) : ℂ) * I))‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        (‖u b‖ + ∫ x in a..b, ‖u' x‖) := by
  let f : ℝ → ℂ := fun x =>
    zetaChi (linePt x) * Complex.exp (((ω * x : ℝ) : ℂ) * I)
  let F : ℝ → ℂ := zetaChiCriticalTwistPrimitive a ω
  have hf : Continuous f := continuous_zetaChiCriticalTwistIntegrand ω
  apply norm_integral_complexAmplitude_mul_deriv_le hab hu
      (u' := u') (v := F) (v' := f)
  · intro x hx
    exact hasDerivAt_zetaChiCriticalTwistPrimitive a ω x
  · exact hu'
  · exact hf.intervalIntegrable a b
  · exact zetaChiCriticalTwistPrimitive_left a ω
  · intro x hx
    dsimp only [F, zetaChiCriticalTwistPrimitive]
    exact norm_integral_zetaChi_line_mul_exp_subinterval_le
      hT ha hx.1 (hx.2.trans hb) ω

/-- Unconditional displaced-line stationary-frequency bound on every subinterval of a fixed
dyadic block. -/
theorem exists_norm_integral_zetaChi_displacedLinePt_mul_exp_le_subinterval
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T a b : ℝ, 4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T → ∀ ω : ℝ,
        ‖∫ t in a..b,
            zetaChi (displacedLinePt d t) *
              Complex.exp (((ω * t : ℝ) : ℂ) * I)‖ ≤
          (6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) := by
  have hd₀half : d₀ < 1 / 2 := hd₀quarter.trans_lt (by norm_num)
  obtain ⟨K, hK, hchi⟩ :=
    exists_norm_zetaChi_displacedLinePt_le_dyadic hd₀0 hd₀half
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T a b hT ha hab hb ω
  have hdquarter : d ≤ 1 / 4 := hdd₀.trans hd₀quarter
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  let u : ℝ → ℂ := zetaChiDisplacedCriticalRatio d
  let u' : ℝ → ℂ := zetaChiDisplacedCriticalRatioDeriv d
  have hu : ∀ t ∈ Set.uIcc a b, HasDerivAt u (u' t) t := by
    intro t ht
    exact hasDerivAt_zetaChiDisplacedCriticalRatio' hd hdhalf t
  have hu' : IntervalIntegrable u' volume a b :=
    (continuous_zetaChiDisplacedCriticalRatioDeriv hd hdhalf).intervalIntegrable a b
  have hstationary :=
    norm_integral_complexAmplitude_mul_zetaChi_line_mul_exp_subinterval_le
      hT ha hab hb ω hu hu'
  have heq :
      (∫ t in a..b,
        zetaChi (displacedLinePt d t) *
          Complex.exp (((ω * t : ℝ) : ℂ) * I)) =
      ∫ t in a..b,
        u t * (zetaChi (linePt t) *
          Complex.exp (((ω * t : ℝ) : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hpt : displacedLinePt 0 t = linePt t := by
      simp [displacedLinePt, linePt]
    have hne : zetaChi (linePt t) ≠ 0 := zetaChi_line_ne_zero t
    dsimp only [u]
    rw [zetaChiDisplacedCriticalRatio, hpt]
    field_simp [hne]
  rw [heq]
  refine hstationary.trans ?_
  have hchiBlock : ∀ t ∈ Set.Icc T (2 * T),
      ‖zetaChi (displacedLinePt d t)‖ ≤ K * (2 * T) ^ d := by
    intro t ht
    exact hchi d hd.le hdd₀ T t (by linarith) ht
  have hbBlock : b ∈ Set.Icc T (2 * T) := ⟨ha.trans hab, hb⟩
  have hEnd : ‖u b‖ ≤ K * (2 * T) ^ d := by
    dsimp only [u]
    rw [norm_zetaChiDisplacedCriticalRatio]
    exact hchiBlock b hbBlock
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖u' t‖ ≤ (K * (2 * T) ^ d) * ((8 + 4 * Real.pi) / T) := by
    intro t ht
    have htBlock : t ∈ Set.Icc T (2 * T) :=
      ⟨ha.trans ht.1, ht.2.trans hb⟩
    exact norm_zetaChiDisplacedCriticalRatioDeriv_le_dyadic
      hK hd hdquarter hT htBlock (hchiBlock t htBlock)
  have hcont := continuous_zetaChiDisplacedCriticalRatioDeriv hd hdhalf
  have hVarMono := intervalIntegral.integral_mono_on hab
    (hcont.norm.intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (μ := volume)) hpoint
  have hTpos : 0 < T := by linarith
  have hwidth : b - a ≤ T := by linarith
  have hC0 : 0 ≤ K * (2 * T) ^ d := by positivity
  have hV0 : 0 ≤ 8 + 4 * Real.pi := by positivity
  have hVar :
      (∫ t in a..b, ‖u' t‖) ≤
        (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := by
    refine hVarMono.trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hdiv0 : 0 ≤ (8 + 4 * Real.pi) / T := div_nonneg hV0 hTpos.le
    calc
      (b - a) * ((K * (2 * T) ^ d) * ((8 + 4 * Real.pi) / T)) ≤
          T * ((K * (2 * T) ^ d) * ((8 + 4 * Real.pi) / T)) :=
        mul_le_mul_of_nonneg_right hwidth (mul_nonneg hC0 hdiv0)
      _ = (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := by
        field_simp [hTpos.ne']
  have hsum :
      ‖u b‖ + ∫ t in a..b, ‖u' t‖ ≤
        (K * (2 * T) ^ d) * (9 + 4 * Real.pi) := by
    calc
      _ ≤ (K * (2 * T) ^ d) +
          (K * (2 * T) ^ d) * (8 + 4 * Real.pi) := add_le_add hEnd hVar
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end

end RHTower
