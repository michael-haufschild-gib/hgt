import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP

/-!
# Electron-acoustic KP physical coefficient chambers (arXiv:2609.03539)

Closed consequences of the coefficients below equation (16) and the phase-correction equation
(19).  The PLK interaction coefficient has an exact critical temperature ratio: it is positive
below that ratio, zero on it, and negative above it.  Total square-root/logistic parameterizations
make all three statements premise-free.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

theorem mondalA1_closed_form (q : ℝ) :
    mondalA1 q = 1 + 1 / Real.exp q := by
  have hexp : Real.exp q ≠ 0 := Real.exp_ne_zero q
  unfold mondalA1 mondalKappa
  field_simp [hexp]
  ring

theorem mondalB1_closed_form (q : ℝ) :
    mondalB1 q = mondalA1 q * (2 * mondalA1 q - 1) / 2 := by
  have hexp : Real.exp q ≠ 0 := Real.exp_ne_zero q
  unfold mondalB1 mondalA1 mondalKappa
  field_simp [hexp]
  ring

noncomputable def mondalE (q p s : ℝ) : ℝ :=
  2 * mondalHotConcentration p * mondalB1 q / mondalA1 q
    + mondalHotConcentration p ^ 2 * mondalA1 q
    - mondalPhaseSpeedSq q p s * mondalA1 q ^ 2 * mondalHotConcentration p ^ 2

noncomputable def mondalF (q p s : ℝ) : ℝ :=
  4 * mondalPhaseSpeedSq q p s * mondalA1 q * mondalHotConcentration p

theorem mondalE_reduced (q p s : ℝ) :
    mondalE q p s =
      2 * mondalHotConcentration p * mondalB1 q / mondalA1 q
        - mondalA1 q ^ 2 * mondalHotConcentration p ^ 3 * mondalTemperatureRatio s := by
  have hA1 : mondalA1 q ≠ 0 := ne_of_gt (mondalA1_pos q)
  unfold mondalE mondalPhaseSpeedSq
  field_simp [hA1]
  ring

theorem mondalF_pos (q p s : ℝ) : 0 < mondalF q p s := by
  unfold mondalF mondalHotConcentration
  positivity [mondalPhaseSpeedSq_pos q p s, mondalA1_pos q]

noncomputable def mondalCriticalTemperatureRatio (q p : ℝ) : ℝ :=
  2 * mondalB1 q / (mondalA1 q ^ 3 * mondalHotConcentration p ^ 2)

theorem mondalCriticalTemperatureRatio_pos (q p : ℝ) :
    0 < mondalCriticalTemperatureRatio q p := by
  unfold mondalCriticalTemperatureRatio
  unfold mondalHotConcentration
  positivity [mondalA1_pos q, mondalB1_pos q]

theorem mondalE_critical_factor (q p s : ℝ) :
    mondalE q p s =
      mondalA1 q ^ 2 * mondalHotConcentration p ^ 3 *
        (mondalCriticalTemperatureRatio q p - mondalTemperatureRatio s) := by
  have hA1 : mondalA1 q ≠ 0 := ne_of_gt (mondalA1_pos q)
  have hp : mondalHotConcentration p ≠ 0 := by
    unfold mondalHotConcentration
    exact Real.exp_ne_zero p
  rw [mondalE_reduced]
  unfold mondalCriticalTemperatureRatio
  field_simp [hA1, hp]

noncomputable def mondalCriticalTemperatureAmplitude (q p : ℝ) : ℝ :=
  Real.sqrt (mondalCriticalTemperatureRatio q p)

theorem mondalCriticalTemperatureAmplitude_sq (q p : ℝ) :
    mondalTemperatureRatio (mondalCriticalTemperatureAmplitude q p) =
      mondalCriticalTemperatureRatio q p := by
  unfold mondalTemperatureRatio mondalCriticalTemperatureAmplitude
  exact Real.sq_sqrt (le_of_lt (mondalCriticalTemperatureRatio_pos q p))

theorem mondalE_at_critical_zero (q p : ℝ) :
    mondalE q p (mondalCriticalTemperatureAmplitude q p) = 0 := by
  rw [mondalE_critical_factor, mondalCriticalTemperatureAmplitude_sq]
  ring

noncomputable def mondalSubcriticalTemperatureAmplitude (q p r : ℝ) : ℝ :=
  Real.sqrt (mondalCriticalTemperatureRatio q p * HTGeometry.logisticVar r)

theorem mondalSubcriticalTemperatureAmplitude_sq (q p r : ℝ) :
    mondalTemperatureRatio (mondalSubcriticalTemperatureAmplitude q p r) =
      mondalCriticalTemperatureRatio q p * HTGeometry.logisticVar r := by
  unfold mondalTemperatureRatio mondalSubcriticalTemperatureAmplitude
  apply Real.sq_sqrt
  positivity [mondalCriticalTemperatureRatio_pos q p, HTGeometry.logisticVar_pos r]

theorem mondalE_subcritical_pos (q p r : ℝ) :
    0 < mondalE q p (mondalSubcriticalTemperatureAmplitude q p r) := by
  rw [mondalE_critical_factor, mondalSubcriticalTemperatureAmplitude_sq]
  have hcritical := mondalCriticalTemperatureRatio_pos q p
  have hlogistic := HTGeometry.logisticVar_lt_one r
  have hgap : 0 < mondalCriticalTemperatureRatio q p -
      mondalCriticalTemperatureRatio q p * HTGeometry.logisticVar r := by
    nlinarith [HTGeometry.logisticVar_pos r]
  unfold mondalHotConcentration
  positivity [mondalA1_pos q]

noncomputable def mondalSupercriticalTemperatureAmplitude (q p r : ℝ) : ℝ :=
  Real.sqrt (mondalCriticalTemperatureRatio q p + Real.exp r)

theorem mondalSupercriticalTemperatureAmplitude_sq (q p r : ℝ) :
    mondalTemperatureRatio (mondalSupercriticalTemperatureAmplitude q p r) =
      mondalCriticalTemperatureRatio q p + Real.exp r := by
  unfold mondalTemperatureRatio mondalSupercriticalTemperatureAmplitude
  apply Real.sq_sqrt
  positivity [mondalCriticalTemperatureRatio_pos q p]

theorem mondalE_supercritical_neg (q p r : ℝ) :
    mondalE q p (mondalSupercriticalTemperatureAmplitude q p r) < 0 := by
  rw [mondalE_critical_factor, mondalSupercriticalTemperatureAmplitude_sq]
  have hfactor : 0 < mondalA1 q ^ 2 * mondalHotConcentration p ^ 3 := by
    unfold mondalHotConcentration
    positivity [mondalA1_pos q]
  have hexp : 0 < Real.exp r := Real.exp_pos r
  nlinarith

/-! ## Soliton amplitude as a function of hot-electron concentration -/

theorem mondalB_reduced (q p s : ℝ) :
    mondalB q p s =
      2 * mondalA1 q - 1
        + 3 * mondalA1 q * mondalHotConcentration p ^ 2
        + 2 * mondalA1 q ^ 2 * mondalHotConcentration p ^ 3 *
          mondalTemperatureRatio s := by
  have hA1 : mondalA1 q ≠ 0 := ne_of_gt (mondalA1_pos q)
  unfold mondalB
  rw [mondalB1_closed_form]
  unfold mondalPhaseSpeedSq
  field_simp [hA1]
  ring

noncomputable def mondalAmplitudeDenominator (q s concentration : ℝ) : ℝ :=
  mondalA1 q *
    (2 * mondalA1 q - 1
      + 3 * mondalA1 q * concentration ^ 2
      + 2 * mondalA1 q ^ 2 * concentration ^ 3 * mondalTemperatureRatio s)

noncomputable def mondalAmplitudeAtConcentration (q s concentration : ℝ) : ℝ :=
  concentration / mondalAmplitudeDenominator q s concentration

theorem mondalBeta_div_alpha_eq_amplitudeAtConcentration (q p s : ℝ) :
    mondalBeta q p s / mondalAlpha q p s =
      mondalAmplitudeAtConcentration q s (mondalHotConcentration p) := by
  have hA1 : mondalA1 q ≠ 0 := ne_of_gt (mondalA1_pos q)
  have hB : mondalB q p s ≠ 0 := ne_of_gt (mondalB_pos q p s)
  rw [mondalBeta_div_alpha, mondalB_reduced]
  unfold mondalC mondalAmplitudeAtConcentration mondalAmplitudeDenominator
  field_simp [hA1, hB]

noncomputable def mondalAmplitudeConcentrationSlope (q s concentration : ℝ) : ℝ :=
  mondalA1 q *
      (2 * mondalA1 q - 1
        - 3 * mondalA1 q * concentration ^ 2
        - 4 * mondalA1 q ^ 2 * concentration ^ 3 * mondalTemperatureRatio s) /
    mondalAmplitudeDenominator q s concentration ^ 2

theorem hasDerivAt_mondalAmplitudeDenominator (q s concentration : ℝ) :
    HasDerivAt (mondalAmplitudeDenominator q s)
      (mondalA1 q *
        (6 * mondalA1 q * concentration
          + 6 * mondalA1 q ^ 2 * concentration ^ 2 * mondalTemperatureRatio s))
      concentration := by
  have hzero := hasDerivAt_const concentration (2 * mondalA1 q - 1)
  have htwo := ((hasDerivAt_id concentration).pow 2).const_mul (3 * mondalA1 q)
  have hthree := (((hasDerivAt_id concentration).pow 3).const_mul
    (2 * mondalA1 q ^ 2)).mul_const (mondalTemperatureRatio s)
  have h := ((hzero.add htwo).add hthree).const_mul (mondalA1 q)
  apply (h.congr_deriv (by
    norm_num
    apply Or.inl
    ring)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => by
    simp [mondalAmplitudeDenominator, id_eq]

theorem mondalAmplitudeDenominator_zero_pos (q s : ℝ) :
    0 < mondalAmplitudeDenominator q s 0 := by
  have hA1 := mondalA1_gt_one q
  unfold mondalAmplitudeDenominator
  norm_num
  nlinarith

theorem mondalAmplitudeDenominator_one_pos (q s : ℝ) :
    0 < mondalAmplitudeDenominator q s 1 := by
  have hA1 := mondalA1_gt_one q
  have hs : 0 ≤ mondalTemperatureRatio s := by
    unfold mondalTemperatureRatio
    positivity
  rw [show mondalAmplitudeDenominator q s 1 =
      mondalA1 q *
        (5 * mondalA1 q - 1 +
          2 * mondalA1 q ^ 2 * mondalTemperatureRatio s) by
    unfold mondalAmplitudeDenominator
    ring]
  have hinner : 0 < 5 * mondalA1 q - 1 +
      2 * mondalA1 q ^ 2 * mondalTemperatureRatio s := by
    nlinarith [sq_nonneg (mondalA1 q)]
  exact mul_pos (mondalA1_pos q) hinner

theorem hasDerivAt_mondalAmplitudeAtConcentration_zero (q s : ℝ) :
    HasDerivAt (mondalAmplitudeAtConcentration q s)
      (mondalAmplitudeConcentrationSlope q s 0) 0 := by
  have hden := hasDerivAt_mondalAmplitudeDenominator q s 0
  have hne : mondalAmplitudeDenominator q s 0 ≠ 0 :=
    ne_of_gt (mondalAmplitudeDenominator_zero_pos q s)
  have h := (hasDerivAt_id 0).div hden hne
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall fun z => by
      simp [mondalAmplitudeAtConcentration, id_eq]
  · unfold mondalAmplitudeConcentrationSlope
    field_simp [hne]
    unfold mondalAmplitudeDenominator
    norm_num
    apply Or.inl
    ring

theorem hasDerivAt_mondalAmplitudeAtConcentration_one (q s : ℝ) :
    HasDerivAt (mondalAmplitudeAtConcentration q s)
      (mondalAmplitudeConcentrationSlope q s 1) 1 := by
  have hden := hasDerivAt_mondalAmplitudeDenominator q s 1
  have hne : mondalAmplitudeDenominator q s 1 ≠ 0 :=
    ne_of_gt (mondalAmplitudeDenominator_one_pos q s)
  have h := (hasDerivAt_id 1).div hden hne
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall fun z => by
      simp [mondalAmplitudeAtConcentration, id_eq]
  · unfold mondalAmplitudeConcentrationSlope
    field_simp [hne]
    unfold mondalAmplitudeDenominator
    norm_num
    ring

theorem mondalAmplitudeConcentrationSlope_zero_pos (q s : ℝ) :
    0 < mondalAmplitudeConcentrationSlope q s 0 := by
  have hA1 := mondalA1_gt_one q
  have hden := mondalAmplitudeDenominator_zero_pos q s
  unfold mondalAmplitudeConcentrationSlope
  norm_num
  have hnum : 0 < mondalA1 q * (2 * mondalA1 q - 1) := by
    apply mul_pos (mondalA1_pos q)
    nlinarith
  exact div_pos hnum (sq_pos_of_pos hden)

theorem mondalAmplitudeConcentrationSlope_one_neg (q s : ℝ) :
    mondalAmplitudeConcentrationSlope q s 1 < 0 := by
  have hA1 := mondalA1_gt_one q
  have hden := mondalAmplitudeDenominator_one_pos q s
  have hs : 0 ≤ mondalTemperatureRatio s := by
    unfold mondalTemperatureRatio
    positivity
  unfold mondalAmplitudeConcentrationSlope
  norm_num
  have hnum : 2 * mondalA1 q - 1 - 3 * mondalA1 q -
      4 * mondalA1 q ^ 2 * mondalTemperatureRatio s < 0 := by
    nlinarith [sq_nonneg (mondalA1 q)]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mondalA1_pos q) hnum)
    (sq_pos_of_pos hden)

noncomputable def mondalPhaseCorrectionRatio (q p s : ℝ) : ℝ := mondalE q p s / mondalF q p s

theorem mondalPhaseCorrectionRatio_subcritical_pos (q p r : ℝ) :
    0 < mondalPhaseCorrectionRatio q p (mondalSubcriticalTemperatureAmplitude q p r) := by
  unfold mondalPhaseCorrectionRatio
  exact div_pos (mondalE_subcritical_pos q p r)
    (mondalF_pos q p (mondalSubcriticalTemperatureAmplitude q p r))

theorem mondalPhaseCorrectionRatio_critical_zero (q p : ℝ) :
    mondalPhaseCorrectionRatio q p (mondalCriticalTemperatureAmplitude q p) = 0 := by
  unfold mondalPhaseCorrectionRatio
  rw [mondalE_at_critical_zero]
  exact zero_div _

theorem mondalPhaseCorrectionRatio_supercritical_neg (q p r : ℝ) :
    mondalPhaseCorrectionRatio q p (mondalSupercriticalTemperatureAmplitude q p r) < 0 := by
  unfold mondalPhaseCorrectionRatio
  exact div_neg_of_neg_of_pos (mondalE_supercritical_neg q p r)
    (mondalF_pos q p (mondalSupercriticalTemperatureAmplitude q p r))

end GaloisForLFunctions.HTGeometry.DispersivePDE
