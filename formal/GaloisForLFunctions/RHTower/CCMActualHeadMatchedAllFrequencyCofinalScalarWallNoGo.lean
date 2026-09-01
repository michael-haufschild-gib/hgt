import GaloisForLFunctions.RHTower.CCMActualHeadMatchedAllFrequencyMetricLineTransportNoGo

/-!
# All-frequency reporter fidelity forces cofinal scalar singular walls

The exact matched all-frequency reporter does not merely have one positive and one negative
frequency.  For every literal prime power its orientation alternates at every translated
half-period, cofinally in positive frequency.  The cosine profile is strictly positive at every
nonzero frequency, so these signs are strict at the reporter level.

Consequently every continuous real scalar with exactly the reporter's Boolean orientation must
vanish above every bound.  This kills every continuous scalar Ward repair whose degeneracies are
bounded, finite, or eventually absent.  The positive survivor is sharp: a scalar realization must
have cofinal singular walls; otherwise the source-to-Ward mechanism must be discontinuous or use
genuinely phase-sensitive non-scalar data.
-/

open Complex MeasureTheory Set

noncomputable section
namespace RHTower

/-- Positive reporter frequency translated by `k` full arithmetic periods. -/
def ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency
    (n k : ℕ) : ℝ :=
  ccmActualHeadMatchedPhasePositiveReporterFrequency n +
    (k : ℝ) * ccmActualHeadMatchedPhasePositiveReporterFrequency n

/-- Negative reporter frequency translated by `k` full arithmetic periods. -/
def ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
    (n k : ℕ) : ℝ :=
  ccmActualHeadMatchedPhaseNegativeReporterFrequency n +
    (k : ℝ) * ccmActualHeadMatchedPhasePositiveReporterFrequency n

theorem ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency_phase
    {n : ℕ} (hn : 1 < n) (k : ℕ) :
    2 * Real.pi * Real.log n *
        ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency n k =
      2 * Real.pi + (k : ℝ) * (2 * Real.pi) := by
  rw [ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency]
  have h := ccmActualHeadMatchedPhasePositiveReporterFrequency_phase hn
  rw [mul_add, h]
  have hrewrite :
      2 * Real.pi * Real.log ↑n *
          ((k : ℝ) * ccmActualHeadMatchedPhasePositiveReporterFrequency n) =
        (k : ℝ) * (2 * Real.pi) := by
    calc
      _ = (k : ℝ) * (2 * Real.pi * Real.log ↑n *
          ccmActualHeadMatchedPhasePositiveReporterFrequency n) := by ring
      _ = _ := by rw [h]
  rw [hrewrite]

theorem ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_phase
    {n : ℕ} (hn : 1 < n) (k : ℕ) :
    2 * Real.pi * Real.log n *
        ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k =
      Real.pi + (k : ℝ) * (2 * Real.pi) := by
  rw [ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency]
  have hnphase := ccmActualHeadMatchedPhaseNegativeReporterFrequency_phase hn
  have hpphase := ccmActualHeadMatchedPhasePositiveReporterFrequency_phase hn
  rw [mul_add, hnphase]
  have hrewrite :
      2 * Real.pi * Real.log ↑n *
          ((k : ℝ) * ccmActualHeadMatchedPhasePositiveReporterFrequency n) =
        (k : ℝ) * (2 * Real.pi) := by
    calc
      _ = (k : ℝ) * (2 * Real.pi * Real.log ↑n *
          ccmActualHeadMatchedPhasePositiveReporterFrequency n) := by ring
      _ = _ := by rw [hpphase]
  rw [hrewrite]

theorem ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency_ne_zero
    {n : ℕ} (hn : 1 < n) (k : ℕ) :
    ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency n k ≠ 0 := by
  have hbase : 0 < ccmActualHeadMatchedPhasePositiveReporterFrequency n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    unfold ccmActualHeadMatchedPhasePositiveReporterFrequency
    exact one_div_pos.mpr hlog
  unfold ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency
  positivity

theorem ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_ne_zero
    {n : ℕ} (hn : 1 < n) (k : ℕ) :
    ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k ≠ 0 := by
  have hpos : 0 < ccmActualHeadMatchedPhasePositiveReporterFrequency n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    unfold ccmActualHeadMatchedPhasePositiveReporterFrequency
    exact one_div_pos.mpr hlog
  have hneg : 0 < ccmActualHeadMatchedPhaseNegativeReporterFrequency n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    unfold ccmActualHeadMatchedPhaseNegativeReporterFrequency
    exact one_div_pos.mpr (mul_pos (by norm_num) hlog)
  unfold ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
  positivity

/-- The oriented source symbol is positive at every full-period translated reporter. -/
theorem ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveTranslatedReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) (k : ℕ) :
    0 < (ccmActualHeadMatchedOrientedPhaseSymbol n
      (ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency n k)).re := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re,
    ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency_phase hn]
  have hcos := Real.cos_add_int_mul_two_pi (2 * Real.pi) (k : ℤ)
  have hsin := Real.sin_add_int_mul_two_pi (2 * Real.pi) (k : ℤ)
  simp only [Int.cast_natCast] at hcos hsin
  rw [hcos, hsin]
  simp only [Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
  exact ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero hw
    (ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency_ne_zero hn k)

/-- The oriented source symbol is negative at every antipodal translated reporter. -/
theorem ccmActualHeadMatchedOrientedPhaseSymbol_re_neg_at_negativeTranslatedReporterFrequency
    {n : ℕ} (hn : 1 < n) (hw : 0 < criticalMellinAtomWeight n) (k : ℕ) :
    (ccmActualHeadMatchedOrientedPhaseSymbol n
      (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k)).re < 0 := by
  rw [ccmActualHeadMatchedOrientedPhaseSymbol_re,
    ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_phase hn]
  have hcos := Real.cos_add_int_mul_two_pi Real.pi (k : ℤ)
  have hsin := Real.sin_add_int_mul_two_pi Real.pi (k : ℤ)
  simp only [Int.cast_natCast] at hcos hsin
  rw [hcos, hsin]
  simp only [Real.cos_pi, Real.sin_pi, neg_one_mul, zero_mul, add_zero]
  exact neg_lt_zero.mpr <|
    ccmActualHeadMatchedCosinePhaseProfile_pos_of_weight_pos_of_ne_zero hw
      (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_ne_zero hn k)

/-- Exact all-frequency Boolean orientation of one arithmetic atom. -/
def ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation
    (n : ℕ) (xi : ℝ) : Bool :=
  decide (1 < ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio xi n)

/-- Every translated full-period reporter has positive orientation. -/
theorem ccmActualHeadMatchedPhasePrimePowerPositiveTranslatedReporterOrientation_true
    (p : Nat.Primes) (e k : ℕ) :
    ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation
      (xiGammaEulerValuationNat (p, e))
      (ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency
        (xiGammaEulerValuationNat (p, e)) k) = true := by
  have hn : 1 < xiGammaEulerValuationNat (p, e) :=
    one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  simp only [ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation,
    decide_eq_true_eq]
  rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global,
    ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
    ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.one_lt_exp_iff]
  exact mul_pos (by norm_num) <|
    ccmActualHeadMatchedOrientedPhaseSymbol_re_pos_at_positiveTranslatedReporterFrequency
      hn hw k

/-- Every translated antipodal reporter has negative orientation. -/
theorem ccmActualHeadMatchedPhasePrimePowerNegativeTranslatedReporterOrientation_false
    (p : Nat.Primes) (e k : ℕ) :
    ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation
      (xiGammaEulerValuationNat (p, e))
      (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
        (xiGammaEulerValuationNat (p, e)) k) = false := by
  have hn : 1 < xiGammaEulerValuationNat (p, e) :=
    one_lt_xiGammaEulerValuationNat p e
  have hw : 0 < criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have hlt :
      ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
          (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
            (xiGammaEulerValuationNat (p, e)) k)
          (xiGammaEulerValuationNat (p, e)) < 1 := by
    rw [ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio_eq_global,
      ccmActualHeadMatchedPhaseGlobalProjectiveFockRatio,
      ccmActualHeadMatchedPhaseProjectiveFockRatio_eq_exp, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by norm_num) <|
      ccmActualHeadMatchedOrientedPhaseSymbol_re_neg_at_negativeTranslatedReporterFrequency
        hn hw k
  have hnot : ¬ 1 <
      ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockRatio
        (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
          (xiGammaEulerValuationNat (p, e)) k)
        (xiGammaEulerValuationNat (p, e)) := not_lt_of_ge hlt.le
  simp [ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation, hnot]

/-- A scalar has exactly the Boolean orientation of one prime-power all-frequency reporter. -/
def CCMActualHeadMatchedPhasePrimePowerScalarReporterFaithful
    (p : Nat.Primes) (e : ℕ) (c : ℝ → ℝ) : Prop :=
  ∀ xi : ℝ,
    GaloisForLFunctions.HTGeometry.signOrientation c xi =
      ccmActualHeadMatchedPhaseAllFrequencyReporterOrientation
        (xiGammaEulerValuationNat (p, e)) xi

theorem ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_lt_positive
    {n : ℕ} (hn : 1 < n) (k : ℕ) :
    ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k <
      ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency n k := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hbase : ccmActualHeadMatchedPhaseNegativeReporterFrequency n <
      ccmActualHeadMatchedPhasePositiveReporterFrequency n := by
    unfold ccmActualHeadMatchedPhaseNegativeReporterFrequency
      ccmActualHeadMatchedPhasePositiveReporterFrequency
    exact one_div_lt_one_div_of_lt hlog (by nlinarith)
  unfold ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
    ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency
  linarith

/-- Translated negative reporters are cofinal in positive frequency. -/
theorem exists_ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_above
    {n : ℕ} (hn : 1 < n) (B : ℝ) :
    ∃ k : ℕ, B < ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k := by
  have hperiod : 0 < ccmActualHeadMatchedPhasePositiveReporterFrequency n := by
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    unfold ccmActualHeadMatchedPhasePositiveReporterFrequency
    exact one_div_pos.mpr hlog
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((B - ccmActualHeadMatchedPhaseNegativeReporterFrequency n) /
      ccmActualHeadMatchedPhasePositiveReporterFrequency n)
  have hk' :
      B - ccmActualHeadMatchedPhaseNegativeReporterFrequency n <
        (k : ℝ) * ccmActualHeadMatchedPhasePositiveReporterFrequency n :=
    (div_lt_iff₀ hperiod).mp hk
  refine ⟨k, ?_⟩
  unfold ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency
  linarith

/-- **Cofinal scalar-wall survivor.** Every continuous scalar faithful to one literal
prime-power all-frequency reporter has a zero above every real bound. -/
theorem ccmActualHeadMatchedPhasePrimePowerContinuousScalarReporterFaithful_cofinal_zero
    (p : Nat.Primes) (e : ℕ) (c : ℝ → ℝ) (hc : Continuous c)
    (hfaith : CCMActualHeadMatchedPhasePrimePowerScalarReporterFaithful p e c) :
    ∀ B : ℝ, ∃ xi : ℝ, B < xi ∧ c xi = 0 := by
  intro B
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 1 < n := one_lt_xiGammaEulerValuationNat p e
  obtain ⟨k, hBneg⟩ :=
    exists_ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_above hn B
  let a := ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency n k
  let b := ccmActualHeadMatchedPhasePositiveTranslatedReporterFrequency n k
  have hab : a ≤ b :=
    (ccmActualHeadMatchedPhaseNegativeTranslatedReporterFrequency_lt_positive hn k).le
  have hca : ¬ 0 < c a := by
    apply of_decide_eq_false
    change GaloisForLFunctions.HTGeometry.signOrientation c a = false
    rw [hfaith a]
    exact ccmActualHeadMatchedPhasePrimePowerNegativeTranslatedReporterOrientation_false p e k
  have hcb : 0 < c b := by
    apply of_decide_eq_true
    change GaloisForLFunctions.HTGeometry.signOrientation c b = true
    rw [hfaith b]
    exact ccmActualHeadMatchedPhasePrimePowerPositiveTranslatedReporterOrientation_true p e k
  have hz : (0 : ℝ) ∈ Set.Icc (c a) (c b) :=
    ⟨le_of_not_gt hca, hcb.le⟩
  have himage := intermediate_value_Icc hab hc.continuousOn hz
  rcases himage with ⟨xi, hxi, hcxi⟩
  refine ⟨xi, ?_, hcxi⟩
  exact hBneg.trans_le hxi.1

/-- An eventually nondegenerate continuous scalar claimed to realize the exact reporter. -/
def CCMActualHeadMatchedPhasePrimePowerTailRegularScalarWardAt
    (p : Nat.Primes) (e : ℕ) : Prop :=
  ∃ (c : ℝ → ℝ) (B : ℝ),
    Continuous c ∧
    (∀ xi : ℝ, B < xi → c xi ≠ 0) ∧
    CCMActualHeadMatchedPhasePrimePowerScalarReporterFaithful p e c

/-- Tail-regular scalar realization at even one literal prime power. -/
def CCMActualHeadMatchedPhaseTailRegularScalarWardRoute : Prop :=
  ∃ (p : Nat.Primes) (e : ℕ),
    CCMActualHeadMatchedPhasePrimePowerTailRegularScalarWardAt p e

/-- **Tail-regular scalar Ward route kill.**  No eventually nondegenerate continuous scalar can
orient even one literal prime-power all-frequency reporter. -/
theorem ccmActualHeadMatchedPhaseTailRegularScalarWardRouteKilled :
    ¬ CCMActualHeadMatchedPhaseTailRegularScalarWardRoute := by
  rintro ⟨p, e, c, B, hc, hnonzero, hfaith⟩
  obtain ⟨xi, hBxi, hzero⟩ :=
    ccmActualHeadMatchedPhasePrimePowerContinuousScalarReporterFaithful_cofinal_zero
      p e c hc hfaith B
  exact hnonzero xi hBxi hzero

end RHTower
