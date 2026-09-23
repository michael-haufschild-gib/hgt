import GaloisForLFunctions.RHTower.CCMActualHeadQuantileGammaChiSquareProducer


/-!
# Coherent quantile Γ producer on actual heads

This module preserves the literal prime--polar--Γ cancellation that scalar completed-error
bounds destroy. Each quantile cell is translated from its actual prime logarithm, the oriented
terminal cell is translated from the physical aperture, and all resulting vectors are added in
`SoninL2` before taking the reciprocal-higher-Γ chi-square norm.

For the canonical actual Γ-head `f`, the completed signed current is exactly

`∫ Re ⟪U_r f - f, coherentField(r)⟫ dr`.

Weighted Cauchy--Schwarz and completion of the higher-Γ square then give the unconditional
source-relative producer

`(2 * gammaHardyPhaseRate 0 + 4) * ‖f‖^(2 : ℕ) - 2 * coherentChiSquare(f) ≤ source(a,u)`.

Unlike the scalar chi-square predecessor, `coherentChiSquare` retains all cross-prime and
prime--terminal autocorrelations. No RH premise, computation, absolute completed-error split,
or new postulate is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted
    (r s : ℝ) (f : SoninL2) :
    ccmActualHeadSymmetricAutocorrelation (r + s) f -
        ccmActualHeadSymmetricAutocorrelation s f =
      (inner ℂ (logTranslationCLM r f - f)
        (logTranslationCLM (-s) f)).re := by
  rw [ccmActualHeadSymmetricAutocorrelation_eq_re_inner,
    ccmActualHeadSymmetricAutocorrelation_eq_re_inner]
  rw [← Complex.sub_re, ← inner_sub_left]
  rw [show logTranslationCLM (r + s) f - logTranslationCLM s f =
      logTranslationCLM s (logTranslationCLM r f - f) by
    rw [map_sub, logTranslationCLM_add_apply]
    congr 2
    ring_nf]
  rw [inner_logTranslationCLM]

/-- Oriented terminal cell translated to displacement from physical endpoint `T`. -/
def ccmActualHeadQuantileTerminalDisplacementDensity (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  let b := ccmOutgoingPrimeQuantileBoundary N
  if b ≤ T then
    (Ioc (b - T) 0).indicator (fun s : ℝ => Real.exp ((s + T) / 2)) r
  else
    -((Ioc 0 (b - T)).indicator (fun s : ℝ => Real.exp ((s + T) / 2)) r)

def ccmActualHeadQuantileCellCoherentField (n : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
    logTranslationCLM (-Real.log n) f

def ccmActualHeadQuantileTerminalCoherentField (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  (ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) • logTranslationCLM (-T) f

def ccmActualHeadQuantileBulkCoherentField (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ∑ n ∈ Finset.range N, ccmActualHeadQuantileCellCoherentField n f r

def ccmActualHeadQuantileCompletedCoherentField (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ccmActualHeadQuantileBulkCoherentField N f r + ccmActualHeadQuantileTerminalCoherentField T N f r

theorem measurable_ccmActualHeadQuantileTerminalDisplacementDensity (T : ℝ) (N : ℕ) :
    Measurable (ccmActualHeadQuantileTerminalDisplacementDensity T N) := by
  unfold ccmActualHeadQuantileTerminalDisplacementDensity
  dsimp only
  split_ifs
  · exact (by fun_prop : Measurable fun s : ℝ =>
      Real.exp ((s + T) / 2)).indicator measurableSet_Ioc
  · exact ((by fun_prop : Measurable fun s : ℝ =>
      Real.exp ((s + T) / 2)).indicator measurableSet_Ioc).neg

theorem aestronglyMeasurable_ccmActualHeadQuantileCellCoherentField (n : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadQuantileCellCoherentField n f) := by
  unfold ccmActualHeadQuantileCellCoherentField
  exact (Complex.ofRealCLM.continuous.measurable.comp
      (measurable_ccmOutgoingQuantileDisplacementCellDensity n)).aestronglyMeasurable.smul
        stronglyMeasurable_const.aestronglyMeasurable

theorem aestronglyMeasurable_ccmActualHeadQuantileTerminalCoherentField (T : ℝ) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadQuantileTerminalCoherentField T N f) := by
  unfold ccmActualHeadQuantileTerminalCoherentField
  exact (Complex.ofRealCLM.continuous.measurable.comp
      (measurable_ccmActualHeadQuantileTerminalDisplacementDensity T N)).aestronglyMeasurable.smul
        stronglyMeasurable_const.aestronglyMeasurable

theorem aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField (T : ℝ) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadQuantileCompletedCoherentField T N f) := by
  unfold ccmActualHeadQuantileCompletedCoherentField ccmActualHeadQuantileBulkCoherentField
  have hsum : AEStronglyMeasurable (fun r : ℝ =>
      ∑ n ∈ Finset.range N, ccmActualHeadQuantileCellCoherentField n f r) := by
    refine (Finset.aestronglyMeasurable_sum (Finset.range N) fun n _ =>
      aestronglyMeasurable_ccmActualHeadQuantileCellCoherentField n f).congr ?_
    filter_upwards with r
    simp only [Finset.sum_apply]
  exact hsum.add (aestronglyMeasurable_ccmActualHeadQuantileTerminalCoherentField T N f)

theorem ccmOutgoingQuantileCellCurrent_eq_integral_inner_coherentField
    (n : ℕ) (f : SoninL2) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) *
        (ccmActualHeadSymmetricAutocorrelation h f -
          ccmActualHeadSymmetricAutocorrelation (Real.log n) f)) =
      ∫ r : ℝ, (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCellCoherentField n f r)).re := by
  let lo := ccmOutgoingPrimeQuantileBoundary n - Real.log n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n
  let S : Set ℝ := Ioc lo hi
  let G : ℝ → ℝ := fun r => Real.exp ((r + Real.log n) / 2) *
    (ccmActualHeadSymmetricAutocorrelation (r + Real.log n) f -
      ccmActualHeadSymmetricAutocorrelation (Real.log n) f)
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := ccmOutgoingPrimeQuantileBoundary n)
    (b := ccmOutgoingPrimeQuantileBoundary (n + 1)) G (Real.log n)
  have hlohi : lo ≤ hi := by
    dsimp only [lo, hi]
    exact sub_le_sub_right (ccmOutgoingPrimeQuantileBoundary_mono_step n) _
  calc
    _ = ∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1), G (h - Real.log n) := by
      apply intervalIntegral.integral_congr
      intro h hh
      dsimp only [G]
      congr 2 <;> ring_nf
    _ = ∫ r in lo..hi, G r := by simpa only [lo, hi] using hshift
    _ = ∫ r in S, G r := by rw [intervalIntegral.integral_of_le hlohi]
    _ = ∫ r : ℝ, S.indicator G r := by rw [integral_indicator measurableSet_Ioc]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ S
      · rw [Set.indicator_of_mem hr]
        dsimp only [G, ccmActualHeadQuantileCellCoherentField]
        rw [show ccmOutgoingQuantileDisplacementCellDensity n r =
            Real.exp ((r + Real.log n) / 2) by
          simp [ccmOutgoingQuantileDisplacementCellDensity, S, lo, hi, hr]]
        rw [ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted]
        simp only [inner_smul_right, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      · rw [Set.indicator_of_notMem hr]
        have hd : ccmOutgoingQuantileDisplacementCellDensity n r = 0 := by
          simp [ccmOutgoingQuantileDisplacementCellDensity, S, lo, hi, hr]
        unfold ccmActualHeadQuantileCellCoherentField
        rw [hd]
        simp

theorem ccmOutgoingQuantileTerminalCurrent_eq_integral_inner_coherentField
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (N : ℕ) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
      Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) =
      ∫ r : ℝ, (inner ℂ (logTranslationCLM r f.1 - f.1)
        (ccmActualHeadQuantileTerminalCoherentField (2 * a.1) N f.1 r)).re := by
  let T : ℝ := 2 * a.1
  let b := ccmOutgoingPrimeQuantileBoundary N
  let lo := b - T
  let Spos : Set ℝ := Ioc lo 0
  let Sneg : Set ℝ := Ioc 0 lo
  let G : ℝ → ℝ := fun r => Real.exp ((r + T) / 2) *
    (ccmActualHeadSymmetricAutocorrelation (r + T) f.1 -
      ccmActualHeadSymmetricAutocorrelation T f.1)
  have hT : ccmActualHeadSymmetricAutocorrelation T f.1 = 0 := by
    dsimp only [T]
    exact ccmActualHeadSymmetricAutocorrelation_two_aperture_eq_zero a f
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := b) (b := T) G T
  have hbase :
      (∫ h in b..T, Real.exp (h / 2) *
          ccmActualHeadSymmetricAutocorrelation h f.1) = ∫ r in lo..0, G r := by
    calc
      _ = ∫ h in b..T, G (h - T) := by
        apply intervalIntegral.integral_congr
        intro h hh
        dsimp only [G]
        rw [hT, sub_zero]
        congr 2 <;> ring_nf
      _ = _ := by simpa only [lo, sub_self] using hshift
  rw [hbase]
  by_cases hb : b ≤ T
  · have hlo : lo ≤ 0 := by dsimp only [lo]; linarith
    rw [intervalIntegral.integral_of_le hlo]
    rw [show (∫ r in Spos, G r) = ∫ r : ℝ, Spos.indicator G r by
      rw [integral_indicator measurableSet_Ioc]]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Spos
    · rw [Set.indicator_of_mem hr]
      dsimp only [G, ccmActualHeadQuantileTerminalCoherentField]
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]]
      rw [ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted]
      simp only [inner_smul_right, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      dsimp only [T]
    · rw [Set.indicator_of_notMem hr]
      have hd : ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 := by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      rw [hd]
      simp
  · have hlt : T < b := lt_of_not_ge hb
    have hlo : 0 ≤ lo := by dsimp only [lo]; linarith
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hlo]
    rw [show -(∫ r in Sneg, G r) = ∫ r : ℝ, -(Sneg.indicator G r) by
      rw [integral_neg, integral_indicator measurableSet_Ioc]]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Sneg
    · rw [Set.indicator_of_mem hr]
      dsimp only [G, ccmActualHeadQuantileTerminalCoherentField]
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = -Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]]
      rw [ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted]
      simp only [inner_smul_right, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      dsimp only [T]
      ring_nf
    · rw [Set.indicator_of_notMem hr, neg_zero]
      have hd : ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 := by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      rw [hd]
      simp

theorem integrable_ccmActualHeadQuantileCellInnerField (n : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileCellCoherentField n f r)).re) := by
  let lo := ccmOutgoingPrimeQuantileBoundary n - Real.log n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n
  let S : Set ℝ := Ioc lo hi
  let F : ℝ → ℝ := fun r => (inner ℂ (logTranslationCLM r f - f)
    ((Real.exp ((r + Real.log n) / 2) : ℂ) •
      logTranslationCLM (-Real.log n) f)).re
  have hF : Continuous F := by
    dsimp only [F]
    exact Complex.continuous_re.comp (continuous_inner.comp
      (((continuous_logTranslationCLM f).sub continuous_const).prodMk
        ((Complex.continuous_ofReal.comp (by fun_prop)).smul continuous_const)))
  have hint : IntegrableOn F S := by
    have hbase : IntegrableOn F (Icc lo hi) := hF.integrableOn_Icc
    exact hbase.mono_set fun r hr => ⟨hr.1.le, hr.2⟩
  have hind := hint.integrable_indicator measurableSet_Ioc
  refine hind.congr (Filter.Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ S
  · rw [Set.indicator_of_mem hr]
    unfold ccmActualHeadQuantileCellCoherentField
    change F r = (inner ℂ (logTranslationCLM r f - f)
      ((ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
        logTranslationCLM (-Real.log n) f)).re
    rw [show ccmOutgoingQuantileDisplacementCellDensity n r =
        Real.exp ((r + Real.log n) / 2) by
      simp [ccmOutgoingQuantileDisplacementCellDensity, S, lo, hi, hr]]
  · rw [Set.indicator_of_notMem hr]
    unfold ccmActualHeadQuantileCellCoherentField
    change 0 = (inner ℂ (logTranslationCLM r f - f)
      ((ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
        logTranslationCLM (-Real.log n) f)).re
    rw [show ccmOutgoingQuantileDisplacementCellDensity n r = 0 by
      simp [ccmOutgoingQuantileDisplacementCellDensity, S, lo, hi, hr]]
    simp

theorem integrable_ccmActualHeadQuantileTerminalInnerField
    (T : ℝ) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileTerminalCoherentField T N f r)).re) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let lo := b - T
  let Spos : Set ℝ := Ioc lo 0
  let Sneg : Set ℝ := Ioc 0 lo
  let F : ℝ → ℝ := fun r => (inner ℂ (logTranslationCLM r f - f)
    ((Real.exp ((r + T) / 2) : ℂ) • logTranslationCLM (-T) f)).re
  have hF : Continuous F := by
    dsimp only [F]
    exact Complex.continuous_re.comp (continuous_inner.comp
      (((continuous_logTranslationCLM f).sub continuous_const).prodMk
        ((Complex.continuous_ofReal.comp (by fun_prop)).smul continuous_const)))
  by_cases hb : b ≤ T
  · have hlo : lo ≤ 0 := by dsimp only [lo]; linarith
    have hint : IntegrableOn F Spos :=
      (hF.integrableOn_Icc (a := lo) (b := 0)).mono_set
        (fun r hr => ⟨hr.1.le, hr.2⟩)
    have hind := hint.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Spos
    · rw [Set.indicator_of_mem hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      change F r = (inner ℂ (logTranslationCLM r f - f)
        ((ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) • logTranslationCLM (-T) f)).re
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]]
    · rw [Set.indicator_of_notMem hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      change 0 = (inner ℂ (logTranslationCLM r f - f)
        ((ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) • logTranslationCLM (-T) f)).re
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]]
      simp
  · have hlt : T < b := lt_of_not_ge hb
    have hlo : 0 ≤ lo := by dsimp only [lo]; linarith
    have hint : IntegrableOn (-F) Sneg := by
      exact (hF.neg.integrableOn_Icc (a := 0) (b := lo)).mono_set
        (fun r hr => ⟨hr.1.le, hr.2⟩)
    have hind := hint.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Sneg
    · rw [Set.indicator_of_mem hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      change (-F) r = (inner ℂ (logTranslationCLM r f - f)
        ((ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) • logTranslationCLM (-T) f)).re
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = -Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]]
      dsimp only [F]
      simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [Pi.neg_apply, neg_mul]
    · rw [Set.indicator_of_notMem hr]
      unfold ccmActualHeadQuantileTerminalCoherentField
      change 0 = (inner ℂ (logTranslationCLM r f - f)
        ((ccmActualHeadQuantileTerminalDisplacementDensity T N r : ℂ) • logTranslationCLM (-T) f)).re
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]]
      simp

theorem integrable_ccmActualHeadQuantileBulkInnerField (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileBulkCoherentField N f r)).re) := by
  have heq : (fun r : ℝ => (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileBulkCoherentField N f r)).re) = fun r : ℝ =>
      ∑ n ∈ Finset.range N, (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCellCoherentField n f r)).re := by
    funext r
    unfold ccmActualHeadQuantileBulkCoherentField
    rw [inner_sum, Complex.re_sum]
  rw [heq]
  exact integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_ccmActualHeadQuantileCellInnerField n f

theorem ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    ccmOutgoingQuantileCellAutocorrelationCurrent N f.1 +
        (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
          Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) =
      ∫ r : ℝ, (inner ℂ (logTranslationCLM r f.1 - f.1)
        (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N f.1 r)).re := by
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hbulk : ccmOutgoingQuantileCellAutocorrelationCurrent N f.1 =
      ∫ r : ℝ, (inner ℂ (logTranslationCLM r f.1 - f.1)
        (ccmActualHeadQuantileBulkCoherentField N f.1 r)).re := by
    unfold ccmOutgoingQuantileCellAutocorrelationCurrent
    calc
      _ = ∑ n ∈ Finset.range N, ∫ r : ℝ,
          (inner ℂ (logTranslationCLM r f.1 - f.1)
            (ccmActualHeadQuantileCellCoherentField n f.1 r)).re := by
        apply Finset.sum_congr rfl
        intro n hn
        exact ccmOutgoingQuantileCellCurrent_eq_integral_inner_coherentField n f.1
      _ = ∫ r : ℝ, ∑ n ∈ Finset.range N,
          (inner ℂ (logTranslationCLM r f.1 - f.1)
            (ccmActualHeadQuantileCellCoherentField n f.1 r)).re := by
        rw [integral_finsetSum (Finset.range N) fun n _ =>
          integrable_ccmActualHeadQuantileCellInnerField n f.1]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with r
        unfold ccmActualHeadQuantileBulkCoherentField
        rw [inner_sum, Complex.re_sum]
  have hterminal := ccmOutgoingQuantileTerminalCurrent_eq_integral_inner_coherentField a f N
  have hbint := integrable_ccmActualHeadQuantileBulkInnerField N f.1
  have htint := integrable_ccmActualHeadQuantileTerminalInnerField (2 * a.1) N f.1
  dsimp only
  rw [hbulk, hterminal, ← integral_add hbint htint]
  apply integral_congr_ae
  filter_upwards with r
  unfold ccmActualHeadQuantileCompletedCoherentField
  rw [inner_add_right, Complex.add_re]

/-- Operator-valued coherent chi-square cost. Prime cells and the oriented terminal
cell add in `SoninL2` before the norm is taken. -/
def ccmActualHeadCoherentQuantileGammaChiSquare (T : ℝ) (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 *
    ccmGammaHigherBinetDualDensity |r|

theorem integrable_ccmActualHeadQuantileTerminalDensity_sq_mul_dual (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  let b := ccmOutgoingPrimeQuantileBoundary N
  let lo := b - T
  let Spos : Set ℝ := Ioc lo 0
  let Sneg : Set ℝ := Ioc 0 lo
  let F : ℝ → ℝ := fun r => Real.exp ((r + T) / 2) ^ 2 *
    ccmGammaHigherBinetDualDensity |r|
  have hF : Continuous F := by
    dsimp only [F]
    unfold ccmGammaHigherBinetDualDensity
    fun_prop
  by_cases hb : b ≤ T
  · have hlo : lo ≤ 0 := by dsimp only [lo]; linarith
    have hint : IntegrableOn F Spos :=
      (hF.integrableOn_Icc (a := lo) (b := 0)).mono_set
        (fun r hr => ⟨hr.1.le, hr.2⟩)
    have hind := hint.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Spos
    · rw [Set.indicator_of_mem hr]
      change F r = ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]]
    · rw [Set.indicator_of_notMem hr]
      change 0 = ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Spos, lo, hr]]
      simp
  · have hlt : T < b := lt_of_not_ge hb
    have hlo : 0 ≤ lo := by dsimp only [lo]; linarith
    have hint : IntegrableOn F Sneg :=
      (hF.integrableOn_Icc (a := 0) (b := lo)).mono_set
        (fun r hr => ⟨hr.1.le, hr.2⟩)
    have hind := hint.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Sneg
    · rw [Set.indicator_of_mem hr]
      change F r = ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = -Real.exp ((r + T) / 2) by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]]
      dsimp only [F]
      ring_nf
    · rw [Set.indicator_of_notMem hr]
      change 0 = ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|
      rw [show ccmActualHeadQuantileTerminalDisplacementDensity T N r = 0 by
        simp [ccmActualHeadQuantileTerminalDisplacementDensity, b, hb, Sneg, lo, hr]]
      simp

theorem norm_logTranslationCLM_apply_le (s : ℝ) (f : SoninL2) :
    ‖logTranslationCLM s f‖ ≤ ‖f‖ := by
  calc
    ‖logTranslationCLM s f‖ ≤ ‖logTranslationCLM s‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_logTranslationCLM_le_one s) (norm_nonneg _)
    _ = ‖f‖ := one_mul _

theorem norm_ccmActualHeadQuantileCellCoherentField_le (n : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileCellCoherentField n f r‖ ≤
      ccmOutgoingQuantileDisplacementCellDensity n r * ‖f‖ := by
  unfold ccmActualHeadQuantileCellCoherentField
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ccmOutgoingQuantileDisplacementCellDensity_nonneg n r)]
  exact mul_le_mul_of_nonneg_left
    (norm_logTranslationCLM_apply_le (-Real.log n) f)
    (ccmOutgoingQuantileDisplacementCellDensity_nonneg n r)

theorem norm_ccmActualHeadQuantileBulkCoherentField_le (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileBulkCoherentField N f r‖ ≤
      ccmOutgoingQuantileDisplacementDensity N r * ‖f‖ := by
  unfold ccmActualHeadQuantileBulkCoherentField ccmOutgoingQuantileDisplacementDensity
  calc
    ‖∑ n ∈ Finset.range N, ccmActualHeadQuantileCellCoherentField n f r‖ ≤
        ∑ n ∈ Finset.range N, ‖ccmActualHeadQuantileCellCoherentField n f r‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        ccmOutgoingQuantileDisplacementCellDensity n r * ‖f‖ := by
      exact Finset.sum_le_sum fun n hn => norm_ccmActualHeadQuantileCellCoherentField_le n f r
    _ = (∑ n ∈ Finset.range N,
        ccmOutgoingQuantileDisplacementCellDensity n r) * ‖f‖ := by
      rw [Finset.sum_mul]

theorem norm_ccmActualHeadQuantileTerminalCoherentField_le (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileTerminalCoherentField T N f r‖ ≤ |ccmActualHeadQuantileTerminalDisplacementDensity T N r| * ‖f‖ := by
  unfold ccmActualHeadQuantileTerminalCoherentField
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_logTranslationCLM_apply_le (-T) f) (abs_nonneg _)

theorem norm_ccmActualHeadQuantileCompletedCoherentField_sq_mul_dual_le
    (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 * ccmGammaHigherBinetDualDensity |r| ≤
      (2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
          ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) * ‖f‖ ^ 2) *
        ccmGammaHigherBinetDualDensity |r| := by
  have hbulk := norm_ccmActualHeadQuantileBulkCoherentField_le N f r
  have hterminal := norm_ccmActualHeadQuantileTerminalCoherentField_le T N f r
  have hρ := ccmOutgoingQuantileDisplacementDensity_nonneg N r
  have htd : 0 ≤ |ccmActualHeadQuantileTerminalDisplacementDensity T N r| := abs_nonneg _
  have hfn : 0 ≤ ‖f‖ := norm_nonneg _
  have hdual := ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  have hnorm : ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ≤
      (ccmOutgoingQuantileDisplacementDensity N r +
        |ccmActualHeadQuantileTerminalDisplacementDensity T N r|) * ‖f‖ := by
    calc
      ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ≤
          ‖ccmActualHeadQuantileBulkCoherentField N f r‖ + ‖ccmActualHeadQuantileTerminalCoherentField T N f r‖ := by
        unfold ccmActualHeadQuantileCompletedCoherentField
        exact norm_add_le _ _
      _ ≤ ccmOutgoingQuantileDisplacementDensity N r * ‖f‖ +
          |ccmActualHeadQuantileTerminalDisplacementDensity T N r| * ‖f‖ := add_le_add hbulk hterminal
      _ = _ := by ring_nf
  have hsquare : ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 ≤
      2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
        ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) * ‖f‖ ^ 2 := by
    have hsq1 := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (add_nonneg hρ htd) hfn)).mpr hnorm
    have habs_sq : |ccmActualHeadQuantileTerminalDisplacementDensity T N r| ^ 2 =
        ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 := sq_abs _
    nlinarith [sq_nonneg
      (ccmOutgoingQuantileDisplacementDensity N r -
        |ccmActualHeadQuantileTerminalDisplacementDensity T N r|)]
  exact mul_le_mul_of_nonneg_right hsquare hdual

theorem integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity
    (T : ℝ) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  have hbulk := integrable_ccmOutgoingQuantileGammaChiSquareDensity N
  have hterminal := integrable_ccmActualHeadQuantileTerminalDensity_sq_mul_dual T N
  have hmajor : Integrable (fun r : ℝ =>
      (2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
          ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) * ‖f‖ ^ 2) *
        ccmGammaHigherBinetDualDensity |r|) := by
    have hsum : Integrable (fun r : ℝ =>
        (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
          ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) *
          ccmGammaHigherBinetDualDensity |r|) := by
      have h := hbulk.add hterminal
      change Integrable (fun r : ℝ =>
        ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
            ccmGammaHigherBinetDualDensity |r| +
          ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2 *
            ccmGammaHigherBinetDualDensity |r|) at h
      simpa only [add_mul] using h
    convert hsum.const_mul (2 * ‖f‖ ^ 2) using 1
    funext r
    ring_nf
  have hdualMeas : AEStronglyMeasurable
      (fun r : ℝ => ccmGammaHigherBinetDualDensity |r|) volume := by
    apply Continuous.aestronglyMeasurable
    unfold ccmGammaHigherBinetDualDensity
    fun_prop
  have hmeas := (aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField T N f).norm.pow 2 |>.mul hdualMeas
  refine hmajor.mono' hmeas
    (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
  exact norm_ccmActualHeadQuantileCompletedCoherentField_sq_mul_dual_le T N f r

theorem ccmActualHeadCoherentQuantileGammaChiSquare_nonneg (T : ℝ) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadCoherentQuantileGammaChiSquare T N f := by
  unfold ccmActualHeadCoherentQuantileGammaChiSquare
  apply integral_nonneg
  intro r
  exact mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem integrable_ccmActualHeadCoherentNorm_mul_sqrtDefect_and_le_gamma
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (T : ℝ) (N : ℕ) :
    let f : SoninL2 := ccmArchimedeanFormToAperture a u
    Integrable (fun r : ℝ => ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ *
        Real.sqrt (ccmActualHeadTranslationDefect r f)) ∧
      (∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ *
          Real.sqrt (ccmActualHeadTranslationDefect r f)) ≤
        Real.sqrt (ccmActualHeadCoherentQuantileGammaChiSquare T N f) *
          Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy f) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let ρ : ℝ → ℝ := fun r => ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖
  let κ : ℝ → ℝ := fun r => ccmGammaHigherBinetDualDensity |r|
  let e : ℝ → ℝ := fun r =>
    ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| f
  let A : ℝ → ℂ := fun r => Complex.ofReal (ρ r * Real.sqrt (κ r))
  let B : ℝ → ℂ := fun r => Complex.ofReal (Real.sqrt (e r))
  have hρm : AEStronglyMeasurable ρ volume := by
    exact (aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField T N f).norm
  have hκc : Continuous κ := by
    dsimp only [κ]
    unfold ccmGammaHigherBinetDualDensity
    fun_prop
  have hγm : Measurable fun r : ℝ => ccmGammaHigherBinetModeDensity |r| := by
    unfold ccmGammaHigherBinetModeDensity
    fun_prop
  have hEm : Measurable fun r : ℝ => ccmActualHeadTranslationDefect |r| f := by
    unfold ccmActualHeadTranslationDefect
    exact ((((continuous_logTranslationCLM f).comp continuous_abs).sub
      continuous_const).norm.pow 2).measurable
  have hem : Measurable e := by
    dsimp only [e]
    exact hγm.mul hEm
  have hAm : AEStronglyMeasurable A volume := by
    dsimp only [A]
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hρm.mul (Real.continuous_sqrt.comp_aestronglyMeasurable
        hκc.aestronglyMeasurable))
  have hBm : AEStronglyMeasurable B volume := by
    apply Measurable.aestronglyMeasurable
    dsimp only [B]
    fun_prop
  have hρ0 (r : ℝ) : 0 ≤ ρ r := norm_nonneg _
  have hκ0 (r : ℝ) : 0 ≤ κ r :=
    ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  have hγ0 (r : ℝ) : 0 ≤ ccmGammaHigherBinetModeDensity |r| := by
    by_cases hr : r = 0
    · subst r
      simp [ccmGammaHigherBinetModeDensity]
    · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le
  have hE0 (r : ℝ) : 0 ≤ ccmActualHeadTranslationDefect |r| f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have he0 (r : ℝ) : 0 ≤ e r := mul_nonneg (hγ0 r) (hE0 r)
  have hAint : Integrable (fun r : ℝ => ‖A r‖ ^ 2) := by
    refine (integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity T N f).congr
      (Filter.Eventually.of_forall fun r => ?_)
    dsimp only [A, ρ, κ]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)), mul_pow,
      Real.sq_sqrt (hκ0 r)]
  have hBint : Integrable (fun r : ℝ => ‖B r‖ ^ 2) := by
    refine (integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u).congr
      (Filter.Eventually.of_forall fun r => ?_)
    dsimp only [B, e]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (he0 r)]
  have hroot (r : ℝ) :
      ‖A r‖ * ‖B r‖ =
        ρ r * Real.sqrt (ccmActualHeadTranslationDefect r f) := by
    have hsqrt : Real.sqrt (κ r) * Real.sqrt (e r) =
        Real.sqrt (ccmActualHeadTranslationDefect |r| f) := by
      by_cases hr : r = 0
      · subst r
        have hdefzero : ccmActualHeadTranslationDefect 0 f = 0 := by
          unfold ccmActualHeadTranslationDefect
          rw [logTranslationCLM_zero_apply]
          simp
        dsimp only [κ, e]
        simp [hdefzero, ccmGammaHigherBinetDualDensity,
          ccmGammaHigherBinetModeDensity]
      · rw [← Real.sqrt_mul (hκ0 r)]
        congr 1
        dsimp only [κ, e]
        calc
          ccmGammaHigherBinetDualDensity |r| *
              (ccmGammaHigherBinetModeDensity |r| *
                ccmActualHeadTranslationDefect |r| f) =
            (ccmGammaHigherBinetModeDensity |r| *
              ccmGammaHigherBinetDualDensity |r|) *
                ccmActualHeadTranslationDefect |r| f := by ring_nf
          _ = ccmActualHeadTranslationDefect |r| f := by
            rw [ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr)]
            ring_nf
    dsimp only [A, B]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_assoc, hsqrt, ccmActualHeadTranslationDefect_abs]
  have hprod : Integrable (fun r : ℝ => ‖A r‖ * ‖B r‖) :=
    GaloisForLFunctions.HTGeometry.integrable_mul_norm_of_integrable_sq
      hAm hBm hAint hBint
  have htarget : Integrable (fun r : ℝ => ρ r *
      Real.sqrt (ccmActualHeadTranslationDefect r f)) := by
    exact hprod.congr (Filter.Eventually.of_forall hroot)
  have hcs := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
    hAm hBm hAint hBint
  have hAeq : (∫ r : ℝ, ‖A r‖ ^ 2) =
      ccmActualHeadCoherentQuantileGammaChiSquare T N f := by
    unfold ccmActualHeadCoherentQuantileGammaChiSquare
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [A, ρ, κ]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ0 r) (Real.sqrt_nonneg _)), mul_pow,
      Real.sq_sqrt (hκ0 r)]
  have hBeq : (∫ r : ℝ, ‖B r‖ ^ 2) =
      2 * ccmActualHeadGammaHigherBinetModeEnergy f := by
    rw [← integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [B, e]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (he0 r)]
  have hleft : (∫ r : ℝ, ‖A r‖ * ‖B r‖) =
      ∫ r : ℝ, ρ r * Real.sqrt (ccmActualHeadTranslationDefect r f) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hroot
  constructor
  · simpa only [ρ, f] using htarget
  · rw [hleft, hAeq, hBeq] at hcs
    simpa only [ρ, f] using hcs

theorem integrable_ccmActualHeadCompletedCoherentInnerField (T : ℝ) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileCompletedCoherentField T N f r)).re) := by
  have hbulk := integrable_ccmActualHeadQuantileBulkInnerField N f
  have hterminal := integrable_ccmActualHeadQuantileTerminalInnerField T N f
  have h := hbulk.add hterminal
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  unfold ccmActualHeadQuantileCompletedCoherentField
  change (inner ℂ (logTranslationCLM r f - f) (ccmActualHeadQuantileBulkCoherentField N f r)).re +
      (inner ℂ (logTranslationCLM r f - f) (ccmActualHeadQuantileTerminalCoherentField T N f r)).re =
    (inner ℂ (logTranslationCLM r f - f)
      (ccmActualHeadQuantileBulkCoherentField N f r + ccmActualHeadQuantileTerminalCoherentField T N f r)).re
  rw [inner_add_right, Complex.add_re]

theorem abs_re_inner_increment_ccmActualHeadCompletedCoherentField_le
    (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    |(inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re| ≤
      ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ *
        Real.sqrt (ccmActualHeadTranslationDefect r f) := by
  calc
    _ ≤ ‖inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖logTranslationCLM r f - f‖ *
        ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ := norm_inner_le_norm _ _
    _ = _ := by
      have hnorm := norm_logTranslationCLM_sub_logTranslationCLM_eq_sqrt_defect r 0 f
      rw [logTranslationCLM_zero_apply] at hnorm
      rw [hnorm]
      ring_nf

theorem abs_integral_ccmActualHeadCompletedCoherentInner_le_gamma
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (T : ℝ) (N : ℕ) :
    let f : SoninL2 := ccmArchimedeanFormToAperture a u
    |∫ r : ℝ, (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re| ≤
      Real.sqrt (ccmActualHeadCoherentQuantileGammaChiSquare T N f) *
        Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy f) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  have hpair := integrable_ccmActualHeadCoherentNorm_mul_sqrtDefect_and_le_gamma a u T N
  have hinner := integrable_ccmActualHeadCompletedCoherentInnerField T N f
  dsimp only at hpair ⊢
  calc
    |∫ r : ℝ, (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re| ≤
      ∫ r : ℝ, |(inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re| := abs_integral_le_integral_abs
    _ ≤ ∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ *
        Real.sqrt (ccmActualHeadTranslationDefect r f) := by
      exact integral_mono hinner.abs hpair.1
        (fun r => abs_re_inner_increment_ccmActualHeadCompletedCoherentField_le T N f r)
    _ ≤ _ := hpair.2

theorem abs_ccmActualHeadCompletedQuantileCurrent_le_coherentGamma
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    |ccmOutgoingQuantileCellAutocorrelationCurrent N (f : SoninL2) +
        (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
          Real.exp (h / 2) *
            ccmActualHeadSymmetricAutocorrelation h (f : SoninL2))| ≤
      Real.sqrt (ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2)) *
        Real.sqrt (2 * ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2)) := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hid := ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f
  have hbound := abs_integral_ccmActualHeadCompletedCoherentInner_le_gamma a u (2 * a.1) N
  dsimp only at hid hbound ⊢
  rw [hid]
  exact hbound

/-- Literal cell-plus-terminal completed current with prime and polar masses already
cancelled at the common quantile clock. -/
def ccmActualHeadCompletedQuantileCurrent
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  ccmOutgoingQuantileCellAutocorrelationCurrent N f.1 +
    (∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
      Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1)

/-- Higher Γ energy absorbs the literal signed prime--polar completed current at
the operator-valued coherent chi-square price. No prime cell or completed error
is separated by an absolute value. -/
theorem ccmActualHeadCompletedQuantileCurrent_higherGamma_signedControl
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1;
    -(2 * ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2)) ≤
      ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        2 * ccmActualHeadCompletedQuantileCurrent a f := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let A := ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2)
  let H := ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2)
  let C := ccmActualHeadCompletedQuantileCurrent a f
  have hA : 0 ≤ A := ccmActualHeadCoherentQuantileGammaChiSquare_nonneg _ _ _
  have hH : 0 ≤ H := ccmActualHeadGammaHigherBinetModeEnergy_nonneg _
  have habs : |C| ≤ Real.sqrt A * Real.sqrt (2 * H) := by
    simpa only [A, H, C, f, N, ccmActualHeadCompletedQuantileCurrent] using
      abs_ccmActualHeadCompletedQuantileCurrent_le_coherentGamma a u
  have hC : -(Real.sqrt A * Real.sqrt (2 * H)) ≤ C :=
    (neg_le_neg habs).trans (neg_abs_le C)
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hsH : Real.sqrt (2 * H) ^ 2 = 2 * H :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hH)
  have hsq : 0 ≤ (Real.sqrt (2 * H) - 2 * Real.sqrt A) ^ 2 := sq_nonneg _
  dsimp only [A, H, C, f, N] at hC hsA hsH hsq ⊢
  nlinarith

theorem higherGamma_add_outgoingCurrent_ge_coherentProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2 * a.1)) + 1
    4 * ‖f‖ ^ 2 -
        2 * ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2) ≤
      ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  let S := ccmOutgoingQuantileCellAutocorrelationCurrent N (f : SoninL2)
  let R := ∫ h in ccmOutgoingPrimeQuantileBoundary N..(2 * a.1),
    Real.exp (h / 2) *
      ccmActualHeadSymmetricAutocorrelation h (f : SoninL2)
  have hsigned := ccmActualHeadCompletedQuantileCurrent_higherGamma_signedControl a u
  have hcurrent : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * S + 2 * R := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
    dsimp only [N, S, R, ccmOutgoingQuantileCellAutocorrelationCurrent]
  dsimp only at hsigned ⊢
  rw [hcurrent]
  change -(2 * ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2)) ≤
    ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) + 2 * (S + R) at hsigned
  nlinarith

/-- Canonical operator-valued signed producer on the actual Γ-head. -/
def ccmActualHeadCoherentQuantileGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 -
    2 * ccmActualHeadCoherentQuantileGammaChiSquare (2 * a.1) N (f : SoninL2)

/-- Unconditional source-relative finite-block lower bound preserving prime--polar--Γ
cancellation. Remaining sign question is positivity of this literal coherent producer,
not separate scalar control of completed error or prime cells. -/
theorem ccmActualHeadCoherentQuantileGammaProducer_le_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadCoherentQuantileGammaProducer a u ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2 * a.1)) + 1
  have hcore := higherGamma_add_outgoingCurrent_ge_coherentProducer a u
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation a u
  dsimp only at hcore hsource
  unfold ccmActualHeadCoherentQuantileGammaProducer
  dsimp only
  rw [hsource]
  nlinarith

end RHTower
