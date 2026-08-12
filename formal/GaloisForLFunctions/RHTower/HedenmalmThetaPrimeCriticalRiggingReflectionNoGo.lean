import GaloisForLFunctions.RHTower.HedenmalmThetaPrimeCriticalRiggedCarrier
import GaloisForLFunctions.RHTower.HedenmalmThetaCompactDivisorEigenmode

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

theorem two_mul_cosh_mul_criticalWeight_le_shift_sum
    {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    2 * Real.cosh L * criticalWeight x ≤
      criticalWeight (x - L) + criticalWeight (x + L) := by
  rcases le_total L |x| with hout | hin
  · rcases le_total 0 x with hx | hx
    · have hxL : L ≤ x := by simpa [abs_of_nonneg hx] using hout
      rw [criticalWeight, criticalWeight, criticalWeight,
        abs_of_nonneg hx, abs_of_nonneg (by linarith : 0 ≤ x - L),
        abs_of_nonneg (by linarith : 0 ≤ x + L), Real.cosh_eq]
      ring_nf
      simp only [Real.exp_add]
      ring_nf
      exact le_rfl
    · have hxL : x ≤ -L := by
        rw [abs_of_nonpos hx] at hout
        linarith
      rw [criticalWeight, criticalWeight, criticalWeight,
        abs_of_nonpos hx, abs_of_nonpos (by linarith : x - L ≤ 0),
        abs_of_nonpos (by linarith : x + L ≤ 0), Real.cosh_eq]
      ring_nf
      rw [show L - x = L + (-x) by ring_nf,
        show -L - x = -L + (-x) by ring_nf]
      simp only [Real.exp_add]
      ring_nf
      exact le_rfl
  · have hdiff : -L ≤ x := by
      have habs : -|x| ≤ x := neg_abs_le x
      linarith
    have hsum : x ≤ L := by
      have habs : x ≤ |x| := le_abs_self x
      linarith
    rcases le_total 0 x with hx | hx
    · rw [criticalWeight, criticalWeight, criticalWeight,
        abs_of_nonneg hx, abs_of_nonpos (by linarith : x - L ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ x + L), Real.cosh_eq]
      ring_nf
      have he : Real.exp (-L + x) ≤ Real.exp (L - x) := by
        apply Real.exp_le_exp.2
        linarith
      rw [show Real.exp (-L) * Real.exp x = Real.exp (-L + x) by
          rw [Real.exp_add]]
      have hcommon : Real.exp L * Real.exp x = Real.exp (L + x) := by
        rw [Real.exp_add]
      rw [hcommon]
      linarith
    · rw [criticalWeight, criticalWeight, criticalWeight,
        abs_of_nonpos hx, abs_of_nonpos (by linarith : x - L ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ x + L), Real.cosh_eq]
      ring_nf
      have he : Real.exp (-L - x) ≤ Real.exp (L + x) := by
        apply Real.exp_le_exp.2
        linarith
      rw [show Real.exp L * Real.exp (-x) = Real.exp (L - x) by
          rw [← Real.exp_add]; congr 1,
        show Real.exp (-L) * Real.exp (-x) = Real.exp (-L - x) by
          rw [← Real.exp_add]; congr 1]
      linarith

def criticalEnergyDensity (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖f x‖ ^ 2 * criticalWeight x

def criticalForwardPulledEnergyDensity (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖f x‖ ^ 2 * criticalWeight (x - L)

def criticalBackwardPulledEnergyDensity (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖f x‖ ^ 2 * criticalWeight (x + L)

def criticalCenteredForwardTranslationEnergy (L : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x, ‖f (x + L)‖ ^ 2 * criticalWeight x

def criticalCenteredBackwardTranslationEnergy (L : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x, ‖f (x - L)‖ ^ 2 * criticalWeight x

theorem criticalCenteredForwardTranslationEnergy_eq_pulled
    (L : ℝ) (f : ℝ → ℂ) :
    criticalCenteredForwardTranslationEnergy L f =
      ∫ x, criticalForwardPulledEnergyDensity L f x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => ‖f y‖ ^ 2 * criticalWeight (y - L)) L
  simpa only [criticalCenteredForwardTranslationEnergy,
    criticalForwardPulledEnergyDensity, add_sub_cancel_right] using h

theorem criticalCenteredBackwardTranslationEnergy_eq_pulled
    (L : ℝ) (f : ℝ → ℂ) :
    criticalCenteredBackwardTranslationEnergy L f =
      ∫ x, criticalBackwardPulledEnergyDensity L f x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => ‖f y‖ ^ 2 * criticalWeight (y + L)) (-L)
  simpa only [criticalCenteredBackwardTranslationEnergy,
    criticalBackwardPulledEnergyDensity, sub_eq_add_neg, add_assoc,
    neg_add_cancel, add_zero] using h

theorem criticalEnergyDensity_hyperbolic_le_shift_sum
    {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℂ) (x : ℝ) :
    2 * Real.cosh L * criticalEnergyDensity f x ≤
      criticalForwardPulledEnergyDensity L f x +
        criticalBackwardPulledEnergyDensity L f x := by
  unfold criticalEnergyDensity criticalForwardPulledEnergyDensity
    criticalBackwardPulledEnergyDensity
  have h := two_mul_cosh_mul_criticalWeight_le_shift_sum hL x
  nlinarith [sq_nonneg ‖f x‖]

theorem integral_criticalEnergyDensity_hyperbolic_le_shift_sum
    {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℂ)
    (hbase : Integrable (criticalEnergyDensity f))
    (hforward : Integrable (criticalForwardPulledEnergyDensity L f))
    (hbackward : Integrable (criticalBackwardPulledEnergyDensity L f)) :
    2 * Real.cosh L * ∫ x, criticalEnergyDensity f x ≤
      (∫ x, criticalForwardPulledEnergyDensity L f x) +
        ∫ x, criticalBackwardPulledEnergyDensity L f x := by
  rw [← integral_const_mul, ← integral_add hforward hbackward]
  apply integral_mono_ae (hbase.const_mul _) (hforward.add hbackward)
  exact Filter.Eventually.of_forall
    (criticalEnergyDensity_hyperbolic_le_shift_sum hL f)

theorem not_both_critical_pulled_energies_contract
    {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hbase : Integrable (criticalEnergyDensity f))
    (hforward : Integrable (criticalForwardPulledEnergyDensity L f))
    (hbackward : Integrable (criticalBackwardPulledEnergyDensity L f))
    (henergy : 0 < ∫ x, criticalEnergyDensity f x) :
    ¬ ((∫ x, criticalForwardPulledEnergyDensity L f x) ≤
          ∫ x, criticalEnergyDensity f x ∧
        (∫ x, criticalBackwardPulledEnergyDensity L f x) ≤
          ∫ x, criticalEnergyDensity f x) := by
  rintro ⟨hforwardLe, hbackwardLe⟩
  have hsum := integral_criticalEnergyDensity_hyperbolic_le_shift_sum
    hL.le f hbase hforward hbackward
  have hcosh : 1 < Real.cosh L := Real.one_lt_cosh.mpr hL.ne'
  nlinarith

theorem criticalWeight_shift_le
    {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    criticalWeight (x - L) ≤ Real.exp L * criticalWeight x := by
  rw [criticalWeight, criticalWeight, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := abs_sub x L
  rw [abs_of_nonneg hL] at h
  linarith

theorem criticalWeight_add_le
    {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    criticalWeight (x + L) ≤ Real.exp L * criticalWeight x := by
  rw [criticalWeight, criticalWeight, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := abs_add_le x L
  rw [abs_of_nonneg hL] at h
  linarith

theorem integrable_criticalForwardPulledEnergyDensity
    {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f)
    (hbase : Integrable (criticalEnergyDensity f)) :
    Integrable (criticalForwardPulledEnergyDensity L f) := by
  refine Integrable.mono' (hbase.const_mul (Real.exp L)) ?_ ?_
  · have hw : Continuous (fun x : ℝ => criticalWeight (x - L)) := by
      unfold criticalWeight
      fun_prop
    exact (hf.norm.pow 2).mul hw.aestronglyMeasurable
  · filter_upwards with x
    unfold criticalForwardPulledEnergyDensity criticalEnergyDensity
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (criticalWeight_pos _).le)]
    nlinarith [criticalWeight_shift_le hL x, sq_nonneg ‖f x‖]

theorem integrable_criticalBackwardPulledEnergyDensity
    {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f)
    (hbase : Integrable (criticalEnergyDensity f)) :
    Integrable (criticalBackwardPulledEnergyDensity L f) := by
  refine Integrable.mono' (hbase.const_mul (Real.exp L)) ?_ ?_
  · have hw : Continuous (fun x : ℝ => criticalWeight (x + L)) := by
      unfold criticalWeight
      fun_prop
    exact (hf.norm.pow 2).mul hw.aestronglyMeasurable
  · filter_upwards with x
    unfold criticalBackwardPulledEnergyDensity criticalEnergyDensity
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (criticalWeight_pos _).le)]
    nlinarith [criticalWeight_add_le hL x, sq_nonneg ‖f x‖]

theorem criticalWeight_mul_thetaSource_le_thetaBound (x : ℝ) :
    criticalWeight x * thetaSource.k x ≤ thetaBound := by
  have hk := abs_thetaCuspFullSource_le x
  rw [abs_of_pos (thetaCuspFullSource_pos_all x)] at hk
  rw [criticalWeight, thetaSource_k]
  calc
    Real.exp |x| * thetaCuspFullSource x ≤
        Real.exp |x| * (thetaBound * Real.exp (-|x|)) :=
      mul_le_mul_of_nonneg_left hk (Real.exp_nonneg _)
    _ = thetaBound := by
      rw [show Real.exp |x| * (thetaBound * Real.exp (-|x|)) =
          thetaBound * (Real.exp |x| * Real.exp (-|x|)) by ring,
        ← Real.exp_add]
      simp

theorem continuous_criticalEnergyDensity_sourceModeF
    {z : ℂ} (hz : |z.im| < 1) :
    Continuous (criticalEnergyDensity (sourceModeF thetaSource z)) := by
  unfold criticalEnergyDensity criticalWeight
  unfold sourceModeF
  exact ((continuous_const.mul (continuous_sourceModeU hz)).norm.pow 2).mul (by fun_prop)

theorem integrable_criticalEnergyDensity_sourceModeF
    {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    Integrable (criticalEnergyDensity (sourceModeF thetaSource z)) := by
  have hweighted := integrable_sourceModeFWeightedEnergyDensity hz hzero
  refine Integrable.mono' (hweighted.const_mul thetaBound)
    (continuous_criticalEnergyDensity_sourceModeF hz).aestronglyMeasurable ?_
  filter_upwards with x
  unfold criticalEnergyDensity sourceModeFWeightedEnergyDensity
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (criticalWeight_pos _).le)]
  have hk : 0 < thetaSource.k x := thetaSource.pos_k x
  have hweight := criticalWeight_mul_thetaSource_le_thetaBound x
  have hsq : 0 ≤ ‖sourceModeF thetaSource z x‖ ^ 2 := sq_nonneg _
  rw [show ‖sourceModeF thetaSource z x‖ ^ 2 * criticalWeight x =
      (‖sourceModeF thetaSource z x‖ ^ 2 / thetaSource.k x) *
        (criticalWeight x * thetaSource.k x) by field_simp]
  have hdiv : 0 ≤ ‖sourceModeF thetaSource z x‖ ^ 2 / thetaSource.k x :=
    div_nonneg hsq hk.le
  nlinarith

theorem integral_criticalEnergyDensity_sourceModeF_pos
    {z : ℂ} (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    0 < ∫ x, criticalEnergyDensity (sourceModeF thetaSource z) x := by
  let f : ℝ → ℂ := sourceModeF thetaSource z
  have hfint := integrable_criticalEnergyDensity_sourceModeF hz hzero
  have hnonneg : ∀ x, 0 ≤ criticalEnergyDensity f x := fun x =>
    mul_nonneg (sq_nonneg _) (criticalWeight_pos x).le
  have htotal := integral_sourceModeF_thetaSource_eq_mass hz hzero
  have hmass : (thetaSource.mass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
  have hnotzero : ¬ f =ᵐ[volume] 0 := by
    intro hfzero
    have hintzero : (∫ x, f x) = 0 := by
      rw [integral_congr_ae hfzero]
      simp
    exact hmass (htotal ▸ hintzero)
  have hdensityNotZero : ¬ criticalEnergyDensity f =ᵐ[volume] 0 := by
    intro hzeroDensity
    apply hnotzero
    filter_upwards [hzeroDensity] with x hx
    unfold criticalEnergyDensity at hx
    have hweight : criticalWeight x ≠ 0 := (criticalWeight_pos x).ne'
    have hnorm : ‖f x‖ ^ 2 = 0 := (mul_eq_zero.mp hx).resolve_right hweight
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hne : (∫ x, criticalEnergyDensity f x) ≠ 0 := by
    exact fun heq => hdensityNotZero
      ((integral_eq_zero_iff_of_nonneg hnonneg hfint).mp heq)
  exact lt_of_le_of_ne (integral_nonneg hnonneg) hne.symm

def criticalConjReflection (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (f (-x))

theorem criticalEnergyDensity_conjReflection (f : ℝ → ℂ) (x : ℝ) :
    criticalEnergyDensity (criticalConjReflection f) x =
      criticalEnergyDensity f (-x) := by
  unfold criticalEnergyDensity criticalConjReflection criticalWeight
  rw [RCLike.norm_conj, abs_neg]

theorem criticalForwardPulledEnergyDensity_conjReflection
    (L : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    criticalForwardPulledEnergyDensity L (criticalConjReflection f) x =
      criticalBackwardPulledEnergyDensity L f (-x) := by
  unfold criticalForwardPulledEnergyDensity criticalBackwardPulledEnergyDensity
    criticalConjReflection criticalWeight
  rw [RCLike.norm_conj]
  congr 1
  rw [show -x + L = -(x - L) by ring, abs_neg]

theorem integral_criticalEnergyDensity_conjReflection (f : ℝ → ℂ) :
    (∫ x, criticalEnergyDensity (criticalConjReflection f) x) =
      ∫ x, criticalEnergyDensity f x := by
  rw [show (fun x => criticalEnergyDensity (criticalConjReflection f) x) =
      fun x => criticalEnergyDensity f (-x) by
    funext x
    exact criticalEnergyDensity_conjReflection f x]
  exact integral_neg_eq_self _ volume

theorem integral_criticalForwardPulledEnergyDensity_conjReflection
    (L : ℝ) (f : ℝ → ℂ) :
    (∫ x, criticalForwardPulledEnergyDensity L (criticalConjReflection f) x) =
      ∫ x, criticalBackwardPulledEnergyDensity L f x := by
  rw [show (fun x =>
      criticalForwardPulledEnergyDensity L (criticalConjReflection f) x) =
      fun x => criticalBackwardPulledEnergyDensity L f (-x) by
    funext x
    exact criticalForwardPulledEnergyDensity_conjReflection L f x]
  exact integral_neg_eq_self _ volume

theorem sourceModeF_xiSpectralPoint_lineConj_eq_criticalConjReflection
    (q : XiZeroCopy) :
    sourceModeF thetaSource (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) =
      criticalConjReflection (sourceModeF thetaSource (xiSpectralPoint q)) := by
  funext x
  rw [xiSpectralPoint_lineConj, criticalConjReflection]
  let z : ℂ := (starRingEnd ℂ) (xiSpectralPoint q)
  have hz : |z.im| < 1 := by
    dsimp [z]
    rw [abs_neg]
    exact thetaXiSpectralPoint_mem_sourceStrip q
  have hzero : xiC thetaSource z = 0 := by
    dsimp [z]
    rw [← xiSpectralPoint_lineConj]
    exact xiC_thetaSource_xiSpectralPoint_eq_zero (xiZeroCopyLineConjEquiv q)
  calc
    sourceModeF thetaSource z x =
        sourceModeF thetaSource (-z) (-x) :=
      (sourceModeF_neg thetaSource thetaSource_even
        (hasShiftedTail_thetaSource hz) hzero x).symm
    _ = (starRingEnd ℂ)
          (sourceModeF thetaSource (xiSpectralPoint q) (-x)) := by
      rw [conj_sourceModeF]

def criticalXiSourceModeEnergy (q : XiZeroCopy) : ℝ :=
  ∫ x, criticalEnergyDensity (sourceModeF thetaSource (xiSpectralPoint q)) x

def criticalXiSourceModeForwardEnergy (L : ℝ) (q : XiZeroCopy) : ℝ :=
  criticalCenteredForwardTranslationEnergy L
    (sourceModeF thetaSource (xiSpectralPoint q))

theorem criticalXiSourceModeEnergy_lineConj (q : XiZeroCopy) :
    criticalXiSourceModeEnergy (xiZeroCopyLineConjEquiv q) =
      criticalXiSourceModeEnergy q := by
  rw [criticalXiSourceModeEnergy, criticalXiSourceModeEnergy,
    sourceModeF_xiSpectralPoint_lineConj_eq_criticalConjReflection,
    integral_criticalEnergyDensity_conjReflection]

theorem criticalXiSourceModeForwardEnergy_lineConj_eq_backward
    (L : ℝ) (q : XiZeroCopy) :
    criticalXiSourceModeForwardEnergy L (xiZeroCopyLineConjEquiv q) =
      criticalCenteredBackwardTranslationEnergy L
        (sourceModeF thetaSource (xiSpectralPoint q)) := by
  rw [criticalXiSourceModeForwardEnergy,
    criticalCenteredForwardTranslationEnergy_eq_pulled,
    sourceModeF_xiSpectralPoint_lineConj_eq_criticalConjReflection,
    integral_criticalForwardPulledEnergyDensity_conjReflection,
    criticalCenteredBackwardTranslationEnergy_eq_pulled]

theorem criticalXiSourceModeEnergy_pos (q : XiZeroCopy) :
    0 < criticalXiSourceModeEnergy q := by
  exact integral_criticalEnergyDensity_sourceModeF_pos
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)

/-- Reflection-paired canonical Xi response modes cannot both be contractive under the centered
forward translation in the critical rigging.  Hence the missing Route-P half-density gain cannot
come from any diagonal positive-norm realization on these source modes. -/
theorem not_both_criticalXiSourceModeForwardEnergy_le
    {L : ℝ} (hL : 0 < L) (q : XiZeroCopy) :
    ¬ (criticalXiSourceModeForwardEnergy L q ≤ criticalXiSourceModeEnergy q ∧
        criticalXiSourceModeForwardEnergy L (xiZeroCopyLineConjEquiv q) ≤
          criticalXiSourceModeEnergy (xiZeroCopyLineConjEquiv q)) := by
  let f : ℝ → ℂ := sourceModeF thetaSource (xiSpectralPoint q)
  have hz := thetaXiSpectralPoint_mem_sourceStrip q
  have hzero := xiC_thetaSource_xiSpectralPoint_eq_zero q
  have hbase := integrable_criticalEnergyDensity_sourceModeF hz hzero
  have hf : AEStronglyMeasurable f := by
    dsimp [f]
    unfold sourceModeF
    exact (continuous_const.mul (continuous_sourceModeU hz)).aestronglyMeasurable
  have hforward := integrable_criticalForwardPulledEnergyDensity hL.le hf hbase
  have hbackward := integrable_criticalBackwardPulledEnergyDensity hL.le hf hbase
  have hno := not_both_critical_pulled_energies_contract hL f
    hbase hforward hbackward
    (integral_criticalEnergyDensity_sourceModeF_pos hz hzero)
  rw [criticalXiSourceModeForwardEnergy, criticalXiSourceModeEnergy,
    criticalCenteredForwardTranslationEnergy_eq_pulled,
    criticalXiSourceModeForwardEnergy_lineConj_eq_backward,
    criticalCenteredBackwardTranslationEnergy_eq_pulled,
    criticalXiSourceModeEnergy_lineConj]
  exact hno

end HedenmalmThetaSource
end
end RHTower
