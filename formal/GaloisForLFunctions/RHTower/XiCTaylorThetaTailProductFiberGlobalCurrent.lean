import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCenteredSeam
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteArithmeticEndpoint

/-!
# Global product-fibre current of the exact canonical theta density

The positive-half-line phase transform of each exact square-index density atom is absolutely
summable, as is its spectral derivative.  Consequently the full canonical phase current is the
absolutely convergent sum of the actual Hermitian currents on the positive product fibres.

This is the global companion of the common-centre seam decomposition: it retains the ordered
value--derivative polarization and introduces no pointwise sign or absolute-value replacement into
the current itself.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_phase
    (n : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        spectralTranslationPhase x z) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ 0) (Ioi 0) :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower n 0
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ 0)
      (volume.restrict (Ioi 0)) at hbase
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
      spectralTranslationPhase x z) (volume.restrict (Ioi 0))
  apply hbase.mono
  · have hphase : Continuous (fun x : ℝ => spectralTranslationPhase x z) := by
      unfold spectralTranslationPhase
      fun_prop
    convert hbase.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict using 1
    funext x
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hphase := norm_spectralTranslationPhase_le_one hx.le hz
    simpa only [pow_zero, mul_one, norm_mul, norm_one, mul_one] using
      mul_le_mul_of_nonneg_left hphase
        (norm_nonneg (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ))

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_phaseDerivative
    (n : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  have hbase :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower n 1
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ 1)
      (volume.restrict (Ioi 0)) at hbase
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z))
        (volume.restrict (Ioi 0))
  apply hbase.mono
  · have hphase : Continuous (fun x : ℝ => I * spectralTranslationPhase x z) := by
      unfold spectralTranslationPhase
      fun_prop
    convert hbase.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict using 1
    funext x
    simp only [pow_one, Pi.mul_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hphase := norm_spectralTranslationPhase_le_one hx.le hz
    simp only [norm_mul, norm_I, mul_one]
    have hxpow : ‖(x : ℂ)‖ * ‖spectralTranslationPhase x z‖ ≤
        ‖(x : ℂ) ^ 1‖ := by
      simpa only [pow_one] using
        mul_le_of_le_one_right (norm_nonneg (x : ℂ)) hphase
    exact mul_le_mul_of_nonneg_left
      hxpow
      (norm_nonneg (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ))

theorem norm_thetaCuspTailSecondDensityAtomPhase_le_moment
    (n : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖thetaCuspTailSecondDensityAtomPhase (n + 1) z‖ ≤
      thetaCuspTailSecondDensityAtomMoment (n + 1) 0 := by
  unfold thetaCuspTailSecondDensityAtomPhase
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          spectralTranslationPhase x z‖ ≤
        ∫ x : ℝ in Ioi 0, thetaCuspTailSecondDensityAtom (n + 1) x := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        (integrableOn_pow_mul_thetaCuspTailSecondDensityAtom 0 (Nat.succ_pos n) |>.congr
          (ae_of_all _ fun x => by simp))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hatom := (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx.le).le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hatom]
      exact mul_le_of_le_one_right hatom
        (norm_spectralTranslationPhase_le_one hx.le hz)
    _ = thetaCuspTailSecondDensityAtomMoment (n + 1) 0 := by
      unfold thetaCuspTailSecondDensityAtomMoment
      simp

theorem norm_thetaCuspTailSecondDensityAtomPhaseDerivative_le_moment
    (n : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z‖ ≤
      thetaCuspTailSecondDensityAtomMoment (n + 1) 1 := by
  unfold thetaCuspTailSecondDensityAtomPhaseDerivative
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z)‖ ≤
        ∫ x : ℝ in Ioi 0, x * thetaCuspTailSecondDensityAtom (n + 1) x := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        (integrableOn_pow_mul_thetaCuspTailSecondDensityAtom 1 (Nat.succ_pos n) |>.congr
          (ae_of_all _ fun x => by simp))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hatom := (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx0).le
      have hphase := norm_spectralTranslationPhase_le_one hx0 hz
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hatom,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
        norm_I, mul_one]
      calc
        thetaCuspTailSecondDensityAtom (n + 1) x *
            (x * ‖spectralTranslationPhase x z‖) ≤
            thetaCuspTailSecondDensityAtom (n + 1) x * x := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right hx0 hphase) hatom
        _ = x * thetaCuspTailSecondDensityAtom (n + 1) x := by ring
    _ = thetaCuspTailSecondDensityAtomMoment (n + 1) 1 := by
      unfold thetaCuspTailSecondDensityAtomMoment
      simp

theorem summable_thetaCuspTailSecondDensityAtomPhase
    {z : ℂ} (hz : 0 ≤ z.im) :
    Summable (fun n : ℕ => thetaCuspTailSecondDensityAtomPhase (n + 1) z) := by
  exact Summable.of_norm_bounded
    (summable_thetaCuspTailSecondDensityAtomMoment 0)
    (fun n => norm_thetaCuspTailSecondDensityAtomPhase_le_moment n hz)

theorem summable_thetaCuspTailSecondDensityAtomPhaseDerivative
    {z : ℂ} (hz : 0 ≤ z.im) :
    Summable (fun n : ℕ =>
      thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z) := by
  exact Summable.of_norm_bounded
    (summable_thetaCuspTailSecondDensityAtomMoment 1)
    (fun n => norm_thetaCuspTailSecondDensityAtomPhaseDerivative_le_moment n hz)

theorem thetaCuspTailSecondDensityFiniteAtomPhaseValue_eq_sum
    (M : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityFiniteAtomPhaseValue M z =
      ∑ n ∈ Finset.range M, thetaCuspTailSecondDensityAtomPhase (n + 1) z := by
  unfold thetaCuspTailSecondDensityFiniteAtomPhaseValue
    thetaCuspTailSecondDensityFiniteAtomSource
  rw [show (fun x : ℝ =>
      ((∑ n ∈ Finset.range M, thetaCuspTailSecondDensityAtom (n + 1) x : ℝ) : ℂ) *
        spectralTranslationPhase x z) =
      fun x : ℝ => ∑ n ∈ Finset.range M,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          spectralTranslationPhase x z by
    funext x
    push_cast
    simp only [Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum]
  · rfl
  · intro n _hn
    exact integrableOn_thetaCuspTailSecondDensityAtom_mul_phase n hz

theorem thetaCuspTailSecondDensityFiniteAtomPhaseDerivative_eq_sum
    (M : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z =
      ∑ n ∈ Finset.range M,
        thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z := by
  unfold thetaCuspTailSecondDensityFiniteAtomPhaseDerivative
    thetaCuspTailSecondDensityFiniteAtomSource
  rw [show (fun x : ℝ =>
      ((∑ n ∈ Finset.range M, thetaCuspTailSecondDensityAtom (n + 1) x : ℝ) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) =
      fun x : ℝ => ∑ n ∈ Finset.range M,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z) by
    funext x
    push_cast
    simp only [Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum]
  · rfl
  · intro n _hn
    exact integrableOn_thetaCuspTailSecondDensityAtom_mul_phaseDerivative n hz

theorem tsum_thetaCuspTailSecondDensityAtomPhase_eq_full
    {z : ℂ} (hz : 0 ≤ z.im) :
    (∑' n : ℕ, thetaCuspTailSecondDensityAtomPhase (n + 1) z) =
      thetaCuspTailSecondDensityPhaseValue z := by
  have hsum := (summable_thetaCuspTailSecondDensityAtomPhase hz).hasSum.tendsto_sum_nat
  have hfinite : Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M,
        thetaCuspTailSecondDensityAtomPhase (n + 1) z)
      atTop (nhds (thetaCuspTailSecondDensityPhaseValue z)) := by
    rw [show (fun M : ℕ => ∑ n ∈ Finset.range M,
        thetaCuspTailSecondDensityAtomPhase (n + 1) z) =
        fun M : ℕ => thetaCuspTailSecondDensityFiniteAtomPhaseValue M z by
      funext M
      exact (thetaCuspTailSecondDensityFiniteAtomPhaseValue_eq_sum M hz).symm]
    exact tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseValue hz
  exact tendsto_nhds_unique hsum hfinite

theorem tsum_thetaCuspTailSecondDensityAtomPhaseDerivative_eq_full
    {z : ℂ} (hz : 0 ≤ z.im) :
    (∑' n : ℕ, thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z) =
      thetaCuspTailSecondDensityPhaseDerivative z := by
  have hsum :=
    (summable_thetaCuspTailSecondDensityAtomPhaseDerivative hz).hasSum.tendsto_sum_nat
  have hfinite : Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M,
        thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z)
      atTop (nhds (thetaCuspTailSecondDensityPhaseDerivative z)) := by
    rw [show (fun M : ℕ => ∑ n ∈ Finset.range M,
        thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z) =
        fun M : ℕ => thetaCuspTailSecondDensityFiniteAtomPhaseDerivative M z by
      funext M
      exact (thetaCuspTailSecondDensityFiniteAtomPhaseDerivative_eq_sum M hz).symm]
    exact tendsto_thetaCuspTailSecondDensityFiniteAtomPhaseDerivative hz
  exact tendsto_nhds_unique hsum hfinite

/-- Ordered Hermitian atom-pair coefficient before taking its oriented current. -/
def thetaCuspTailSecondDensityAtomPhasePairCorrelation
    (z : ℂ) (q : ℕ × ℕ) : ℂ :=
  thetaCuspTailSecondDensityAtomPhaseDerivative (q.1 + 1) z *
    (starRingEnd ℂ) (thetaCuspTailSecondDensityAtomPhase (q.2 + 1) z)

theorem summable_thetaCuspTailSecondDensityAtomPhasePairCorrelation
    {z : ℂ} (hz : 0 ≤ z.im) :
    Summable (thetaCuspTailSecondDensityAtomPhasePairCorrelation z) := by
  have hD := summable_thetaCuspTailSecondDensityAtomPhaseDerivative hz
  have hV := summable_thetaCuspTailSecondDensityAtomPhase hz
  have hstar : Summable (fun n : ℕ =>
      ‖(starRingEnd ℂ) (thetaCuspTailSecondDensityAtomPhase (n + 1) z)‖) := by
    simpa using hV.norm
  refine (summable_mul_of_summable_norm hD.norm hstar).congr fun q => ?_
  rfl

theorem summable_thetaProductFiberActualPhaseCurrent
    {z : ℂ} (hz : 0 ≤ z.im) :
    Summable (fun k : ℕ => thetaProductFiberActualPhaseCurrent k z) := by
  have hpair : Summable (fun q : ℕ × ℕ =>
      (thetaCuspTailSecondDensityAtomPhasePairCorrelation z q).im) := by
    have hm := (summable_thetaCuspTailSecondDensityAtomPhasePairCorrelation hz).map
      Complex.imCLM Complex.imCLM.continuous
    simpa only [Function.comp_def, Complex.imCLM_apply] using hm
  have hfiber := hpair.hasSum.tsum_fiberwise thetaPositivePairProduct
  rw [show (fun k : ℕ => thetaProductFiberActualPhaseCurrent k z) =
      fun k : ℕ => ∑' q : thetaPositivePairProduct ⁻¹' {k},
        (thetaCuspTailSecondDensityAtomPhasePairCorrelation z q).im by
    funext k
    rw [thetaPositivePairProduct_fiber]
    exact (Finset.tsum_subtype' (thetaPositiveFactorPairs k)
      (fun q => (thetaCuspTailSecondDensityAtomPhasePairCorrelation z q).im)).symm]
  exact hfiber.summable

/-- **Global exact product-fibre bridge.**  The current of the full canonical density phase is the
absolutely convergent sum of the actual Hermitian product-fibre currents. -/
theorem thetaCuspTailSecondDensityPhase_current_eq_tsum_productFiberActualPhaseCurrent
    {z : ℂ} (hz : 0 ≤ z.im) :
    (thetaCuspTailSecondDensityPhaseDerivative z *
        (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im =
      ∑' k : ℕ, thetaProductFiberActualPhaseCurrent k z := by
  have hD := summable_thetaCuspTailSecondDensityAtomPhaseDerivative hz
  have hV := summable_thetaCuspTailSecondDensityAtomPhase hz
  have hstar : Summable (fun n : ℕ =>
      ‖(starRingEnd ℂ) (thetaCuspTailSecondDensityAtomPhase (n + 1) z)‖) := by
    simpa using hV.norm
  have hpair := summable_thetaCuspTailSecondDensityAtomPhasePairCorrelation hz
  rw [← tsum_thetaCuspTailSecondDensityAtomPhaseDerivative_eq_full hz,
    ← tsum_thetaCuspTailSecondDensityAtomPhase_eq_full hz,
    Complex.conj_tsum,
    tsum_mul_tsum_of_summable_norm hD.norm hstar]
  change (∑' q : ℕ × ℕ,
      thetaCuspTailSecondDensityAtomPhasePairCorrelation z q).im = _
  rw [Complex.im_tsum hpair]
  exact tsum_eq_tsum_thetaPositiveFactorPairs
    (fun q : ℕ × ℕ =>
      (thetaCuspTailSecondDensityAtomPhasePairCorrelation z q).im)
    (by
      have hm := hpair.map Complex.imCLM Complex.imCLM.continuous
      simpa only [Function.comp_def, Complex.imCLM_apply] using hm)

end

end RHTower
