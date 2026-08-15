import GaloisForLFunctions.RHTower.CCMUnitRieszCesaroCurvature
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroCompleteness

/-!
# Literal FU--UR curvature transport

The completed-error unit-Riesz response is exactly the curvature pairing of the actual CCM-FU
Cesàro primitive.  The proof uses the finite prime-polar Stieltjes flux identity, then two genuine
absolutely-continuous integrations by parts.  It never differentiates or smooths the prime
staircase.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitRieszCompletedSourceTestReal (t s : ℝ) : ℝ :=
  3 * (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s))

def unitRieszCompletedSourceTestDerivReal (t s : ℝ) : ℝ :=
  (3 / 2) * Real.exp (-t + s / 2) -
    3 * Real.exp (-3 * t / 2 + s)

theorem hasDerivAt_unitRieszCompletedSourceTestReal (t s : ℝ) :
    HasDerivAt (unitRieszCompletedSourceTestReal t)
      (unitRieszCompletedSourceTestDerivReal t s) s := by
  have h₁ : HasDerivAt (fun x : ℝ => Real.exp (-t + x / 2))
      ((1 / 2 : ℝ) * Real.exp (-t + s / 2)) s := by
    simpa only [Function.comp_def, id_eq, mul_comm] using
      (Real.hasDerivAt_exp (-t + s / 2)).comp s
        (((hasDerivAt_id s).div_const 2).const_add (-t))
  have h₂ : HasDerivAt (fun x : ℝ => Real.exp (-3 * t / 2 + x))
      (Real.exp (-3 * t / 2 + s)) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (-3 * t / 2 + s)).comp s
        ((hasDerivAt_id s).const_add (-3 * t / 2))
  unfold unitRieszCompletedSourceTestReal unitRieszCompletedSourceTestDerivReal
  have h := (h₁.sub h₂).mul_const 3
  have hd :
      (((1 / 2 : ℝ) * Real.exp (-t + s / 2) -
          Real.exp (-3 * t / 2 + s)) * 3) =
        (3 / 2) * Real.exp (-t + s / 2) -
          3 * Real.exp (-3 * t / 2 + s) := by
    ring
  simpa only [Pi.sub_apply, mul_comm] using h.congr_deriv hd

theorem unitRieszThirdGrade_mul_cesaroTest
    {t s : ℝ} (hs : s ≠ 0) :
    ccmGuinandWeilThirdGradeWeight s * unitRieszCesaroTest t s =
      unitRieszCompletedSourceTestReal t s := by
  rw [ccmGuinandWeilThirdGradeWeight, unitRieszCesaroTest,
    unitRieszCompletedSourceTestReal]
  field_simp [hs]

theorem unitRieszThirdGrade_productDeriv
    {t s : ℝ} (hs : s ≠ 0) :
    ccmGuinandWeilThirdGradeWeight s * unitRieszCesaroTestDeriv t s +
        ccmGuinandWeilThirdGradeWeightDeriv s * unitRieszCesaroTest t s =
      unitRieszCompletedSourceTestDerivReal t s := by
  rw [ccmGuinandWeilThirdGradeWeight, ccmGuinandWeilThirdGradeWeightDeriv,
    unitRieszCesaroTest, unitRieszCesaroTestDeriv,
    unitRieszCompletedSourceTestDerivReal]
  field_simp [hs]
  ring

theorem intervalIntegrable_criticalMellinCompletedError_on_Icc
    {b t : ℝ} (hbt : b ≤ t) :
    IntervalIntegrable criticalMellinCompletedError volume b t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hbt]
  rw [show criticalMellinCompletedError = fun s : ℝ =>
      4 * Real.sinh (s / 2) - criticalMellinPrimeMass s by
    funext s
    exact criticalMellinCompletedError_eq_polar_sub_primeMass s]
  apply IntegrableOn.sub
  · exact (continuous_const.mul
      (Real.continuous_sinh.comp
        (continuous_id.div_const 2))).continuousOn.integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
  · exact integrableOn_criticalMellinPrimeMass_Ioc

/-- Literal FU source equals completed-error endpoint plus completed-error flux at every positive
upper wall. -/
theorem thirdGradeCumulative_eq_completedErrorFlux
    {b s : ℝ} (hb : 0 < b) (hbs : b ≤ s) :
    ccmGuinandWeilThirdGradeCumulativeMeasurable b s =
      ccmGuinandWeilThirdGradeWeight b * criticalMellinCompletedError b -
        ccmGuinandWeilThirdGradeWeight s * criticalMellinCompletedError s +
          ∫ v in b..s,
            criticalMellinCompletedError v *
              ccmGuinandWeilThirdGradeWeightDeriv v := by
  rw [ccmGuinandWeilThirdGradeCumulativeMeasurable_eq_primePolar hbs,
    ccmGuinandWeilThirdGradePrimePolarWindow_eq_completedErrorFlux hb hbs]

/-- Exact first Abel transform from the literal FU cumulative source to the completed-error
unit-Riesz response. Prime jumps enter only through the established Stieltjes flux law. -/
theorem unitRieszCesaro_actualSource_firstIntegrationByParts
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    (∫ s in b..t,
        ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
          unitRieszCesaroTestDeriv t s) =
      -criticalMellinCompletedError b *
          unitRieszCompletedSourceTestReal t b -
        ∫ s in b..t,
          criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s := by
  let A : ℝ → ℝ := fun s =>
    ∫ v in b..s,
      criticalMellinCompletedError v *
        ccmGuinandWeilThirdGradeWeightDeriv v
  have hEInt : IntervalIntegrable criticalMellinCompletedError volume b t :=
    intervalIntegrable_criticalMellinCompletedError_on_Icc hbt
  have hwCont : ContinuousOn ccmGuinandWeilThirdGradeWeight (Set.Icc b t) := by
    intro s hs
    exact (hasDerivAt_ccmGuinandWeilThirdGradeWeight
      (ne_of_gt (hb.trans_le hs.1))).continuousAt.continuousWithinAt
  have hwdCont : ContinuousOn ccmGuinandWeilThirdGradeWeightDeriv
      (Set.Icc b t) := by
    intro s hs
    unfold ccmGuinandWeilThirdGradeWeightDeriv
    exact (continuousAt_const.div (continuousAt_id.pow 4)
      (pow_ne_zero 4 (ne_of_gt (hb.trans_le hs.1)))).continuousWithinAt
  have hwContU : ContinuousOn ccmGuinandWeilThirdGradeWeight (Set.uIcc b t) := by
    simpa only [Set.uIcc_of_le hbt] using hwCont
  have hwdContU : ContinuousOn ccmGuinandWeilThirdGradeWeightDeriv
      (Set.uIcc b t) := by
    simpa only [Set.uIcc_of_le hbt] using hwdCont
  have hEwInt : IntervalIntegrable
      (fun s => criticalMellinCompletedError s *
        ccmGuinandWeilThirdGradeWeight s) volume b t :=
    hEInt.mul_continuousOn hwContU
  have hEwdInt : IntervalIntegrable
      (fun s => criticalMellinCompletedError s *
        ccmGuinandWeilThirdGradeWeightDeriv s) volume b t :=
    hEInt.mul_continuousOn hwdContU
  have hgdCont : Continuous (unitRieszCesaroTestDeriv t) := by
    unfold unitRieszCesaroTestDeriv
    fun_prop
  have hgCont : Continuous (unitRieszCesaroTest t) := by
    unfold unitRieszCesaroTest
    fun_prop
  have hgdInt : IntervalIntegrable (unitRieszCesaroTestDeriv t) volume b t :=
    hgdCont.intervalIntegrable b t
  have hgcd : ContDiff ℝ 1 (unitRieszCesaroTest t) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨?_, ?_⟩
    · intro s
      exact (hasDerivAt_unitRieszCesaroTest t s).differentiableAt
    · apply hgdCont.congr
      intro s
      exact (hasDerivAt_unitRieszCesaroTest t s).deriv.symm
  have hgac : AbsolutelyContinuousOnInterval (unitRieszCesaroTest t) b t :=
    hgcd.contDiffOn.absolutelyContinuousOnInterval
  have hAac : AbsolutelyContinuousOnInterval A b t := by
    exact hEwdInt.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b t by simp [hbt])
  have hAb : A b = 0 := by simp [A]
  have hgt : unitRieszCesaroTest t t = 0 := by
    rw [unitRieszCesaroTest]
    have he : Real.exp (-t + t / 2) = Real.exp (-3 * t / 2 + t) := by
      congr 1
      ring
    rw [he]
    ring
  have hAibp :
      (∫ s in b..t, A s * unitRieszCesaroTestDeriv t s) =
        -(∫ s in b..t,
          (criticalMellinCompletedError s *
            ccmGuinandWeilThirdGradeWeightDeriv s) *
              unitRieszCesaroTest t s) := by
    have hibp := hAac.integral_mul_deriv_eq_deriv_mul hgac
    have hleft : (∫ s in b..t, A s * deriv (unitRieszCesaroTest t) s) =
        ∫ s in b..t, A s * unitRieszCesaroTestDeriv t s := by
      apply intervalIntegral.integral_congr
      intro s _
      change A s * deriv (unitRieszCesaroTest t) s =
        A s * unitRieszCesaroTestDeriv t s
      rw [(hasDerivAt_unitRieszCesaroTest t s).deriv]
    have hright :
        (∫ s in b..t, deriv A s * unitRieszCesaroTest t s) =
          ∫ s in b..t,
            (criticalMellinCompletedError s *
              ccmGuinandWeilThirdGradeWeightDeriv s) *
                unitRieszCesaroTest t s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hEwdInt.ae_hasDerivAt_integral] with s hs hmem
      have hd : HasDerivAt A
          (criticalMellinCompletedError s *
            ccmGuinandWeilThirdGradeWeightDeriv s) s :=
        hs (uIoc_subset_uIcc hmem) b (by simp [hbt])
      rw [hd.deriv]
    rw [hleft, hright, hAb, hgt] at hibp
    simpa using hibp
  have hFTC :
      (∫ s in b..t, unitRieszCesaroTestDeriv t s) =
        -unitRieszCesaroTest t b := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_unitRieszCesaroTest t s) hgdInt
    rw [hgt] at h
    simpa using h
  have hEwgdInt : IntervalIntegrable
      (fun s => (criticalMellinCompletedError s *
        ccmGuinandWeilThirdGradeWeight s) *
          unitRieszCesaroTestDeriv t s) volume b t :=
    hEwInt.mul_continuousOn hgdCont.continuousOn
  have hEwdgInt : IntervalIntegrable
      (fun s => (criticalMellinCompletedError s *
        ccmGuinandWeilThirdGradeWeightDeriv s) *
          unitRieszCesaroTest t s) volume b t :=
    hEwdInt.mul_continuousOn hgCont.continuousOn
  have hAgdInt : IntervalIntegrable
      (fun s => A s * unitRieszCesaroTestDeriv t s) volume b t :=
    (hAac.continuousOn.mul hgdCont.continuousOn).intervalIntegrable
  have hqexpand :
      (∫ s in b..t,
          ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
            unitRieszCesaroTestDeriv t s) =
        ccmGuinandWeilThirdGradeWeight b *
            criticalMellinCompletedError b *
              (∫ s in b..t, unitRieszCesaroTestDeriv t s) -
          (∫ s in b..t,
            (criticalMellinCompletedError s *
              ccmGuinandWeilThirdGradeWeight s) *
                unitRieszCesaroTestDeriv t s) +
          ∫ s in b..t, A s * unitRieszCesaroTestDeriv t s := by
    calc
      (∫ s in b..t,
          ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
            unitRieszCesaroTestDeriv t s) =
          ∫ s in b..t,
            ((ccmGuinandWeilThirdGradeWeight b *
                criticalMellinCompletedError b) *
                  unitRieszCesaroTestDeriv t s -
              (criticalMellinCompletedError s *
                ccmGuinandWeilThirdGradeWeight s) *
                  unitRieszCesaroTestDeriv t s) +
              A s * unitRieszCesaroTestDeriv t s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hbt] at hs
        change ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
            unitRieszCesaroTestDeriv t s = _
        rw [thirdGradeCumulative_eq_completedErrorFlux hb hs.1]
        dsimp only [A]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hgdInt.const_mul
            (ccmGuinandWeilThirdGradeWeight b *
              criticalMellinCompletedError b)).sub hEwgdInt) hAgdInt,
          intervalIntegral.integral_sub
            (hgdInt.const_mul
              (ccmGuinandWeilThirdGradeWeight b *
                criticalMellinCompletedError b)) hEwgdInt,
          intervalIntegral.integral_const_mul]
  have hcompletedProduct :
      (∫ s in b..t,
          criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s) =
        (∫ s in b..t,
          (criticalMellinCompletedError s *
            ccmGuinandWeilThirdGradeWeight s) *
              unitRieszCesaroTestDeriv t s) +
        ∫ s in b..t,
          (criticalMellinCompletedError s *
            ccmGuinandWeilThirdGradeWeightDeriv s) *
              unitRieszCesaroTest t s := by
    calc
      (∫ s in b..t,
          criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s) =
          ∫ s in b..t,
            ((criticalMellinCompletedError s *
              ccmGuinandWeilThirdGradeWeight s) *
                unitRieszCesaroTestDeriv t s +
            (criticalMellinCompletedError s *
              ccmGuinandWeilThirdGradeWeightDeriv s) *
                unitRieszCesaroTest t s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hbt] at hs
        change criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s = _
        rw [← unitRieszThirdGrade_productDeriv
          (ne_of_gt (hb.trans_le hs.1))]
        ring
      _ = _ := intervalIntegral.integral_add hEwgdInt hEwdgInt
  rw [hqexpand, hFTC, hAibp]
  rw [hcompletedProduct]
  have hbProduct := unitRieszThirdGrade_mul_cesaroTest
    (t := t) (s := b) hb.ne'
  rw [← hbProduct]
  ring

/-- Exact actual-source second integration by parts: the CCM-FU Cesàro primitive controls the
cubically renormalized CCM-UR test with no smoothness assumption on the prime staircase. -/
theorem unitRieszCesaro_actualSource_secondIntegrationByParts
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    (∫ s in b..t,
        ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
          unitRieszCesaroTestDeriv t s) =
      ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t *
            unitRieszCesaroTestDeriv t t -
        ∫ s in b..t,
          ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s *
            unitRieszCesaroTestSecondDeriv t s := by
  let q := ccmGuinandWeilThirdGradeCumulativeMeasurable b
  let Q := ccmCesaroPrimitive q b
  let G := unitRieszCesaroTestDeriv t
  have hqInt : IntervalIntegrable q volume b t :=
    intervalIntegrable_thirdGradeCumulative hb hbt
  have hQac : AbsolutelyContinuousOnInterval Q b t := by
    exact hqInt.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b t by simp [hbt])
  have hGcd : ContDiff ℝ 1 G := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨?_, ?_⟩
    · intro s
      exact (hasDerivAt_unitRieszCesaroTestDeriv t s).differentiableAt
    · have hc : Continuous (unitRieszCesaroTestSecondDeriv t) := by
        unfold unitRieszCesaroTestSecondDeriv
        fun_prop
      apply hc.congr
      intro s
      exact (hasDerivAt_unitRieszCesaroTestDeriv t s).deriv.symm
  have hGac : AbsolutelyContinuousOnInterval G b t :=
    hGcd.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hGac.integral_mul_deriv_eq_deriv_mul hQac
  have hleft : (∫ s in b..t, G s * deriv Q s) =
      ∫ s in b..t, G s * q s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqInt.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt Q (q s) s :=
      hs (uIoc_subset_uIcc hmem) b (by simp [hbt])
    rw [hd.deriv]
  have hright : (∫ s in b..t, deriv G s * Q s) =
      ∫ s in b..t, unitRieszCesaroTestSecondDeriv t s * Q s := by
    apply intervalIntegral.integral_congr
    intro s _
    change deriv (unitRieszCesaroTestDeriv t) s * Q s = _
    rw [(hasDerivAt_unitRieszCesaroTestDeriv t s).deriv]
  have hQb : Q b = 0 := by simp [Q, ccmCesaroPrimitive]
  rw [hleft, hright, hQb, mul_zero, sub_zero] at hibp
  dsimp only [G, Q, q] at hibp ⊢
  calc
    (∫ s in b..t,
        ccmGuinandWeilThirdGradeCumulativeMeasurable b s *
          unitRieszCesaroTestDeriv t s) =
        ∫ s in b..t,
          unitRieszCesaroTestDeriv t s *
            ccmGuinandWeilThirdGradeCumulativeMeasurable b s := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = unitRieszCesaroTestDeriv t t *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t -
        ∫ s in b..t,
          unitRieszCesaroTestSecondDeriv t s *
            ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s := hibp
    _ = _ := by
      congr 1
      · ring
      · apply intervalIntegral.integral_congr
        intro s _
        ring

/-- **Literal FU--UR curvature transport.** The shifted completed-error unit-Riesz response is
exactly the endpoint reporter plus the second-derivative pairing against the actual FU Cesàro
primitive. No regularity hypothesis is imposed on the prime staircase. -/
theorem unitRieszCompletedSource_eq_FUCesaroCurvature
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    -criticalMellinCompletedError b *
          unitRieszCompletedSourceTestReal t b -
        (∫ s in b..t,
          criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s) =
      ccmCesaroPrimitive
          (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t *
            unitRieszCesaroTestDeriv t t -
        ∫ s in b..t,
          ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s *
            unitRieszCesaroTestSecondDeriv t s := by
  rw [← unitRieszCesaro_actualSource_firstIntegrationByParts hb hbt]
  exact unitRieszCesaro_actualSource_secondIntegrationByParts hb hbt

/-- Endpoint-normalized form: surviving boundary channel is exact slow exponential coefficient
`-(3/64) t^3 exp(-t/2)`. -/
theorem unitRieszCompletedSource_eq_FUCesaroCurvature_explicitEndpoint
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    -criticalMellinCompletedError b *
          unitRieszCompletedSourceTestReal t b -
        (∫ s in b..t,
          criticalMellinCompletedError s *
            unitRieszCompletedSourceTestDerivReal t s) =
      -(3 / 64) * t ^ 3 * Real.exp (-t / 2) *
          ccmCesaroPrimitive
            (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t -
        ∫ s in b..t,
          ccmCesaroPrimitive
              (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s *
            unitRieszCesaroTestSecondDeriv t s := by
  rw [unitRieszCompletedSource_eq_FUCesaroCurvature hb hbt,
    unitRieszCesaroTestDeriv_endpoint]
  ring

end GaloisForLFunctions.RHTower

end
