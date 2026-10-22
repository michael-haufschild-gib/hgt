import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureProjectiveGlobal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CompletedGateReduction
/-! Exact Green descent for the complete theta source. On 0<t<=u, a positive
source density and kernel represent the negative center numerator and its
negative displacement derivative. Completed C5 compensation is the exact
signed integral of this same density. Its normalized kernel strictly
decreases and its diagonal value is negative, so pointwise positivity
cannot close the gate. Full integral positivity remains open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section

def descentDenominator (u s : ℝ) : ℝ := s*completedDecayEvenPrimitive u s

def localDescentNumerator (u s : ℝ) : ℝ :=
  completedCurvatureOddJet u s*
    (3*((thetaCuspLogCurvatureJet (u+s)-thetaCuspLogCurvatureJet (u-s))/2)+
      s*((thetaCuspLogCurvatureJetTwo (u+s)+thetaCuspLogCurvatureJetTwo (u-s))/2))-
    ((thetaCuspLogCurvatureJetTwo (u+s)-thetaCuspLogCurvatureJetTwo (u-s))/2)*completedLocalDenominator u s

def localDescentDensity (u s : ℝ) : ℝ :=
  localDescentNumerator u s/(completedLocalDenominator u s)^2

def descentGreenKernel (u t s : ℝ) : ℝ :=
  completedFirstDenominator u t*descentDenominator u s+
    completedFirstDenominator u s*((t-s)*completedFirstDenominator u t-descentDenominator u t)

theorem completedLocalDenominator_pos_nonneg (u : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 < completedLocalDenominator u s := by
  have hv := thetaCuspLogCurvatureJet_strictMono.monotone (show u-s ≤ u+s by linarith)
  have he := completedCurvatureEven_pos u s
  have hp : 0 ≤ s*((thetaCuspLogCurvatureJet (u+s)-thetaCuspLogCurvatureJet (u-s))/2) :=
    mul_nonneg hs (div_nonneg (sub_nonneg.mpr hv) (by norm_num))
  unfold completedLocalDenominator
  linarith only [he,hp]

theorem completedFirstDenominator_strictMonoOn (u : ℝ) :
    StrictMonoOn (completedFirstDenominator u) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro s _
    exact (hasDerivAt_completedFirstDenominator u s).continuousAt.continuousWithinAt
  · intro s hs
    have hs0 : 0 < s := by simpa only [interior_Ici,mem_Ioi] using hs
    rw [(hasDerivAt_completedFirstDenominator u s).deriv]
    exact completedLocalDenominator_pos_nonneg u hs0.le

theorem completedFirstDenominator_zero (u : ℝ) : completedFirstDenominator u 0=0 := by
  simp [completedFirstDenominator,completedDecayEvenPrimitive_zero]

theorem completedFirstDenominator_pos (u : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < completedFirstDenominator u s := by
  have h := completedFirstDenominator_strictMonoOn u
    (show (0:ℝ) ∈ Ici 0 by change (0:ℝ) ≤ 0; exact le_rfl) hs.le hs
  rwa [completedFirstDenominator_zero] at h

theorem descentDenominator_pos (u : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < descentDenominator u s := by
  unfold descentDenominator
  rw [completedDecayEvenPrimitive_eq]
  exact mul_pos hs (div_pos (thetaCuspReflectedLogJetOne_pos u hs) (by norm_num))

theorem localDescentNumerator_pos {u s : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    0 < localDescentNumerator u s := by
  have h := local_ratio_deriv_neg hs hsu (show (0:ℝ) ≤ 0 from le_rfl) (sub_nonneg.mpr hsu)
    (fun x _ hx => thetaCuspLogCurvatureJet_pos_of_pos hx)
    (fun x _ => thetaCuspLogCurvatureJetTwo_pos_all x)
    (fun x hx _ => by
      rcases eq_or_lt_of_le hx with rfl | hx
      · simp only [thetaCuspLogCurvatureJetThree,thetaCuspLogCurvatureJet,
          iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 from ⟨2,rfl⟩),
          iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),
          neg_zero,mul_zero,zero_mul,le_refl]
      · have hp := projectiveEnergy_pos hx
        unfold thetaCuspCompletedCurvatureProjectiveEnergy at hp
        linarith only [hp])
  unfold localDescentNumerator
  linarith only [h]

theorem localDescentDensity_pos {u s : ℝ} (hs : 0 < s) (hsu : s ≤ u) :
    0 < localDescentDensity u s :=
  div_pos (localDescentNumerator_pos hs hsu)
    (pow_pos (completedLocalDenominator_pos_nonneg u hs.le) 2)

theorem hasDerivAt_localDescentRatio (u : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun r => completedCurvatureOddJet u r/completedLocalDenominator u r)
      (-localDescentDensity u s) s := by
  convert! (hasDerivAt_completedCurvatureOddJet u s).div
    (hasDerivAt_completedLocalDenominator u s) (completedLocalDenominator_pos_nonneg u hs).ne' using 1
  unfold localDescentDensity localDescentNumerator
  ring

theorem hasDerivAt_descentGreenKernel_inner (u t s : ℝ) :
    HasDerivAt (descentGreenKernel u t)
      (completedLocalDenominator u s*((t-s)*completedFirstDenominator u t-descentDenominator u t)) s := by
  have hd := ((hasDerivAt_mul_completedDecayEvenPrimitive u s).const_mul (completedFirstDenominator u t)).add
    ((hasDerivAt_completedFirstDenominator u s).mul
      (((hasDerivAt_id s).const_sub t).mul_const (completedFirstDenominator u t) |>.sub_const (descentDenominator u t)))
  convert! hd using 1
  simp only [id_eq]
  ring

theorem descentGreenKernel_zero (u t : ℝ) : descentGreenKernel u t 0=0 := by
  simp [descentGreenKernel,descentDenominator,completedFirstDenominator_zero]

theorem descentGreenKernel_self (u t : ℝ) : descentGreenKernel u t t=0 := by
  unfold descentGreenKernel
  ring

theorem descentGreenKernel_pos (u : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    0 < descentGreenKernel u t s := by
  have ht := hs.trans hst
  have hDs := completedFirstDenominator_pos u hs
  have hD1 := descentDenominator_pos u hs
  have hdiff := sub_pos.mpr (completedFirstDenominator_strictMonoOn u hs.le ht.le hst)
  obtain ⟨z,hz,hzderiv⟩ := exists_hasDerivAt_eq_slope (descentDenominator u)
    (completedFirstDenominator u) hst
    (fun x _ => (hasDerivAt_mul_completedDecayEvenPrimitive u x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_mul_completedDecayEvenPrimitive u x)
  have hzt := completedFirstDenominator_strictMonoOn u (hs.le.trans hz.1.le) ht.le hz.2
  have hmul := mul_lt_mul_of_pos_right hzt (sub_pos.mpr hst)
  rw [hzderiv,div_mul_cancel₀ _ (sub_ne_zero.mpr hst.ne')] at hmul
  have hgap : 0 < descentDenominator u s-descentDenominator u t+
      (t-s)*completedFirstDenominator u t := by linarith only [hmul]
  have he : descentGreenKernel u t s =
      descentDenominator u s*(completedFirstDenominator u t-completedFirstDenominator u s)+
      completedFirstDenominator u s*(descentDenominator u s-descentDenominator u t+
        (t-s)*completedFirstDenominator u t) := by unfold descentGreenKernel; ring
  rw [he]
  positivity

private def descentGreenPrimitive (u t s : ℝ) : ℝ :=
  completedCurvatureOdd u s*((t-s)*completedFirstDenominator u t-descentDenominator u t)+
    completedDecayOddPrimitive u s*completedFirstDenominator u t-
    (completedCurvatureOddJet u s/completedLocalDenominator u s)*descentGreenKernel u t s

private theorem hasDerivAt_descentGreenPrimitive (u t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (descentGreenPrimitive u t)
      (localDescentDensity u s*descentGreenKernel u t s) s := by
  have ho : HasDerivAt (completedCurvatureOdd u) (completedCurvatureOddJet u s) s :=
    hasDerivAt_completedCurvatureOdd u s
  have hlin := ((hasDerivAt_id s).const_sub t).mul_const (completedFirstDenominator u t)
    |>.sub_const (descentDenominator u t)
  have hd := ((ho.mul hlin).add ((hasDerivAt_completedDecayOddPrimitive u s).mul_const
    (completedFirstDenominator u t))).sub ((hasDerivAt_localDescentRatio u hs).mul
      (hasDerivAt_descentGreenKernel_inner u t s))
  convert! hd using 1
  simp only [id_eq]
  field_simp [(completedLocalDenominator_pos_nonneg u hs).ne']
  ring

private theorem continuousOn_localDescentDensity (u : ℝ) {t : ℝ} :
    ContinuousOn (localDescentDensity u) (Icc 0 t) := by
  intro s hs
  have h0 := (hasDerivAt_completedLocalDenominator u s).continuousAt
  have h1 := (hasDerivAt_completedCurvatureOddJet u s).continuousAt
  have hv (x : ℝ) := (hasDerivAt_thetaCuspLogCurvatureJet x).continuousAt
  have hB (x : ℝ) := (hasDerivAt_thetaCuspLogCurvatureJetTwo x).continuousAt
  have hden := (completedLocalDenominator_pos_nonneg u hs.1).ne'
  apply ContinuousAt.continuousWithinAt
  unfold localDescentDensity localDescentNumerator
  fun_prop (disch := positivity)

theorem neg_centerNumerator_eq_positive_integral (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    -thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t =
      4*(∫ s in (0:ℝ)..t, localDescentDensity u s*descentGreenKernel u t s) := by
  have hi : IntervalIntegrable (fun s => localDescentDensity u s*descentGreenKernel u t s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable_of_Icc ht
    apply (continuousOn_localDescentDensity u).mul
    intro s _
    exact (hasDerivAt_descentGreenKernel_inner u t s).continuousAt.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_descentGreenPrimitive u t ((uIcc_of_le ht ▸ hs).1)) hi
  rw [hftc]
  unfold descentGreenPrimitive
  rw [descentGreenKernel_self,descentGreenKernel_zero,completedCurvatureOdd_zero,
    completedDecayOddPrimitive_zero]
  unfold descentDenominator completedFirstDenominator
  rw [completedDecayEvenPrimitive_eq,completedDecayOddPrimitive_eq,
    completedCurvatureEven_eq,completedCurvatureOdd_eq]
  unfold thetaCuspReflectedActionVelocityFixedActionCenterNumerator
  ring


def descentGreenKernelOuter (u t s : ℝ) : ℝ :=
  completedLocalDenominator u t*
    (descentDenominator u s+(t-s)*completedFirstDenominator u s)

theorem hasDerivAt_descentGreenKernel_outer (u t s : ℝ) :
    HasDerivAt (fun r => descentGreenKernel u r s) (descentGreenKernelOuter u t s) t := by
  have hd := ((hasDerivAt_completedFirstDenominator u t).mul_const (descentDenominator u s)).add
    ((((hasDerivAt_id t).sub_const s).mul (hasDerivAt_completedFirstDenominator u t)
      |>.sub (hasDerivAt_mul_completedDecayEvenPrimitive u t)).const_mul (completedFirstDenominator u s))
  convert! hd using 1
  simp only [id_eq]
  unfold descentGreenKernelOuter
  ring

theorem descentGreenKernelOuter_pos (u : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    0 < descentGreenKernelOuter u t s := by
  unfold descentGreenKernelOuter
  exact mul_pos (completedLocalDenominator_pos_nonneg u (hs.le.trans hst))
    (add_pos_of_pos_of_nonneg (descentDenominator_pos u hs)
      (mul_nonneg (sub_nonneg.mpr hst) (completedFirstDenominator_pos u hs).le))

private def descentGreenOuterPrimitive (u t s : ℝ) : ℝ :=
  completedLocalDenominator u t*(completedCurvatureOdd u s*(t-s)+completedDecayOddPrimitive u s-
    (completedCurvatureOddJet u s/completedLocalDenominator u s)*
      (descentDenominator u s+(t-s)*completedFirstDenominator u s))

private theorem hasDerivAt_descentGreenOuterPrimitive (u t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (descentGreenOuterPrimitive u t)
      (localDescentDensity u s*descentGreenKernelOuter u t s) s := by
  have ho : HasDerivAt (completedCurvatureOdd u) (completedCurvatureOddJet u s) s :=
    hasDerivAt_completedCurvatureOdd u s
  have hm := (hasDerivAt_mul_completedDecayEvenPrimitive u s).add
    (((hasDerivAt_id s).const_sub t).mul (hasDerivAt_completedFirstDenominator u s))
  have hd := (((ho.mul ((hasDerivAt_id s).const_sub t)).add
    (hasDerivAt_completedDecayOddPrimitive u s)).sub
    ((hasDerivAt_localDescentRatio u hs).mul hm)).const_mul (completedLocalDenominator u t)
  convert! hd using 1
  simp only [id_eq]
  simp only [Pi.add_apply,Pi.mul_apply]
  unfold descentGreenKernelOuter descentDenominator
  field_simp [(completedLocalDenominator_pos_nonneg u hs).ne']
  ring

private theorem continuous_descentGreenKernelOuter (u t : ℝ) :
    Continuous (descentGreenKernelOuter u t) := by
  have h1 : Continuous (descentDenominator u) :=
    continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_mul_completedDecayEvenPrimitive u s).continuousAt)
  have h2 : Continuous (completedFirstDenominator u) :=
    continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_completedFirstDenominator u s).continuousAt)
  unfold descentGreenKernelOuter
  fun_prop

theorem neg_centerTimeJet_eq_positive_integral (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    -thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t =
      4*(∫ s in (0:ℝ)..t, localDescentDensity u s*descentGreenKernelOuter u t s) := by
  have hi : IntervalIntegrable (fun s => localDescentDensity u s*descentGreenKernelOuter u t s) volume 0 t :=
    ((continuousOn_localDescentDensity u).mul
      (continuous_descentGreenKernelOuter u t).continuousOn).intervalIntegrable_of_Icc ht
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_descentGreenOuterPrimitive u t ((uIcc_of_le ht ▸ hs).1)) hi
  rw [hftc]
  unfold descentGreenOuterPrimitive descentDenominator
  rw [completedCurvatureOdd_zero,completedDecayOddPrimitive_zero,completedFirstDenominator_zero]
  have hd := (completedLocalDenominator_pos_nonneg u ht).ne'
  simp only [sub_self,zero_mul,mul_zero,add_zero,sub_zero]
  field_simp [hd]
  unfold thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet completedLocalDenominator
    completedCurvatureOddJet
  rw [completedDecayEvenPrimitive_eq,completedDecayOddPrimitive_eq,completedCurvatureEven_eq]
  unfold thetaCuspReflectedLogCenterMixedJetThree thetaCuspReflectedLogJetThree
  ring

theorem centerTimeJet_neg {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t < 0 := by
  have hi : IntervalIntegrable (fun s => localDescentDensity u s*descentGreenKernelOuter u t s) volume 0 t :=
    ((continuousOn_localDescentDensity u).mul
      (continuous_descentGreenKernelOuter u t).continuousOn).intervalIntegrable_of_Icc ht.le
  have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun s hs => mul_pos (localDescentDensity_pos hs.1 (hs.2.le.trans htu))
      (descentGreenKernelOuter_pos u hs.1 hs.2.le)) ht
  have he := neg_centerTimeJet_eq_positive_integral u ht.le
  linarith only [he,hp]



def compensationGreenKernel (u t s : ℝ) : ℝ :=
  (c5CompletedBoseWeight u t-5)*descentGreenKernel u t s-
    5*t*descentGreenKernelOuter u t s

theorem completedCompensation_eq_signed_integral {u t : ℝ} (ht : 0 < t) (htu : t < u) :
    c5CompletedCompensationMargin u t =
      4*(∫ s in (0:ℝ)..t, localDescentDensity u s*compensationGreenKernel u t s) := by
  have hc : ContinuousOn (fun s => localDescentDensity u s*descentGreenKernel u t s) (Icc 0 t) := by
    apply (continuousOn_localDescentDensity u).mul
    intro s _
    exact (hasDerivAt_descentGreenKernel_inner u t s).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun s => localDescentDensity u s*descentGreenKernel u t s) volume 0 t :=
    hc.intervalIntegrable_of_Icc ht.le
  have hi' : IntervalIntegrable (fun s => localDescentDensity u s*descentGreenKernelOuter u t s) volume 0 t :=
    ((continuousOn_localDescentDensity u).mul
    (continuous_descentGreenKernelOuter u t).continuousOn).intervalIntegrable_of_Icc ht.le
  have he : (fun s => localDescentDensity u s*compensationGreenKernel u t s) =
      (fun s => (c5CompletedBoseWeight u t-5)*(localDescentDensity u s*descentGreenKernel u t s)-
        (5*t)*(localDescentDensity u s*descentGreenKernelOuter u t s)) := by
    funext s
    unfold compensationGreenKernel
    ring
  rw [he,intervalIntegral.integral_sub (hi.const_mul _) (hi'.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have h0 := neg_centerNumerator_eq_positive_integral u ht.le
  have h1 := neg_centerTimeJet_eq_positive_integral u ht.le
  have h2 : (∫ s in (0:ℝ)..t, localDescentDensity u s*descentGreenKernel u t s) =
      -thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t/4 := by linarith only [h0]
  have h3 : (∫ s in (0:ℝ)..t, localDescentDensity u s*descentGreenKernelOuter u t s) =
      -thetaCuspReflectedActionVelocityFixedActionCenterNumeratorTimeJet u t/4 := by linarith only [h1]
  rw [h2,h3,c5CompletedCompensationMargin_eq_excess_form ht htu]
  unfold c5CompletedScalingExcess
  ring

theorem compensationGreenKernel_endpoint_neg (u : ℝ) {t : ℝ} (ht : 0 < t) :
    compensationGreenKernel u t t < 0 := by
  unfold compensationGreenKernel
  rw [descentGreenKernel_self,mul_zero]
  exact sub_neg.mpr (mul_pos (mul_pos (by norm_num) ht)
    (descentGreenKernelOuter_pos u ht le_rfl))

theorem hasDerivAt_descentGreenKernelOuter_inner (u t s : ℝ) :
    HasDerivAt (descentGreenKernelOuter u t)
      (completedLocalDenominator u t*(t-s)*completedLocalDenominator u s) s := by
  have hd := ((hasDerivAt_mul_completedDecayEvenPrimitive u s).add
    (((hasDerivAt_id s).const_sub t).mul (hasDerivAt_completedFirstDenominator u s))).const_mul
      (completedLocalDenominator u t)
  convert! hd using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_descentGreenLogGrowth (u : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (fun r => descentGreenKernelOuter u t r/descentGreenKernel u t r)
      (completedLocalDenominator u t*completedLocalDenominator u s*
        descentDenominator u t*descentDenominator u s/descentGreenKernel u t s^2) s := by
  have hd := (hasDerivAt_descentGreenKernelOuter_inner u t s).div
    (hasDerivAt_descentGreenKernel_inner u t s) (descentGreenKernel_pos u hs hst).ne'
  convert! hd using 1
  unfold descentGreenKernelOuter descentGreenKernel
  ring

theorem descentGreenLogGrowth_strictMonoOn (u : ℝ) {t : ℝ} (ht : 0 < t) :
    StrictMonoOn (fun s => descentGreenKernelOuter u t s/descentGreenKernel u t s) (Ioo 0 t) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro s hs
    exact (hasDerivAt_descentGreenLogGrowth u hs.1 hs.2).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 t := interior_subset hs
    rw [(hasDerivAt_descentGreenLogGrowth u hs'.1 hs'.2).deriv]
    exact div_pos (mul_pos (mul_pos (mul_pos (completedLocalDenominator_pos_nonneg u ht.le)
      (completedLocalDenominator_pos_nonneg u hs'.1.le)) (descentDenominator_pos u ht))
      (descentDenominator_pos u hs'.1)) (sq_pos_of_pos (descentGreenKernel_pos u hs'.1 hs'.2))



theorem compensationGreenRatio_strictAntiOn (u : ℝ) {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun s => compensationGreenKernel u t s/descentGreenKernel u t s) (Ioo 0 t) := by
  have he (s : ℝ) (hs : s ∈ Ioo 0 t) :
      compensationGreenKernel u t s/descentGreenKernel u t s =
        c5CompletedBoseWeight u t-5-5*t*(descentGreenKernelOuter u t s/descentGreenKernel u t s) := by
    unfold compensationGreenKernel
    field_simp [(descentGreenKernel_pos u hs.1 hs.2).ne']
  intro a ha b hb hab
  dsimp only
  rw [he a ha,he b hb]
  have hm := descentGreenLogGrowth_strictMonoOn u ht ha hb hab
  have hp := mul_lt_mul_of_pos_left hm (mul_pos (by norm_num : (0:ℝ)<5) ht)
  linarith only [hp]


end
end RHTower.ThetaCuspDefect
