import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthCubicTailIsolation
/-!
# Eighth-moment budget retaining every mixed deep factor

The cubic mixed remainder is dominated by three copies of
D * (M * M), where M is the full tilted source and D its deep part.
Even-power convexity then yields
E3_8 <= 384 * (D8*M0^2 + 256*D0*M0*M8).
The literal source transport keeps a deep moment in each term and avoids
the failed pure-dominant cubic monomial estimate. No positivity of the
complete absorption residual is asserted here.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
noncomputable section

private theorem measureConv_mono (μ μ' ν ν' : Measure ℝ) [IsFiniteMeasure ν']
    (hμ : μ ≤ μ') (hν : ν ≤ ν') : μ ∗ ν ≤ μ' ∗ ν' := by
  unfold Measure.conv
  exact Measure.map_mono (Measure.prod_mono hμ hν) (by fun_prop)

theorem mixedConvolutionRemainder_three_le (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    mixedConvolutionRemainder μ ν 3 ≤
      (ν ∗ ((μ+ν) ∗ (μ+ν))+ν ∗ ((μ+ν) ∗ (μ+ν)))+ν ∗ ((μ+ν) ∗ (μ+ν)) := by
  have hμ : μ ≤ μ+ν := Measure.le_add_right le_rfl
  have h1 : (μ+ν) ∗ ((μ+ν) ∗ ν)=ν ∗ ((μ+ν) ∗ (μ+ν)) := by
    rw [←Measure.conv_assoc,Measure.conv_comm]
  have h2 : (μ+ν) ∗ (ν ∗ μ) ≤ ν ∗ ((μ+ν) ∗ (μ+ν)) := by
    calc
      _ ≤ (μ+ν) ∗ (ν ∗ (μ+ν)) :=
        measureConv_mono _ _ _ _ le_rfl (measureConv_mono _ _ _ _ le_rfl hμ)
      _ = _ := by rw [←Measure.conv_assoc,Measure.conv_comm (μ+ν) ν,Measure.conv_assoc]
  have h3 : ν ∗ (μ ∗ μ) ≤ ν ∗ ((μ+ν) ∗ (μ+ν)) :=
    measureConv_mono _ _ _ _ le_rfl (measureConv_mono _ _ _ _ hμ hμ)
  simp only [mixedConvolutionRemainder,convolutionPower,Measure.conv_zero,zero_add,
    Measure.conv_dirac_zero]
  rw [Measure.conv_add,h1]
  exact add_le_add (add_le_add le_rfl h2) h3

theorem measureMoment_conv_eight_le (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν) :
    measureMoment (μ ∗ ν) 8 ≤ (2:ℝ)^7*
      (measureMoment μ 8*measureMoment ν 0+measureMoment μ 0*measureMoment ν 8) := by
  have hleft : Integrable (fun z : ℝ×ℝ => z.1^8*(z.2^0)) (μ.prod ν) :=
    (hμ 8).mul_prod (hν 0)
  have hright : Integrable (fun z : ℝ×ℝ => z.1^0*(z.2^8)) (μ.prod ν) :=
    (hμ 0).mul_prod (hν 8)
  have hsum := (hleft.add hright).const_mul ((2:ℝ)^7)
  have hpow : Integrable (fun z : ℝ×ℝ => (z.1+z.2)^8) (μ.prod ν) := by
    have h := integrable_pow_measure_conv μ ν hμ hν 8
    unfold Measure.conv at h
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).mp h
  unfold measureMoment Measure.conv
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫ z : ℝ×ℝ, (2:ℝ)^7*(z.1^8*z.2^0+z.1^0*z.2^8) ∂μ.prod ν := by
      apply integral_mono_ae hpow hsum
      filter_upwards with z
      simpa only [pow_zero,mul_one,one_mul,Nat.reduceSub,Pi.add_apply] using
        (show Even (8:ℕ) by norm_num).add_pow_le (a:=z.1) (b:=z.2)
    _ = _ := by
      rw [integral_const_mul,integral_add hleft hright,
        integral_prod_mul (μ:=μ) (ν:=ν) (fun t : ℝ => t^8) (fun t : ℝ => t^0),
        integral_prod_mul (μ:=μ) (ν:=ν) (fun t : ℝ => t^0) (fun t : ℝ => t^8)]

theorem mixedConvolutionRemainder_eight_budget (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j) ν) :
    measureMoment (mixedConvolutionRemainder μ ν 3) 8 ≤
      384*(measureMoment ν 8*measureMoment (μ+ν) 0^2+
        256*measureMoment ν 0*measureMoment (μ+ν) 0*measureMoment (μ+ν) 8) := by
  let M := μ+ν
  have hM (j : ℕ) : Integrable (fun t : ℝ => t^j) M := (hμ j).add_measure (hν j)
  have hMM := integrable_pow_measure_conv M M hM hM
  have hDMM := integrable_pow_measure_conv ν (M ∗ M) hν hMM
  have hmeasure := mixedConvolutionRemainder_three_le μ ν
  have he : measureMoment (mixedConvolutionRemainder μ ν 3) 8 ≤
      3*measureMoment (ν ∗ (M ∗ M)) 8 := by
    have hnonneg : 0 ≤ᵐ[(ν ∗ (M ∗ M)+ν ∗ (M ∗ M))+ν ∗ (M ∗ M)]
        (fun t : ℝ => t^8) := by filter_upwards with t; positivity
    have h := integral_mono_measure hmeasure hnonneg
      (((hDMM 8).add_measure (hDMM 8)).add_measure (hDMM 8))
    rw [integral_add_measure ((hDMM 8).add_measure (hDMM 8)) (hDMM 8),
      integral_add_measure (hDMM 8) (hDMM 8)] at h
    change measureMoment (mixedConvolutionRemainder μ ν 3) 8 ≤
      measureMoment (ν ∗ (M ∗ M)) 8+measureMoment (ν ∗ (M ∗ M)) 8+
        measureMoment (ν ∗ (M ∗ M)) 8 at h
    linarith
  have hb := measureMoment_conv_eight_le ν (M ∗ M) hν hMM
  have hmm := measureMoment_conv_eight_le M M hM hM
  have hz : measureMoment (M ∗ M) 0=measureMoment M 0^2 := by
    rw [measureMoment_conv M M hM hM]
    norm_num [momentConvolution]
    ring
  have hd0 : 0 ≤ measureMoment ν 0 := by unfold measureMoment; simp only [pow_zero]; positivity
  have hstep := mul_le_mul_of_nonneg_left hmm hd0
  rw [hz] at hb
  change measureMoment (mixedConvolutionRemainder μ ν 3) 8 ≤
    384*(measureMoment ν 8*measureMoment M 0^2+
      256*measureMoment ν 0*measureMoment M 0*measureMoment M 8)
  norm_num at hb hstep
  nlinarith only [he,hb,hstep]

theorem mixedPowerMoment_three_eight_budget {q : ℝ} (hq : 0 < q) :
    mixedPowerMoment q 3 8 ≤
      384*(thetaCuspDeepTailMoment q 8*thetaCuspHigherLikelihoodSpectralMoment q 0^2+
        256*thetaCuspDeepTailMoment q 0*thetaCuspHigherLikelihoodSpectralMoment q 0*
          thetaCuspHigherLikelihoodSpectralMoment q 8) := by
  let A := componentTilt q thetaCuspSecondAtomSpectralMeasure
  let D := componentTilt q thetaCuspDeepTailSpectralMeasure
  have hiA := integrable_pow_componentTilt q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq)
  have hiD := integrable_pow_componentTilt q thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq)
  letI : IsFiniteMeasure A := componentTilt_finite q thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq)
  letI : IsFiniteMeasure D := componentTilt_finite q thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq)
  have hA : measureMoment A=atomMoment 2 q := by
    funext j
    rw [measureMoment_componentTilt]
    simp only [atomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul]
  have hD : measureMoment D=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  have hsum : measureMoment (A+D)=thetaCuspHigherLikelihoodSpectralMoment q := by
    funext j
    have he : measureMoment (A+D) j=measureMoment A j+measureMoment D j := by
      unfold measureMoment
      exact integral_add_measure (hiA j) (hiD j)
    rw [he,hA,hD]
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      (thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq j).symm
  have hmass : measureMoment (convolutionPower (A+D) 3) 8=
      measureMoment (convolutionPower A 3) 8+measureMoment (mixedConvolutionRemainder A D 3) 8 := by
    rw [convolutionPower_add_split]
    unfold measureMoment
    exact integral_add_measure (integrable_pow_convolutionPower A hiA 3 8)
      (integrable_pow_mixedConvolutionRemainder A D hiA hiD 3 8)
  rw [measureMoment_convolutionPower (A+D) (fun j => (hiA j).add_measure (hiD j)) 3 (by omega : 8 ≤ 8),
    measureMoment_convolutionPower A hiA 3 (by omega : 8 ≤ 8),hsum,hA] at hmass
  have he : mixedPowerMoment q 3 8=measureMoment (mixedConvolutionRemainder A D 3) 8 := by
    unfold mixedPowerMoment
    linarith
  have hb := mixedConvolutionRemainder_eight_budget A D hiA hiD
  rw [hD,hsum] at hb
  rw [he]
  exact hb

end
end RHTower.ThetaCuspDefect

