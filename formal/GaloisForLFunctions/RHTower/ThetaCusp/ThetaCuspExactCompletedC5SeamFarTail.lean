import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamOrientation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCassiniMarkovBoundaryTransport
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Exact completed C5 seam orientation on the physical far tail

The fixed positive higher-likelihood spectral measure has support in `[3, ∞)`. Its tilted
moments therefore decay exponentially under likelihood cooling, even after multiplication by
an arbitrary fixed polynomial. Transport through the exact cumulant formulas proves that all
higher-likelihood source log jets through order seven are `o(A)`, where
`A = thetaCuspSingleAtomReflectionScale 1 x`.

The first Born--Witten atom has normalized logarithmic jets tending to
`4, 8, 16, 32, 64, 128`. Substitution into the exact completed C5 orientation cancels every
cubic contribution after fourth-scale normalization and leaves

`-18 * 4^(3 : ℕ) * 32 + 36 * 4^(2 : ℕ) * 16 * 8 = 36864`.

Thus the literal physical C5 orientation is strictly positive on a cofinal source tail. This
removes the entire noncompact part of the C5 orbit-first-contact burden: only a compact physical
incidence problem remains.

RH chain: cofinal exact C5 orientation plus compact physical incidence -> global exact C5 seam
orientation -> direct local Jacobian orientation -> reflection-odd rank-four/Ptolemy wall ->
cofinal no-escape -> CLG/TTF or Weil polarization positivity -> RH.
-/

open Real Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

theorem thetaCuspC5FarTail_moment_nonneg (B : ℝ) (m : ℕ) :
    0 ≤ thetaCuspHigherLikelihoodSpectralMoment B m := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  exact mul_nonneg (pow_nonneg (by linarith) m) (Real.exp_pos _).le

theorem thetaCuspC5FarTail_moment_exp_bound
    {B : ℝ} (hB : 1 ≤ B) (m : ℕ) :
    thetaCuspHigherLikelihoodSpectralMoment B m ≤
      Real.exp (-3 * (B - 1)) *
        thetaCuspHigherLikelihoodSpectralMoment 1 m := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral,
    thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m
      (by linarith : (0 : ℝ) < B))
    ((integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m
      (by norm_num : (0 : ℝ) < 1)).const_mul _)
  filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  have ht0 : 0 ≤ t := by linarith
  have hBm : 0 ≤ B - 1 := sub_nonneg.mpr hB
  have hexp : Real.exp (-(B * t)) ≤
      Real.exp (-3 * (B - 1)) * Real.exp (-(1 * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    t ^ m * Real.exp (-B * t) ≤
        t ^ m * (Real.exp (-3 * (B - 1)) * Real.exp (-(1 * t))) :=
      mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using hexp)
        (pow_nonneg ht0 m)
    _ = Real.exp (-3 * (B - 1)) * (t ^ m * Real.exp (-1 * t)) := by ring_nf

theorem thetaCuspC5FarTail_scaled_moment_tendsto_zero (q m : ℕ) :
    Tendsto (fun B : ℝ => B ^ q *
      thetaCuspHigherLikelihoodSpectralMoment B m) atTop (nhds 0) := by
  have hupper : Tendsto (fun B : ℝ =>
      thetaCuspHigherLikelihoodSpectralMoment 1 m *
        (Real.exp 3 * (B ^ q * Real.exp (-(3 * B)))))
      atTop (nhds 0) := by
    have hdecay :=
      GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop
      (b := (3 : ℝ)) (by norm_num) q
    simpa only [mul_zero] using
      (hdecay.const_mul (Real.exp 3)).const_mul
        (thetaCuspHigherLikelihoodSpectralMoment 1 m)
  have hnonneg : ∀ᶠ B : ℝ in atTop,
      0 ≤ B ^ q * thetaCuspHigherLikelihoodSpectralMoment B m := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    exact mul_nonneg (pow_nonneg (by linarith) q) (thetaCuspC5FarTail_moment_nonneg B m)
  refine squeeze_zero' hnonneg ?_ hupper
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hM0 := thetaCuspC5FarTail_moment_nonneg B m
  have hbound := thetaCuspC5FarTail_moment_exp_bound hB m
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hB0 q)
  calc
      B ^ q * thetaCuspHigherLikelihoodSpectralMoment B m ≤
          B ^ q * (Real.exp (-3 * (B - 1)) *
            thetaCuspHigherLikelihoodSpectralMoment 1 m) := hmul
      _ = thetaCuspHigherLikelihoodSpectralMoment 1 m *
          (Real.exp 3 * (B ^ q * Real.exp (-(3 * B)))) := by
        rw [show -3 * (B - 1) = 3 + -(3 * B) by ring_nf, Real.exp_add]
        ring_nf

theorem thetaCuspC5FarTail_partition_tendsto_one :
    Tendsto thetaCuspLikelihoodPartition atTop (nhds 1) := by
  have h0 := thetaCuspC5FarTail_scaled_moment_tendsto_zero 0 0
  have hzero : Tendsto
      (fun B : ℝ => thetaCuspHigherLikelihoodSpectralMoment B 0)
      atTop (nhds 0) := by simpa using h0
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := hone.add hzero
  have h0 : Tendsto (fun B : ℝ =>
      1 + thetaCuspHigherLikelihoodSpectralMoment B 0)
      atTop (nhds 1) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  symm
  exact thetaCuspLikelihoodPartition_eq_one_add_moment_zero (by linarith)

theorem thetaCuspC5FarTail_scaled_normalized_moment_tendsto_zero (q m : ℕ) :
    Tendsto (fun B : ℝ => B ^ q *
      thetaCuspLikelihoodNormalizedMoment B m) atTop (nhds 0) := by
  have hnum := thetaCuspC5FarTail_scaled_moment_tendsto_zero q m
  have hdiv := hnum.div thetaCuspC5FarTail_partition_tendsto_one (by norm_num : (1 : ℝ) ≠ 0)
  have hdiv0 : Tendsto
      ((fun B : ℝ => B ^ q * thetaCuspHigherLikelihoodSpectralMoment B m) /
        thetaCuspLikelihoodPartition) atTop (nhds 0) := by
    simpa only [zero_div] using hdiv
  refine hdiv0.congr' (Eventually.of_forall fun B => ?_)
  simp only [Pi.div_apply]
  unfold thetaCuspLikelihoodNormalizedMoment
  ring_nf

theorem thetaCuspC5FarTail_scale_tendsto_atTop :
    Tendsto (thetaCuspSingleAtomReflectionScale 1) atTop atTop := by
  have hlin : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hexp : Tendsto (fun x : ℝ => Real.exp (2 * x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  convert (Filter.Tendsto.const_mul_atTop Real.pi_pos hexp) using 1
  funext x
  norm_num [thetaCuspSingleAtomReflectionScale]

theorem thetaCuspC5FarTail_scale_eq_coordinate_add (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspLikelihoodCoordinate x + 3 / 2 := by
  unfold thetaCuspSingleAtomReflectionScale thetaCuspLikelihoodCoordinate
  norm_num
  rw [show Real.exp (2 * x) = Real.exp x ^ (2 : ℕ) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf]

theorem thetaCuspC5FarTail_coordinate_tendsto_atTop :
    Tendsto thetaCuspLikelihoodCoordinate atTop atTop := by
  have h := tendsto_atTop_add_const_right atTop (-(3 / 2 : ℝ))
    thetaCuspC5FarTail_scale_tendsto_atTop
  convert h using 1
  funext x
  rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
  ring_nf

theorem thetaCuspC5FarTail_scale_div_coordinate_tendsto_one :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x /
        thetaCuspLikelihoodCoordinate x) atTop (nhds 1) := by
  have hcoord := thetaCuspC5FarTail_coordinate_tendsto_atTop
  have hinv : Tendsto (fun x : ℝ =>
      (thetaCuspLikelihoodCoordinate x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcoord
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsmall := hinv.const_mul (3 / 2 : ℝ)
  have h := hone.add hsmall
  have h0 : Tendsto (fun x : ℝ =>
      1 + 3 / 2 * (thetaCuspLikelihoodCoordinate x)⁻¹)
      atTop (nhds 1) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hcoord0 := (thetaCuspLikelihoodCoordinate_pos hx).ne'
  symm
  calc
    thetaCuspSingleAtomReflectionScale 1 x /
          thetaCuspLikelihoodCoordinate x =
        (thetaCuspLikelihoodCoordinate x + 3 / 2) /
          thetaCuspLikelihoodCoordinate x := by rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
    _ = 1 + 3 / 2 * (thetaCuspLikelihoodCoordinate x)⁻¹ := by
      field_simp [hcoord0]

theorem thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero (q m : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodNormalizedMoment
          (thetaCuspLikelihoodCoordinate x) m) atTop (nhds 0) := by
  have hratio := thetaCuspC5FarTail_scale_div_coordinate_tendsto_one
  have hmoment := (thetaCuspC5FarTail_scaled_normalized_moment_tendsto_zero q m).comp
    thetaCuspC5FarTail_coordinate_tendsto_atTop
  have hprod := hratio.pow q |>.mul hmoment
  have hprod0 : Tendsto
      (fun x : ℝ =>
        (thetaCuspSingleAtomReflectionScale 1 x /
          thetaCuspLikelihoodCoordinate x) ^ q *
        (thetaCuspLikelihoodCoordinate x ^ q *
          thetaCuspLikelihoodNormalizedMoment
            (thetaCuspLikelihoodCoordinate x) m)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, one_pow, one_mul, mul_zero] using hprod
  refine hprod0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hcoord := (thetaCuspLikelihoodCoordinate_pos hx).ne'
  rw [← mul_assoc, ← mul_pow, div_mul_cancel₀ _ hcoord]

theorem thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  simpa [thetaCuspLikelihoodMean,
    thetaCuspLikelihoodNormalizedMoment] using
    thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 1

theorem thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he2 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 2
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h := he2.sub (hm.mul hm0)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodVariance thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

theorem thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he3 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 3
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have he20 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 2
  have h := (he3.sub ((hm.mul he20).const_mul 3)).add
    (((hm.mul hm0).mul hm0).const_mul 2)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodThirdCumulant thetaCuspLikelihoodMean
      thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

theorem thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he4 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 4
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have he20 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 2
  have he30 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 3
  have he2 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 2
  have h := (((he4.sub ((hm.mul he30).const_mul 4)).sub
      ((he2.mul he20).const_mul 3)).add
      ((((hm.mul hm0).mul he20).const_mul 12))).sub
      (((((hm.mul hm0).mul hm0).mul hm0).const_mul 6))
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodMean
      thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

theorem thetaCuspC5FarTail_scaled_likelihoodFifthCumulant_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he5 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 5
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have he2 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 2
  have he20 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 2
  have he30 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 3
  have he40 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 4
  have h1 := he5.sub ((hm.mul he40).const_mul 5)
  have h2 := h1.sub ((he2.mul he30).const_mul 10)
  have h3 := h2.add (((hm.mul hm0).mul he30).const_mul 20)
  have h4 := h3.add (((hm.mul he20).mul he20).const_mul 30)
  have h5 := h4.sub ((((hm.mul hm0).mul hm0).mul he20).const_mul 60)
  have h := h5.add (((((hm.mul hm0).mul hm0).mul hm0).mul hm0).const_mul 24)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodFifthCumulant thetaCuspLikelihoodMean
      thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

theorem thetaCuspC5FarTail_scaled_likelihoodSixthCumulant_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he6 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 6
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have he2 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 2
  have he3 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 3
  have he20 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 2
  have he30 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 3
  have he40 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 4
  have he50 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 5
  have h1 := he6.sub ((hm.mul he50).const_mul 6)
  have h2 := h1.sub ((he2.mul he40).const_mul 15)
  have h3 := h2.sub ((he3.mul he30).const_mul 10)
  have h4 := h3.add (((hm.mul hm0).mul he40).const_mul 30)
  have h5 := h4.add (((hm.mul he20).mul he30).const_mul 120)
  have h6 := h5.sub ((((hm.mul hm0).mul hm0).mul he30).const_mul 120)
  have h7 := h6.add (((he2.mul he20).mul he20).const_mul 30)
  have h8 := h7.sub ((((hm.mul hm0).mul he20).mul he20).const_mul 270)
  have h9 := h8.add (((((hm.mul hm0).mul hm0).mul hm0).mul he20).const_mul 360)
  have h := h9.sub ((((((hm.mul hm0).mul hm0).mul hm0).mul hm0).mul hm0).const_mul 120)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodMean
      thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

theorem thetaCuspC5FarTail_scaled_likelihoodSeventhCumulant_source_tendsto_zero (q : ℕ) :
    Tendsto (fun x : ℝ =>
      thetaCuspSingleAtomReflectionScale 1 x ^ q *
        thetaCuspLikelihoodSeventhCumulant (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
  have he7 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 7
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero q
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have he2 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 2
  have he3 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero q 3
  have he20 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 2
  have he30 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 3
  have he40 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 4
  have he50 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 5
  have he60 := thetaCuspC5FarTail_scaled_normalized_moment_source_tendsto_zero 0 6
  have h1 := he7.sub ((hm.mul he60).const_mul 7)
  have h2 := h1.sub ((he2.mul he50).const_mul 21)
  have h3 := h2.sub ((he3.mul he40).const_mul 35)
  have h4 := h3.add (((hm.mul hm0).mul he50).const_mul 42)
  have h5 := h4.add (((hm.mul he20).mul he40).const_mul 210)
  have h6 := h5.add (((hm.mul he30).mul he30).const_mul 140)
  have h7 := h6.add (((he2.mul he20).mul he30).const_mul 210)
  have h8 := h7.sub ((((hm.mul hm0).mul hm0).mul he40).const_mul 210)
  have h9 := h8.sub ((((hm.mul hm0).mul he20).mul he30).const_mul 1260)
  have h10 := h9.sub ((((hm.mul he20).mul he20).mul he20).const_mul 630)
  have h11 := h10.add (((((hm.mul hm0).mul hm0).mul hm0).mul he30).const_mul 840)
  have h12 := h11.add (((((hm.mul hm0).mul hm0).mul he20).mul he20).const_mul 2520)
  have h13 := h12.sub ((((((hm.mul hm0).mul hm0).mul hm0).mul hm0).mul he20).const_mul 2520)
  have h := h13.add (((((((hm.mul hm0).mul hm0).mul hm0).mul hm0).mul hm0).mul hm0).const_mul 720)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSeventhCumulant thetaCuspLikelihoodMean
      thetaCuspLikelihoodNormalizedMoment
    ring_nf
  · norm_num

private theorem thetaCuspC5FarTail_reflectionScale_ne_zero (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

theorem thetaCuspC5FarTail_likelihoodJetTwo_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetTwo x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h := (hv.const_mul 4).sub (hm.const_mul 4)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_likelihoodJetThree_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetThree x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hk := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 2
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h := ((hk.const_mul (-8)).add (hv.const_mul 24)).sub (hm.const_mul 8)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_likelihoodJetFour_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetFour x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 3
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 2
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h := (((hk4.const_mul 16).sub (hk3.const_mul 96)).add
    (hv.const_mul 112)).sub (hm.const_mul 16)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetFour
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_likelihoodJetFive_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetFive x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hk5 := thetaCuspC5FarTail_scaled_likelihoodFifthCumulant_source_tendsto_zero 4
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 3
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 2
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h1 := (hk5.const_mul (-32)).add (hk4.const_mul 320)
  have h2 := h1.sub (hk3.const_mul 800)
  have h3 := h2.add (hv.const_mul 480)
  have h := h3.sub (hm.const_mul 32)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetFive
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_likelihoodJetSix_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetSix x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hk6 := thetaCuspC5FarTail_scaled_likelihoodSixthCumulant_source_tendsto_zero 5
  have hk5 := thetaCuspC5FarTail_scaled_likelihoodFifthCumulant_source_tendsto_zero 4
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 3
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 2
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h1 := (hk6.const_mul 64).sub (hk5.const_mul 960)
  have h2 := h1.add (hk4.const_mul 4160)
  have h3 := h2.sub (hk3.const_mul 5760)
  have h4 := h3.add (hv.const_mul 1984)
  have h := h4.sub (hm.const_mul 64)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetSix
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_likelihoodJetSeven_div_scale_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodSourceLogPartitionJetSeven x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 0) := by
  have hk7 := thetaCuspC5FarTail_scaled_likelihoodSeventhCumulant_source_tendsto_zero 6
  have hk6 := thetaCuspC5FarTail_scaled_likelihoodSixthCumulant_source_tendsto_zero 5
  have hk5 := thetaCuspC5FarTail_scaled_likelihoodFifthCumulant_source_tendsto_zero 4
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 3
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 2
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 1
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have h1 := (hk7.const_mul (-128)).add (hk6.const_mul 2688)
  have h2 := h1.sub (hk5.const_mul 17920)
  have h3 := h2.add (hk4.const_mul 44800)
  have h4 := h3.sub (hk3.const_mul 38528)
  have h5 := h4.add (hv.const_mul 8064)
  have h := h5.sub (hm.const_mul 128)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetSeven
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

theorem thetaCuspC5FarTail_morseScale_one_eq_reflectionScale (x : ℝ) :
    thetaCuspMorseScale 1 x = thetaCuspSingleAtomReflectionScale 1 x := by
  unfold thetaCuspMorseScale thetaCuspSingleAtomReflectionScale
  norm_num
  rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf]

theorem thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate (x : ℝ) :
    thetaCuspBornWittenWeight 1 x = thetaCuspLikelihoodCoordinate x := by
  rw [thetaCuspBornWittenWeight_eq, thetaCuspC5FarTail_morseScale_one_eq_reflectionScale,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  ring_nf

theorem thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x : ℝ =>
      1 / thetaCuspLikelihoodCoordinate x ^ m) atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ =>
      (thetaCuspLikelihoodCoordinate x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp thetaCuspC5FarTail_coordinate_tendsto_atTop
  have h := hinv.pow m
  simpa only [inv_pow, one_div, zero_pow (Nat.ne_of_gt hm)] using h

theorem thetaCuspC5FarTail_bornWittenLogCurvature_div_scale_tendsto_four :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogCurvature 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 4) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (nhds 4) :=
    tendsto_const_nhds
  have h := hc.add (h2.const_mul 6)
  have h0 : Tendsto (fun x : ℝ =>
      4 + 6 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)))
      atTop (nhds 4) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogCurvature thetaCuspBornWittenCurvature
  rw [thetaCuspC5FarTail_morseScale_one_eq_reflectionScale,
    thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_bornWittenLogThirdDerivative_div_scale_tendsto_eight :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogThirdDerivative 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 8) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (8 : ℝ)) atTop (nhds 8) :=
    tendsto_const_nhds
  have h := (hc.sub (h2.const_mul 12)).sub (h3.const_mul 36)
  have h0 : Tendsto (fun x : ℝ =>
      8 - 12 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)) -
        36 * (1 / thetaCuspLikelihoodCoordinate x ^ (3 : ℕ)))
      atTop (nhds 8) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogThirdDerivative
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_bornWittenLogFourthDerivative_div_scale_tendsto_sixteen :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogFourthDerivative 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 16) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have h4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (16 : ℝ)) atTop (nhds 16) :=
    tendsto_const_nhds
  have h := ((hc.add (h2.const_mul 24)).add
    (h3.const_mul 216)).add (h4.const_mul 324)
  have h0 : Tendsto (fun x : ℝ =>
      16 + 24 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)) +
        216 * (1 / thetaCuspLikelihoodCoordinate x ^ (3 : ℕ)) +
        324 * (1 / thetaCuspLikelihoodCoordinate x ^ (4 : ℕ)))
      atTop (nhds 16) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogFourthDerivative
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_bornWittenLogFifthDerivative_div_scale_tendsto_thirtytwo :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogFifthDerivative 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 32) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have h4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have h5 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 5 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (32 : ℝ)) atTop (nhds 32) :=
    tendsto_const_nhds
  have h := ((((hc.sub (h2.const_mul 48)).sub
    (h3.const_mul 1008)).sub (h4.const_mul 3888)).sub
    (h5.const_mul 3888))
  have h0 : Tendsto (fun x : ℝ =>
      32 - 48 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)) -
        1008 * (1 / thetaCuspLikelihoodCoordinate x ^ (3 : ℕ)) -
        3888 * (1 / thetaCuspLikelihoodCoordinate x ^ (4 : ℕ)) -
        3888 * (1 / thetaCuspLikelihoodCoordinate x ^ (5 : ℕ)))
      atTop (nhds 32) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogFifthDerivative
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_bornWittenLogSixthDerivative_div_scale_tendsto_sixtyfour :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogSixthDerivative 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 64) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have h4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have h5 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 5 (by norm_num)
  have h6 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 6 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (64 : ℝ)) atTop (nhds 64) :=
    tendsto_const_nhds
  have h := (((((hc.add (h2.const_mul 96)).add
    (h3.const_mul 4320)).add (h4.const_mul 32400)).add
    (h5.const_mul 77760)).add (h6.const_mul 58320))
  have h0 : Tendsto (fun x : ℝ =>
      64 + 96 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)) +
        4320 * (1 / thetaCuspLikelihoodCoordinate x ^ (3 : ℕ)) +
        32400 * (1 / thetaCuspLikelihoodCoordinate x ^ (4 : ℕ)) +
        77760 * (1 / thetaCuspLikelihoodCoordinate x ^ (5 : ℕ)) +
        58320 * (1 / thetaCuspLikelihoodCoordinate x ^ (6 : ℕ)))
      atTop (nhds 64) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogSixthDerivative
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_bornWittenLogSeventhDerivative_div_scale_tendsto_oneTwentyEight :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogSeventhDerivative 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 128) := by
  have h2 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 2 (by norm_num)
  have h3 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 3 (by norm_num)
  have h4 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 4 (by norm_num)
  have h5 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 5 (by norm_num)
  have h6 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 6 (by norm_num)
  have h7 := thetaCuspC5FarTail_coordinate_inv_pow_tendsto_zero 7 (by norm_num)
  have hc : Tendsto (fun _ : ℝ => (128 : ℝ)) atTop (nhds 128) :=
    tendsto_const_nhds
  have h1 := hc.sub (h2.const_mul 192)
  have h2' := h1.sub (h3.const_mul 17856)
  have h3' := h2'.sub (h4.const_mul 233280)
  have h4' := h3'.sub (h5.const_mul 1010880)
  have h5' := h4'.sub (h6.const_mul 1749600)
  have h := h5'.sub (h7.const_mul 1049760)
  have h0 : Tendsto (fun x : ℝ =>
      128 - 192 * (1 / thetaCuspLikelihoodCoordinate x ^ (2 : ℕ)) -
        17856 * (1 / thetaCuspLikelihoodCoordinate x ^ (3 : ℕ)) -
        233280 * (1 / thetaCuspLikelihoodCoordinate x ^ (4 : ℕ)) -
        1010880 * (1 / thetaCuspLikelihoodCoordinate x ^ (5 : ℕ)) -
        1749600 * (1 / thetaCuspLikelihoodCoordinate x ^ (6 : ℕ)) -
        1049760 * (1 / thetaCuspLikelihoodCoordinate x ^ (7 : ℕ)))
      atTop (nhds 128) := by simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hq := thetaCuspBornWittenWeight_pos (n := 1) (by norm_num) hx
  have hs := thetaCuspC5FarTail_reflectionScale_ne_zero x
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate] at hq
  unfold thetaCuspBornWittenLogSeventhDerivative
  rw [thetaCuspC5FarTail_bornWittenWeight_one_eq_coordinate,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs, hq.ne']
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 2 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 4) := by
  have h := thetaCuspC5FarTail_bornWittenLogCurvature_div_scale_tendsto_four.sub
    thetaCuspC5FarTail_likelihoodJetTwo_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogCurvature 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetTwo x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 4) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_two_thetaCuspLogSource_eq_factor hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx0]
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetThree_div_scale_tendsto_eight :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 3 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 8) := by
  have h := thetaCuspC5FarTail_bornWittenLogThirdDerivative_div_scale_tendsto_eight.sub
    thetaCuspC5FarTail_likelihoodJetThree_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogThirdDerivative 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetThree x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 8) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_three_thetaCuspLogSource_eq_full_jets hx0,
    thetaCuspFirstAtomLogJetThree,
    ← thetaCuspLikelihoodSourceLogPartitionJetThree_eq_higherLikelihoodLogJetThree hx0]
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetFour_div_scale_tendsto_sixteen :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 4 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 16) := by
  have h := thetaCuspC5FarTail_bornWittenLogFourthDerivative_div_scale_tendsto_sixteen.sub
    thetaCuspC5FarTail_likelihoodJetFour_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogFourthDerivative 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetFour x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 16) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_four_thetaCuspLogSource_eq_factor hx0,
    ← thetaCuspLikelihoodSourceLogPartitionJetFour_eq_higherLikelihoodLogJetFour hx0]
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetFive_div_scale_tendsto_thirtytwo :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 5 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 32) := by
  have h := thetaCuspC5FarTail_bornWittenLogFifthDerivative_div_scale_tendsto_thirtytwo.sub
    thetaCuspC5FarTail_likelihoodJetFive_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogFifthDerivative 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetFive x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 32) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_five_thetaCuspLogSource_eq_full_jets hx0]
  unfold thetaCuspFullLogJetFive
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetSix_div_scale_tendsto_sixtyfour :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 6 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 64) := by
  have h := thetaCuspC5FarTail_bornWittenLogSixthDerivative_div_scale_tendsto_sixtyfour.sub
    thetaCuspC5FarTail_likelihoodJetSix_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogSixthDerivative 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetSix x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 64) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_six_thetaCuspLogSource_eq_full_jets hx0]
  unfold thetaCuspFullLogJetSix
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_neg_logJetSeven_div_scale_tendsto_oneTwentyEight :
    Tendsto (fun x : ℝ =>
      (-iteratedDeriv 7 thetaCuspLogSource x) /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 128) := by
  have h := thetaCuspC5FarTail_bornWittenLogSeventhDerivative_div_scale_tendsto_oneTwentyEight.sub
    thetaCuspC5FarTail_likelihoodJetSeven_div_scale_tendsto_zero
  have h0 : Tendsto (fun x : ℝ =>
      thetaCuspBornWittenLogSeventhDerivative 1 x /
          thetaCuspSingleAtomReflectionScale 1 x -
        thetaCuspLikelihoodSourceLogPartitionJetSeven x /
          thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 128) := by
    simpa using h
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [iteratedDeriv_seven_thetaCuspLogSource_eq_full_jets hx0]
  unfold thetaCuspFullLogJetSeven
  field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  ring_nf

theorem thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero :
    Tendsto (fun x : ℝ =>
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp thetaCuspC5FarTail_scale_tendsto_atTop

/-- Exact far-tail constant for completed C5 orientation. The cubic part loses one scale,
while surviving quartic first-atom terms have constant `36864`. -/
theorem tendsto_thetaCuspC5ExactCompletedSeamOrientation_div_scale_four_atTop :
    Tendsto (fun x : ℝ =>
      thetaCuspC5ExactCompletedSeamOrientation x /
        thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ))
      atTop (nhds 36864) := by
  have hs := thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hA := thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four
  have hB := thetaCuspC5FarTail_neg_logJetFour_div_scale_tendsto_sixteen
  have hC := thetaCuspC5FarTail_neg_logJetSix_div_scale_tendsto_sixtyfour
  have hE := thetaCuspC5FarTail_neg_logJetThree_div_scale_tendsto_eight
  have hF := thetaCuspC5FarTail_neg_logJetFive_div_scale_tendsto_thirtytwo
  have hG := thetaCuspC5FarTail_neg_logJetSeven_div_scale_tendsto_oneTwentyEight
  have h1 := hs.mul ((hA.pow 2).mul hG)
  have h2 := (hs.mul ((hA.mul hC).mul hE)).const_mul 3
  have h3 := (hs.mul ((hA.mul hB).mul hF)).const_mul 2
  have h4 := (hs.mul ((hB.pow 2).mul hE)).const_mul 4
  have h5 := ((hA.pow 3).mul hF).const_mul 18
  have h6 := (((hA.pow 2).mul hB).mul hE).const_mul 36
  have h := ((((h1.sub h2).sub h3).add h4).sub h5).add h6
  convert h using 1
  · funext x
    unfold thetaCuspC5ExactCompletedSeamOrientation
    field_simp [thetaCuspC5FarTail_reflectionScale_ne_zero x]
  · norm_num

/-- The exact completed C5 seam orientation is strictly positive on a cofinal physical tail. -/
theorem eventually_thetaCuspC5ExactCompletedSeamOrientation_pos :
    ∀ᶠ x : ℝ in atTop, 0 < thetaCuspC5ExactCompletedSeamOrientation x := by
  have hnormalized := tendsto_thetaCuspC5ExactCompletedSeamOrientation_div_scale_four_atTop
  have hpositive : ∀ᶠ x : ℝ in atTop,
      0 < thetaCuspC5ExactCompletedSeamOrientation x /
        thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) :=
    (tendsto_order.1 hnormalized).1 0 (by norm_num)
  filter_upwards [hpositive] with x hx
  have hs : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hmul := mul_pos hx (pow_pos hs 4)
  rwa [div_mul_cancel₀ _ (pow_ne_zero 4 hs.ne')] at hmul

/-- Threshold form of cofinal positivity: the remaining exact C5 orientation burden is confined
to one compact physical source interval. -/
theorem exists_forall_ge_thetaCuspC5ExactCompletedSeamOrientation_pos :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      0 < thetaCuspC5ExactCompletedSeamOrientation x := by
  exact eventually_atTop.1 eventually_thetaCuspC5ExactCompletedSeamOrientation_pos

end

end RHTower
