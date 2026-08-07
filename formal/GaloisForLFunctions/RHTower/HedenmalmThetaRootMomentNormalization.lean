import GaloisForLFunctions.RHTower.HedenmalmThetaSourceModeNormalization

/-!
# Canonical monopole and dipole of the theta-source root mode

The source-side mass normalization transports to the explicit quantile root mode.  At every
theta-source divisor in the strip, `rootG` is genuinely integrable on `(0,1)` and has exact mean
one.  Integrating the pinned ODE `rootH' = rootG - 1` against the centered coordinate then gives

`∫ (t - 1/2) rootG(t) dt = -∫ rootH(t) dt`.

Thus the universal rank-two boundary state of every actual divisor mode has a fixed monopole and
only one remaining dipole scalar.  The ordered-correlation flux identity identifies its hyperbolic
boundary pairing exactly with `2 Im(z)` times the positive quantile energy.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

/-- The source-mode quantile transform is `√M` times the explicit root mode. -/
theorem quantileTransform_sourceModeF_eq_rootG {z : ℂ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileTransform thetaSource (sourceModeF thetaSource z) t =
      (Real.sqrt thetaSource.mass : ℂ) * rootG thetaSource z t := by
  rw [quantileTransform, sourceModeF, rootG_eq,
    rootH_eq_sourceModeU thetaSource z ht, quantileSpeed]
  have hM : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  have hk : (thetaSource.k (thetaSource.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.pos_k _).ne'
  push_cast
  field_simp
  rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring

/-- **Canonical monopole.**  Every theta-source divisor root mode has total quantile mass one. -/
theorem integral_rootG_thetaSource_eq_one {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (∫ t in Ioo (0 : ℝ) 1, rootG thetaSource z t) = 1 := by
  have htransform := integral_quantileTransform thetaSource
    (integrable_sourceModeF_thetaSource hz hzero).aestronglyMeasurable
  have heq : (∫ t in Ioo (0 : ℝ) 1,
      quantileTransform thetaSource (sourceModeF thetaSource z) t) =
      ∫ t in Ioo (0 : ℝ) 1,
        (Real.sqrt thetaSource.mass : ℂ) * rootG thetaSource z t := by
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro t ht
    exact quantileTransform_sourceModeF_eq_rootG ht
  rw [heq, MeasureTheory.integral_const_mul,
    integral_sourceModeF_thetaSource_eq_mass hz hzero] at htransform
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  have hsq : (Real.sqrt thetaSource.mass : ℂ) *
      (Real.sqrt thetaSource.mass : ℂ) = (thetaSource.mass : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt thetaSource.mass_pos.le]
  apply (mul_left_cancel₀ hsqrt)
  calc
    (Real.sqrt thetaSource.mass : ℂ) *
        (∫ t in Ioo (0 : ℝ) 1, rootG thetaSource z t) =
        (thetaSource.mass : ℂ) / (Real.sqrt thetaSource.mass : ℂ) := htransform
    _ = (Real.sqrt thetaSource.mass : ℂ) * 1 := by
      apply (div_eq_iff hsqrt).2
      simpa [pow_two] using hsq.symm

/-- The canonical quantile root mode is genuinely `L¹`, not merely improperly integrable. -/
theorem integrableOn_rootG_thetaSource {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    IntegrableOn (rootG thetaSource z) (Ioo (0 : ℝ) 1) volume := by
  by_contra hnot
  have hundef : (∫ t in Ioo (0 : ℝ) 1, rootG thetaSource z t) = 0 :=
    integral_undef hnot
  rw [integral_rootG_thetaSource_eq_one hz hzero] at hundef
  exact one_ne_zero hundef

/-- The explicit root function is continuous on the open quantile interval. -/
theorem continuousOn_rootG {S : PositiveDensitySource} {z : ℂ}
    (hz : HasShiftedTail S z) :
    ContinuousOn (rootG S z) (Ioo (0 : ℝ) 1) := by
  rw [show rootG S z = fun t =>
    -(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootH S z t by
      funext t
      exact rootG_eq S t]
  have hq : ContinuousOn (fun t : ℝ => ((quantileSpeed S t : ℝ) : ℂ))
      (Ioo (0 : ℝ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_quantileSpeed S)
  exact (ContinuousOn.neg (continuousOn_const.mul hq)).mul (continuousOn_rootH S hz)

/-- Integration by parts reduces the centered root moment on any interior interval to endpoint
values, the root primitive, and the elementary centered-coordinate integral. -/
theorem centeredRootMoment_two_point {S : PositiveDensitySource} {z : ℂ}
    (hz : HasShiftedTail S z) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    (∫ t in a..b, (((t : ℝ) : ℂ) - 1 / 2) * rootG S z t) =
      (((b : ℝ) : ℂ) - 1 / 2) * rootH S z b
        - (((a : ℝ) : ℂ) - 1 / 2) * rootH S z a
        - (∫ t in a..b, rootH S z t)
        + (∫ t in a..b, (((t : ℝ) : ℂ) - 1 / 2)) := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 :=
    Set.ordConnected_Ioo.uIcc_subset ha hb
  have hu : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) - 1 / 2) 1 t := by
    intro t _
    simpa using (hasDerivAt_id t).ofReal_comp.sub_const (1 / 2 : ℂ)
  have hv : ∀ t ∈ uIcc a b,
      HasDerivAt (rootH S z) (rootG S z t - 1) t := by
    intro t ht
    exact hasDerivAt_rootH S hz (hsub ht)
  have hu' : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a b :=
    intervalIntegrable_const
  have hv' : IntervalIntegrable (fun t => rootG S z t - 1) volume a b :=
    (((continuousOn_rootG hz).sub continuousOn_const).mono hsub).intervalIntegrable
  have hc : IntervalIntegrable (fun t : ℝ => ((t : ℝ) : ℂ) - 1 / 2) volume a b := by
    exact (Complex.continuous_ofReal.sub continuous_const).intervalIntegrable a b
  have hcg : IntervalIntegrable
      (fun t : ℝ => (((t : ℝ) : ℂ) - 1 / 2) * rootG S z t) volume a b :=
    hc.mul_continuousOn ((continuousOn_rootG hz).mono hsub)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hleft : (∫ t in a..b,
      (((t : ℝ) : ℂ) - 1 / 2) * (rootG S z t - 1)) =
      (∫ t in a..b, (((t : ℝ) : ℂ) - 1 / 2) * rootG S z t)
        - ∫ t in a..b, (((t : ℝ) : ℂ) - 1 / 2) := by
    rw [← intervalIntegral.integral_sub hcg hc]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hleft] at hparts
  simp only [one_mul] at hparts
  refine ((sub_eq_iff_eq_add).mp hparts).trans ?_
  abel

/-- On the symmetric interior exhaustion the elementary centered integral vanishes identically. -/
theorem centeredRootMoment_interiorSeq {S : PositiveDensitySource} {z : ℂ}
    (hz : HasShiftedTail S z) (n : ℕ) :
    (∫ t in interiorSeq n..(1 - interiorSeq n),
        (((t : ℝ) : ℂ) - 1 / 2) * rootG S z t) =
      ((((1 - interiorSeq n : ℝ) : ℝ) : ℂ) - 1 / 2) *
          rootH S z (1 - interiorSeq n)
        - (((interiorSeq n : ℝ) : ℂ) - 1 / 2) * rootH S z (interiorSeq n)
        - (∫ t in interiorSeq n..(1 - interiorSeq n), rootH S z t) := by
  have ha : interiorSeq n ∈ Ioo (0 : ℝ) 1 :=
    ⟨interiorSeq_pos n,
      lt_of_le_of_lt (interiorSeq_le_half n) (by norm_num)⟩
  have hb : 1 - interiorSeq n ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [interiorSeq_le_half n], by linarith [interiorSeq_pos n]⟩
  have h := centeredRootMoment_two_point hz ha hb
  have hcenter : (∫ t in interiorSeq n..(1 - interiorSeq n),
      (((t : ℝ) : ℂ) - 1 / 2)) = 0 := by
    rw [intervalIntegral.integral_sub
      (Complex.continuous_ofReal.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_ofReal]
    simp
    ring
  rw [hcenter, add_zero] at h
  exact h

/-- The centered quantile moment is integrable for every theta-source divisor mode. -/
theorem integrableOn_centered_mul_rootG_thetaSource {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    IntegrableOn (fun t : ℝ => (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t)
      (Ioo (0 : ℝ) 1) volume := by
  refine (integrableOn_rootG_thetaSource hz hzero).bdd_mul (c := 1) ?_ ?_
  · exact (Complex.continuous_ofReal.sub continuous_const).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [show (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]

/-- **Canonical dipole.**  The centered first moment of an actual theta-source divisor mode is the
negative integral of its pinned primitive. -/
theorem integral_centered_rootG_thetaSource_eq_neg_rootH {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    (∫ t in Ioo (0 : ℝ) 1,
      (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) =
        -(∫ t in Ioo (0 : ℝ) 1, rootH thetaSource z t) := by
  have he := rootModeEndpoints_thetaSource hz hzero
  have hcenterInt := integrableOn_centered_mul_rootG_thetaSource hz hzero
  have hlimCenter : Tendsto (fun n : ℕ =>
      ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
        (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) atTop
      (𝓝 (∫ t in Ioo (0 : ℝ) 1,
        (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (fun n : ℕ => measurableSet_Ioc) monotone_interiorIoc
      (by rw [iUnion_interiorIoc]; exact hcenterInt)
    rwa [iUnion_interiorIoc] at h
  have hlimH : Tendsto (fun n : ℕ =>
      ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n), rootH thetaSource z t) atTop
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, rootH thetaSource z t)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (fun n : ℕ => measurableSet_Ioc) monotone_interiorIoc
      (by rw [iUnion_interiorIoc]; exact he.integrableValue)
    rwa [iUnion_interiorIoc] at h
  have hmemL : ∀ n : ℕ, interiorSeq n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨interiorSeq_pos n,
      lt_of_le_of_lt (interiorSeq_le_half n) (by norm_num)⟩
  have hmemR : ∀ n : ℕ, 1 - interiorSeq n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨by linarith [interiorSeq_le_half n], by linarith [interiorSeq_pos n]⟩
  have heq : ∀ n : ℕ,
      (∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
        (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) =
        ((((1 - interiorSeq n : ℝ) : ℝ) : ℂ) - 1 / 2) *
            rootH thetaSource z (1 - interiorSeq n)
          - (((interiorSeq n : ℝ) : ℂ) - 1 / 2) *
            rootH thetaSource z (interiorSeq n)
          - (∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
            rootH thetaSource z t) := by
    intro n
    have h := centeredRootMoment_interiorSeq
      (hasShiftedTail_thetaSource hz) n
    rw [intervalIntegral.integral_of_le (by linarith [interiorSeq_le_half n]),
      intervalIntegral.integral_of_le (by linarith [interiorSeq_le_half n])] at h
    exact h
  have hsqL : Tendsto
      (fun n : ℕ => ‖rootH thetaSource z (interiorSeq n)‖ ^ 2) atTop (𝓝 0) := by
    refine he.tendstoLeft.comp ?_
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_interiorSeq
      (Filter.Eventually.of_forall fun n => interiorSeq_pos n)
  have hsqR : Tendsto
      (fun n : ℕ => ‖rootH thetaSource z (1 - interiorSeq n)‖ ^ 2) atTop (𝓝 0) := by
    refine he.tendstoRight.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall fun n => by
        simp only [mem_Iio]
        linarith [interiorSeq_pos n])
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub tendsto_interiorSeq
  have hnormL : Tendsto
      (fun n : ℕ => ‖rootH thetaSource z (interiorSeq n)‖) atTop (𝓝 0) := by
    have h := hsqL.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using h
  have hnormR : Tendsto
      (fun n : ℕ => ‖rootH thetaSource z (1 - interiorSeq n)‖) atTop (𝓝 0) := by
    have h := hsqR.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using h
  have hvalL : Tendsto
      (fun n : ℕ => rootH thetaSource z (interiorSeq n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormL
  have hvalR : Tendsto
      (fun n : ℕ => rootH thetaSource z (1 - interiorSeq n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormR
  have haC : Tendsto (fun n : ℕ => ((interiorSeq n : ℝ) : ℂ)) atTop (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_interiorSeq
  have hbR : Tendsto (fun n : ℕ => (((1 - interiorSeq n : ℝ) : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hreal : Tendsto (fun n : ℕ => (1 - interiorSeq n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub tendsto_interiorSeq
    exact (Complex.continuous_ofReal.tendsto 1).comp hreal
  have hcoefL : Tendsto (fun n : ℕ => ((interiorSeq n : ℝ) : ℂ) - 1 / 2)
      atTop (𝓝 (-(1 / 2 : ℂ))) := by
    simpa using haC.sub (tendsto_const_nhds (x := (1 / 2 : ℂ)) (f := atTop))
  have hcoefR : Tendsto
      (fun n : ℕ => (((1 - interiorSeq n : ℝ) : ℝ) : ℂ) - 1 / 2)
      atTop (𝓝 (1 / 2 : ℂ)) := by
    convert hbR.sub (tendsto_const_nhds (x := (1 / 2 : ℂ)) (f := atTop)) using 1
    norm_num
  have hboundary : Tendsto (fun n : ℕ =>
      ((((1 - interiorSeq n : ℝ) : ℝ) : ℂ) - 1 / 2) *
          rootH thetaSource z (1 - interiorSeq n)
        - (((interiorSeq n : ℝ) : ℂ) - 1 / 2) *
          rootH thetaSource z (interiorSeq n)) atTop (𝓝 0) := by
    have h := (hcoefR.mul hvalR).sub (hcoefL.mul hvalL)
    simpa using h
  have hlimRhs : Tendsto (fun n : ℕ =>
      ((((1 - interiorSeq n : ℝ) : ℝ) : ℂ) - 1 / 2) *
          rootH thetaSource z (1 - interiorSeq n)
        - (((interiorSeq n : ℝ) : ℂ) - 1 / 2) *
          rootH thetaSource z (interiorSeq n)
        - (∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
          rootH thetaSource z t)) atTop
      (𝓝 (-(∫ t in Ioo (0 : ℝ) 1, rootH thetaSource z t))) := by
    have h := hboundary.sub hlimH
    simpa using h
  have hlimCenter' : Tendsto (fun n : ℕ =>
      ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
        (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t) atTop
      (𝓝 (-(∫ t in Ioo (0 : ℝ) 1, rootH thetaSource z t))) := by
    refine Filter.Tendsto.congr (fun n => (heq n).symm) ?_
    exact hlimRhs
  exact tendsto_nhds_unique hlimCenter hlimCenter'

/-- **Exact divisor boundary charge.**  The fixed monopole and centered dipole reduce the universal
rank-two boundary pairing to `2 Im(z)` times the quantile energy. -/
theorem rootBoundaryMomentPairing_thetaSource {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    let m := (∫ t in Ioo (0 : ℝ) 1, rootG thetaSource z t)
    let c := (∫ t in Ioo (0 : ℝ) 1,
      (((t : ℝ) : ℂ) - 1 / 2) * rootG thetaSource z t)
    let e : ℝ := (∫ t in Ioo (0 : ℝ) 1,
      quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ 2)
    0 - ((starRingEnd ℂ) m * c + (starRingEnd ℂ) c * m) =
      Complex.ofReal (2 * z.im * e) := by
  dsimp only
  have hflux := rootFlux_identity_thetaSource hz hzero
  rw [MeasureTheory.integral_neg] at hflux
  rw [← integral_centered_rootG_thetaSource_eq_neg_rootH hz hzero] at hflux
  rw [integral_rootG_thetaSource_eq_one hz hzero, map_one, one_mul, mul_one, zero_sub,
    Complex.add_conj]
  norm_cast
  linarith [hflux]

end HedenmalmThetaSource

end

end RHTower
