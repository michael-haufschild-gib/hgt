import GaloisForLFunctions.RHTower.SelbergThetaSourceEnergy
import GaloisForLFunctions.RHTower.SelbergResummedSource

/-!
# Actual theta zero modes in the native modular Hilbert space

Complete half-density periodization preserves the strict theta source disk.
Both literal sources are invariant, bounded on the native cell and in native
L2. Absolute unfolding evaluates their means with the complete spectral
shift retained. No native eigenvalue equation or occurrence is asserted.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergThetaNativeSource
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse HedenmalmThetaSource
open SelbergThetaSourcePhase SelbergThetaSourceVariance SelbergThetaSourceEnergy
noncomputable section

private theorem positive_tilt_bound (a : ℝ) (ha : a ≤ 3) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (a*x)*thetaCuspFullSource x ≤ thetaEnvelopeUpper := by
  have he : (1+x)^2 ≤ Real.exp (2*x) := by
    rw [← exp_sq]
    nlinarith [Real.add_one_le_exp x, Real.exp_pos x]
  have hp : 3*Real.exp (2*x) ≤ Real.pi*Real.exp (2*x) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos _).le
  have hex : a*x+9*x/2-Real.pi*Real.exp (2*x) ≤ 0 := by
    have ha' := mul_le_mul_of_nonneg_right ha hx
    nlinarith [sq_nonneg (x-1/4)]
  calc
    _ ≤ Real.exp (a*x)*(thetaEnvelopeUpper*thetaEnvelope x) :=
      mul_le_mul_of_nonneg_left (thetaCuspFullSource_le_envelope hx) (Real.exp_pos _).le
    _ = thetaEnvelopeUpper*Real.exp (a*x+9*x/2-Real.pi*Real.exp (2*x)) := by
      unfold thetaEnvelope
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ ≤ thetaEnvelopeUpper :=
      mul_le_of_le_one_right thetaEnvelopeUpper_pos.le (Real.exp_le_one_iff.mpr hex)

private theorem tilt_bound (a : ℝ) (ha : |a| ≤ 3) (x : ℝ) :
    Real.exp (a*x)*thetaCuspFullSource x ≤ thetaEnvelopeUpper := by
  rcases le_total 0 x with hx | hx
  · exact positive_tilt_bound a ((le_abs_self a).trans ha) hx
  · have h := positive_tilt_bound (-a) ((neg_le_abs a).trans ha) (neg_nonneg.mpr hx)
    simpa only [neg_mul_neg, thetaCuspFullSource_neg] using h

/-- Positive theta half-density in the original height coordinate. -/
def positiveProfile (y : ℝ) : ℝ :=
  Real.exp (Real.log y/2)*thetaCuspFullSource (Real.log y/2)

/-- The original two-ended theta mode with the same half-density. -/
def modeProfile (q : XiZeroCopy) (y : ℝ) : ℂ :=
  (positiveProfile y:ℂ)*sourceRatio q (Real.log y/2)

private theorem profile_pos (y : ℝ) : 0 < positiveProfile y :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

private theorem exp_log_half (y : ℝ) (hy : 0 < y) : Real.exp (2*(Real.log y/2)) = y := by
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), Real.exp_log hy]

private theorem profile_bound (y : ℝ) : positiveProfile y ≤ thetaEnvelopeUpper := by
  simpa only [positiveProfile, one_mul] using tilt_bound 1 (by norm_num) (Real.log y/2)

private theorem profile_bound_sq {y : ℝ} (hy : 0 < y) :
    positiveProfile y ≤ thetaEnvelopeUpper*y^2 := by
  have h := tilt_bound (-3) (by norm_num) (Real.log y/2)
  have he : positiveProfile y = y^2*
      (Real.exp (-3*(Real.log y/2))*thetaCuspFullSource (Real.log y/2)) := by
    have hex : Real.exp (Real.log y/2) = y^2*Real.exp (-3*(Real.log y/2)) := by
      have hy2 : y^2 = Real.exp (4*(Real.log y/2)) := by
        calc
          _ = (Real.exp (2*(Real.log y/2)))^2 := congrArg (fun r : ℝ => r^2) (exp_log_half y hy).symm
          _ = _ := by rw [exp_sq]; congr 1; ring
      rw [hy2, ← Real.exp_add]
      congr 1
      ring
    unfold positiveProfile
    rw [hex]
    ring
  rw [he]
  nlinarith [sq_nonneg y]

private theorem positive_rows_summable (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => positiveProfile (gammaSetMatrix v.1 • z).im) := by
  have hs := (positiveCuspRows_summable 2 (by norm_num) z).mul_left thetaEnvelopeUpper
  apply Summable.of_norm_bounded hs
  intro v
  rw [Real.norm_eq_abs, abs_of_pos (profile_pos (gammaSetMatrix v.1 • z).im), Real.rpow_two]
  exact profile_bound_sq (gammaSetMatrix v.1 • z).im_pos

private theorem mode_rows_summable (q : XiZeroCopy) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => modeProfile q (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C, _, hC⟩ := sourceRatio_bounded q
  apply Summable.of_norm_bounded ((positive_rows_summable z).mul_left C)
  intro v
  rw [modeProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (profile_pos (gammaSetMatrix v.1 • z).im)]
  nlinarith [hC (Real.log (gammaSetMatrix v.1 • z).im/2), profile_pos (gammaSetMatrix v.1 • z).im]

/-- Complete positive primitive-row source. -/
def positiveSource (z : UpperHalfPlane) : ℝ :=
  ∑' v : gammaSetHalf, positiveProfile (gammaSetMatrix v.1 • z).im

/-- The actual complete modular periodization of the original mode seed. -/
def modeSource (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  periodize (cuspHeightSeed (modeProfile q)) z

private theorem modeSource_rows (q : XiZeroCopy) (z : UpperHalfPlane) :
    modeSource q z = ∑' v : gammaSetHalf, modeProfile q (gammaSetMatrix v.1 • z).im :=
  periodize_cuspHeightSeed_eq_rows_of_rows_summable _ z (mode_rows_summable q z)

private theorem positiveSource_periodize (z : UpperHalfPlane) :
    (positiveSource z:ℂ) = periodize (cuspHeightSeed (fun y => (positiveProfile y:ℂ))) z := by
  have hs : Summable (fun v : gammaSetHalf => (positiveProfile (gammaSetMatrix v.1 • z).im:ℂ)) :=
    Complex.ofRealCLM.summable (positive_rows_summable z)
  have hh := periodize_cuspHeightSeed_eq_rows_of_rows_summable
    (fun y : ℝ => (positiveProfile y:ℂ)) z hs
  exact (Complex.ofReal_tsum (fun v : gammaSetHalf => positiveProfile (gammaSetMatrix v.1 • z).im)).trans hh.symm

/-- The positive modular source has positive mass at every original point. -/
theorem positiveSource_pos (z : UpperHalfPlane) : 0 < positiveSource z := by
  exact (positive_rows_summable z).tsum_pos
    (fun v => (profile_pos (gammaSetMatrix v.1 • z).im).le)
    cuspIdentityRow (profile_pos (gammaSetMatrix cuspIdentityRow.1 • z).im)

private theorem profile_disk (q : XiZeroCopy) (y : ℝ) :
    ‖(positiveProfile y:ℂ)+((xiSpectralPoint q).re:ℂ)*modeProfile q y‖ < positiveProfile y := by
  have he : (positiveProfile y:ℂ)+((xiSpectralPoint q).re:ℂ)*modeProfile q y =
      (positiveProfile y:ℂ)*(1+((xiSpectralPoint q).re:ℂ)*sourceRatio q (Real.log y/2)) := by
    unfold modeProfile
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (profile_pos y)]
  exact mul_lt_of_lt_one_right (profile_pos y) (source_ratio_strict_disk q (Real.log y/2))

/-- Every complete modular row is retained in the strict source disk. -/
theorem modeSource_strict_disk (q : XiZeroCopy) (z : UpperHalfPlane) :
    ‖(positiveSource z:ℂ)+((xiSpectralPoint q).re:ℂ)*modeSource q z‖ < positiveSource z := by
  let R (v : gammaSetHalf) : ℝ := (gammaSetMatrix v.1 • z).im
  have hsP : Summable (fun v : gammaSetHalf => (positiveProfile (R v):ℂ)) :=
    Complex.ofRealCLM.summable (positive_rows_summable z)
  have hsU := (mode_rows_summable q z).mul_left ((xiSpectralPoint q).re:ℂ)
  have hs := hsP.add hsU
  have he : (positiveSource z:ℂ)+((xiSpectralPoint q).re:ℂ)*modeSource q z =
      ∑' v : gammaSetHalf, ((positiveProfile (R v):ℂ)+((xiSpectralPoint q).re:ℂ)*modeProfile q (R v)) := by
    rw [hsP.tsum_add hsU, tsum_mul_left, ← Complex.ofReal_tsum, modeSource_rows]
    rfl
  rw [he]
  apply lt_of_le_of_lt (norm_tsum_le_tsum_norm hs.norm)
  exact Summable.tsum_lt_tsum (fun v => (profile_disk q (R v)).le)
    (profile_disk q (R cuspIdentityRow)) hs.norm (positive_rows_summable z)

/-- The complete mode source is invariant under the original modular group. -/
theorem modeSource_invariant (q : XiZeroCopy) (g : PSL2Z) (z : UpperHalfPlane) :
    modeSource q (g • z) = modeSource q z := periodize_invariant _ g z

/-- The positive comparison source has the same original modular invariance. -/
theorem positiveSource_invariant (g : PSL2Z) (z : UpperHalfPlane) :
    positiveSource (g • z) = positiveSource z := by
  apply Complex.ofReal_injective
  rw [positiveSource_periodize, positiveSource_periodize]
  exact periodize_invariant _ g z

private theorem b_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  simpa [xiSpectralPoint, Complex.mul_re, Complex.mul_im] using xi_divisor_support_im_ne_zero q.1

/-- The strict full-row disk gives an explicit pointwise native source bound. -/
theorem modeSource_norm_lt (q : XiZeroCopy) (z : UpperHalfPlane) :
    ‖modeSource q z‖ < 2*positiveSource z/|(xiSpectralPoint q).re| := by
  have hd := modeSource_strict_disk q z
  have ht := norm_sub_le ((positiveSource z:ℂ)+((xiSpectralPoint q).re:ℂ)*modeSource q z)
    (positiveSource z:ℂ)
  have he : ((positiveSource z:ℂ)+((xiSpectralPoint q).re:ℂ)*modeSource q z)-(positiveSource z:ℂ) =
      ((xiSpectralPoint q).re:ℂ)*modeSource q z := by ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (positiveSource_pos z)] at ht
  apply (lt_div_iff₀ (abs_pos.mpr (b_ne_zero q))).2
  nlinarith

/-- The original periodized mode is nonzero at every modular point. -/
theorem modeSource_ne_zero (q : XiZeroCopy) (z : UpperHalfPlane) : modeSource q z ≠ 0 := by
  intro hz
  have hd := modeSource_strict_disk q z
  rw [hz, mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (positiveSource_pos z)] at hd
  exact (lt_irrefl _) hd

private theorem positiveSource_le_rows (z : UpperHalfPlane) :
    positiveSource z ≤ thetaEnvelopeUpper*(1+positiveCuspRows 2 z-z.im^2) := by
  classical
  have hs := positive_rows_summable z
  have hquad : Summable (fun v : gammaSetHalf => (gammaSetMatrix v.1 • z).im^2) := by
    simpa only [Real.rpow_two] using positiveCuspRows_summable 2 (by norm_num) z
  have hn : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else positiveProfile (gammaSetMatrix v.1 • z).im) :=
    hs.of_nonneg_of_le (fun v => by split_ifs <;> first | exact le_rfl | exact (profile_pos _).le)
      (fun v => by split_ifs <;> first | exact le_rfl | exact (profile_pos _).le)
  have hq : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else (gammaSetMatrix v.1 • z).im^2) :=
    hquad.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  have hle := hn.tsum_le_tsum (fun v => show
      (if v=cuspIdentityRow then (0:ℝ) else positiveProfile (gammaSetMatrix v.1 • z).im) ≤
      thetaEnvelopeUpper*(if v=cuspIdentityRow then 0 else (gammaSetMatrix v.1 • z).im^2) from by
    split_ifs
    · simp
    · exact profile_bound_sq (gammaSetMatrix v.1 • z).im_pos) (hq.mul_left thetaEnvelopeUpper)
  rw [tsum_mul_left] at hle
  have hs' := hs.tsum_eq_add_tsum_ite cuspIdentityRow
  have hq' := hquad.tsum_eq_add_tsum_ite cuspIdentityRow
  rw [cuspIdentityRow_height] at hs' hq'
  change positiveSource z = _ at hs'
  have heq : (∑' v : gammaSetHalf, (gammaSetMatrix v.1 • z).im^2) = positiveCuspRows 2 z := by
    simp only [positiveCuspRows, Real.rpow_two]
  rw [heq] at hq'
  have hr : (∑' v : gammaSetHalf, if v=cuspIdentityRow then (0:ℝ)
      else (gammaSetMatrix v.1 • z).im^2) = positiveCuspRows 2 z-z.im^2 := by linarith
  rw [hr] at hle
  rw [hs']
  nlinarith [profile_bound z.im]

/-- The literal positive source is uniformly bounded on the native modular cell. -/
theorem positiveSource_bounded : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ModularGroup.fd, positiveSource z ≤ C := by
  obtain ⟨B,hB,hbound⟩ := SelbergResummedSource.nonparabolic_quadratic_bound
  refine ⟨thetaEnvelopeUpper*(1+B), mul_pos thetaEnvelopeUpper_pos (by linarith), ?_⟩
  intro z hz
  have hheight : 1/2 ≤ z.im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz, z.im_pos]
  have hh := hbound z hheight
  calc
    _ ≤ thetaEnvelopeUpper*(1+positiveCuspRows 2 z-z.im^2) := positiveSource_le_rows z
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) thetaEnvelopeUpper_pos.le

private theorem positiveProfile_measurable : Measurable positiveProfile := by
  unfold positiveProfile
  exact ((Real.measurable_log.div_const 2).exp).mul
    (contDiff_thetaCuspFullSource.continuous.measurable.comp (Real.measurable_log.div_const 2))

private theorem modeProfile_measurable (q : XiZeroCopy) : Measurable (modeProfile q) := by
  unfold modeProfile
  exact (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable).mul
    ((continuous_sourceRatio q).measurable.comp (Real.measurable_log.div_const 2))

/-- Measurability includes the full modular row sum. -/
theorem modeSource_measurable (q : XiZeroCopy) : Measurable (modeSource q) :=
  periodize_measurable _ (cuspHeightSeed_measurable _ (modeProfile_measurable q))

/-- The positive source is measurable in the original native coordinates. -/
theorem positiveSource_measurable : Measurable positiveSource := by
  have hm := periodize_measurable _ (cuspHeightSeed_measurable _
    (Complex.continuous_ofReal.measurable.comp positiveProfile_measurable))
  have he : positiveSource = fun z =>
      (periodize (cuspHeightSeed (fun y => (positiveProfile y:ℂ))) z).re := by
    funext z
    rw [← positiveSource_periodize]
    rfl
  rw [he]
  exact Complex.continuous_re.measurable.comp hm

/-- The positive comparison source belongs to the original native L2 space. -/
theorem positiveSource_memLp : MemLp positiveSource 2 angularMeasure := by
  obtain ⟨C, _, hC⟩ := positiveSource_bounded
  apply MemLp.of_bound positiveSource_measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (positiveSource_pos z)]
  exact hC z hz

/-- The actual complete theta zero mode is admitted in the native Hilbert space. -/
theorem modeSource_memLp (q : XiZeroCopy) : MemLp (modeSource q) 2 angularMeasure := by
  obtain ⟨C, _, hC⟩ := positiveSource_bounded
  have hb : 0 < |(xiSpectralPoint q).re| := abs_pos.mpr (b_ne_zero q)
  apply MemLp.of_bound (modeSource_measurable q).aestronglyMeasurable (2*C/|(xiSpectralPoint q).re|)
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  exact (modeSource_norm_lt q z).le.trans
    (div_le_div_of_nonneg_right (by linarith [hC z hz]) hb.le)

private theorem height_log_continuous : Continuous (fun z : UpperHalfPlane => Real.log z.im/2) :=
  (continuous_im.log (fun z => z.im_pos.ne')).div_const 2

private theorem positive_height_continuous : Continuous (fun z : UpperHalfPlane => positiveProfile z.im) :=
  (Real.continuous_exp.comp height_log_continuous).mul
    (contDiff_thetaCuspFullSource.continuous.comp height_log_continuous)

private theorem mode_height_continuous (q : XiZeroCopy) : Continuous (fun z : UpperHalfPlane => modeProfile q z.im) :=
  (Complex.continuous_ofReal.comp positive_height_continuous).mul
    ((continuous_sourceRatio q).comp height_log_continuous)

private theorem positive_strip_integrable :
    IntegrableOn (fun z : UpperHalfPlane => (positiveProfile z.im:ℂ)) modularStrip volume := by
  apply modularStrip_integrable_of_two_bounds _
    (Complex.continuous_ofReal.comp positive_height_continuous) 2 thetaEnvelopeUpper thetaEnvelopeUpper (by norm_num)
  · intro z _ _
    simp only [Function.comp_apply]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (profile_pos z.im), Real.rpow_two]
    exact profile_bound_sq z.im_pos
  · intro z _ _
    simp only [Function.comp_apply]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (profile_pos z.im)]
    exact profile_bound z.im

private theorem mode_strip_integrable (q : XiZeroCopy) :
    IntegrableOn (fun z : UpperHalfPlane => modeProfile q z.im) modularStrip volume := by
  obtain ⟨C,hC0,hC⟩ := sourceRatio_bounded q
  have hb (y : ℝ) : ‖modeProfile q y‖ ≤ C*positiveProfile y := by
    rw [modeProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (profile_pos y)]
    nlinarith [hC (Real.log y/2), profile_pos y]
  apply modularStrip_integrable_of_two_bounds _ (mode_height_continuous q)
    2 (C*thetaEnvelopeUpper) (C*thetaEnvelopeUpper) (by norm_num)
  · intro z _ _
    calc
      _ ≤ C*positiveProfile z.im := hb z.im
      _ ≤ C*(thetaEnvelopeUpper*z.im^2) :=
        mul_le_mul_of_nonneg_left (profile_bound_sq z.im_pos) hC0.le
      _ = _ := by rw [Real.rpow_two]; ring
  · intro z _ _
    exact (hb z.im).trans (mul_le_mul_of_nonneg_left (profile_bound z.im) hC0.le)

private theorem profile_periodic (h : ℝ → ℂ) (n : ℤ) (z : UpperHalfPlane) :
    h (ModularGroup.T^n • z).im = h z.im := by rw [ModularGroup.im_T_zpow_smul]

private theorem profile_unfold (h : ℝ → ℂ)
    (hs : ∀ z : UpperHalfPlane, Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im))
    (hi : IntegrableOn (fun z : UpperHalfPlane => h z.im) modularStrip volume) :
    (∫ z, periodize (cuspHeightSeed h) z ∂angularMeasure) = ∫ z in modularStrip, h z.im := by
  have hrow (v : gammaSetHalf) :
      Integrable (fun z : UpperHalfPlane => h (gammaSetMatrix v.1 • z).im) angularMeasure :=
    (integrableOn_smul_set_iff _ _ _).mp
      (integrableOn_smul_fd_of_periodic (profile_periodic h) hi _)
  let φ : UpperHalfPlane → ℂ := fun z => (‖h z.im‖:ℂ)
  have hp : ∀ (n : ℤ) (z : UpperHalfPlane), φ (ModularGroup.T^n • z) = φ z := by
    intro n z
    exact congrArg (fun r : ℂ => (‖r‖:ℂ)) (profile_periodic h n z)
  have hφ : IntegrableOn φ modularStrip volume := hi.norm.ofReal
  have hsum : Summable (fun v : gammaSetHalf =>
      ∫ z, ‖h (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure) := by
    have hh := (Complex.reCLM.hasSum (hasSum_fdUnfoldTerm_half hp hφ)).summable
    convert hh using 1
    funext v
    change (∫ z, ‖h (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure) =
      (∫ z, (‖h (gammaSetMatrix v.1 • z).im‖:ℂ) ∂angularMeasure).re
    have he : (∫ z, (‖h (gammaSetMatrix v.1 • z).im‖:ℂ) ∂angularMeasure) =
        ((∫ z, ‖h (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure:ℝ):ℂ) := integral_ofReal
    rw [he, Complex.ofReal_re]
  have ht := (hasSum_integral_of_summable_integral_norm hrow hsum).tsum_eq
  have hu := (hasSum_fdUnfoldTerm_half (profile_periodic h) hi).tsum_eq
  rw [← isFundamentalDomain_modularStrip.setIntegral_eq isFundamentalDomain_iUnion_halfRep_smul_fd
    (translationSubgroup_invariant_of_periodic (profile_periodic h))] at hu
  calc
    _ = ∫ z, ∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im ∂angularMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => periodize_cuspHeightSeed_eq_rows_of_rows_summable h z (hs z))
    _ = _ := ht.symm.trans hu

private theorem strip_height_integral (h : ℝ → ℂ)
    (hi : IntegrableOn (fun z : UpperHalfPlane => h z.im) modularStrip volume) :
    (∫ z in modularStrip, h z.im) = ∫ y in Ioi (0:ℝ), (y^2)⁻¹ • h y := by
  rw [setIntegral_modularStrip_eq_iterated _ hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have him (x : ℝ) : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp only [him, integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul]

private theorem halfDensity_integral (v : ℝ → ℂ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • ((Real.exp (Real.log y/2):ℂ)*v (Real.log y/2))) =
      (2:ℂ)*(∫ x, (Real.exp (-x):ℂ)*v x) := by
  have hrange : (fun x : ℝ => Real.exp (2*x)) '' univ = Ioi (0:ℝ) := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact Real.exp_pos _
    · intro hy
      exact ⟨Real.log y/2, mem_univ _, exp_log_half y hy⟩
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (2*x)) (2*Real.exp (2*x)) x := by
    simpa [id_eq, mul_comm] using ((hasDerivAt_id x).const_mul 2).exp
  have hj : InjOn (fun x : ℝ => Real.exp (2*x)) univ := by
    intro x _ y _ h
    have he := Real.exp_injective h
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hj
    (fun y => (y^2)⁻¹ • ((Real.exp (Real.log y/2):ℂ)*v (Real.log y/2)))
  rw [hrange, Measure.restrict_univ] at h
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (Real.exp_pos _)), Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have he : Real.exp (2*x) = (Real.exp x)^2 := (exp_sq x).symm
  rw [he, Real.exp_neg]
  push_cast
  field_simp [(Real.exp_pos x).ne']

private theorem modeProfile_eq (q : XiZeroCopy) (y : ℝ) :
    modeProfile q y = (Real.exp (Real.log y/2):ℂ)*mode q (Real.log y/2) := by
  unfold modeProfile positiveProfile sourceRatio
  push_cast
  field_simp [(thetaCuspFullSource_pos_all (Real.log y/2)).ne']

private def massDensity (x : ℝ) : ℝ := tiltedSource (-1) x
private def shiftedMode (q : XiZeroCopy) (x : ℝ) : ℂ := weightedMode q (-1) x
private def shift (q : XiZeroCopy) : ℂ := xiSpectralPoint q-Complex.I

private theorem shift_ne_zero (q : XiZeroCopy) : shift q ≠ 0 := by
  intro h
  apply b_ne_zero q
  have he := congrArg Complex.re h
  simpa [shift] using he

private theorem massDensity_pos (x : ℝ) : 0 < massDensity x :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

private theorem massDensity_integrable : Integrable massDensity :=
  HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (-1)

private theorem massDensity_bound_top (x : ℝ) : massDensity x ≤ thetaEnvelopeUpper*Real.exp (-x) := by
  have h := tilt_bound 0 (by norm_num) x
  simp only [zero_mul, Real.exp_zero, one_mul] at h
  dsimp [massDensity, tiltedSource]
  rw [neg_one_mul]
  nlinarith [Real.exp_pos (-x)]

private theorem massDensity_bound_bot (x : ℝ) : massDensity x ≤ thetaEnvelopeUpper*Real.exp x := by
  have h := tilt_bound (-2) (by norm_num) x
  have he : Real.exp (-x) = Real.exp x*Real.exp (-2*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [massDensity, tiltedSource]
  rw [neg_one_mul, he]
  nlinarith [Real.exp_pos x]

private theorem shiftedMode_integrable (q : XiZeroCopy) : Integrable (shiftedMode q) := by
  obtain ⟨C,_,hC⟩ := sourceRatio_bounded q
  have h := massDensity_integrable.ofReal.mul_bdd (continuous_sourceRatio q).aestronglyMeasurable
    (Eventually.of_forall hC)
  have he : shiftedMode q = fun x => (massDensity x:ℂ)*sourceRatio q x := by
    funext x
    exact weightedMode_eq q (-1) x
  rw [he]
  exact h

private theorem shiftedMode_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖shiftedMode q x‖ ≤ C*massDensity x := by
  obtain ⟨C,hC0,hC⟩ := sourceRatio_bounded q
  refine ⟨C,hC0,?_⟩
  intro x
  rw [shiftedMode, weightedMode_eq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  change |massDensity x| * ‖sourceRatio q x‖ ≤ C*massDensity x
  rw [abs_of_pos (massDensity_pos x)]
  nlinarith [hC x, massDensity_pos x]

private theorem shiftedMode_top (q : XiZeroCopy) : Tendsto (shiftedMode q) atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := shiftedMode_bound q
  apply squeeze_zero_norm (a := fun x => C*thetaEnvelopeUpper*Real.exp (-x))
  · intro x
    exact (hC x).trans (by nlinarith [massDensity_bound_top x])
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C*thetaEnvelopeUpper)

private theorem shiftedMode_bot (q : XiZeroCopy) : Tendsto (shiftedMode q) atBot (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := shiftedMode_bound q
  apply squeeze_zero_norm (a := fun x => C*thetaEnvelopeUpper*Real.exp x)
  · intro x
    exact (hC x).trans (by nlinarith [massDensity_bound_bot x])
  · simpa using Real.tendsto_exp_atBot.const_mul (C*thetaEnvelopeUpper)

private theorem shiftedMode_deriv (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (shiftedMode q) (-Complex.I*shift q*shiftedMode q x-Complex.I*(massDensity x:ℂ)) x := by
  have h := weightedMode_hasDerivAt q (-1) x
  have he : xiSpectralPoint q+Complex.I*((-1:ℝ):ℂ) = shift q := by
    unfold shift
    push_cast
    ring
  rw [he] at h
  exact h

private theorem shiftedMode_integral (q : XiZeroCopy) :
    (∫ x, shiftedMode q x) = -(∫ x, massDensity x:ℝ)/shift q := by
  have hu := shiftedMode_integrable q
  have hf := massDensity_integrable
  have hdRaw := integral_of_hasDerivAt_of_tendsto (shiftedMode_deriv q)
    ((hu.const_mul (-Complex.I*shift q)).sub (hf.ofReal.const_mul Complex.I))
    (shiftedMode_bot q) (shiftedMode_top q)
  have hd : (∫ x, -Complex.I*shift q*shiftedMode q x-Complex.I*(massDensity x:ℂ)) = 0 := by
    simpa using! hdRaw
  have he : (∫ x, -Complex.I*shift q*shiftedMode q x-Complex.I*(massDensity x:ℂ)) =
      -Complex.I*shift q*(∫ x, shiftedMode q x)-Complex.I*(∫ x, massDensity x:ℝ) := by
    have hs : (∫ x, -Complex.I*shift q*shiftedMode q x-Complex.I*(massDensity x:ℂ)) =
        (∫ x, -Complex.I*shift q*shiftedMode q x)-(∫ x, Complex.I*(massDensity x:ℂ)) := by
      simpa using! integral_sub (hu.const_mul (-Complex.I*shift q)) (hf.ofReal.const_mul Complex.I)
    rw [hs, integral_const_mul, integral_const_mul, integral_complex_ofReal]
  rw [he] at hd
  apply (eq_div_iff (shift_ne_zero q)).2
  linear_combination (norm := ring_nf) Complex.I*hd
  simp only [I_sq]
  ring

/-- Exact original theta mass in the native half-density normalization. -/
def sourceMass : ℝ := 2*∫ x, Real.exp (-x)*thetaCuspFullSource x

private theorem sourceMass_eq : sourceMass = 2*∫ x, massDensity x := by
  simp only [sourceMass, massDensity, tiltedSource, neg_one_mul]

/-- The source-defined normalization is strictly positive. -/
theorem sourceMass_pos : 0 < sourceMass := by
  rw [sourceMass_eq]
  apply mul_pos (by norm_num : (0:ℝ)<2)
  rw [integral_pos_iff_support_of_nonneg (fun x => (massDensity_pos x).le) massDensity_integrable]
  have hc : Continuous massDensity :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul contDiff_thetaCuspFullSource.continuous
  exact IsOpen.measure_pos volume hc.isOpen_support ⟨0, (massDensity_pos 0).ne'⟩

/-- Complete native unfolding evaluates the positive theta source's actual mean. -/
theorem positiveSource_integral : (∫ z, positiveSource z ∂angularMeasure) = sourceMass := by
  have hs (z : UpperHalfPlane) : Summable (fun v : gammaSetHalf => (positiveProfile (gammaSetMatrix v.1 • z).im:ℂ)) :=
    Complex.ofRealCLM.summable (positive_rows_summable z)
  have hn : (∫ z, (positiveSource z:ℂ) ∂angularMeasure) =
      (2:ℂ)*(∫ x, (Real.exp (-x):ℂ)*(thetaCuspFullSource x:ℂ)) := by
    calc
      _ = ∫ z, periodize (cuspHeightSeed (fun y => (positiveProfile y:ℂ))) z ∂angularMeasure :=
        integral_congr_ae (Eventually.of_forall positiveSource_periodize)
      _ = ∫ z in modularStrip, (positiveProfile z.im:ℂ) := profile_unfold _ hs positive_strip_integrable
      _ = ∫ y in Ioi (0:ℝ), (y^2)⁻¹ • ((Real.exp (Real.log y/2):ℂ)*(thetaCuspFullSource (Real.log y/2):ℂ)) := by
        have he := strip_height_integral (fun y : ℝ => (positiveProfile y:ℂ)) positive_strip_integrable
        rw [he]
        simp only [positiveProfile, Complex.ofReal_mul]
      _ = _ := halfDensity_integral (fun x => (thetaCuspFullSource x:ℂ))
  have hl : (∫ z, (positiveSource z:ℂ) ∂angularMeasure) =
      ((∫ z, positiveSource z ∂angularMeasure:ℝ):ℂ) := integral_ofReal
  have hr : (∫ x, (Real.exp (-x):ℂ)*(thetaCuspFullSource x:ℂ)) =
      ((∫ x, Real.exp (-x)*thetaCuspFullSource x:ℝ):ℂ) := by
    simp_rw [← Complex.ofReal_mul]
    exact integral_ofReal
  rw [hl, hr] at hn
  exact_mod_cast hn

/-- The actual mode mean retains its complete shifted spectral denominator. -/
theorem modeSource_integral (q : XiZeroCopy) :
    (∫ z, modeSource q z ∂angularMeasure) = -(sourceMass:ℂ)/(xiSpectralPoint q-Complex.I) := by
  have hn : (∫ z, modeSource q z ∂angularMeasure) = (2:ℂ)*(∫ x, shiftedMode q x) := by
    calc
      _ = ∫ z in modularStrip, modeProfile q z.im :=
        profile_unfold _ (mode_rows_summable q) (mode_strip_integrable q)
      _ = ∫ y in Ioi (0:ℝ), (y^2)⁻¹ • ((Real.exp (Real.log y/2):ℂ)*mode q (Real.log y/2)) := by
        rw [strip_height_integral _ (mode_strip_integrable q)]
        simp_rw [modeProfile_eq]
      _ = (2:ℂ)*(∫ x, (Real.exp (-x):ℂ)*mode q x) := halfDensity_integral (mode q)
      _ = _ := by simp only [shiftedMode, weightedMode, neg_one_mul]
  rw [hn, shiftedMode_integral, sourceMass_eq]
  dsimp [shift]
  push_cast
  ring

private theorem positive_tilt_bound_all (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (a*x)*thetaCuspFullSource x ≤
      thetaEnvelopeUpper*Real.exp ((a+9/2)^2/12) := by
  have he : x^2 ≤ Real.exp (2*x) := by
    rw [← exp_sq]
    nlinarith [Real.add_one_le_exp x, Real.exp_pos x]
  have hp : 3*Real.exp (2*x) ≤ Real.pi*Real.exp (2*x) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos _).le
  have hex : a*x+9*x/2-Real.pi*Real.exp (2*x) ≤ (a+9/2)^2/12 := by
    nlinarith [sq_nonneg (6*x-(a+9/2))]
  calc
    _ ≤ Real.exp (a*x)*(thetaEnvelopeUpper*thetaEnvelope x) :=
      mul_le_mul_of_nonneg_left (thetaCuspFullSource_le_envelope hx) (Real.exp_pos _).le
    _ = thetaEnvelopeUpper*Real.exp (a*x+9*x/2-Real.pi*Real.exp (2*x)) := by
      unfold thetaEnvelope
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) thetaEnvelopeUpper_pos.le

private theorem tilt_bound_all (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, Real.exp (a*x)*thetaCuspFullSource x ≤ C := by
  refine ⟨thetaEnvelopeUpper*Real.exp ((|a|+9/2)^2/12),
    mul_pos thetaEnvelopeUpper_pos (Real.exp_pos _), ?_⟩
  intro x
  have hphi : thetaCuspFullSource x = thetaCuspFullSource |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, thetaCuspFullSource_neg]
  calc
    _ ≤ Real.exp (|a| * |x|)*thetaCuspFullSource |x| := by
      rw [hphi]
      apply mul_le_mul_of_nonneg_right _ (thetaCuspFullSource_pos_all _).le
      apply Real.exp_le_exp.mpr
      simpa only [abs_mul] using le_abs_self (a*x)
    _ ≤ _ := positive_tilt_bound_all |a| (abs_nonneg x)

/-- Every real height power dominates the complete positive seed with a source-defined constant. -/
theorem positiveProfile_power_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → positiveProfile y ≤ C*y^r := by
  obtain ⟨C,hC0,hC⟩ := tilt_bound_all (1-2*r)
  refine ⟨C,hC0,?_⟩
  intro y hy
  have he : Real.exp (Real.log y/2) = y^r*Real.exp ((1-2*r)*(Real.log y/2)) := by
    rw [Real.rpow_def_of_pos hy, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = y^r*(Real.exp ((1-2*r)*(Real.log y/2))*thetaCuspFullSource (Real.log y/2)) := by
      rw [positiveProfile, he]
      ring
    _ ≤ y^r*C := mul_le_mul_of_nonneg_left (hC _) (Real.rpow_nonneg hy.le _)
    _ = _ := mul_comm _ _

/-- The original theta mode seed has all height-power bounds before periodization. -/
theorem modeProfile_power_bound (q : XiZeroCopy) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖modeProfile q y‖ ≤ C*y^r := by
  obtain ⟨A,hA0,hA⟩ := sourceRatio_bounded q
  obtain ⟨B,hB0,hB⟩ := positiveProfile_power_bound r
  refine ⟨A*B,mul_pos hA0 hB0,?_⟩
  intro y hy
  have hh : ‖modeProfile q y‖ ≤ A*positiveProfile y := by
    rw [modeProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (profile_pos y)]
    nlinarith [hA (Real.log y/2), profile_pos y]
  calc
    _ ≤ A*positiveProfile y := hh
    _ ≤ A*(B*y^r) := mul_le_mul_of_nonneg_left (hB y hy) hA0.le
    _ = _ := by ring

end
end RHTower.SelbergThetaNativeSource
