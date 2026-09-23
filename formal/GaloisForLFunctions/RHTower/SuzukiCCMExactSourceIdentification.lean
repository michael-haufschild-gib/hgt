import GaloisForLFunctions.RHTower.SuzukiCCMSourceFormBridge
import GaloisForLFunctions.RHTower.SuzukiHyperbolicTailBridge

/-!
# Exact identification of Suzuki's source form with the CCM Weil source

Suzuki's four-block restricted form and the Connes--Consani--Moscovici source quadratic use
different finite-part presentations of the same global Weil distribution.  This file proves the
missing equality.  The endpoint logarithm and the infinite archimedean tail are retained until
they cancel exactly; no cutoff or comparison-form premise is introduced.
-/

open Complex Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

private theorem intervalIntegral_even_eq_two_mul
    {R : ℝ} {f : ℝ → ℝ} (hcont : Continuous f) (heven : ∀ h, f (-h) = f h) :
    (∫ h in (-R)..R, f h) = 2 * ∫ h in (0 : ℝ)..R, f h := by
  have hreflect := intervalIntegral.integral_comp_neg
    (f := f) (a := (0 : ℝ)) (b := R)
  simp only [neg_zero] at hreflect
  have heq : (∫ h in (0 : ℝ)..R, f (-h)) = ∫ h in (0 : ℝ)..R, f h := by
    apply intervalIntegral.integral_congr
    intro h _
    exact heven h
  have hleft : (∫ h in (-R)..(0 : ℝ), f h) = ∫ h in (0 : ℝ)..R, f h := by
    rw [← hreflect, heq]
  have hleftInt : IntervalIntegrable f volume (-R) 0 :=
    hcont.intervalIntegrable (-R) 0
  have hrightInt : IntervalIntegrable f volume 0 R :=
    hcont.intervalIntegrable 0 R
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  rw [← hsplit, hleft]
  ring

theorem suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal
    {a h : ℝ} (u : SuzukiRestrictedWeilCore a) :
    suzukiRestrictedWeilCoreAutocorrelationTest u h =
      (suzukiCoreAutocorrelation u h : ℂ) := by
  rw [suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation,
    apertureAutocorrelation_suzukiRestrictedWeilCore_eq]

/-- Suzuki's finite-part block in the positive-lag autocorrelation coordinate. -/
theorem suzukiWeilFinitePartBlock_eq_oneSidedAutocorrelation
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilFinitePartBlock A.1 u u =
      -(∫ h in (0 : ℝ)..(2 * A.1),
          dslope (suzukiCoreAutocorrelation u) 0 h) -
        suzukiCoreAutocorrelation u 0 * Real.log (2 * A.1) := by
  let R : ℝ := 2 * A.1
  let c : ℝ → ℝ := suzukiCoreAutocorrelation u
  have hodd : ∀ h : ℝ, dslope c 0 (-h) = -dslope c 0 h := by
    intro h
    by_cases hh : h = 0
    · subst h
      have hzero : deriv c 0 = 0 := by
        apply deriv_eq_zero_of_even_at_zero
        · intro h
          dsimp only [c]
          exact suzukiCoreAutocorrelation_neg u h
        · intro h
          exact (hasDerivAt_suzukiCoreAutocorrelation u h).differentiableAt
      simp [dslope, hzero]
    · rw [dslope_of_ne c (neg_ne_zero.mpr hh), dslope_of_ne c hh]
      simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
      dsimp only [c]
      rw [suzukiCoreAutocorrelation_neg]
      field_simp [hh]
  have hreflect := intervalIntegral.integral_comp_neg
    (f := fun h => dslope c 0 h) (a := (0 : ℝ)) (b := R)
  simp only [neg_zero] at hreflect
  have hleft : (∫ h in (-R)..(0 : ℝ), dslope c 0 h) =
      -(∫ h in (0 : ℝ)..R, dslope c 0 h) := by
    rw [← hreflect, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro h _
    exact hodd h
  have hcenter := centeredCauchyFinitePart_suzukiCoreAutocorrelation A u
  have hfinite := suzukiWeilFinitePartBlock_eq_energy A u
  unfold centeredCauchyFinitePart at hcenter
  dsimp only [R, c] at hleft hcenter ⊢
  rw [hleft] at hcenter
  linarith

/-- Suzuki's smooth remainder block is its even positive-lag autocorrelation integral. -/
theorem weilSmoothBlock_suzukiOriginRemainderCurvature_eq_oneSided
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u =
      -2 * ∫ h in (0 : ℝ)..(2 * A.1),
        suzukiOriginRemainderCurvature h * suzukiCoreAutocorrelation u h := by
  let R : ℝ := 2 * A.1
  let c : ℝ → ℝ := suzukiCoreAutocorrelation u
  have hdouble := suzukiCoreDoubleIntegral_eq_correlation A u
    continuous_suzukiOriginRemainderCurvature
  have hsmooth : weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u =
      -(∫ h in (-R)..R, suzukiOriginRemainderCurvature h * c h) := by
    unfold weilSmoothBlock
    have hmove :
        (∫ x in (-A.1)..A.1,
          (∫ y in (-A.1)..A.1, suzukiOriginRemainderCurvature (x - y) * u y) * u x) =
          ∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
            suzukiOriginRemainderCurvature (x - y) * u y * u x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [intervalIntegral.integral_mul_const]
    dsimp only [R, c] at hdouble ⊢
    rw [hmove, hdouble]
  have hcont : Continuous (fun h => suzukiOriginRemainderCurvature h * c h) :=
    continuous_suzukiOriginRemainderCurvature.mul
      (continuous_suzukiCoreAutocorrelation_bridge u)
  have heven : ∀ h,
      suzukiOriginRemainderCurvature (-h) * c (-h) =
        suzukiOriginRemainderCurvature h * c h := by
    intro h
    dsimp only [c]
    rw [suzukiOriginRemainderCurvature_neg, suzukiCoreAutocorrelation_neg]
  have hhalve := intervalIntegral_even_eq_two_mul (R := R) hcont heven
  dsimp only [R, c] at hsmooth hhalve ⊢
  rw [hsmooth, hhalve]
  ring

/-- The source constant is exactly the completed real-place Weil constant. -/
theorem suzukiWeilArchimedeanConstant_completed_identity :
    2 * suzukiWeilArchimedeanConstant + 1 + Real.log 2 =
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant := by
  unfold suzukiWeilArchimedeanConstant
  rw [digamma_two_re, real_log_four_mul_pi]
  have hlog : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  rw [hlog]
  ring

private theorem pairing_shift_suzukiCore_eq_autocorrelation
    {a h : ℝ} (u : SuzukiRestrictedWeilCore a) :
    l2Pairing (fun x => u (x + h)) u = suzukiCoreAutocorrelation u h := by
  unfold l2Pairing suzukiCoreAutocorrelation screwCrossCorr
  apply integral_congr_ae
  filter_upwards with x
  rw [add_comm h x]
  ring

/-- Suzuki's prime block is exactly the negative atomic autocorrelation carrier. -/
theorem weilPrimeBlock_suzukiRestrictedWeilIndices_eq_autocorrelation
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u =
      -2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊,
        criticalMellinAtomWeight n * suzukiCoreAutocorrelation u (Real.log n) := by
  classical
  unfold weilPrimeBlock suzukiRestrictedWeilIndices suzukiVisibleWeilIndices
  rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1
  rw [pairing_shift_suzukiCore_eq_autocorrelation]
  have hminus : l2Pairing (fun x => u (x - Real.log n)) u =
      suzukiCoreAutocorrelation u (Real.log n) := by
    have h := pairing_shift_suzukiCore_eq_autocorrelation
      (u := u) (h := -Real.log n)
    simp only [sub_eq_add_neg]
    rw [h, suzukiCoreAutocorrelation_neg]
  rw [hminus, criticalMellinAtomWeight_eq_primePairWeight hnpos]
  ring

/-- The CCM polar--prime quadratic is Suzuki's continuous polar carrier plus his prime block. -/
theorem polarPrimeAutocorrelationQuadratic_eq_polar_add_weilPrimeBlock
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    polarPrimeAutocorrelationQuadratic A.1 (fun x => (u x : ℂ)) =
      4 * (∫ h in Ioc (0 : ℝ) (2 * A.1),
        Real.cosh (h / 2) * suzukiCoreAutocorrelation u h) +
      weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by
  have hcont : Continuous (fun h : ℝ =>
      apertureAutocorrelation (fun x => (u x : ℂ)) h *
        (2 * Real.cosh (h / 2) : ℂ)) := by
    rw [show apertureAutocorrelation (fun x => (u x : ℂ)) =
        suzukiRestrictedWeilCoreAutocorrelationTest u by
      funext h
      exact (suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation
        u).symm]
    exact (suzukiRestrictedWeilCoreAutocorrelationTest u).toSchwartzMap.continuous.mul
      (by fun_prop)
  have hint : Integrable
      (fun h => apertureAutocorrelation (fun x => (u x : ℂ)) h *
        (2 * Real.cosh (h / 2) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) (2 * A.1))) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hscale :
      (∫ h in Ioc (0 : ℝ) (2 * A.1),
        suzukiCoreAutocorrelation u h * (2 * Real.cosh (h / 2))) =
        2 * ∫ h in Ioc (0 : ℝ) (2 * A.1),
          Real.cosh (h / 2) * suzukiCoreAutocorrelation u h := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    ring
  rw [polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum hint,
    weilPrimeBlock_suzukiRestrictedWeilIndices_eq_autocorrelation]
  simp_rw [apertureAutocorrelation_suzukiRestrictedWeilCore_eq]
  simp only [ofReal_re]
  rw [hscale]
  ring

/-- Positive-ray identity which turns Suzuki's smooth curvature into the real-place Weil
density after the finite-part divided difference is added. -/
theorem two_mul_suzukiOriginRemainderCurvature_add_four_cosh
    {h : ℝ} (hh : 0 < h) :
    2 * suzukiOriginRemainderCurvature h + 4 * Real.cosh (h / 2) =
      Real.exp (h / 2) / Real.sinh h - 1 / h := by
  have hh0 : h ≠ 0 := hh.ne'
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh0
  have hext := suzukiCschMinusInvExtension_of_pos hh
  unfold suzukiCschMinusInvExtension suzukiHalfExponentialSinhRatio at hext
  rw [if_neg hh0] at hext
  field_simp [hh0, hsinh] at hext ⊢
  linarith

/-- Autocorrelation mass at zero is exactly the aperture-square mass used by Suzuki's scalar
block. -/
theorem integral_interval_sq_suzukiRestrictedWeilCore_eq_autocorrelation_zero
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    (∫ x in (-A.1)..A.1, u x ^ 2) = suzukiCoreAutocorrelation u 0 := by
  have hinterval : (∫ x in (-A.1)..A.1, u x ^ 2) = ∫ x : ℝ, u x ^ 2 := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hux : u x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    have hmem := u.support_subset_aperture hux
    exact ⟨hmem.1, hmem.2.le⟩
  rw [hinterval, suzukiCoreAutocorrelation_zero]

/-- Suzuki's scalar block in autocorrelation coordinates. -/
theorem weilScalarBlock_suzukiWeilArchimedeanConstant_eq_autocorrelation_zero
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilScalarBlock A.1 suzukiWeilArchimedeanConstant u u =
      -(2 * suzukiWeilArchimedeanConstant + 1) *
        suzukiCoreAutocorrelation u 0 := by
  unfold weilScalarBlock
  have hmass := integral_interval_sq_suzukiRestrictedWeilCore_eq_autocorrelation_zero A u
  have hmul : (∫ x in (-A.1)..A.1, u x * u x) =
      suzukiCoreAutocorrelation u 0 := by
    simpa only [pow_two] using hmass
  rw [hmul]

private theorem suzukiCoreAutocorrelation_eq_zero_of_two_aperture_lt
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    {h : ℝ} (hh : 2 * A.1 < h) :
    suzukiCoreAutocorrelation u h = 0 := by
  apply screwCrossCorr_eq_zero_of_support_radius_pos
    u.support_subset u.support_subset
  linarith [u.supportRadius_lt_aperture]

/-- Pointwise real-place density after evenizing Suzuki's real autocorrelation. -/
theorem ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_re
    {a h : ℝ} (u : SuzukiRestrictedWeilCore a) (hh : h ≠ 0) :
    (ccmArchimedeanWeilSharpIntegrand
      (ccmCompactSchwartzLogEvenization
        (suzukiRestrictedWeilCoreAutocorrelationTest u)) h).re =
      (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
        suzukiCoreAutocorrelation u 0) / Real.sinh h := by
  have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh
  unfold ccmArchimedeanWeilSharpIntegrand ccmArchimedeanWeilSharpNumerator
  rw [ccmCompactSchwartzLogEvenization_apply,
    ccmCompactSchwartzLogEvenization_apply]
  simp_rw [suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal]
  rw [suzukiCoreAutocorrelation_neg]
  rw [show Real.exp h - Real.exp (-h) = 2 * Real.sinh h by
    rw [Real.sinh_eq]
    ring]
  push_cast
  have hexpC : Complex.exp ((h : ℂ) / 2) = (Real.exp (h / 2) : ℂ) := by
    rw [show (h : ℂ) / 2 = ((h / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hsinhC : Complex.sinh (h : ℂ) = (Real.sinh h : ℂ) := by
    rw [← Complex.ofReal_sinh]
  have hcomplex :
      (2 : ℂ) * ((Real.exp (h / 2) : ℂ) *
          (suzukiCoreAutocorrelation u h : ℂ) -
        (suzukiCoreAutocorrelation u 0 : ℂ)) /
          ((2 : ℂ) * (Real.sinh h : ℂ)) =
        (((Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
          suzukiCoreAutocorrelation u 0) / Real.sinh h : ℝ) : ℂ) := by
    push_cast
    field_simp [hsinh]
  rw [hexpC, hsinhC]
  simp only [neg_zero]
  have hnum :
      (Real.exp (h / 2) : ℂ) *
          ((suzukiCoreAutocorrelation u h : ℂ) +
            (suzukiCoreAutocorrelation u h : ℂ)) -
        ((suzukiCoreAutocorrelation u 0 : ℂ) +
          (suzukiCoreAutocorrelation u 0 : ℂ)) =
      (2 : ℂ) * ((Real.exp (h / 2) : ℂ) *
          (suzukiCoreAutocorrelation u h : ℂ) -
        (suzukiCoreAutocorrelation u 0 : ℂ)) := by ring
  rw [hnum, hcomplex]
  simp
  rw [hexpC, hsinhC]
  norm_cast

/-- Finite positive-aperture piece of the global real-place Weil distribution on Suzuki's
autocorrelation. -/
theorem ccmRestrictedArchimedeanSharp_evenized_suzukiCore_re
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    (ccmRestrictedArchimedeanSharp A.1
      (ccmCompactSchwartzLogEvenization
        (suzukiRestrictedWeilCoreAutocorrelationTest u))).re =
      suzukiCoreAutocorrelation u 0 *
          (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) +
        ∫ h in Ioc (0 : ℝ) (2 * A.1),
          (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
            suzukiCoreAutocorrelation u 0) / Real.sinh h := by
  let H := suzukiRestrictedWeilCoreAutocorrelationTest u
  let F := ccmCompactSchwartzLogEvenization H
  have hInt : Integrable (ccmArchimedeanWeilSharpIntegrand F)
      (volume.restrict (Ioc (0 : ℝ) (2 * A.1))) :=
    (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F).mono_set
      (fun h hh => hh.1)
  have hF0 : F 0 = ((2 * suzukiCoreAutocorrelation u 0 : ℝ) : ℂ) := by
    dsimp only [F, H]
    rw [ccmCompactSchwartzLogEvenization_apply]
    simp_rw [suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal]
    simp
    ring
  have hIntegral :
      (∫ h in Ioc (0 : ℝ) (2 * A.1),
          (ccmArchimedeanWeilSharpIntegrand F h).re) =
        ∫ h in Ioc (0 : ℝ) (2 * A.1),
          (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
            suzukiCoreAutocorrelation u 0) / Real.sinh h := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    dsimp only [F, H]
    exact ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_re u hh.1.ne'
  change (F 0 / 2 *
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ) +
        ∫ h in Ioc (0 : ℝ) (2 * A.1),
          ccmArchimedeanWeilSharpIntegrand F h).re = _
  have hreIntegral :
      (∫ h in Ioc (0 : ℝ) (2 * A.1),
        ccmArchimedeanWeilSharpIntegrand F h).re =
        ∫ h in Ioc (0 : ℝ) (2 * A.1),
          (ccmArchimedeanWeilSharpIntegrand F h).re :=
    (integral_re hInt).symm
  have hconstant :
      (F 0 / 2 *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)).re =
      suzukiCoreAutocorrelation u 0 *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
    rw [hF0]
    push_cast
    norm_num
  rw [Complex.add_re, hreIntegral, hIntegral, hconstant]

/-- Beyond the aperture, compact support removes the autocorrelation and leaves precisely the
negative hyperbolic mass tail. -/
theorem ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_tail_re
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    (∫ h in Ioi (2 * A.1),
      ccmArchimedeanWeilSharpIntegrand
        (ccmCompactSchwartzLogEvenization
          (suzukiRestrictedWeilCoreAutocorrelationTest u)) h).re =
      -suzukiCoreAutocorrelation u 0 *
        ∫ h in Ioi (2 * A.1), 1 / Real.sinh h := by
  let F := ccmCompactSchwartzLogEvenization
    (suzukiRestrictedWeilCoreAutocorrelationTest u)
  have hInt : Integrable (ccmArchimedeanWeilSharpIntegrand F)
      (volume.restrict (Ioi (2 * A.1))) :=
    (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F).mono_set
      (fun _ hh => lt_trans (mul_pos zero_lt_two A.property) hh)
  change (∫ h in Ioi (2 * A.1),
      ccmArchimedeanWeilSharpIntegrand F h).re = _
  have hreIntegral :
      (∫ h in Ioi (2 * A.1),
        ccmArchimedeanWeilSharpIntegrand F h).re =
        ∫ h in Ioi (2 * A.1),
          (ccmArchimedeanWeilSharpIntegrand F h).re :=
    (integral_re hInt).symm
  rw [hreIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hzero := suzukiCoreAutocorrelation_eq_zero_of_two_aperture_lt A u hh
  dsimp only [F]
  rw [ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_re u
    (ne_of_gt (lt_trans (mul_pos zero_lt_two A.property) hh)), hzero]
  field_simp
  ring

/-- Exact global real-place Weil distribution on Suzuki's autocorrelation, split at the literal
aperture.  The last term is the nonzero compact-support tail created by evenization at zero. -/
theorem ccmArchimedeanWeilDistribution_suzukiCore_re_eq_restricted_add_tail
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    (ccmArchimedeanWeilDistribution
      (suzukiRestrictedWeilCoreAutocorrelationTest u)).re =
      suzukiCoreAutocorrelation u 0 *
          (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) +
        (∫ h in Ioc (0 : ℝ) (2 * A.1),
          (Real.exp (h / 2) * suzukiCoreAutocorrelation u h -
            suzukiCoreAutocorrelation u 0) / Real.sinh h) -
        suzukiCoreAutocorrelation u 0 *
          ∫ h in Ioi (2 * A.1), 1 / Real.sinh h := by
  let H := suzukiRestrictedWeilCoreAutocorrelationTest u
  let F := ccmCompactSchwartzLogEvenization H
  let aNN : NNReal := Real.toNNReal A.1
  have haNN : (aNN : ℝ) = A.1 := by
    dsimp only [aNN]
    rw [Real.coe_toNNReal A.1 A.property.le]
  have hsplit := ccmArchimedeanWeilSharpDistribution_eq_restricted_add_tail F aNN
  have hre := congrArg Complex.re hsplit
  have hrestricted := ccmRestrictedArchimedeanSharp_evenized_suzukiCore_re A u
  have htail := ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_tail_re A u
  change (ccmArchimedeanWeilSharpDistribution F).re = _
  rw [haNN] at hre
  dsimp only [H, F] at hre
  rw [hre, Complex.add_re, hrestricted, htail]
  ring

/-- The three archimedean blocks in Suzuki's source form are exactly the polar continuous
carrier minus the global CCM real-place Weil distribution. -/
theorem suzukiArchimedeanBlocks_eq_polar_sub_globalWeil
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilFinitePartBlock A.1 u u +
        weilScalarBlock A.1 suzukiWeilArchimedeanConstant u u +
        weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u =
      4 * (∫ h in Ioc (0 : ℝ) (2 * A.1),
        Real.cosh (h / 2) * suzukiCoreAutocorrelation u h) -
      (ccmArchimedeanWeilDistribution
        (suzukiRestrictedWeilCoreAutocorrelationTest u)).re := by
  let R : ℝ := 2 * A.1
  let c : ℝ → ℝ := suzukiCoreAutocorrelation u
  let g : ℝ → ℝ := fun h =>
    (Real.exp (h / 2) * c h - c 0) / Real.sinh h
  let e : ℝ → ℝ := suzukiCschMinusInvExtension
  have hR : 0 < R := mul_pos zero_lt_two A.property
  have hccont : Continuous c := continuous_suzukiCoreAutocorrelation_bridge u
  have hdscont : Continuous (fun h => dslope c 0 h) := by
    rw [continuous_iff_continuousAt]
    intro h
    by_cases hh : h = 0
    · subst h
      exact continuousAt_dslope_same.mpr
        (hasDerivAt_suzukiCoreAutocorrelation u 0).differentiableAt
    · exact (continuousAt_dslope_of_ne hh).mpr hccont.continuousAt
  let S := Ioc (0 : ℝ) R
  have hdsInt : Integrable (fun h => dslope c 0 h) (volume.restrict S) :=
    hdscont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hcurvInt : Integrable
      (fun h => suzukiOriginRemainderCurvature h * c h)
      (volume.restrict S) :=
    (continuous_suzukiOriginRemainderCurvature.mul hccont).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hcoshInt : Integrable (fun h => Real.cosh (h / 2) * c h)
      (volume.restrict S) :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hccont).continuousOn
      |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heInt : Integrable e (volume.restrict S) :=
    continuous_suzukiCschMinusInvExtension.continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hgInt : Integrable g (volume.restrict S) := by
    let F := ccmCompactSchwartzLogEvenization
      (suzukiRestrictedWeilCoreAutocorrelationTest u)
    have hcm := (ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F).mono_set
      (show S ⊆ Ioi (0 : ℝ) by intro h hh; exact hh.1)
    refine hcm.re.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    dsimp only [g, c, F]
    exact ccmArchimedeanWeilSharpIntegrand_evenized_suzukiCore_re u hh.1.ne'
  have hpoint : ∀ h ∈ S,
      -dslope c 0 h + (-2) *
          (suzukiOriginRemainderCurvature h * c h) =
        4 * (Real.cosh (h / 2) * c h) - g h - c 0 * e h := by
    intro h hh
    have hh0 : h ≠ 0 := hh.1.ne'
    have hsinh : Real.sinh h ≠ 0 := (Real.sinh_ne_zero).2 hh0
    have hk := two_mul_suzukiOriginRemainderCurvature_add_four_cosh hh.1
    have hcurv : 2 * suzukiOriginRemainderCurvature h =
        Real.exp (h / 2) / Real.sinh h - 1 / h - 4 * Real.cosh (h / 2) := by
      linarith
    dsimp only [g, e]
    rw [dslope_of_ne c hh0, suzukiCschMinusInvExtension_of_pos hh.1]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    rw [show (-2 : ℝ) * (suzukiOriginRemainderCurvature h * c h) =
      -(2 * suzukiOriginRemainderCurvature h) * c h by ring, hcurv]
    field_simp [hh0, hsinh]
    ring
  have hkernel :
      -(∫ h in S, dslope c 0 h) -
          2 * (∫ h in S, suzukiOriginRemainderCurvature h * c h) =
        4 * (∫ h in S, Real.cosh (h / 2) * c h) -
          (∫ h in S, g h) - c 0 * ∫ h in S, e h := by
    calc
      _ = (∫ h in S, -dslope c 0 h) +
          ∫ h in S, (-2) *
            (suzukiOriginRemainderCurvature h * c h) := by
        rw [integral_neg, integral_const_mul]
        ring
      _ = ∫ h in S,
          -dslope c 0 h + (-2) *
            (suzukiOriginRemainderCurvature h * c h) := by
        exact (integral_add hdsInt.neg (hcurvInt.const_mul (-2))).symm
      _ = ∫ h in S,
          4 * (Real.cosh (h / 2) * c h) - g h - c 0 * e h := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
        exact hpoint h hh
      _ = (∫ h in S, 4 * (Real.cosh (h / 2) * c h) - g h) -
          ∫ h in S, c 0 * e h :=
        integral_sub ((hcoshInt.const_mul 4).sub hgInt) (heInt.const_mul (c 0))
      _ = ((∫ h in S, 4 * (Real.cosh (h / 2) * c h)) -
          ∫ h in S, g h) - ∫ h in S, c 0 * e h := by
        rw [integral_sub (hcoshInt.const_mul 4) hgInt]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
  have hfinite := suzukiWeilFinitePartBlock_eq_oneSidedAutocorrelation A u
  have hsmooth := weilSmoothBlock_suzukiOriginRemainderCurvature_eq_oneSided A u
  have hscalar :=
    weilScalarBlock_suzukiWeilArchimedeanConstant_eq_autocorrelation_zero A u
  have hW := ccmArchimedeanWeilDistribution_suzukiCore_re_eq_restricted_add_tail A u
  have heval := integral_suzukiCschMinusInvExtension hR
  have htail := integral_Ioi_inv_sinh hR
  have hconstant := suzukiWeilArchimedeanConstant_completed_identity
  have hinterval : ∀ f : ℝ → ℝ,
      (∫ h in (0 : ℝ)..R, f h) = ∫ h in S, f h := by
    intro f
    rw [intervalIntegral.integral_of_le hR.le]
  dsimp only [R, c, g, e, S] at hkernel hinterval heval htail ⊢
  rw [hinterval suzukiCschMinusInvExtension] at heval
  rw [hfinite, hsmooth, hscalar, hW,
    hinterval (fun h => dslope (suzukiCoreAutocorrelation u) 0 h),
    hinterval (fun h => suzukiOriginRemainderCurvature h *
      suzukiCoreAutocorrelation u h)]
  have hconstantMul := congrArg
    (fun z : ℝ => suzukiCoreAutocorrelation u 0 * z) hconstant
  calc
    _ = (-(∫ h in Ioc (0 : ℝ) (2 * A.1),
          dslope (suzukiCoreAutocorrelation u) 0 h) -
        2 * ∫ h in Ioc (0 : ℝ) (2 * A.1),
          suzukiOriginRemainderCurvature h * suzukiCoreAutocorrelation u h) -
        suzukiCoreAutocorrelation u 0 * Real.log (2 * A.1) -
        (2 * suzukiWeilArchimedeanConstant + 1) *
          suzukiCoreAutocorrelation u 0 := by ring
    _ = _ := by
      rw [hkernel, heval, htail]
      linarith

/-- Exact equality of Suzuki's source-locked four-block form with the canonical polar--prime
carrier minus the global archimedean Weil distribution. -/
theorem suzukiRestrictedWeilForm_eq_polarPrime_sub_globalWeil
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    suzukiRestrictedWeilForm A.1 u u =
      polarPrimeAutocorrelationQuadratic A.1 (fun x => (u x : ℂ)) -
        (ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u)).re := by
  have harch := suzukiArchimedeanBlocks_eq_polar_sub_globalWeil A u
  have hpolar := polarPrimeAutocorrelationQuadratic_eq_polar_add_weilPrimeBlock A u
  rw [suzukiRestrictedWeilForm_eq_originRemainderFourBlocks]
  calc
    weilFinitePartBlock A.1 u u +
          weilScalarBlock A.1 suzukiWeilArchimedeanConstant u u +
          weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u +
          weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u =
        (weilFinitePartBlock A.1 u u +
          weilScalarBlock A.1 suzukiWeilArchimedeanConstant u u +
          weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u) +
          weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by ring
    _ = (4 * (∫ h in Ioc (0 : ℝ) (2 * A.1),
          Real.cosh (h / 2) * suzukiCoreAutocorrelation u h) -
        (ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u)).re) +
          weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by rw [harch]
    _ = (4 * (∫ h in Ioc (0 : ℝ) (2 * A.1),
          Real.cosh (h / 2) * suzukiCoreAutocorrelation u h) +
          weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u) -
        (ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u)).re := by ring
    _ = _ := by rw [← hpolar]

/-- The canonical CCM source quadratic and Suzuki's literal restricted Weil form coincide on
every source core vector, with no comparison-form hypothesis. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_suzukiRestrictedWeilForm
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    ccmRestrictedWeilSourceQuadratic A
        (suzukiRestrictedWeilCoreCCMFormVector A u) =
      suzukiRestrictedWeilForm A.1 u u := by
  rw [ccmRestrictedWeilSourceQuadratic_suzukiRestrictedWeilCore_eq,
    suzukiRestrictedWeilForm_eq_polarPrime_sub_globalWeil]

/-- The exact CCM restricted Weil form is real on its diagonal.  This is a structural
consequence of the self-adjoint bounded remainder, not an extra reality premise. -/
theorem ccmRestrictedWeilForm_self_im_eq_zero
    (A : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain A) :
    (ccmRestrictedWeilForm A q q).im = 0 := by
  let f := ccmArchimedeanFormToAperture A q
  have hconj :
      (starRingEnd ℂ) (inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f) =
        inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f := by
    calc
      (starRingEnd ℂ) (inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f) =
          inner ℂ f (ccmRestrictedWeilBoundedRemainder A f) :=
        inner_conj_symm f (ccmRestrictedWeilBoundedRemainder A f)
      _ = inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f :=
        ((ccmRestrictedWeilBoundedRemainder_isSelfAdjoint A).isSymmetric f f).symm
  have hqim : (inner ℂ q q).im = 0 :=
    Complex.conj_eq_iff_im.mp (inner_conj_symm q q)
  have hfim :
      (inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj
  unfold ccmRestrictedWeilForm
  change (inner ℂ q q).im +
      (inner ℂ (ccmRestrictedWeilBoundedRemainder A f) f).im = 0
  rw [hqim, hfim, add_zero]

/-- Exact complex diagonal identification: the CCM closed form on a real Suzuki source-core
vector is the literal real four-block Weil form, not merely equal after taking real parts. -/
theorem ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    ccmRestrictedWeilForm A (suzukiRestrictedWeilCoreCCMFormVector A u)
        (suzukiRestrictedWeilCoreCCMFormVector A u) =
      (suzukiRestrictedWeilForm A.1 u u : ℂ) := by
  apply Complex.ext
  · rw [ccmRestrictedWeilForm_self_re_eq_source,
      ccmRestrictedWeilSourceQuadratic_eq_suzukiRestrictedWeilForm]
    simp
  · rw [ccmRestrictedWeilForm_self_im_eq_zero]
    simp

/-- Exact diagonal form bridge between Suzuki's literal compressed screw operator and the CCM
closed restricted Weil form on every real strict-interior smooth source vector. -/
theorem inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_ccmRestrictedWeilForm
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    inner ℂ (suzukiRestrictedWeilCoreDerivativeZeroMean A u)
        (suzukiScrewZeroMeanOperator A
          (suzukiRestrictedWeilCoreDerivativeZeroMean A u)) =
      ccmRestrictedWeilForm A (suzukiRestrictedWeilCoreCCMFormVector A u)
        (suzukiRestrictedWeilCoreCCMFormVector A u) := by
  rw [inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_restrictedWeilForm,
    ccmRestrictedWeilForm_suzukiCore_eq_restrictedWeilForm]

end RHTower
