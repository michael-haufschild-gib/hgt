import GaloisForLFunctions.RHTower.XiMassBesselHeightDerivative
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingCurrent

/-!
# The differentiated exterior envelope

Outside a fixed slope cone `h ≥ κu` the mass Fourier profile is differentiable in the height and
its derivative obeys the same envelope as the profile:

`|F_u'(h)| ≤ C u^{-1/2} e^{-a√(h²−u²)}`.

The derivative computed from the differentiated Fourier integral and the derivative computed from
the Fourier–Bessel identity agree by uniqueness, so the closed expression
`2aτ h (a K₁'(az) z − K₁(az))/z³` may be used for the estimate.  All three ratios `‖τ‖/‖z‖`,
`h/‖z‖`, `1/‖z‖` are bounded by cone constants, and both Schläfli envelopes carry the same
exponential decay with the same square-root gain.

Adding the damping factor gives the differentiated envelope of the outgoing kernel.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Identification of the two derivatives -/

theorem xiMassStripMem_of_lt {sigma u t : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u) (ht : u < t) :
    ((sigma : ℂ) + (u : ℂ) * I) ∈ xiMassBesselStrip t := by
  constructor
  · simpa using hsigma
  · have him : ((sigma : ℂ) + (u : ℂ) * I).im = u := by simp
    rw [him, abs_of_nonneg hu]
    exact ht

/-- The Bessel side differentiates the mass Fourier profile in the height. -/
theorem hasDerivAt_stripFourier_xiMass_bessel {a sigma u h : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u) (huh : u < h) :
    HasDerivAt
      (fun t : ℝ => stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (t : ℂ))
      (xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)) h := by
  have hpos : 0 < (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2).re :=
    xiMassPropagation_re_pos (xiMassStripMem_of_lt hsigma hu huh)
  have hbase : HasDerivAt
      (fun t : ℝ => xiMassBesselHeightSide a ((sigma : ℂ) + (u : ℂ) * I) (t : ℂ))
      (xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)) h :=
    (hasDerivAt_xiMassBesselHeightSide ha hpos).comp_ofReal
  refine hbase.congr_of_eventuallyEq ?_
  have hnb : {t : ℝ | u < t} ∈ nhds h :=
    (isOpen_lt continuous_const continuous_id).mem_nhds huh
  filter_upwards [hnb] with t ht
  show stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (t : ℂ)
      = xiMassBesselHeightSide a ((sigma : ℂ) + (u : ℂ) * I) (t : ℂ)
  rw [xiMassBesselHeightSide_ofReal]
  exact stripFourier_xiMass_eq_bessel ha (lt_of_le_of_lt hu ht)
    (xiMassStripMem_of_lt hsigma hu ht)

/-- **The Fourier derivative in closed Bessel form.** -/
theorem xiMassFourierDerivative_eq_besselHeightDeriv {a sigma u h : ℝ} (ha : 0 < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u < h) :
    xiMassFourierDerivative a sigma u h
      = xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ) :=
  (hasDerivAt_xiMassRealFourierProfile ha hsigma u h).unique
    (hasDerivAt_stripFourier_xiMass_bessel ha hsigma hu huh)

/-! ## The exterior envelope of the height derivative -/

/-- The exterior envelope constant of the height derivative. -/
def xiMassBesselDerivExteriorSqrtConstant (a sigma kappa : ℝ) : ℝ :=
  2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) * (kappa / Real.sqrt (kappa ^ 2 - 1))
    * (a + 1 / sigma) * Real.exp (2 / (a * sigma))
    * Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1)))

theorem xiMassBesselDerivExteriorSqrtConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) :
    0 ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa := by
  have hkappa2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hkappa2
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  rw [xiMassBesselDerivExteriorSqrtConstant]
  positivity

/-- The real assembly of the exterior derivative estimate. -/
private theorem derivEnvelope_assemble {a sigma kappa u h K N Tn : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hh : 0 < h)
    (hcone : kappa * u ≤ h) (hKsig : sigma ≤ K)
    (hKgap : Real.sqrt (h ^ 2 - u ^ 2) ≤ K) (hKslope : Real.sqrt (kappa ^ 2 - 1) * u ≤ K)
    (hKN : K ≤ N) (hT : Tn ≤ sigma + u) :
    2 * a * (Tn / N) * (|h| / N) * (a + 1 / K)
        * (Real.exp (-(a * K)) * Real.exp (2 / (a * K)) * Real.sqrt (2 * Real.pi / (a * K)))
      ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hkappa2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_pos.2 hkappa2
  have hssq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2.le
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le hsigma hKsig
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hKpos hKN
  -- ratio one
  have hr1 : Tn / N ≤ 1 + 1 / Real.sqrt (kappa ^ 2 - 1) := by
    rw [div_le_iff₀ hNpos]
    have hu' : u ≤ 1 / Real.sqrt (kappa ^ 2 - 1) * N := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
      nlinarith [hKslope, hKN]
    nlinarith [hT, hKsig, hKN, hu']
  -- ratio two
  have hr2 : |h| / N ≤ kappa / Real.sqrt (kappa ^ 2 - 1) := by
    rw [div_le_div_iff₀ hNpos hs, abs_of_pos hh]
    have hcone2 : (kappa * u) ^ 2 ≤ h ^ 2 := by
      have hnn : (0 : ℝ) ≤ kappa * u := by positivity
      nlinarith [hcone, hnn]
    have hnn : (0 : ℝ) ≤ h * Real.sqrt (kappa ^ 2 - 1) / kappa := by positivity
    have hsqle : (h * Real.sqrt (kappa ^ 2 - 1) / kappa) ^ 2 ≤ h ^ 2 - u ^ 2 := by
      have hex : (h * Real.sqrt (kappa ^ 2 - 1) / kappa) ^ 2
          = h ^ 2 * (kappa ^ 2 - 1) / kappa ^ 2 := by
        rw [div_pow, mul_pow, hssq]
      rw [hex, div_le_iff₀ (by positivity : (0 : ℝ) < kappa ^ 2)]
      nlinarith [hcone2]
    have hlow : h * Real.sqrt (kappa ^ 2 - 1) / kappa ≤ Real.sqrt (h ^ 2 - u ^ 2) := by
      have hstep := Real.sqrt_le_sqrt hsqle
      rwa [Real.sqrt_sq hnn] at hstep
    have hfin : h * Real.sqrt (kappa ^ 2 - 1) / kappa ≤ N := le_trans hlow (le_trans hKgap hKN)
    rw [div_le_iff₀ hkappa0] at hfin
    nlinarith [hfin]
  -- ratio three
  have hr3 : a + 1 / K ≤ a + 1 / sigma := by
    have := one_div_le_one_div_of_le hsigma hKsig
    linarith
  -- the envelope
  have he1 : Real.exp (-(a * K)) ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) :=
    Real.exp_le_exp.2 (by nlinarith [hKgap])
  have he2 : Real.exp (2 / (a * K)) ≤ Real.exp (2 / (a * sigma)) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hKsig, hsigma, ha]
  have he3 : Real.sqrt (2 * Real.pi / (a * K))
      ≤ Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u := by
    have hval : Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u
        = Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1) * u)) := by
      rw [← Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi
        / (a * Real.sqrt (kappa ^ 2 - 1)))]
      congr 1
      field_simp
    rw [hval]
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [hKslope]
  have hE : Real.exp (-(a * K)) * Real.exp (2 / (a * K)) * Real.sqrt (2 * Real.pi / (a * K))
      ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) * Real.exp (2 / (a * sigma))
        * (Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ 2 - 1))) / Real.sqrt u) := by
    have hfirst : Real.exp (-(a * K)) * Real.exp (2 / (a * K))
        ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) * Real.exp (2 / (a * sigma)) :=
      mul_le_mul he1 he2 (Real.exp_nonneg _) (Real.exp_nonneg _)
    exact mul_le_mul hfirst he3 (Real.sqrt_nonneg _) (by positivity)
  have hEnn : (0 : ℝ) ≤ Real.exp (-(a * K)) * Real.exp (2 / (a * K))
      * Real.sqrt (2 * Real.pi / (a * K)) := by positivity
  have s1 : 2 * a * (Tn / N) ≤ 2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) :=
    mul_le_mul_of_nonneg_left hr1 (by positivity)
  have s2 : 2 * a * (Tn / N) * (|h| / N)
      ≤ 2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) * (kappa / Real.sqrt (kappa ^ 2 - 1)) :=
    mul_le_mul s1 hr2 (by positivity) (by positivity)
  have s3 : 2 * a * (Tn / N) * (|h| / N) * (a + 1 / K)
      ≤ 2 * a * (1 + 1 / Real.sqrt (kappa ^ 2 - 1)) * (kappa / Real.sqrt (kappa ^ 2 - 1))
        * (a + 1 / sigma) :=
    mul_le_mul s2 hr3 (by positivity) (by positivity)
  have s4 := mul_le_mul s3 hE hEnn (by positivity)
  refine s4.trans (le_of_eq ?_)
  rw [xiMassBesselDerivExteriorSqrtConstant]
  ring

/-- **(19.2) The exterior envelope of the height derivative.** -/
theorem norm_xiMassBesselHeightDeriv_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖xiMassBesselHeightDeriv a ((sigma : ℂ) + (u : ℂ) * I) (h : ℂ)‖
      ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hkappa2 : (0 : ℝ) < kappa ^ 2 - 1 := by nlinarith
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  have hh : 0 < h := lt_of_lt_of_le hu huh
  have hprop : ((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2
      = xiMassSpacelikePropagationArgument sigma u h :=
    (xiMassSpacelikePropagationArgument_eq sigma u h).symm
  have hzre : (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re
      = HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
    rw [HTGeometry.csqrt_re, hprop]
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re = K := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ,
      ‖HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)‖ = N := ⟨_, rfl⟩
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℝ, ‖(sigma : ℂ) + (u : ℂ) * I‖ = Tn := ⟨_, rfl⟩
  have hKsig : sigma ≤ K := by
    rw [← hK, hzre]
    exact sigma_le_csqrtRe_propagationArgument hsigma hu.le huh
  have hKgap : Real.sqrt (h ^ 2 - u ^ 2) ≤ K := by
    rw [← hK, hzre]
    refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu.le huh)
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hKslope : Real.sqrt (kappa ^ 2 - 1) * u ≤ K := by
    rw [← hK, hzre]
    exact sqrt_slopeGap_mul_le_csqrtRe_propagationArgument hsigma hkappa hu.le hcone
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le hsigma hKsig
  have hKN : K ≤ N := by
    rw [← hK, ← hN]
    exact Complex.re_le_norm _
  have hT : Tn ≤ sigma + u := by
    rw [← hTn]
    have hb := Complex.norm_le_abs_re_add_abs_im ((sigma : ℂ) + (u : ℂ) * I)
    have hre : ((sigma : ℂ) + (u : ℂ) * I).re = sigma := by simp
    have him : ((sigma : ℂ) + (u : ℂ) * I).im = u := by simp
    rw [hre, him, abs_of_pos hsigma, abs_of_pos hu] at hb
    exact hb
  have hzrepos : 0 < (HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re := by
    rw [hK]; exact hKpos
  have hXre : ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re
      = a * K := by
    rw [Complex.mul_re, hK]
    simp
  have hX : 0 < ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2)).re := by
    rw [hXre]; exact mul_pos ha hKpos
  have hE2 := HTGeometry.norm_besselK1CDeriv_le hX
  have hE1base := HTGeometry.norm_besselK1C_le hX
  rw [hXre] at hE2 hE1base
  have hE1 : ‖HTGeometry.besselK1C
      ((a : ℂ) * HTGeometry.csqrt (((sigma : ℂ) + (u : ℂ) * I) ^ 2 + (h : ℂ) ^ 2))‖
      ≤ Real.exp (-(a * K)) * Real.exp (2 / (a * K)) * Real.sqrt (2 * Real.pi / (a * K)) := by
    refine hE1base.trans ?_
    have hmono : Real.exp (1 / (2 * (a * K))) ≤ Real.exp (2 / (a * K)) := by
      refine Real.exp_le_exp.2 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha hKpos]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg _)) (Real.sqrt_nonneg _)
  have hEnn : (0 : ℝ) ≤ Real.exp (-(a * K)) * Real.exp (2 / (a * K))
      * Real.sqrt (2 * Real.pi / (a * K)) := by positivity
  rw [xiMassBesselHeightDeriv]
  refine (norm_besselHeightDerivCore_le (t := h) ha hzrepos hEnn hE1 hE2).trans ?_
  rw [hK, hN, hTn]
  exact derivEnvelope_assemble ha hsigma hkappa hu hh hcone hKsig hKgap hKslope hKN hT

/-- **(19.2) The exterior envelope of the Fourier derivative.** -/
theorem norm_xiMassFourierDerivative_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖xiMassFourierDerivative a sigma u h‖
      ≤ xiMassBesselDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have huh : u < h := lt_of_lt_of_le (by nlinarith) hcone
  rw [xiMassFourierDerivative_eq_besselHeightDeriv ha hsigma hu.le huh]
  exact norm_xiMassBesselHeightDeriv_le ha hsigma hkappa hu hcone

/-- The exterior envelope constant of the outgoing kernel derivative. -/
def xiMassOutgoingDerivExteriorSqrtConstant (a sigma kappa : ℝ) : ℝ :=
  xiMassBesselDerivExteriorSqrtConstant a sigma kappa
    + (1 / 2) * xiMassBesselExteriorSqrtConstant a sigma kappa

/-- **(19.2) The differentiated exterior envelope of the outgoing kernel.** -/
theorem norm_xiMassCriticalOutgoingDerivative_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖xiMassCriticalOutgoingDerivative a sigma u h‖
      ≤ xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hD := norm_xiMassFourierDerivative_le ha hsigma hkappa hu hcone
  have hF := norm_stripFourier_xiMass_le_besselExteriorSqrt ha hsigma hkappa hu hcone
  have hsplit : ‖xiMassCriticalOutgoingDerivative a sigma u h‖
      ≤ (1 / 2) * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖
        + ‖xiMassFourierDerivative a sigma u h‖ := by
    rw [xiMassCriticalOutgoingDerivative]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    congr 1
    rw [norm_mul]
    norm_num
  refine hsplit.trans ?_
  rw [xiMassOutgoingDerivExteriorSqrtConstant]
  have hroot : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  have hexp : (0 : ℝ) < Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := Real.exp_pos _
  have hhalf : (1 / 2 : ℝ)
      * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖
      ≤ (1 / 2) * (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
    mul_le_mul_of_nonneg_left hF (by norm_num)
  have hgoal : (xiMassBesselDerivExteriorSqrtConstant a sigma kappa
        + (1 / 2) * xiMassBesselExteriorSqrtConstant a sigma kappa) / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
      = (1 / 2) * (xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
        + xiMassBesselDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    field_simp
    ring
  rw [hgoal]
  linarith [hhalf, hD]

end

end RHTower
