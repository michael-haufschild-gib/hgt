import GaloisForLFunctions.RHTower.ProlateIndexedConstrainedCoordinate
import GaloisForLFunctions.RHTower.ProlateGlobalBandEigen
import GaloisForLFunctions.RHTower.ConstrainedProlateBesselBound
import GaloisForLFunctions.RHTower.ProlateIndexedJointSpectrum

/-!
# The constrained-prolate coordinate converges to its Hermite value

The analytic layer describes a signed prolate mode by its canonical radial datum `Phi`, an even
smooth real band eigenfunction at the squared signed value; the constrained tower describes the same
mode by its pointwise source `S`, whose integral over the aperture is the constraint coordinate.
Both channels of the unit-band extension of `S` are real band eigenfunctions at the same eigenvalue,
so each is a real multiple of `Phi`, and therefore

```text
S (a·x)  =  z · Phi x      on the open aperture,
```

for a single complex constant `z`.  The constraint coordinate is then the shape ratio of `Phi`:
the `L²` normalization of the mode fixes `|z|²·a·∫Phi² = 1`, and the coordinate is
`z·a·∫Phi`, so

```text
‖ℓ_n(a)‖²  =  a · ( ∫_{−1}^{1} Phi )² / ∫_{−1}^{1} Phi² ,
```

which is exactly the quantity whose limit the indexed coordinate theorem computes.  Hence

```text
‖evenProlateConstraintCoord a (2j)‖  →  constrainedProlateHermiteCoordinate j .
```
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

variable {a : ℝ} {n : ℕ}

/-- **One complex constant relates the two descriptions of a signed prolate mode.** -/
theorem exists_unitExtension_eq_const_mul_radialPhi (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ z : ℂ, ∀ x : ℝ, evenProlateSignedUnitExtension a n hvalue x
      = z * ((signedModeRadialData a n).Phi x : ℂ) := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hc : (0 : ℝ) < 2 * Real.pi * a ^ (2 : ℕ) := by positivity
  have hlam : evenProlateSignedValue a n ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hvalue
  have hcont : Continuous (evenProlateSignedUnitExtension a n hvalue) :=
    continuous_evenProlateSignedUnitExtension a n hvalue
  obtain ⟨s₁, hs₁⟩ := continuous_real_bandEigen_proportional hc hlam
    hD.1.continuous (Complex.continuous_re.comp hcont) hD.2.1
    hD.2.2.2.2.2.2.2.2.1
    (fun x => bandTransform_evenProlateSignedUnitExtension_re_global ha hvalue x)
  obtain ⟨s₂, hs₂⟩ := continuous_real_bandEigen_proportional hc hlam
    hD.1.continuous (Complex.continuous_im.comp hcont) hD.2.1
    hD.2.2.2.2.2.2.2.2.1
    (fun x => bandTransform_evenProlateSignedUnitExtension_im_global ha hvalue x)
  refine ⟨(s₁ : ℂ) + (s₂ : ℂ) * Complex.I, fun x => ?_⟩
  have hre := hs₁ x
  have him := hs₂ x
  simp only [Function.comp_apply] at hre him
  have hz := Complex.re_add_im (evenProlateSignedUnitExtension a n hvalue x)
  rw [← hz, hre, him]
  push_cast
  ring

/-- The pointwise source is that constant times the radial datum, on the open aperture. -/
theorem evenProlateSignedPointwiseSource_eq_const_mul_radialPhi (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) {z : ℂ}
    (hz : ∀ x : ℝ, evenProlateSignedUnitExtension a n hvalue x
      = z * ((signedModeRadialData a n).Phi x : ℂ))
    {y : ℝ} (hy : y ∈ Ioo (-a) a) :
    evenProlateSignedPointwiseSource a n hvalue y
      = z * (((signedModeRadialData a n).Phi (y / a) : ℝ) : ℂ) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hx : y / a ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · rw [lt_div_iff₀ ha]
      have := hy.1
      linarith
    · rw [div_lt_one ha]
      exact hy.2
  have hpt : a * (y / a) = y := by field_simp
  have h := evenProlateSignedUnitExtension_eq_source ha n hvalue hx
  rw [hpt] at h
  rw [← h, hz]

/-! ## The two aperture integrals -/

theorem integral_evenProlateSignedPointwiseSource_eq (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) {z : ℂ}
    (hz : ∀ x : ℝ, evenProlateSignedUnitExtension a n hvalue x
      = z * ((signedModeRadialData a n).Phi x : ℂ)) :
    (∫ y in Icc (-a) a, evenProlateSignedPointwiseSource a n hvalue y)
      = z * (a : ℂ) * ((∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x : ℝ) : ℂ) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hD := signedModeRadialData_isExact ha n hvalue
  have hPhic : Continuous (signedModeRadialData a n).Phi := hD.1.continuous
  have hstep : (∫ y in Icc (-a) a, evenProlateSignedPointwiseSource a n hvalue y)
      = ∫ y in (-a)..a, evenProlateSignedPointwiseSource a n hvalue y := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hcongr : (∫ y in (-a)..a, evenProlateSignedPointwiseSource a n hvalue y)
      = ∫ y in (-a)..a, z * (((signedModeRadialData a n).Phi (y / a) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le (by linarith : (-a : ℝ) ≤ a)]
    filter_upwards [Ioo_ae_eq_Ioc (a := (-a : ℝ)) (b := a)] with y hy
    intro hyIoc
    exact evenProlateSignedPointwiseSource_eq_const_mul_radialPhi ha n hvalue hz (hy.mpr hyIoc)
  have hpull : (∫ y in (-a)..a, z * (((signedModeRadialData a n).Phi (y / a) : ℝ) : ℂ))
      = z * ∫ y in (-a)..a, (((signedModeRadialData a n).Phi (y / a) : ℝ) : ℂ) :=
    intervalIntegral.integral_const_mul _ _
  have hsub : (∫ y in (-a)..a, (((signedModeRadialData a n).Phi (y / a) : ℝ) : ℂ))
      = (a : ℂ) * ∫ x in (-1 : ℝ)..1, (((signedModeRadialData a n).Phi x : ℝ) : ℂ) := by
    have h := intervalIntegral.integral_comp_div
      (a := (-a : ℝ)) (b := a) (c := a)
      (fun x : ℝ => (((signedModeRadialData a n).Phi x : ℝ) : ℂ)) hane
    rw [h]
    have hd1 : (-a) / a = -1 := by field_simp
    have hd2 : a / a = 1 := by field_simp
    rw [hd1, hd2, Complex.real_smul]
  have hre : (∫ x in (-1 : ℝ)..1, (((signedModeRadialData a n).Phi x : ℝ) : ℂ))
      = ((∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact integral_complex_ofReal (f := (signedModeRadialData a n).Phi)
  rw [hstep, hcongr, hpull, hsub, hre]
  ring

theorem integral_norm_sq_evenProlateSignedPointwiseSource_aperture (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) {z : ℂ}
    (hz : ∀ x : ℝ, evenProlateSignedUnitExtension a n hvalue x
      = z * ((signedModeRadialData a n).Phi x : ℂ)) :
    ‖z‖ ^ (2 : ℕ) * (a * ∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x ^ (2 : ℕ)) = 1 := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hD := signedModeRadialData_isExact ha n hvalue
  have hPhic : Continuous (signedModeRadialData a n).Phi := hD.1.continuous
  have htotal := integral_norm_sq_evenProlateSignedPointwiseSource_eq_one a ha.le n hvalue
  have hzeroOut : ∀ y : ℝ, y ∉ Icc (-a) a →
      ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ) = 0 := by
    intro y hy
    rw [evenProlateSignedPointwiseSource_eq_zero_of_not_mem_Icc ha.le hvalue hy]
    simp
  have hrestrict : (∫ y : ℝ, ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ))
      = ∫ y in Icc (-a) a, ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOut]
  have hstep : (∫ y in Icc (-a) a, ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ))
      = ∫ y in (-a)..a, ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hcongr : (∫ y in (-a)..a, ‖evenProlateSignedPointwiseSource a n hvalue y‖ ^ (2 : ℕ))
      = ∫ y in (-a)..a, ‖z‖ ^ (2 : ℕ) * (signedModeRadialData a n).Phi (y / a) ^ (2 : ℕ) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le (by linarith : (-a : ℝ) ≤ a)]
    filter_upwards [Ioo_ae_eq_Ioc (a := (-a : ℝ)) (b := a)] with y hy
    intro hyIoc
    rw [evenProlateSignedPointwiseSource_eq_const_mul_radialPhi ha n hvalue hz (hy.mpr hyIoc),
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpull : (∫ y in (-a)..a, ‖z‖ ^ (2 : ℕ) * (signedModeRadialData a n).Phi (y / a) ^ (2 : ℕ))
      = ‖z‖ ^ (2 : ℕ) * ∫ y in (-a)..a, (signedModeRadialData a n).Phi (y / a) ^ (2 : ℕ) :=
    intervalIntegral.integral_const_mul _ _
  have hsub : (∫ y in (-a)..a, (signedModeRadialData a n).Phi (y / a) ^ (2 : ℕ))
      = a * ∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x ^ (2 : ℕ) := by
    have h := intervalIntegral.integral_comp_div
      (a := (-a : ℝ)) (b := a) (c := a)
      (fun x : ℝ => (signedModeRadialData a n).Phi x ^ (2 : ℕ)) hane
    rw [h]
    have hd1 : (-a) / a = -1 := by field_simp
    have hd2 : a / a = 1 := by field_simp
    rw [hd1, hd2, smul_eq_mul]
  rw [hrestrict, hstep, hcongr, hpull, hsub] at htotal
  exact htotal

/-! ## The constraint coordinate is the shape ratio -/

/-- **The constraint coordinate squared is the aperture-scaled shape ratio of the radial datum.** -/
theorem norm_sq_evenProlateConstraintCoord_eq (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    ‖evenProlateConstraintCoord a n‖ ^ (2 : ℕ)
      = a * ((∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x) ^ (2 : ℕ)
          / ∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x ^ (2 : ℕ)) := by
  obtain ⟨z, hz⟩ := exists_unitExtension_eq_const_mul_radialPhi ha n hvalue
  have hmass := integral_norm_sq_evenProlateSignedPointwiseSource_aperture ha n hvalue hz
  have hcoord : evenProlateConstraintCoord a n
      = z * (a : ℂ) * ((∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x : ℝ) : ℂ) := by
    rw [evenProlateConstraintCoord_eq_integral]
    have hae := ae_eq_evenProlateSignedPointwiseSource a ha.le n hvalue
    have hcongr : (∫ y in centralInterval a,
        (((evenProlateSignedMode a n : evenSubspace) : SoninL2) : ℝ → ℂ) y)
        = ∫ y in Icc (-a) a, evenProlateSignedPointwiseSource a n hvalue y := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [hae] with y hy
      intro _
      exact hy.symm
    rw [hcongr]
    exact integral_evenProlateSignedPointwiseSource_eq ha n hvalue hz
  have hmasspos : 0 < ∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x ^ (2 : ℕ) := by
    have hznn : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) := by positivity
    have hprod : (0 : ℝ) ≤ ‖z‖ ^ (2 : ℕ) * a := mul_nonneg hznn ha.le
    by_contra hcon
    have hle : (∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x ^ (2 : ℕ)) ≤ 0 := not_lt.1 hcon
    nlinarith [hmass, hprod, hle]
  rw [hcoord]
  have hnorm : ‖z * (a : ℂ) * ((∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x : ℝ) : ℂ)‖ ^ (2 : ℕ)
      = ‖z‖ ^ (2 : ℕ) * a ^ (2 : ℕ) * (∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x) ^ (2 : ℕ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  rw [hnorm]
  field_simp
  nlinarith [hmass, hmasspos, ha]

/-! ## The limit of the constraint coordinate -/

theorem shapeRatio_radialR_eq_radialPhi (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    (∫ u in (-1 : ℝ)..1, (signedModeRadialData a n).R u) ^ (2 : ℕ)
        / ∫ u in (-1 : ℝ)..1, ((signedModeRadialData a n).R u) ^ (2 : ℕ)
      = (∫ x in (-1 : ℝ)..1, (signedModeRadialData a n).Phi x) ^ (2 : ℕ)
        / ∫ x in (-1 : ℝ)..1, ((signedModeRadialData a n).Phi x) ^ (2 : ℕ) := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hRdef : (signedModeRadialData a n).R = prolateEndpointNormalize
      (signedModeRadialData a n).Phi := hD.2.2.2.2.1
  have hone : (signedModeRadialData a n).Phi 1 ≠ 0 := hD.2.2.2.1
  have hfun : (signedModeRadialData a n).R
      = fun x => ((signedModeRadialData a n).Phi 1)⁻¹ * (signedModeRadialData a n).Phi x := by
    funext x
    rw [hRdef, prolateEndpointNormalize, div_eq_inv_mul]
  rw [hfun]
  exact GaloisForLFunctions.HTGeometry.shapeRatio_amplitude_invariant
    (signedModeRadialData a n).Phi (inv_ne_zero hone) 1

/-- **The constrained coordinate converges to the Hermite coordinate, squared.** -/
theorem tendsto_norm_sq_evenProlateConstraintCoord (j : ℕ) :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
        ‖evenProlateConstraintCoord (a : ℝ) (2 * j)‖ ^ (2 : ℕ))
      atTop (𝓝 (constrainedProlateHermiteCoordinate j ^ (2 : ℕ))) := by
  have hbase := GaloisForLFunctions.RHTower.tendsto_indexedRung_constrainedCoordinate j
  have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hne : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      evenProlateSignedValue (a : ℝ) (2 * j) ≠ 0 :=
    GaloisForLFunctions.RHTower.tendsto_prolatePositiveAperture_val_atTop.eventually
      (eventually_evenProlateSignedValue_ne_zero (2 * j))
  have hev : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) *
          ((∫ u in (-1 : ℝ)..1, (signedModeRadialData (a : ℝ) (2 * j)).R u) ^ (2 : ℕ)
            / ∫ u in (-1 : ℝ)..1, ((signedModeRadialData (a : ℝ) (2 * j)).R u) ^ (2 : ℕ))
        = Real.sqrt (2 * Real.pi) * ‖evenProlateConstraintCoord (a : ℝ) (2 * j)‖ ^ (2 : ℕ) := by
    filter_upwards [hne] with a hva
    have ha : (0 : ℝ) < (a : ℝ) := a.property
    have hband : GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
        = 2 * Real.pi * (a : ℝ) ^ (2 : ℕ) := rfl
    have hsqrt : Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)
        = (a : ℝ) * Real.sqrt (2 * Real.pi) := by
      rw [hband, mul_comm (2 * Real.pi) ((a : ℝ) ^ (2 : ℕ)),
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ (2 : ℕ)), Real.sqrt_sq ha.le]
    rw [hsqrt, shapeRatio_radialR_eq_radialPhi ha (2 * j) hva,
      norm_sq_evenProlateConstraintCoord_eq ha (2 * j) hva]
    ring
  have hlim : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      Real.sqrt (2 * Real.pi) * ‖evenProlateConstraintCoord (a : ℝ) (2 * j)‖ ^ (2 : ℕ))
      atTop (𝓝 (Real.sqrt (2 * Real.pi) * constrainedProlateHermiteCoordinate j ^ (2 : ℕ))) :=
    hbase.congr' hev
  have hdiv := hlim.div_const (Real.sqrt (2 * Real.pi))
  rw [mul_div_cancel_left₀ _ hpi.ne'] at hdiv
  refine hdiv.congr fun a => ?_
  rw [mul_div_cancel_left₀ _ hpi.ne']

/-- **The constrained-prolate coordinate limit.** -/
theorem tendsto_norm_evenProlateConstraintCoord (j : ℕ) :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
        ‖evenProlateConstraintCoord (a : ℝ) (2 * j)‖)
      atTop (𝓝 (constrainedProlateHermiteCoordinate j)) := by
  have h := (tendsto_norm_sq_evenProlateConstraintCoord j).sqrt
  have hpos := constrainedProlateHermiteCoordinate_pos j
  rw [Real.sqrt_sq hpos.le] at h
  refine h.congr fun a => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **The constrained-prolate coordinate limit on the aperture axis.**  This is the hypothesis the
constrained-prolate clock tower consumes, for the Fourier-even renumbering `j ↦ 2j`. -/
theorem tendsto_norm_evenProlateConstraintCoord_atTop (j : ℕ) :
    Tendsto (fun lam : ℝ => ‖evenProlateConstraintCoord lam (2 * j)‖) atTop
      (𝓝 (constrainedProlateHermiteCoordinate j)) := by
  have hmap : Filter.map (Subtype.val :
      GaloisForLFunctions.RHTower.ProlatePositiveAperture → ℝ) atTop = atTop := by
    refine Filter.map_val_atTop_of_Ici_subset (a := (1 : ℝ)) (s := {x : ℝ | 0 < x}) ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    exact lt_of_lt_of_le zero_lt_one hx1
  have h := tendsto_norm_evenProlateConstraintCoord j
  rw [← hmap, Filter.tendsto_map'_iff]
  exact h

end RHTower

end
