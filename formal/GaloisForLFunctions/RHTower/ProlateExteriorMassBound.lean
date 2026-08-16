import GaloisForLFunctions.RHTower.ProlateTwoModeRadialLeakage
import GaloisForLFunctions.RHTower.ProlateEndpointEnergy

/-!
# The exterior mass of an endpoint-normalized radial prolate mode

The corpus already transfers the exact exterior density `c·R²` to the regular Bessel density with
`L¹` error `O(1/c)`, and dominates the Bessel density by a *bandwidth-free* multiple of the
arcsine profile density, whose total tail mass is `1/2`.  Together these say that the exterior
density has bounded total mass — that is, that

```text
∫_{x > 1} R(x)² dx = O(1/c) ,
```

for `R` normalized by `R(1) = 1`.  The short collar `[1, 1 + 9/(8c²)]` between the singular
endpoint and the Dunster matching point is handled separately by the endpoint energy, which gives
`|R| ≤ 2` there, so that piece contributes only `O(1/c²)`.

This is the exterior half of the leakage ratio: with the interior mass bounded below by the band
flux energy, the two together bound the leakage of a fixed mode.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The constant in the exterior mass bound. -/
def radialProlateExteriorMassConstant : ℝ :=
  9 / 10 + 2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2
    + 2 * radialProlateDensityTransferConstant / 5

theorem radialProlateExteriorMassConstant_nonneg :
    0 ≤ radialProlateExteriorMassConstant := by
  have h1 := lgBesselCommonEnvelopeConstant_nonneg
  have h2 := radialProlateDensityTransferConstant_nonneg
  rw [radialProlateExteriorMassConstant]
  positivity

variable {s c : ℝ} {R DR DDR : ℝ → ℝ}

/-- The tail mass of the arcsine profile density beyond any exterior point is at most `1/2`. -/
theorem integral_Ioi_profileDensity_le_half {a : ℝ} (ha : 1 < a) :
    (∫ x in Ioi a, profileDensity x) ≤ 1 / 2 := by
  have hsub : Ioi a ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi ha.le
  have hmono : (∫ x in Ioi a, profileDensity x) ≤ ∫ x in Ioi (1 : ℝ), profileDensity x := by
    refine setIntegral_mono_set integrableOn_profileDensity ?_ ((show Ioi a ≤ Ioi (1 : ℝ) from hsub).eventuallyLE)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact profileDensity_nonneg (le_of_lt hx)
  rw [integral_Ioi_profileDensity] at hmono
  exact hmono

/-- **The exterior mass beyond the matching point.** -/
theorem integral_Ioi_crossing_radialProlate_sq_le
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∫ x in Ioi (dunsterEndpointCrossing c), R x ^ 2)
      ≤ (2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2
          + 2 * radialProlateDensityTransferConstant / 5) / c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  set a : ℝ := dunsterEndpointCrossing c with ha
  have ha1 : 1 < a := dunsterEndpointCrossing_gt_one hc0
  have hca : 1 ≤ c * xiEndpointPhase s a := one_le_c_mul_xiEndpointPhase_crossing hs0 hs1 hc
  have hBint : IntegrableOn (radialProlateBesselDensity s c) (Ioi a) :=
    integrableOn_radialProlateBesselDensity hs0 hs1 hc0 ha1 hca
  have hDint : IntegrableOn (radialProlateDensity c R) (Ioi a) :=
    integrableOn_Ioi_radialProlateDensity hs0 hs1 hc ha1 le_rfl hR1 hR hDR hode
  have hdiff : (∫ x in Ioi a,
      |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      ≤ 2 * radialProlateDensityTransferConstant / c :=
    integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le hs0 hs1 hc le_rfl hR1 hR hDR hode
  have hBmass : (∫ x in Ioi a, radialProlateBesselDensity s c x)
      ≤ 2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2 := by
    have h1 := integral_Ioi_radialProlateBesselDensity_le hs0 hs1 hc0 ha1 hca
    have h2 := integral_Ioi_profileDensity_le_half ha1
    have hK : (0 : ℝ) ≤ 4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2 := by
      have := lgBesselCommonEnvelopeConstant_nonneg
      positivity
    have h3 : (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) *
        ∫ x in Ioi a, profileDensity x
        ≤ (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) * (1 / 2) :=
      mul_le_mul_of_nonneg_left h2 hK
    calc (∫ x in Ioi a, radialProlateBesselDensity s c x)
        ≤ (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) *
            ∫ x in Ioi a, profileDensity x := h1
      _ ≤ (4 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2) * (1 / 2) := h3
      _ = 2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2 := by ring
  -- the exact density is the Bessel density plus the difference
  have hsplit : (∫ x in Ioi a, radialProlateDensity c R x)
      ≤ (∫ x in Ioi a, radialProlateBesselDensity s c x)
        + ∫ x in Ioi a, |radialProlateDensity c R x - radialProlateBesselDensity s c x| := by
    have habsint : IntegrableOn
        (fun x => |radialProlateDensity c R x - radialProlateBesselDensity s c x|) (Ioi a) :=
      (hDint.sub hBint).abs
    have hle : ∀ᵐ x ∂(volume.restrict (Ioi a)), radialProlateDensity c R x
        ≤ radialProlateBesselDensity s c x
          + |radialProlateDensity c R x - radialProlateBesselDensity s c x| := by
      filter_upwards with x
      have := le_abs_self (radialProlateDensity c R x - radialProlateBesselDensity s c x)
      linarith
    have hmono : (∫ x in Ioi a, radialProlateDensity c R x)
        ≤ ∫ x in Ioi a, (radialProlateBesselDensity s c x
            + |radialProlateDensity c R x - radialProlateBesselDensity s c x|) :=
      integral_mono_ae hDint (hBint.add habsint) hle
    rwa [integral_add hBint habsint] at hmono
  have hmass : (∫ x in Ioi a, radialProlateDensity c R x)
      ≤ 2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2
        + 2 * radialProlateDensityTransferConstant / c := by linarith
  -- and the exact density is `c` times the squared profile
  have hscale : (∫ x in Ioi a, radialProlateDensity c R x)
      = c * ∫ x in Ioi a, R x ^ 2 := by
    rw [← integral_const_mul]
    rfl
  rw [hscale] at hmass
  rw [le_div_iff₀ hc0]
  have hT : 2 * radialProlateDensityTransferConstant / c
      ≤ 2 * radialProlateDensityTransferConstant / 5 := by
    have := radialProlateDensityTransferConstant_nonneg
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hc
  nlinarith [hmass, hT]

/-- **The collar between the endpoint and the matching point contributes `O(1/c²)`.** -/
theorem integral_Ioc_one_crossing_radialProlate_sq_le
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∫ x in Ioc (1 : ℝ) (dunsterEndpointCrossing c), R x ^ 2) ≤ 9 / (2 * c ^ 2) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  set a : ℝ := dunsterEndpointCrossing c with ha
  have ha1 : 1 < a := dunsterEndpointCrossing_gt_one hc0
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hbound : ∀ x ∈ Ioc (1 : ℝ) a, R x ^ 2 ≤ 4 := by
    intro x hx
    have habs := abs_radialProlate_le_two_endpoint hs0 hs1 hc hR1 hR hDR hode hx.1.le hx.2
    nlinarith [abs_nonneg (R x), sq_abs (R x), habs]
  have hint : IntegrableOn (fun x => R x ^ 2) (Ioc (1 : ℝ) a) :=
    (hRc.pow 2).integrableOn_Ioc
  have hmono : (∫ x in Ioc (1 : ℝ) a, R x ^ 2) ≤ ∫ _x in Ioc (1 : ℝ) a, (4 : ℝ) := by
    refine setIntegral_mono_on hint ((continuous_const : Continuous fun _ : ℝ => (4 : ℝ)).integrableOn_Ioc) measurableSet_Ioc
      hbound
  have hmeas : (volume.real (Ioc (1 : ℝ) a)) = a - 1 := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hconst : (∫ _x in Ioc (1 : ℝ) a, (4 : ℝ)) = 4 * (a - 1) := by
    rw [setIntegral_const, hmeas, smul_eq_mul]
    ring
  rw [hconst] at hmono
  have hwidth : a - 1 = 9 / (8 * c ^ 2) := dunsterEndpointCrossing_sub_one
  rw [hwidth] at hmono
  have hval : 4 * (9 / (8 * c ^ 2)) = 9 / (2 * c ^ 2) := by
    field_simp
    ring
  rwa [hval] at hmono

/-- **The total exterior mass is `O(1/c)`.** -/
theorem integral_Ioi_one_radialProlate_sq_le
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∫ x in Ioi (1 : ℝ), R x ^ 2) ≤ radialProlateExteriorMassConstant / c := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  set a : ℝ := dunsterEndpointCrossing c with ha
  have ha1 : 1 < a := dunsterEndpointCrossing_gt_one hc0
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt
  have hDint : IntegrableOn (radialProlateDensity c R) (Ioi a) :=
    integrableOn_Ioi_radialProlateDensity hs0 hs1 hc ha1 le_rfl hR1 hR hDR hode
  have hsqint : IntegrableOn (fun x => R x ^ 2) (Ioi a) := by
    have h : IntegrableOn (fun x => c⁻¹ * radialProlateDensity c R x) (Ioi a) :=
      hDint.const_mul c⁻¹
    have heq : (fun x => c⁻¹ * radialProlateDensity c R x) = fun x => R x ^ 2 := by
      funext x
      rw [radialProlateDensity]
      field_simp
    rwa [heq] at h
  have hint1 : IntegrableOn (fun x => R x ^ 2) (Ioc (1 : ℝ) a) :=
    (hRc.pow 2).integrableOn_Ioc
  have hunion : Ioc (1 : ℝ) a ∪ Ioi a = Ioi (1 : ℝ) := Ioc_union_Ioi_eq_Ioi ha1.le
  have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi le_rfl
  have hsplit : (∫ x in Ioi (1 : ℝ), R x ^ 2)
      = (∫ x in Ioc (1 : ℝ) a, R x ^ 2) + ∫ x in Ioi a, R x ^ 2 := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint1 hsqint]
  have h1 := integral_Ioc_one_crossing_radialProlate_sq_le hs0 hs1 hc hR1 hR hDR hode
  have h2 := integral_Ioi_crossing_radialProlate_sq_le hs0 hs1 hc hR1 hR hDR hode
  have hcollar : 9 / (2 * c ^ 2) ≤ (9 / 10) / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]
    nlinarith [hc, hc0]
  have hsum : (9 / 10 : ℝ) / c
      + (2 * Real.pi * lgBesselCommonEnvelopeConstant ^ 2
        + 2 * radialProlateDensityTransferConstant / 5) / c
      = radialProlateExteriorMassConstant / c := by
    rw [radialProlateExteriorMassConstant]
    ring
  rw [hsplit, ← hsum]
  linarith [h1, h2, hcollar]

end GaloisForLFunctions.RHTower
