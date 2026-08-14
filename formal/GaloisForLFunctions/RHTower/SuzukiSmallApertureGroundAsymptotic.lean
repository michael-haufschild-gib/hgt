import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundEnergy

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-!
# Suzuki's sharp small-aperture ground-energy asymptotic

This module proves the asymptotic clause of Suzuki (2026), Theorem 1.4 for the
actual CCM/Friedrichs ground energy.  The proof identifies the limiting Rayleigh
infimum `suzukiLimitingLogGroundEnergy`, proves its strict positivity, transfers
all unit-aperture competitors to and from actual smooth CCM sources, and obtains
the stronger uniform estimate

`|lambda_a - (log(1/a) + mu₁ - log(2*pi) + psi(2) - 1)| <= C * a`.

No attainment or spectral perturbation premise is used: exact rescaling and the
uniform Schur bound control the infimum directly in both directions.
-/

/-- Complex remainder in Suzuki's fixed-interval small-aperture form. -/
def suzukiScaledComplexRemainderQuadratic
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) : ℝ :=
  suzukiScaledRemainderQuadraticReal a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart) +
    suzukiScaledRemainderQuadraticReal a
      (suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart)

/-- Uniform complex Schur bound for the exact scaled remainder. -/
theorem suzukiScaledComplexRemainderQuadratic_abs_le
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    |suzukiScaledComplexRemainderQuadratic a u| ≤
      2 * suzukiOriginCurvatureUnitBound *
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u := by
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  have hr := suzukiScaledRemainderQuadraticReal_abs_le a ur
  have hi := suzukiScaledRemainderQuadraticReal_abs_le a ui
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq]
  change |suzukiScaledRemainderQuadraticReal a ur +
      suzukiScaledRemainderQuadraticReal a ui| ≤
    2 * suzukiOriginCurvatureUnitBound *
      ((∫ x in (-1 : ℝ)..1, ur x ^ 2) +
        ∫ x in (-1 : ℝ)..1, ui x ^ 2)
  exact (abs_add_le _ _).trans ((add_le_add hr hi).trans_eq (by ring))

def suzukiSmallApertureSpectralShift (a : ℝ) : ℝ :=
  -Real.log a - (2 * suzukiWeilArchimedeanConstant + 1)

def suzukiSmallApertureRemainderRadius (a : ℝ) : ℝ :=
  2 * a * suzukiOriginCurvatureUnitBound

/-- Exact main-term plus remainder decomposition of Suzuki's scaled form. -/
theorem suzukiPrimeFreeScaledForm_eq_limiting_sub_remainder
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiPrimeFreeScaledForm a u =
      suzukiSmallApertureSpectralShift a.val *
          suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
        suzukiLimitingLogForm u -
          a.val * suzukiScaledComplexRemainderQuadratic a u := by
  let ur := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.realPart
  let ui := suzukiRestrictedWeilRealTestToCore suzukiUnitAperture u.imagPart
  rw [suzukiRestrictedWeilComplexIntervalEnergy_eq]
  simp only [suzukiUnitAperture]
  unfold suzukiPrimeFreeScaledForm suzukiPrimeFreeScaledRealForm
    suzukiSmallApertureSpectralShift suzukiLimitingLogForm
    suzukiScaledComplexRemainderQuadratic
  change ((-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
        (∫ x in (-1 : ℝ)..1, ur x ^ 2) + suzukiFinitePartEnergy 1 ur -
          a.val * suzukiScaledRemainderQuadraticReal a ur) +
      ((-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
        (∫ x in (-1 : ℝ)..1, ui x ^ 2) + suzukiFinitePartEnergy 1 ui -
          a.val * suzukiScaledRemainderQuadraticReal a ui) = _
  change ((-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
        (∫ x in (-1 : ℝ)..1, ur x ^ 2) + suzukiFinitePartEnergy 1 ur -
          a.val * suzukiScaledRemainderQuadraticReal a ur) +
      ((-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
        (∫ x in (-1 : ℝ)..1, ui x ^ 2) + suzukiFinitePartEnergy 1 ui -
          a.val * suzukiScaledRemainderQuadraticReal a ui) =
    (-Real.log a.val - (2 * suzukiWeilArchimedeanConstant + 1)) *
        ((∫ x in (-1 : ℝ)..1, ur x ^ 2) +
          ∫ x in (-1 : ℝ)..1, ui x ^ 2) +
      (suzukiFinitePartEnergy 1 ur + suzukiFinitePartEnergy 1 ui) -
        a.val * (suzukiScaledRemainderQuadraticReal a ur +
          suzukiScaledRemainderQuadraticReal a ui)
  ring

/-- Uniform numerator error, stronger than the paper's pointwise `O(a)`. -/
theorem abs_suzukiPrimeFreeScaledForm_sub_main_le
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    |suzukiPrimeFreeScaledForm a u -
        (suzukiSmallApertureSpectralShift a.val *
            suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
          suzukiLimitingLogForm u)| ≤
      suzukiSmallApertureRemainderRadius a.val *
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u := by
  rw [suzukiPrimeFreeScaledForm_eq_limiting_sub_remainder]
  have h := suzukiScaledComplexRemainderQuadratic_abs_le a u
  rw [show
      suzukiSmallApertureSpectralShift a.val *
            suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
          suzukiLimitingLogForm u -
            a.val * suzukiScaledComplexRemainderQuadratic a u -
          (suzukiSmallApertureSpectralShift a.val *
              suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
            suzukiLimitingLogForm u) =
        -a.val * suzukiScaledComplexRemainderQuadratic a u by ring,
    abs_mul, abs_neg, abs_of_pos a.pos]
  unfold suzukiSmallApertureRemainderRadius
  nlinarith [mul_le_mul_of_nonneg_left h a.pos.le]

theorem suzukiPrimeFreeScaledRayleigh_mem_bounds
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1)
    (henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u) :
    suzukiSmallApertureSpectralShift a.val +
          suzukiLimitingLogForm u /
            suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u -
          suzukiSmallApertureRemainderRadius a.val ≤
        suzukiPrimeFreeScaledForm a u /
          suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ∧
      suzukiPrimeFreeScaledForm a u /
          suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ≤
        suzukiSmallApertureSpectralShift a.val +
          suzukiLimitingLogForm u /
            suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
          suzukiSmallApertureRemainderRadius a.val := by
  let E := suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u
  have habs := abs_suzukiPrimeFreeScaledForm_sub_main_le a u
  have hlower :
      (suzukiSmallApertureSpectralShift a.val -
          suzukiSmallApertureRemainderRadius a.val) * E +
        suzukiLimitingLogForm u ≤ suzukiPrimeFreeScaledForm a u := by
    dsimp only [E] at habs ⊢
    have h := (abs_le.mp habs).1
    ring_nf at h ⊢
    linarith only [h]
  have hupper : suzukiPrimeFreeScaledForm a u ≤
      (suzukiSmallApertureSpectralShift a.val +
          suzukiSmallApertureRemainderRadius a.val) * E +
        suzukiLimitingLogForm u := by
    dsimp only [E] at habs ⊢
    have h := (abs_le.mp habs).2
    ring_nf at h ⊢
    linarith only [h]
  constructor
  · rw [le_div_iff₀ henergy]
    calc
      (suzukiSmallApertureSpectralShift a.val +
            suzukiLimitingLogForm u / E -
          suzukiSmallApertureRemainderRadius a.val) * E =
        (suzukiSmallApertureSpectralShift a.val -
            suzukiSmallApertureRemainderRadius a.val) * E +
          suzukiLimitingLogForm u := by
            calc
              _ = suzukiSmallApertureSpectralShift a.val * E +
                  (suzukiLimitingLogForm u / E) * E -
                    suzukiSmallApertureRemainderRadius a.val * E := by ring
              _ = _ := by rw [div_mul_cancel₀ _ henergy.ne']; ring
      _ ≤ suzukiPrimeFreeScaledForm a u := hlower
  · rw [div_le_iff₀ henergy]
    calc
      suzukiPrimeFreeScaledForm a u ≤
          (suzukiSmallApertureSpectralShift a.val +
              suzukiSmallApertureRemainderRadius a.val) * E +
            suzukiLimitingLogForm u := hupper
      _ = (suzukiSmallApertureSpectralShift a.val +
            suzukiLimitingLogForm u / E +
          suzukiSmallApertureRemainderRadius a.val) * E := by
            calc
              _ = suzukiSmallApertureSpectralShift a.val * E +
                  suzukiSmallApertureRemainderRadius a.val * E +
                    suzukiLimitingLogForm u := by ring
              _ = suzukiSmallApertureSpectralShift a.val * E +
                  (suzukiLimitingLogForm u / E) * E +
                    suzukiSmallApertureRemainderRadius a.val * E := by
                      rw [div_mul_cancel₀ _ henergy.ne']
                      ring
              _ = _ := by ring

/-! ## The limiting ground energy `mu₁` -/

def suzukiLimitingLogRayleighSet : Set ℝ :=
  {r | ∃ u : SuzukiRestrictedWeilComplexTest 1,
    0 < suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u ∧
      r = suzukiLimitingLogForm u /
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u}

theorem suzukiLimitingLogRayleighSet_nonempty :
    suzukiLimitingLogRayleighSet.Nonempty := by
  obtain ⟨u, hu, _⟩ := exists_suzukiSmoothInteriorRayleigh_lt_groundEnergy_add
    suzukiUnitAperture (by norm_num : (0 : ℝ) < 1)
  let v := u.toRestrictedWeilComplexTest
  have hmass : 0 < suzukiWeilIntervalFormMass suzukiUnitAperture
      u.toCCMFormVector := by
    unfold suzukiWeilIntervalFormMass
    exact pow_pos (norm_pos_iff.mpr hu) 2
  have henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy
      suzukiUnitAperture v := by
    rw [← suzukiWeilIntervalFormMass_complexSmooth_eq]
    exact hmass
  exact ⟨suzukiLimitingLogForm v /
      suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture v,
    v, henergy, rfl⟩

theorem suzukiLimitingLogRayleighSet_bddBelow :
    BddBelow suzukiLimitingLogRayleighSet := by
  refine ⟨(1 / 24 : ℝ), ?_⟩
  rintro r ⟨u, henergy, rfl⟩
  rw [le_div_iff₀ henergy]
  exact suzukiLimitingLogForm_coercive u

/-- `mu₁`, the exact ground value of Suzuki's limiting logarithmic form. -/
def suzukiLimitingLogGroundEnergy : ℝ :=
  sInf suzukiLimitingLogRayleighSet

theorem isGLB_suzukiLimitingLogRayleighSet :
    IsGLB suzukiLimitingLogRayleighSet suzukiLimitingLogGroundEnergy := by
  constructor
  · intro r hr
    exact csInf_le suzukiLimitingLogRayleighSet_bddBelow hr
  · intro b hb
    exact le_csInf suzukiLimitingLogRayleighSet_nonempty hb

theorem one_div_twentyFour_le_suzukiLimitingLogGroundEnergy :
    (1 / 24 : ℝ) ≤ suzukiLimitingLogGroundEnergy := by
  apply isGLB_suzukiLimitingLogRayleighSet.2
  rintro r ⟨u, henergy, rfl⟩
  rw [le_div_iff₀ henergy]
  exact suzukiLimitingLogForm_coercive u

theorem suzukiLimitingLogGroundEnergy_pos :
    0 < suzukiLimitingLogGroundEnergy := by
  exact (by norm_num : (0 : ℝ) < 1 / 24).trans_le
    one_div_twentyFour_le_suzukiLimitingLogGroundEnergy

/-! ## Rescaling every unit test back to an actual CCM source -/

def ccmComplexSmoothInteriorSourceOfUnitRescale
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩ where
  toFun x := u (a.val⁻¹ * x)
  smooth := u.contDiff'.comp (contDiff_const.mul contDiff_id)
  hasCompactSupport := by
    change HasCompactSupport
      (u.toFun ∘ (Homeomorph.mulLeft₀ a.val⁻¹ (inv_ne_zero a.pos.ne')))
    exact u.hasCompactSupport'.comp_homeomorph
      (Homeomorph.mulLeft₀ a.val⁻¹ (inv_ne_zero a.pos.ne'))
  tsupport_subset := by
    have hsupport :
        tsupport (fun x : ℝ => u (a.val⁻¹ * x)) =
          (Homeomorph.mulLeft₀ a.val⁻¹ (inv_ne_zero a.pos.ne')) ⁻¹'
            tsupport u.toFun := by
      rw [show (fun x : ℝ => u (a.val⁻¹ * x)) =
        u.toFun ∘ (Homeomorph.mulLeft₀ a.val⁻¹ (inv_ne_zero a.pos.ne')) by rfl,
        tsupport_comp_eq_preimage]
    rw [hsupport]
    intro x hx
    have hxunit := u.tsupport_subset' hx
    change -1 < a.val⁻¹ * x ∧ a.val⁻¹ * x < 1 at hxunit
    have hxdiv : -1 < x / a.val ∧ x / a.val < 1 := by
      simpa only [div_eq_mul_inv, mul_comm] using hxunit
    change -a.val < x ∧ x < a.val
    constructor
    · simpa using (lt_div_iff₀ a.pos).mp hxdiv.1
    · simpa using (div_lt_iff₀ a.pos).mp hxdiv.2

@[simp] theorem ccmComplexSmoothInteriorSourceOfUnitRescale_apply
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) (x : ℝ) :
    ccmComplexSmoothInteriorSourceOfUnitRescale a u x = u (a.val⁻¹ * x) := rfl

theorem ccmComplexSmoothInteriorSourceUnitPullback_ofUnitRescale
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    ccmComplexSmoothInteriorSourceUnitPullback a
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u) = u := by
  ext x
  change u (a.val⁻¹ * (a.val * x)) = u x
  rw [← mul_assoc, inv_mul_cancel₀ a.pos.ne', one_mul]

theorem ccmRestrictedWeilSourceQuadratic_ofUnitRescale_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector =
      suzukiRescaledComplexSourceForm a u := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_rescaledComplexSourceForm,
    ccmComplexSmoothInteriorSourceUnitPullback_ofUnitRescale]

theorem suzukiWeilIntervalFormMass_ofUnitRescale_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1) :
    suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector =
      a.val * suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u := by
  rw [suzukiWeilIntervalFormMass_complexSmooth_eq,
    suzukiRestrictedWeilComplexIntervalEnergy_unitPullback,
    ccmComplexSmoothInteriorSourceUnitPullback_ofUnitRescale]

theorem suzukiWeilIntervalFormRayleigh_ofUnitRescale_eq
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1)
    (henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u) :
    suzukiWeilIntervalFormRayleigh ⟨a.val, a.pos⟩
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector =
      suzukiPrimeFreeScaledForm a u /
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u := by
  rw [suzukiWeilIntervalFormRayleigh,
    ccmRestrictedWeilSourceQuadratic_ofUnitRescale_eq,
    suzukiWeilIntervalFormMass_ofUnitRescale_eq,
    ← suzukiRescaledComplexSourceForm_eq]
  field_simp [a.pos.ne', henergy.ne']

theorem suzukiWeilIntervalFormEmbedding_ofUnitRescale_ne_zero
    (a : SuzukiPrimeFreeSmallAperture)
    (u : SuzukiRestrictedWeilComplexTest 1)
    (henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u) :
    suzukiWeilIntervalFormEmbedding ⟨a.val, a.pos⟩
        (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector ≠ 0 := by
  have hmass := suzukiWeilIntervalFormMass_ofUnitRescale_eq a u
  have hmassPos : 0 < suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩
      (ccmComplexSmoothInteriorSourceOfUnitRescale a u).toCCMFormVector := by
    rw [hmass]
    exact mul_pos a.pos henergy
  unfold suzukiWeilIntervalFormMass at hmassPos
  exact norm_ne_zero_iff.mp (sq_pos_iff.mp hmassPos)

theorem suzukiWeilIntervalFormRayleigh_eq_scaledUnitPullback
    (a : SuzukiPrimeFreeSmallAperture)
    (u : CCMComplexSmoothInteriorSource ⟨a.val, a.pos⟩)
    (henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture
      (ccmComplexSmoothInteriorSourceUnitPullback a u)) :
    suzukiWeilIntervalFormRayleigh ⟨a.val, a.pos⟩ u.toCCMFormVector =
      suzukiPrimeFreeScaledForm a
          (ccmComplexSmoothInteriorSourceUnitPullback a u) /
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture
          (ccmComplexSmoothInteriorSourceUnitPullback a u) := by
  let v := ccmComplexSmoothInteriorSourceUnitPullback a u
  rw [suzukiWeilIntervalFormRayleigh,
    ccmRestrictedWeilSourceQuadratic_eq_rescaledComplexSourceForm,
    suzukiWeilIntervalFormMass_complexSmooth_eq,
    suzukiRestrictedWeilComplexIntervalEnergy_unitPullback,
    ← suzukiRescaledComplexSourceForm_eq]
  field_simp [a.pos.ne', henergy.ne']

/-! ## Two-sided spectral asymptotic -/

theorem suzukiSmallAperture_intervalGroundEnergy_lower
    (a : SuzukiPrimeFreeSmallAperture) :
    suzukiSmallApertureSpectralShift a.val + suzukiLimitingLogGroundEnergy -
        suzukiSmallApertureRemainderRadius a.val ≤
      suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ := by
  apply (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy
    ⟨a.val, a.pos⟩).2
  rintro r ⟨u, hu, rfl⟩
  let v := ccmComplexSmoothInteriorSourceUnitPullback a u
  have hmass : 0 < suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩
      u.toCCMFormVector := by
    unfold suzukiWeilIntervalFormMass
    exact pow_pos (norm_pos_iff.mpr hu) 2
  have hmassEq : suzukiWeilIntervalFormMass ⟨a.val, a.pos⟩
      u.toCCMFormVector =
        a.val * suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture v := by
    rw [suzukiWeilIntervalFormMass_complexSmooth_eq,
      suzukiRestrictedWeilComplexIntervalEnergy_unitPullback]
  have henergy : 0 < suzukiRestrictedWeilComplexIntervalEnergy
      suzukiUnitAperture v := by
    rw [hmassEq] at hmass
    nlinarith [a.pos]
  have hscaled := suzukiPrimeFreeScaledRayleigh_mem_bounds a v henergy
  have hmu : suzukiLimitingLogGroundEnergy ≤
      suzukiLimitingLogForm v /
        suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture v :=
    isGLB_suzukiLimitingLogRayleighSet.1 ⟨v, henergy, rfl⟩
  rw [suzukiWeilIntervalFormRayleigh_eq_scaledUnitPullback a u henergy]
  linarith [hscaled.1]

theorem suzukiSmallAperture_intervalGroundEnergy_upper
    (a : SuzukiPrimeFreeSmallAperture) :
    suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ ≤
      suzukiSmallApertureSpectralShift a.val + suzukiLimitingLogGroundEnergy +
        suzukiSmallApertureRemainderRadius a.val := by
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  obtain ⟨r, hr, hrlt⟩ := Real.lt_sInf_add_pos
    suzukiLimitingLogRayleighSet_nonempty hepsilon
  obtain ⟨u, henergy, rfl⟩ := hr
  change suzukiLimitingLogForm u /
      suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u <
        suzukiLimitingLogGroundEnergy + epsilon at hrlt
  let U := ccmComplexSmoothInteriorSourceOfUnitRescale a u
  have hUne : suzukiWeilIntervalFormEmbedding ⟨a.val, a.pos⟩
      U.toCCMFormVector ≠ 0 :=
    suzukiWeilIntervalFormEmbedding_ofUnitRescale_ne_zero a u henergy
  have hfloor := (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy
    ⟨a.val, a.pos⟩).1 ⟨U, hUne, rfl⟩
  rw [suzukiWeilIntervalFormRayleigh_ofUnitRescale_eq a u henergy] at hfloor
  have hscaled := suzukiPrimeFreeScaledRayleigh_mem_bounds a u henergy
  calc
    suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ ≤
        suzukiPrimeFreeScaledForm a u /
          suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u := hfloor
    _ ≤ suzukiSmallApertureSpectralShift a.val +
          suzukiLimitingLogForm u /
            suzukiRestrictedWeilComplexIntervalEnergy suzukiUnitAperture u +
          suzukiSmallApertureRemainderRadius a.val := hscaled.2
    _ ≤ (suzukiSmallApertureSpectralShift a.val +
          suzukiLimitingLogGroundEnergy +
          suzukiSmallApertureRemainderRadius a.val) + epsilon := by
      exact le_of_lt (by linarith)

/-- Explicit two-sided `O(a)` estimate for the actual lowest eigenvalue. -/
theorem abs_suzukiSmallAperture_intervalGroundEnergy_sub_main_le
    (a : SuzukiPrimeFreeSmallAperture) :
    |suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ -
        (suzukiSmallApertureSpectralShift a.val +
          suzukiLimitingLogGroundEnergy)| ≤
      suzukiSmallApertureRemainderRadius a.val := by
  have hlower := suzukiSmallAperture_intervalGroundEnergy_lower a
  have hupper := suzukiSmallAperture_intervalGroundEnergy_upper a
  rw [abs_le]
  constructor <;> linarith

theorem suzukiSmallApertureSpectralShift_eq_paperConstant
    {a : ℝ} (_ha : 0 < a) :
    suzukiSmallApertureSpectralShift a =
      Real.log (1 / a) - Real.log (2 * Real.pi) +
        (Complex.digamma (2 : ℂ)).re - 1 := by
  unfold suzukiSmallApertureSpectralShift suzukiWeilArchimedeanConstant
  have hlog : Real.log (1 / a) = -Real.log a := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-- Suzuki 2026, Theorem 1.4: sharp main term and a uniform explicit `O(a)` remainder. -/
theorem abs_suzukiSmallAperture_intervalGroundEnergy_sub_paperMain_le
    (a : SuzukiPrimeFreeSmallAperture) :
    |suzukiWeilIntervalGroundEnergy ⟨a.val, a.pos⟩ -
        (Real.log (1 / a.val) + suzukiLimitingLogGroundEnergy -
          Real.log (2 * Real.pi) + (Complex.digamma (2 : ℂ)).re - 1)| ≤
      2 * suzukiOriginCurvatureUnitBound * a.val := by
  have hmain :
      Real.log (1 / a.val) + suzukiLimitingLogGroundEnergy -
          Real.log (2 * Real.pi) + (Complex.digamma (2 : ℂ)).re - 1 =
        suzukiSmallApertureSpectralShift a.val + suzukiLimitingLogGroundEnergy := by
    rw [suzukiSmallApertureSpectralShift_eq_paperConstant a.pos]
    ring
  rw [hmain]
  have h := abs_suzukiSmallAperture_intervalGroundEnergy_sub_main_le a
  simpa [suzukiSmallApertureRemainderRadius, mul_comm, mul_left_comm, mul_assoc] using h

/-- Quantified neighborhood form of the paper's `a → 0+` asymptotic. -/
theorem exists_suzukiSmallAperture_intervalGroundEnergy_paperAsymptotic :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : SuzukiPositiveAperture, a.1 < delta →
        |suzukiWeilIntervalGroundEnergy a -
            (Real.log (1 / a.1) + suzukiLimitingLogGroundEnergy -
              Real.log (2 * Real.pi) + (Complex.digamma (2 : ℂ)).re - 1)| ≤
          2 * suzukiOriginCurvatureUnitBound * a.1 := by
  let delta : ℝ := min (1 / 2 : ℝ) (Real.log 2 / 2)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by norm_num) (div_pos (Real.log_pos (by norm_num)) (by norm_num))
  refine ⟨delta, hdelta, fun a ha => ?_⟩
  have hahalf : a.1 < 1 / 2 := ha.trans_le (min_le_left _ _)
  have halog : a.1 < Real.log 2 / 2 := ha.trans_le (min_le_right _ _)
  let small : SuzukiPrimeFreeSmallAperture :=
    ⟨a.1, a.2, by nlinarith, by nlinarith⟩
  simpa only [small] using
    abs_suzukiSmallAperture_intervalGroundEnergy_sub_paperMain_le small

end RHTower
