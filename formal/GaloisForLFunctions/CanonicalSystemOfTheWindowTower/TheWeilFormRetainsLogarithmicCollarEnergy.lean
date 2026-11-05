import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicAndWeilFormDomainsAgree
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormDetectsIntervalLength

/-!
# The complete Weil form retains the logarithmic collar energy

The exact Weil form differs from the positive logarithmic form by one
bounded operator on physical L². Its full prime and polar terms therefore
change the energy of a narrow interval only by a fixed multiple of its mass.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The exact bounded correction from logarithmic energy to the Weil form. -/
def weilLogarithmicCorrection (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a - logarithmicDirichletAdjustment a

/-- Both complete forms differ by their literal bounded physical correction. -/
theorem ccmWeilForm_eq_logarithmic_add_correction (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a u v =
      logarithmicFullForm (ccmArchimedeanFormEmbedding a u) (ccmArchimedeanFormEmbedding a v) +
        inner ℂ (weilLogarithmicCorrection a (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a v) := by
  rw [logarithmicFullForm_ccm_embedding, logarithmicDirichletForm_eq_adjustment,
    ccmRestrictedWeilForm]
  simp only [weilLogarithmicCorrection, sub_apply, inner_sub_left]
  ring

/-- The mixed correction has its exact operator-norm bound in physical L². -/
theorem norm_ccmWeilForm_sub_logarithmic_le (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ‖ccmRestrictedWeilForm a u v -
      logarithmicFullForm (ccmArchimedeanFormEmbedding a u) (ccmArchimedeanFormEmbedding a v)‖ ≤
        ‖weilLogarithmicCorrection a‖ * ‖ccmArchimedeanFormToAperture a u‖ *
          ‖ccmArchimedeanFormToAperture a v‖ := by
  rw [ccmWeilForm_eq_logarithmic_add_correction, add_sub_cancel_left]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right ((weilLogarithmicCorrection a).le_opNorm _)
      (norm_nonneg _))

/-- The diagonal correction costs at most its operator norm times the source mass. -/
theorem abs_ccmWeilForm_re_sub_logarithmic_le (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    |(ccmRestrictedWeilForm a u u).re -
      (logarithmicFullForm (ccmArchimedeanFormEmbedding a u) (ccmArchimedeanFormEmbedding a u)).re| ≤
        ‖weilLogarithmicCorrection a‖ * ‖ccmArchimedeanFormToAperture a u‖^2 := by
  have hr := (Complex.abs_re_le_norm (ccmRestrictedWeilForm a u u -
    logarithmicFullForm (ccmArchimedeanFormEmbedding a u) (ccmArchimedeanFormEmbedding a u))).trans
      (norm_ccmWeilForm_sub_logarithmic_le a u u)
  simpa only [Complex.sub_re, pow_two, mul_assoc] using hr

/-- The actual complete Weil form retains the sharp leading logarithmic interval floor. -/
theorem ccmWeilForm_ge_log_inverse_width (a : SuzukiPositiveAperture)
    {lo h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : CCMArchimedeanFormDomain a)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc lo (lo+h) → ccmArchimedeanFormEmbedding a u x = 0) :
    (Real.log (1/h)-‖weilLogarithmicCorrection a‖) *
      ‖ccmArchimedeanFormToAperture a u‖^2 ≤ (ccmRestrictedWeilForm a u u).re := by
  have hl := logarithmicFullForm_ge_log_inverse_width hh hh1
    (ccmArchimedeanFormEmbedding a u) (hasLogarithmicEnergy_ccm_form a u) hs
  have hb := (abs_le.mp (abs_ccmWeilForm_re_sub_logarithmic_le a u)).1
  change Real.log (1/h)*‖ccmArchimedeanFormToAperture a u‖^2 ≤ _ at hl
  nlinarith only [hl, hb]

/-- A constant interval source lies in every enclosing physical aperture. -/
theorem logarithmicIntervalSource_mem_aperture (a : SuzukiPositiveAperture)
    {lo hi : ℝ} (hs : Ioc lo hi ⊆ centralInterval a.1) :
    logarithmicIntervalSource lo hi ∈ centralPhysicalForbidden a.1 := by
  rw [centralPhysicalForbidden, mem_physicalForbidden_iff]
  filter_upwards [logarithmicIntervalSource_coeFn lo hi] with x hx hout
  rw [hx]
  exact indicator_of_notMem (fun h => hout (hs h)) _

/-- Literal constant collar profiles are admitted in the complete Weil form domain. -/
theorem exists_ccm_form_of_intervalSource (a : SuzukiPositiveAperture) (lo : ℝ)
    {h : ℝ} (hh : 0 ≤ h) (hs : Ioc lo (lo+h) ⊆ centralInterval a.1) :
    ∃ u : CCMArchimedeanFormDomain a,
      ccmArchimedeanFormEmbedding a u = logarithmicIntervalSource lo (lo+h) := by
  let f : suzukiApertureHilbert a :=
    ⟨logarithmicIntervalSource lo (lo+h), logarithmicIntervalSource_mem_aperture a hs⟩
  obtain ⟨u, hu⟩ := exists_ccm_form_of_logarithmicEnergy a f
    (hasLogarithmicEnergy_logarithmicIntervalSource_at lo hh)
  exact ⟨u, congrArg (fun v : suzukiApertureHilbert a => (v : SoninL2)) hu⟩

/-- Every literal constant collar test has the matching leading full Weil energy bound. -/
theorem ccmWeilForm_intervalSource_upper (a : SuzukiPositiveAperture) (lo : ℝ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : CCMArchimedeanFormDomain a)
    (hu : ccmArchimedeanFormEmbedding a u = logarithmicIntervalSource lo (lo+h)) :
    (ccmRestrictedWeilForm a u u).re ≤ h*(Real.log (1/h)+3+‖weilLogarithmicCorrection a‖) := by
  have hn : ‖ccmArchimedeanFormToAperture a u‖^2 = h := by
    change ‖ccmArchimedeanFormEmbedding a u‖^2 = h
    rw [hu, norm_logarithmicIntervalSource_sq (by linarith only [hh]), add_sub_cancel_left]
  have hq := logarithmicFullForm_intervalSource_upper_at lo hh hh1
  have hb := (abs_le.mp (abs_ccmWeilForm_re_sub_logarithmic_le a u)).2
  rw [hu, hn] at hb
  nlinarith only [hq, hb]

#print axioms exists_ccm_form_of_intervalSource
#print axioms ccmWeilForm_intervalSource_upper
#print axioms ccmWeilForm_eq_logarithmic_add_correction
#print axioms norm_ccmWeilForm_sub_logarithmic_le
#print axioms ccmWeilForm_ge_log_inverse_width
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
