import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature

/-!
# The aperture restriction defect is not additive

The scalar curvature of the aperture cocycle is minus the coupling energy, and the coupling is
nonzero at an actual dilation scale.  So the curvature operator itself is nonzero there, and the
restriction defect fails to be additive along the flag.

The anomaly is therefore real, not a bookkeeping artefact: no reindexing of the flag can make the
defect additive.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **The aperture curvature is nonzero at an actual scale.** -/
theorem exists_scale_evenSoninApertureRestrictionCurvature_ne_zero
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenSoninApertureRestrictionCurvature a b c r hr ≠ 0 := by
  obtain ⟨r, hr, hcr, hneg⟩ :=
    exists_scale_re_opTrace_evenSoninApertureRestrictionCurvature_neg a b c ha hb hab hbc q
      haq hqb
  refine ⟨r, hr, hcr, ?_⟩
  intro hzero
  rw [hzero, opTrace_zero] at hneg
  simp at hneg

/-- **Non-additivity of the restriction defect.**  At that scale the defect of the outer step is
not the sum of the defects of the two inner steps. -/
theorem exists_scale_evenSoninApertureRestrictionDefect_ne_add
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenSoninApertureRestrictionDefect a c r hr ≠
        evenSoninApertureRestrictionDefect a b r hr +
          evenSoninApertureRestrictionDefect b c r hr := by
  obtain ⟨r, hr, hcr, hne⟩ :=
    exists_scale_evenSoninApertureRestrictionCurvature_ne_zero a b c ha hb hab hbc q haq hqb
  refine ⟨r, hr, hcr, ?_⟩
  intro hadd
  refine hne ?_
  unfold evenSoninApertureRestrictionCurvature
  rw [hadd]
  abel

end RHTower
