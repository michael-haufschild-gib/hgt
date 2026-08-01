import GaloisForLFunctions.RHTower.SoninApertureDefectSupport
import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature

/-!
# The aperture defect does not descend to the smaller carrier

The diagonal aperture defect is the compression of a dilation sandwich by the projection at the
larger aperture, so the successive-layer coupling vanishes exactly when one explicit product of
projections and dilations vanishes.  That product is an equality between two operators built only
from the tower, with nothing analytic left in it.

It is not zero.  The cofinal nonannihilation of the coupling gives an actual dilation scale at
which the product is nonzero, so the defect — a positive operator always carried by the aperture-`b`
Sonin space — genuinely fails to be carried by the smaller aperture-`c` space.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The diagonal aperture defect as an explicit compression of the dilation sandwich. -/
theorem evenSoninApertureRestrictionDefect_eq_compression
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenSoninApertureRestrictionDefect a b r hr =
      evenCentralSoninProjection b * evenDilationSum r hr *
        evenSoninApertureLayer a b * evenDilationSum r hr *
          evenCentralSoninProjection b :=
  evenCentralSoninQuadraticCorner_restrictionDefect hab hr hr

/-- **The carrier equation.**  The successive-layer coupling vanishes exactly when the explicit
projection–dilation product does.  Both sides are built only from Sonin projections and the
dilation sum. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_tripleProduct
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      evenCentralSoninProjection b * evenDilationSum r hr *
          evenSoninApertureLayer a b * evenDilationSum r hr *
            evenSoninApertureLayer b c = 0 := by
  have hQ : evenCentralSoninProjection b * (1 - evenCentralSoninProjection c) =
      evenSoninApertureLayer b c := by
    rw [evenSoninApertureLayer, mul_sub, mul_one, (evenCentralSoninProjection_mul_of_le hbc).2]
  have hsplit : evenSoninApertureRestrictionDefect a b r hr *
      (1 - evenCentralSoninProjection c) =
      evenCentralSoninProjection b * evenDilationSum r hr *
        evenSoninApertureLayer a b * evenDilationSum r hr *
          evenSoninApertureLayer b c := by
    rw [evenSoninApertureRestrictionDefect_eq_compression hab hr, mul_assoc, hQ]
  rw [evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_outer hab hbc hr,
    ← hsplit, mul_sub, mul_one, sub_eq_zero]
  exact eq_comm

/-- **The carrier equation fails.**  At an actual dilation scale the explicit product is nonzero. -/
theorem exists_scale_soninApertureTripleProduct_ne_zero
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenCentralSoninProjection b * evenDilationSum r hr *
          evenSoninApertureLayer a b * evenDilationSum r hr *
            evenSoninApertureLayer b c ≠ 0 := by
  obtain ⟨r, hr, hcr, hne⟩ := exists_scale_soninApertureCoupling_ne_zero a b c ha hb hab hbc q
    haq hqb
  refine ⟨r, hr, hcr, ?_⟩
  intro hzero
  exact hne
    ((evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_tripleProduct hab.le hbc.le hr).mpr
      hzero)

/-- **The defect escapes the smaller carrier.**  The aperture defect is always carried by the
aperture-`b` Sonin space, and at an actual dilation scale it is not carried by the aperture-`c`
space. -/
theorem exists_scale_evenSoninApertureRestrictionDefect_mul_outer_ne
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ∃ (r : ℝ) (hr : 1 < r), c < r * a ∧
      evenSoninApertureRestrictionDefect a b r hr * evenCentralSoninProjection b =
          evenSoninApertureRestrictionDefect a b r hr ∧
        evenSoninApertureRestrictionDefect a b r hr * evenCentralSoninProjection c ≠
          evenSoninApertureRestrictionDefect a b r hr := by
  obtain ⟨r, hr, hcr, hne⟩ := exists_scale_soninApertureCoupling_ne_zero a b c ha hb hab hbc q
    haq hqb
  refine ⟨r, hr, hcr,
    evenSoninApertureRestrictionDefect_mul_evenCentralSoninProjection hab.le hr, ?_⟩
  intro hcarrier
  exact hne
    ((evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_outer hab.le hbc.le hr).mpr
      hcarrier)

end RHTower
