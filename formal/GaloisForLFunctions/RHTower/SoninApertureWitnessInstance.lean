import GaloisForLFunctions.RHTower.SoninCountertermCoboundaryNoGo
import GaloisForLFunctions.RHTower.SoninCompressedDilationOffDiagonal
import GaloisForLFunctions.RHTower.SoninApertureDefectNonadditive
import GaloisForLFunctions.RHTower.SoninDefectCarrierEscape
import GaloisForLFunctions.RHTower.SoninCompletionUnboundedRequirement

/-!
# A worked instance of the aperture flag

Everything in the aperture nonannihilation chain is stated for a strict flag `0 < a < q < b < c`.
This module fixes the numerical flag `1 < 3/2 < 2 < 3` and records the consequences at it, so the
whole chain is visibly about an inhabited hypothesis class rather than an empty one.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The coupling is nonzero on the flag `1 < 2 < 3`. -/
theorem soninApertureCoupling_ne_zero_instance :
    ∃ (r : ℝ) (hr : 1 < r), (3 : ℝ) < r * 1 ∧
      evenSoninApertureSuccessiveLayerTransition 1 2 3 r hr ≠ 0 :=
  exists_scale_soninApertureCoupling_ne_zero 1 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (3 / 2) (by norm_num) (by norm_num)

/-- The aperture curvature is strictly negative on that flag. -/
theorem re_opTrace_evenSoninApertureRestrictionCurvature_neg_instance :
    ∃ (r : ℝ) (hr : 1 < r), (3 : ℝ) < r * 1 ∧
      (opTrace (evenSoninApertureRestrictionCurvature 1 2 3 r hr)).re < 0 :=
  exists_scale_re_opTrace_evenSoninApertureRestrictionCurvature_neg 1 2 3 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (3 / 2) (by norm_num) (by norm_num)

/-- The restriction defect is not additive on that flag. -/
theorem evenSoninApertureRestrictionDefect_ne_add_instance :
    ∃ (r : ℝ) (hr : 1 < r), (3 : ℝ) < r * 1 ∧
      evenSoninApertureRestrictionDefect 1 3 r hr ≠
        evenSoninApertureRestrictionDefect 1 2 r hr +
          evenSoninApertureRestrictionDefect 2 3 r hr :=
  exists_scale_evenSoninApertureRestrictionDefect_ne_add 1 2 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (3 / 2) (by norm_num) (by norm_num)

/-- The packet channel has no lower floor on that flag, even after any coboundary counterterm. -/
theorem not_exists_lower_bound_instance (f : ℝ → ℝ) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s 1 2 3 (soninCrossingClock 1 3)
            (one_lt_soninCrossingClock 1 3) (fun _ => 1))).re +
          ((f 3 - f 1) - (f 2 - f 1) - (f 3 - f 2)) :=
  not_exists_lower_bound_soninAperturePacketCurvature_add_coboundary 1 2 3 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (3 / 2) (by norm_num) (by norm_num) f

/-- The explicit carrier equation fails on that flag. -/
theorem soninApertureTripleProduct_ne_zero_instance :
    ∃ (r : ℝ) (hr : 1 < r), (3 : ℝ) < r * 1 ∧
      evenCentralSoninProjection 2 * evenDilationSum r hr *
          evenSoninApertureLayer 1 2 * evenDilationSum r hr *
            evenSoninApertureLayer 2 3 ≠ 0 :=
  exists_scale_soninApertureTripleProduct_ne_zero 1 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (3 / 2) (by norm_num) (by norm_num)

/-- On that flag the defect lives on the aperture-`2` carrier and not on the aperture-`3` one. -/
theorem evenSoninApertureRestrictionDefect_mul_outer_ne_instance :
    ∃ (r : ℝ) (hr : 1 < r), (3 : ℝ) < r * 1 ∧
      evenSoninApertureRestrictionDefect 1 2 r hr * evenCentralSoninProjection 2 =
          evenSoninApertureRestrictionDefect 1 2 r hr ∧
        evenSoninApertureRestrictionDefect 1 2 r hr * evenCentralSoninProjection 3 ≠
          evenSoninApertureRestrictionDefect 1 2 r hr :=
  exists_scale_evenSoninApertureRestrictionDefect_mul_outer_ne 1 2 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (3 / 2) (by norm_num) (by norm_num)

/-- On that flag no counterterm bounded above on the packet family restores a lower floor. -/
theorem not_exists_lower_bound_bounded_instance (C : Finset ℕ → ℝ) (M₀ : ℝ)
    (hC : ∀ s, C s ≤ M₀) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s 1 2 3 (soninCrossingClock 1 3)
            (one_lt_soninCrossingClock 1 3) (fun _ => 1))).re + C s :=
  not_exists_lower_bound_soninAperturePacketCurvature_add_bounded 1 2 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (3 / 2) (by norm_num) (by norm_num) C M₀ hC

end RHTower
