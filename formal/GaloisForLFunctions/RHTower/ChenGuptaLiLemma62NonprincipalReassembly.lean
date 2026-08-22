import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62InitialMellin
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedReassembly

/-!
# Chen--Gupta--Li Lemma 6.2: nonprincipal physical-side reassembly

This closes the source's nonprincipal route from the physical smoothed
character sum through the initial Mellin integral to the reflected finite and
complementary windows.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- In CGL's nonprincipal case, the normalized physical character sum is
exactly the reflected line integral. -/
theorem cglLemma62_nonprincipal_smoothedCharacterSum_eq_reflected
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    (2 * Real.pi : ℝ) •
      (cglMellinPhase t N.value *
        cglLemma62SmoothedCharacterSum w N B.ambient B.character t) =
      ∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v := by
  have hshift :
      (∫ v : ℝ, cglLemma62ContourIntegrand w N B t ((2 : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [VerticalIntegral, smul_eq_mul] using
      cglLemma62_nonprincipal_initialVerticalIntegral_eq_reflected w N B t
  calc
    (2 * Real.pi : ℝ) •
        (cglMellinPhase t N.value *
          cglLemma62SmoothedCharacterSum w N B.ambient B.character t) =
      ∫ v : ℝ, cglInitialLFunctionIntegrand w N B.ambient B.character t v :=
        cglLemma62_smoothedCharacterSum_initialMellin_lfunction w N B.ambient B.character t
    _ = ∫ v : ℝ, cglLemma62ContourIntegrand w N B t ((2 : ℂ) + (v : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with v
      rfl
    _ = _ := hshift

/-- CGL's nonprincipal physical side differs from the sum of its literal
small-time critical finite and far-left tail windows by a closed `X⁻²⁰⁰`
error. -/
theorem cglLemma62_nonprincipal_smallTime_window_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(2 * Real.pi : ℝ) •
          (cglMellinPhase t N.value *
            cglLemma62SmoothedCharacterSum w N B.ambient B.character t) -
          ((∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  rw [cglLemma62_nonprincipal_smoothedCharacterSum_eq_reflected w N B t]
  exact cglLemma62_smallTime_reflected_truncation_error_X200_bound S w

end

end RHTower
