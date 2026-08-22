import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeReflectedReassembly
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62NonprincipalReassembly

/-!
# Chen--Gupta--Li Lemma 6.2: large-time nonprincipal reassembly

The nonprincipal physical Mellin identity is independent of the source time
regime.  Combining it with the large-time reflected-window theorem gives the
complete normalized nonprincipal source branch at CGL's literal window.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's normalized nonprincipal physical side differs from the sum of its
literal large-time critical finite and far-left tail windows by a closed
`X⁻²⁰⁰` error. -/
theorem cglLemma62_nonprincipal_largeTime_window_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(2 * Real.pi : ℝ) •
          (cglMellinPhase t N.value *
            cglLemma62SmoothedCharacterSum w N B.ambient B.character t) -
          ((∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  rw [cglLemma62_nonprincipal_smoothedCharacterSum_eq_reflected w N B t]
  exact cglLemma62_largeTime_reflected_truncation_error_X200_bound S w

end

end RHTower
