import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: large-time height and window arithmetic

This converts CGL's literal local height and truncation radius into the
single source height factor used by the `I₂` estimate.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The large-time Gamma-height factor and the window length are bounded by
their literal `4T₀` and `2T₀` source envelopes. -/
theorem cglLemma62_largeTime_heightWindow_factor_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (1 + |t| + S.truncationWindow.radius) ^
        (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius) ≤
      (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time) := by
  have hheight : 1 + |t| + S.truncationWindow.radius ≤ 4 * S.time := by
    simpa [CGLLemma62LargeTimeSourceRegime.truncationWindow] using
      cglLemma62_largeTime_height_envelope S
  have hradius : S.truncationWindow.radius ≤ S.time := by
    simpa [CGLLemma62LargeTimeSourceRegime.truncationWindow] using
      cglLemma62_largeTime_truncationRadius_le_time S
  have hexponent : 0 ≤ 2 * (d.value : ℝ) + 1 / 2 := by
    have hdnonneg : 0 ≤ (d.value : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hpower : (1 + |t| + S.truncationWindow.radius) ^
      (2 * (d.value : ℝ) + 1 / 2) ≤
      (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    apply Real.rpow_le_rpow
    · nlinarith [abs_nonneg t, S.truncationWindow.radius_nonneg]
    · exact hheight
    · exact hexponent
  have hwidth : 2 * S.truncationWindow.radius ≤ 2 * S.time := by
    gcongr
  calc
    (1 + |t| + S.truncationWindow.radius) ^
        (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius) ≤
        (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) *
          (2 * S.truncationWindow.radius) :=
      mul_le_mul_of_nonneg_right hpower
        (mul_nonneg (by norm_num) S.truncationWindow.radius_nonneg)
    _ ≤ (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time) :=
      mul_le_mul_of_nonneg_left hwidth
        (Real.rpow_nonneg (by nlinarith [S.time_pos]) _)

end

end RHTower
