import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: exact large-time length/cutoff cancellation

The factor `N^(-2k)` in the shifted Mellin integral cancels the `/N` in
CGL's literal large-time cutoff.  This module records that identity exactly.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's retained far-line length power cancels the length in the real
large-time cutoff scale. -/
theorem cglLemma62_largeTime_length_cutoffScale_negativePower_eq
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        S.cutoffScale ^ (-2 * (d.value : ℝ)) =
      (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
        (-2 * (d.value : ℝ)) := by
  have hbasePos : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hambientPos : 0 < (B.ambient.value : ℝ) := by
    exact_mod_cast B.ambient.positive
  have hlengthPos : 0 < (N.value : ℝ) := by
    exact_mod_cast N.positive
  have hcorePos : 0 < S.base ^ (2 * S.epsilon) *
      (B.ambient.value : ℝ) * S.time := by
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hbasePos _) hambientPos) S.time_pos
  have hlengthPow : (N.value : ℝ) ^ (-2 * (d.value : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hlengthPos _).ne'
  unfold CGLLemma62LargeTimeSourceRegime.cutoffScale
  rw [Real.div_rpow hcorePos.le hlengthPos.le]
  field_simp [hlengthPow]

end

end RHTower
