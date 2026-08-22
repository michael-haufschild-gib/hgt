import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: exact small-time length/cutoff cancellation
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's retained far-line length power cancels the `/N` in its literal
small-time cutoff `X^(2ε)q/N`. -/
theorem cglLemma62_smallTime_length_cutoffScale_negativePower_eq
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        S.cutoffScale ^ (-2 * (d.value : ℝ)) =
      (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
        (-2 * (d.value : ℝ)) := by
  have hbasePos : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hambientPos : 0 < (B.ambient.value : ℝ) := by
    exact_mod_cast B.ambient.positive
  have hlengthPos : 0 < (N.value : ℝ) := by
    exact_mod_cast N.positive
  have hcorePos : 0 < S.base ^ (2 * S.epsilon) *
      (B.ambient.value : ℝ) := by
    exact mul_pos (Real.rpow_pos_of_pos hbasePos _) hambientPos
  have hlengthPow : (N.value : ℝ) ^ (-2 * (d.value : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hlengthPos _).ne'
  unfold CGLLemma62SmallTimeSourceRegime.cutoffScale
  rw [Real.div_rpow hcorePos.le hlengthPos.le]
  field_simp [hlengthPow]

end

end RHTower
