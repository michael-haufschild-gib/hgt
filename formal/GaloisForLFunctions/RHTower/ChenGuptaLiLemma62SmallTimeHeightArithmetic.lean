import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: small-time height and window arithmetic
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The small-time Gamma-height factor and literal window length collapse to
the exact `X^(ε(2k+1/2)+ε/2)` source power. -/
theorem cglLemma62_smallTime_heightWindow_factor_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (1 + 2 * S.base ^ S.epsilon) ^
        (2 * (d.value : ℝ) + 1 / 2) *
      (2 * S.truncationRadius) ≤
      (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
        S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
          S.epsilon / 2) := by
  have hbase : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hbasepow : 1 ≤ S.base ^ S.epsilon :=
    Real.one_le_rpow S.base_one S.epsilon_pos.le
  have hexponent : 0 ≤ 2 * (d.value : ℝ) + 1 / 2 := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hheight : 1 + 2 * S.base ^ S.epsilon ≤ 3 * S.base ^ S.epsilon := by
    nlinarith
  have hheightPow : (1 + 2 * S.base ^ S.epsilon) ^
      (2 * (d.value : ℝ) + 1 / 2) ≤
      (3 * S.base ^ S.epsilon) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact hheight
    · exact hexponent
  have hwidth : 0 ≤ 2 * S.truncationRadius := by
    unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg hbase.le _)
  calc
    (1 + 2 * S.base ^ S.epsilon) ^
        (2 * (d.value : ℝ) + 1 / 2) *
        (2 * S.truncationRadius) ≤
        (3 * S.base ^ S.epsilon) ^ (2 * (d.value : ℝ) + 1 / 2) *
          (2 * S.truncationRadius) :=
      mul_le_mul_of_nonneg_right hheightPow hwidth
    _ = (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
        S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
          S.epsilon / 2) := by
      unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
      have hcombine : S.base ^ (S.epsilon *
          (2 * (d.value : ℝ) + 1 / 2)) * S.base ^ (S.epsilon / 2) =
          S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
            S.epsilon / 2) := by
        rw [← Real.rpow_add hbase]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le]
      calc
        3 ^ (2 * (d.value : ℝ) + 1 / 2) *
            S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2)) *
            (2 * S.base ^ (S.epsilon / 2)) =
            (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
              (S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2)) *
                S.base ^ (S.epsilon / 2)) := by ring
        _ = _ := by rw [hcombine]

end

end RHTower
