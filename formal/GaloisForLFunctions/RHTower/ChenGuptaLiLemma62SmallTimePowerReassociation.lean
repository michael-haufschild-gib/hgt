import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeHeightArithmetic

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Exact real-power re-association of CGL's surviving small-time source
factors after the length/cutoff and conductor reductions. -/
theorem cglLemma62_smallTime_sourcePower_reassociation
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
        (-2 * (d.value : ℝ)) *
      (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) *
      S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
        S.epsilon / 2) =
      S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (2 : ℝ) := by
  have hbase : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hq : 0 < (B.ambient.value : ℝ) := by exact_mod_cast B.ambient.positive
  have hX : (S.base ^ (2 * S.epsilon)) ^ (-2 * (d.value : ℝ)) =
      S.base ^ (-4 * S.epsilon * (d.value : ℝ)) := by
    rw [← Real.rpow_mul hbase.le]
    congr 1
    ring
  have hqpow : (B.ambient.value : ℝ) ^ (-2 * (d.value : ℝ)) *
      (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) =
        (B.ambient.value : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hbasepow : S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
      S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
        S.epsilon / 2) =
        S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  rw [Real.mul_rpow (Real.rpow_nonneg hbase.le _) hq.le, hX]
  calc
    S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) *
        S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
          S.epsilon / 2) =
        (S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
          S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
            S.epsilon / 2)) *
          ((B.ambient.value : ℝ) ^ (-2 * (d.value : ℝ)) *
            (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2)) := by ring
    _ = _ := by rw [hbasepow, hqpow]

end

end RHTower
