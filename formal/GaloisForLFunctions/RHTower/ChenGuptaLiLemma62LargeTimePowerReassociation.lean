import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeScaleCollapse

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Exact real-power re-association of CGL's surviving large-time source
factors after the length/cutoff and conductor reductions. -/
theorem cglLemma62_largeTime_sourcePower_reassociation
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
        (-2 * (d.value : ℝ)) *
      (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) *
      (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time) =
      (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
        S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (3 / 2 : ℝ) := by
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
  have htimepow : S.time ^ (-2 * (d.value : ℝ)) *
      S.time ^ (2 * (d.value : ℝ) + 1 / 2) * S.time =
        S.time ^ (3 / 2 : ℝ) := by
    calc
      _ = (S.time ^ (-2 * (d.value : ℝ)) *
          S.time ^ (2 * (d.value : ℝ) + 1 / 2)) * S.time ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = S.time ^ (-2 * (d.value : ℝ) +
          (2 * (d.value : ℝ) + 1 / 2)) * S.time ^ (1 : ℝ) := by
            rw [← Real.rpow_add S.time_pos]
      _ = _ := by
        rw [← Real.rpow_add S.time_pos]
        congr 1
        ring
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hbase.le _) hq.le) S.time_pos.le,
    Real.mul_rpow (Real.rpow_nonneg hbase.le _) hq.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) S.time_pos.le, hX]
  calc
    S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (-2 * (d.value : ℝ)) * S.time ^ (-2 * (d.value : ℝ)) *
        (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) *
        (4 ^ (2 * (d.value : ℝ) + 1 / 2) * S.time ^ (2 * (d.value : ℝ) + 1 / 2)) *
          (2 * S.time) =
        (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
          S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
          ((B.ambient.value : ℝ) ^ (-2 * (d.value : ℝ)) *
            (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2)) *
            (S.time ^ (-2 * (d.value : ℝ)) *
              S.time ^ (2 * (d.value : ℝ) + 1 / 2) * S.time) := by ring
    _ = _ := by rw [hqpow, htimepow]

end

end RHTower
