import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: large-time cutoff arithmetic

This isolates the exact floor-cutoff loss in CGL's large-time `I₂` argument.
The loss is a fixed factor `2^(2k)` and is independent of the source scale.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Rounding CGL's cutoff down introduces at most the explicit factor
`2^(2k)` in the negative far-left tail power. -/
theorem cglLemma62_largeTime_tailCutoff_negativePower_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) ≤
      2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^ (-2 * (d.value : ℝ)) := by
  have hscalePos := cglLemma62_largeTime_cutoffScale_pos S
  have hhalf : S.cutoffScale / 2 ≤ (S.tailCutoff.value : ℝ) :=
    cglLemma62_largeTime_tailCutoff_half_scale_le S
  have hpow := Real.rpow_le_rpow_of_nonpos
    (div_pos hscalePos (by norm_num : (0 : ℝ) < 2)) hhalf
      (neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Nat.cast_nonneg d.value)))
  calc
    (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) ≤
        (S.cutoffScale / 2) ^ (-(2 * (d.value : ℝ))) := by
          convert hpow using 1 <;> ring
    _ = 2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^ (-2 * (d.value : ℝ)) := by
      rw [Real.div_rpow hscalePos.le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_neg hscalePos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_inv_eq_mul]
      have hneg : -2 * (d.value : ℝ) = -(2 * (d.value : ℝ)) := by ring
      rw [hneg]
      rw [Real.rpow_neg hscalePos.le]
      ring

end

end RHTower
