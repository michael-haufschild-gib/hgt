import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: small-time source-scale collapse

In CGL's small-time branch the global source scale is already at least the
ambient conductor.  The residual conductor square therefore costs at most
`X²`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The residual ambient-conductor square in CGL's small-time `I₂` bound is
at most the global source-scale square. -/
theorem cglLemma62_smallTime_ambientSq_le_baseSq
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    (B.ambient.value : ℝ) ^ (2 : ℝ) ≤ S.base ^ (2 : ℝ) := by
  apply Real.rpow_le_rpow
  · positivity
  · exact S.ambient_le_base
  · norm_num

end

end RHTower
