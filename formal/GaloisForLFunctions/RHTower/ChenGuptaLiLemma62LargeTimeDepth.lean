import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: closed large-time contour-depth selection

CGL leaves the depth `k` to be chosen sufficiently large in terms of
`ε`.  This module makes that choice explicit and proves its required source
exponent inequality without taking a numerical premise.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The least natural depth sufficient for CGL's displayed `X^-200` target
after the large-time source-factor calculation. -/
noncomputable def CGLLemma62LargeTimeSourceRegime.decayDepth
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : CGLLemma62TailContourDepth where
  value := Nat.ceil ((202 + S.epsilon / 2) / (4 * S.epsilon))
  positive := by
    apply Nat.ceil_pos.mpr
    have hnum : 0 < 202 + S.epsilon / 2 := by linarith [S.epsilon_pos]
    have hden : 0 < 4 * S.epsilon := by linarith [S.epsilon_pos]
    exact div_pos hnum hden

/-- The selected contour depth makes CGL's final source exponent at most
`-200`. -/
theorem cglLemma62_largeTime_decayDepth_source_exponent_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    2 + S.epsilon / 2 - 4 * S.epsilon *
        (S.decayDepth.value : ℝ) ≤ -200 := by
  have hden : 0 < 4 * S.epsilon := by linarith [S.epsilon_pos]
  have hceil : (202 + S.epsilon / 2) / (4 * S.epsilon) ≤
      (S.decayDepth.value : ℝ) := by
    exact Nat.le_ceil _
  have hmul := (div_le_iff₀ hden).mp hceil
  nlinarith [hmul]

end

end RHTower
