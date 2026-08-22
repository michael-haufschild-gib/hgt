import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeSourceRegime

/-!
# Chen--Gupta--Li Lemma 6.2: closed small-time contour-depth selection

The small-time source exponent is `2 + ε - 2εk`, so this branch uses its
own explicit depth rather than importing the large-time choice.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The least natural depth sufficient for CGL's small-time displayed
`X⁻²⁰⁰` tail target. -/
noncomputable def CGLLemma62SmallTimeSourceRegime.decayDepth
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : CGLLemma62TailContourDepth where
  value := Nat.ceil ((202 + S.epsilon) / (2 * S.epsilon))
  positive := by
    apply Nat.ceil_pos.mpr
    exact div_pos (by linarith [S.epsilon_pos]) (by linarith [S.epsilon_pos])

/-- The certified small-time depth forces its exact source exponent below
`-200`, without a caller supplying a sufficient-depth premise. -/
theorem cglLemma62_smallTime_decayDepth_source_exponent_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    2 + S.epsilon - 2 * S.epsilon *
        (S.decayDepth.value : ℝ) ≤ -200 := by
  have hden : 0 < 2 * S.epsilon := by linarith [S.epsilon_pos]
  have hceil : (202 + S.epsilon) / (2 * S.epsilon) ≤
      (S.decayDepth.value : ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hden).mp hceil
  nlinarith [hmul]

end

end RHTower
