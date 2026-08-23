import GaloisForLFunctions.RHTower.CoshQuartetEnvelope

noncomputable section

open scoped BigOperators

namespace RHTower

/-- A positive real displacement lying strictly outside every real part in a finite packet. -/
def finiteQuartetEnvelopeDisplacement {J : Type} [Fintype J] (α : J → ℂ) : ℝ :=
  1 + ∑ j, |(α j).re|

theorem finiteQuartetEnvelopeDisplacement_pos {J : Type} [Fintype J] (α : J → ℂ) :
    0 < finiteQuartetEnvelopeDisplacement α := by
  unfold finiteQuartetEnvelopeDisplacement
  positivity

theorem abs_re_lt_finiteQuartetEnvelopeDisplacement {J : Type} [Fintype J]
    (α : J → ℂ) (j : J) :
    |(α j).re| < finiteQuartetEnvelopeDisplacement α := by
  have hle : |(α j).re| ≤ ∑ i, |(α i).re| :=
    Finset.single_le_sum (fun i _ => abs_nonneg ((α i).re)) (Finset.mem_univ j)
  unfold finiteQuartetEnvelopeDisplacement
  linarith

/-- The explicit finite displacement avoids every zero line of the cosh quartet envelope. -/
theorem coshQuartetEnvelope_ne_zero_finiteQuartetEnvelopeDisplacement
    {J : Type} [Fintype J] (α : J → ℂ) (j : J) :
    coshQuartetEnvelope (finiteQuartetEnvelopeDisplacement α) (α j) ≠ 0 := by
  let a : ℝ := finiteQuartetEnvelopeDisplacement α
  have ha : 0 < a := finiteQuartetEnvelopeDisplacement_pos α
  have hbound : |(α j).re| < a := abs_re_lt_finiteQuartetEnvelopeDisplacement α j
  have hsub : ((α j) - (a : ℂ)).re ≠ 0 := by
    change (α j).re - a ≠ 0
    intro h
    have hre : (α j).re = a := sub_eq_zero.mp h
    have habs : |(α j).re| = a := by rw [hre, abs_of_pos ha]
    linarith
  have hadd : ((α j) + (a : ℂ)).re ≠ 0 := by
    change (α j).re + a ≠ 0
    intro h
    have hre : (α j).re = -a := by linarith
    have habs : |(α j).re| = a := by rw [hre, abs_neg, abs_of_pos ha]
    linarith
  exact mul_ne_zero (cosh_ne_zero_of_re_ne_zero hsub) (cosh_ne_zero_of_re_ne_zero hadd)

end RHTower
