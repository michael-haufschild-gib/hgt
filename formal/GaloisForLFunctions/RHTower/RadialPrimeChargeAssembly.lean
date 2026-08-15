import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Assembling the radial prime charge from its diagonal and off-diagonal parts

The finite-aperture radial prime charge splits, after normalization by the first leakage scale, as

```text
diagonal  +  off-diagonal (j,k ≥ 2)  +  low first row  +  high first row .
```

The diagonal converges to the universal constant, and each of the three remaining pieces is
dominated by an explicit bound that vanishes.  This file is the last step of that chain: a
dominated error term vanishes, and a convergent head plus vanishing errors converges to the head's
limit.

The content of the law is entirely in the three domination bounds; what is recorded here is that
they combine, with no further hypothesis on the pieces themselves.
-/

open Filter

namespace GaloisForLFunctions.RHTower

/-- A term dominated by a vanishing bound vanishes. -/
theorem tendsto_zero_of_abs_le {ι : Type*} {l : Filter ι} {E B : ι → ℝ}
    (hle : ∀ x, |E x| ≤ B x) (hB : Tendsto B l (nhds 0)) :
    Tendsto E l (nhds 0) := by
  have hlow : ∀ x, -B x ≤ E x := fun x => neg_le_of_abs_le (hle x)
  have hup : ∀ x, E x ≤ B x := fun x => le_of_abs_le (hle x)
  have hnegB : Tendsto (fun x => -B x) l (nhds 0) := by simpa using hB.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hnegB hB hlow hup

/-- **The assembly of the radial prime charge.**  A convergent diagonal head plus three error
terms, each dominated by a vanishing bound, converges to the diagonal limit. -/
theorem tendsto_head_add_three_vanishing {ι : Type*} {l : Filter ι}
    {D E₁ E₂ E₃ B₁ B₂ B₃ : ι → ℝ} {L : ℝ}
    (hD : Tendsto D l (nhds L))
    (h₁ : ∀ x, |E₁ x| ≤ B₁ x) (hB₁ : Tendsto B₁ l (nhds 0))
    (h₂ : ∀ x, |E₂ x| ≤ B₂ x) (hB₂ : Tendsto B₂ l (nhds 0))
    (h₃ : ∀ x, |E₃ x| ≤ B₃ x) (hB₃ : Tendsto B₃ l (nhds 0)) :
    Tendsto (fun x => D x + (E₁ x + E₂ x + E₃ x)) l (nhds L) := by
  have hE₁ := tendsto_zero_of_abs_le h₁ hB₁
  have hE₂ := tendsto_zero_of_abs_le h₂ hB₂
  have hE₃ := tendsto_zero_of_abs_le h₃ hB₃
  have hsum : Tendsto (fun x => E₁ x + E₂ x + E₃ x) l (nhds 0) := by
    simpa using (hE₁.add hE₂).add hE₃
  simpa using hD.add hsum

end GaloisForLFunctions.RHTower
