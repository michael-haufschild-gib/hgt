import GaloisForLFunctions.RHTower.NymanBeurlingCriterion
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Bridging to mathlib's zeta zero set

Mathlib carries the zero set of `riemannZeta` as `riemannZetaZeros`, with its closedness, discreteness, and the
finiteness of its intersection with any compact set.  The corpus states its zero facts through the `Ξ` divisor
instead, so the two vocabularies never met.  This file connects them at the one point that matters for the
Nyman--Beurling lane.

* `exists_mem_riemannZetaZeros_of_not_riemannHypothesis` — failure of the Riemann hypothesis produces a member
  of `riemannZetaZeros` in the right half of the critical strip;
* `riemannHypothesis_of_forall_mem_riemannZetaZeros` — conversely, if every zero in the strip has real part at
  most `½`, the Riemann hypothesis holds.

With these, statements proved here can be quoted against mathlib's zero-set API, and mathlib's discreteness and
compact-finiteness lemmas apply to the zeros this development produces.
-/

open Complex

noncomputable section

namespace RHTower

/-- Failure of the Riemann hypothesis produces a zero in mathlib's zero set, inside the right half of the
critical strip. -/
theorem exists_mem_riemannZetaZeros_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ ρ ∈ riemannZetaZeros, 1 / 2 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  refine ⟨ρ, ?_, hρ, hρ1⟩
  rw [mem_riemannZetaZeros]
  exact hzero

/-- Conversely: if no member of mathlib's zero set has real part beyond `½` inside the strip, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_forall_mem_riemannZetaZeros
    (h : ∀ ρ ∈ riemannZetaZeros, ρ.re < 1 → ρ.re ≤ 1 / 2) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hmem, hρ, hρ1⟩ := exists_mem_riemannZetaZeros_of_not_riemannHypothesis hRH
  exact absurd (h ρ hmem hρ1) (not_le.mpr hρ)

end RHTower

end
