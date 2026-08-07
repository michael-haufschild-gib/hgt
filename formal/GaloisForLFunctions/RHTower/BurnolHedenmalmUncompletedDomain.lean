import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain

/-!
# The uncompleted coordinate domain of the divided zeta vectors

On the critical line the first divided vector of a zeta zero is `x_ρ(s) = ζ(s)/(s-ρ)`.  If both
`x_ρ` and `s x_ρ` were square integrable on the line then so would be their combination
`(s-ρ)x_ρ = ζ`.  This module proves that implication, which is the algebraic step of the
uncompleted domain exclusion: the coordinate recurrence `M_s x_ρ = ρ x_ρ + ζ` transports square
integrability from the divided vector to the zeta source itself.

Together with the archimedean completion package it exhibits the exchange: the completed divided
vector does lie in the maximal domain of the real coordinate, and the defect there is the nonzero
completed source.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- The critical line as a map from the real parameter. -/
def criticalLinePoint (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * Complex.I

theorem criticalLinePoint_re (t : ℝ) : (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

/-- The first divided vector of a point `ρ`, read along the critical line. -/
def dividedZetaLine (ρ : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (criticalLinePoint t) / (criticalLinePoint t - ρ)

/-- **The uncompleted coordinate recurrence transports square integrability to the source.**

If the first divided vector of `ρ` and its coordinate multiple are both square integrable on the
critical line, then `ζ` itself is square integrable there.  This is the exact algebraic content of
the step `ζ(s) = s x_ρ(s) - ρ x_ρ(s)`. -/
theorem memLp_riemannZeta_criticalLine_of_dividedZetaLine
    {ρ : ℂ} (hρ : ∀ t : ℝ, criticalLinePoint t ≠ ρ)
    (h1 : MemLp (dividedZetaLine ρ) 2 volume)
    (h2 : MemLp (fun t : ℝ => criticalLinePoint t * dividedZetaLine ρ t) 2 volume) :
    MemLp (fun t : ℝ => riemannZeta (criticalLinePoint t)) 2 volume := by
  have hcomb : MemLp
      (fun t : ℝ => criticalLinePoint t * dividedZetaLine ρ t - ρ * dividedZetaLine ρ t)
      2 volume := h2.sub (h1.const_mul ρ)
  refine (memLp_congr_ae ?_).mp hcomb
  filter_upwards with t
  have hne : criticalLinePoint t - ρ ≠ 0 := sub_ne_zero.mpr (hρ t)
  rw [dividedZetaLine, ← sub_mul, mul_div_cancel₀ _ hne]

/-- **The exclusion in its contrapositive form.**  If `ζ` is not square integrable on the critical
line then no point of the line can carry a divided vector lying in the maximal domain of
coordinate multiplication inside `L²` of that line. -/
theorem not_memLp_coordinate_dividedZetaLine
    (hζ : ¬ MemLp (fun t : ℝ => riemannZeta (criticalLinePoint t)) 2 volume)
    {ρ : ℂ} (hρ : ∀ t : ℝ, criticalLinePoint t ≠ ρ)
    (h1 : MemLp (dividedZetaLine ρ) 2 volume) :
    ¬ MemLp (fun t : ℝ => criticalLinePoint t * dividedZetaLine ρ t) 2 volume := fun h2 =>
  hζ (memLp_riemannZeta_criticalLine_of_dividedZetaLine hρ h1 h2)

end RHTower
