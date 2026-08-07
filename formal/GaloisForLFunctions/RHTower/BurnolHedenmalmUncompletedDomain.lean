import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain
import GaloisForLFunctions.RHTower.ZetaCriticalLineNotSquareIntegrable

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
def criticalLineCoordinate (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * Complex.I

theorem criticalLineCoordinate_re (t : ℝ) : (criticalLineCoordinate t).re = 1 / 2 := by
  simp [criticalLineCoordinate]

/-- The first divided vector of a point `ρ`, read along the critical line. -/
def dividedZetaLine (ρ : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (criticalLineCoordinate t) / (criticalLineCoordinate t - ρ)

/-- **The uncompleted coordinate recurrence transports square integrability to the source.**

If the first divided vector of `ρ` and its coordinate multiple are both square integrable on the
critical line, then `ζ` itself is square integrable there.  This is the exact algebraic content of
the step `ζ(s) = s x_ρ(s) - ρ x_ρ(s)`. -/
theorem memLp_riemannZeta_criticalLine_of_dividedZetaLine
    {ρ : ℂ} (hρ : ∀ t : ℝ, criticalLineCoordinate t ≠ ρ)
    (h1 : MemLp (dividedZetaLine ρ) 2 volume)
    (h2 : MemLp (fun t : ℝ => criticalLineCoordinate t * dividedZetaLine ρ t) 2 volume) :
    MemLp (fun t : ℝ => riemannZeta (criticalLineCoordinate t)) 2 volume := by
  have hcomb : MemLp
      (fun t : ℝ => criticalLineCoordinate t * dividedZetaLine ρ t - ρ * dividedZetaLine ρ t)
      2 volume := h2.sub (h1.const_mul ρ)
  refine (memLp_congr_ae ?_).mp hcomb
  filter_upwards with t
  have hne : criticalLineCoordinate t - ρ ≠ 0 := sub_ne_zero.mpr (hρ t)
  rw [dividedZetaLine, ← sub_mul, mul_div_cancel₀ _ hne]

/-- **The exclusion in its contrapositive form.**  If `ζ` is not square integrable on the critical
line then no point of the line can carry a divided vector lying in the maximal domain of
coordinate multiplication inside `L²` of that line. -/
theorem not_memLp_coordinate_dividedZetaLine
    (hζ : ¬ MemLp (fun t : ℝ => riemannZeta (criticalLineCoordinate t)) 2 volume)
    {ρ : ℂ} (hρ : ∀ t : ℝ, criticalLineCoordinate t ≠ ρ)
    (h1 : MemLp (dividedZetaLine ρ) 2 volume) :
    ¬ MemLp (fun t : ℝ => criticalLineCoordinate t * dividedZetaLine ρ t) 2 volume := fun h2 =>
  hζ (memLp_riemannZeta_criticalLine_of_dividedZetaLine hρ h1 h2)


theorem criticalAbscissa_eq_criticalLineCoordinate (xi : ℝ) :
    criticalAbscissa xi = criticalLineCoordinate (2 * Real.pi * xi) := by
  rw [criticalAbscissa, criticalLineCoordinate]

/-- **Zeta is not square integrable on the critical line.** -/
theorem not_memLp_riemannZeta_criticalLine :
    ¬ MemLp (fun t : ℝ => riemannZeta (criticalLineCoordinate t)) 2 volume := by
  intro h
  apply not_memLp_riemannZeta_criticalAbscissa
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have hsq := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  have hcomp : Integrable
      (fun xi : ℝ => ‖riemannZeta (criticalLineCoordinate (2 * Real.pi * xi))‖ ^ 2) volume :=
    (integrable_comp_mul_left_iff
      (fun t : ℝ => ‖riemannZeta (criticalLineCoordinate t)‖ ^ 2) hc).mpr hsq
  have hmeas : AEStronglyMeasurable
      (fun xi : ℝ => riemannZeta (criticalAbscissa xi)) volume := by
    have hq := h.aestronglyMeasurable.comp_quasiMeasurePreserving
      (realMul_quasiMeasurePreserving (2 * Real.pi) hc)
    refine hq.congr ?_
    filter_upwards with xi
    rw [criticalAbscissa_eq_criticalLineCoordinate]
    rfl
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hcomp.congr ?_
  filter_upwards with xi
  rw [criticalAbscissa_eq_criticalLineCoordinate]

/-- **The uncompleted domain exclusion, unconditionally.**  No point of the critical line carries a
first divided vector lying in the maximal domain of coordinate multiplication inside `L²` of that
line: the coordinate recurrence would transport square integrability to `zeta` itself, and `zeta`
is not square integrable there. -/
theorem not_memLp_coordinate_dividedZetaLine_unconditional
    {ρ : ℂ} (hρ : ∀ t : ℝ, criticalLineCoordinate t ≠ ρ)
    (h1 : MemLp (dividedZetaLine ρ) 2 volume) :
    ¬ MemLp (fun t : ℝ => criticalLineCoordinate t * dividedZetaLine ρ t) 2 volume :=
  not_memLp_coordinate_dividedZetaLine not_memLp_riemannZeta_criticalLine hρ h1

end RHTower
