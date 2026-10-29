import GaloisForLFunctions.RHTower.Zeta23SimpleOffLineNearLine

/-!
# Seventy percent or a simple off-line core near the critical line

The multiplicity census gives `S + 2M ≤ (1 − HD(1) + ε)N`, while
`N = N₀ + S + M`. Failure of a critical-line proportion `θ` therefore forces at least
`(1 + HD(1) − 2θ − ε)N` simple off-line zeros. Removing the far mass `N/A` localizes
that core to displacement `A/log T`. For `θ = 7/10`, the coefficient is
`HD(1) − 2/5 − 1/A − ε`.
-/

open Filter Topology
open Zeta23

noncomputable section

namespace RHTower

/-- Every proposed critical-line proportion has an explicit simple off-line alternative. -/
theorem critical_proportion_or_simple_offLine (θ : ℝ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      θ * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (1 + Zeta23.ThmD.HD 1 - 2 * θ - ε) * (Ncount T (2 * T) : ℝ) ≤
          offLineSimpleCount zetaZeroConfig T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  by_cases hline : θ * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T)
  · exact Or.inl hline
  · right
    have hcount := hT₀ T hT
    have hpartition := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
    have hlt := lt_of_not_ge hline
    linarith only [hcount, hpartition, hlt]

/-- The simple off-line alternative lies near the line, with loss exactly `1/A`. -/
theorem critical_proportion_or_simple_offLine_near_line (θ A : ℝ) (hA : 0 < A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      θ * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (1 + Zeta23.ThmD.HD 1 - 2 * θ - 1 / A - ε) * (Ncount T (2 * T) : ℝ) ≤
          offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := critical_proportion_or_simple_offLine θ ε hε
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_offLineFarMass_le A hA)
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  rcases hT₀ T (le_of_max_le_left hT) with hline | hsimple
  · exact Or.inl hline
  · right
    have hfar := hT₁ T (le_of_max_le_right hT)
    have hsplit : (offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) ≤
        offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) +
          offLineFarMass zetaZeroConfig (A / Real.log T) T (2 * T) := by
      exact_mod_cast offLineSimpleCount_le_near_add_far zetaZeroConfig (A / Real.log T) T (2 * T)
    linarith only [hsimple, hfar, hsplit]

/-- Either seventy percent are critical, or the stated fraction is simple, off-line and near. -/
theorem seventy_percent_or_simple_offLine_near_line (A : ℝ) (hA : 0 < A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      7 / 10 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (Zeta23.ThmD.HD 1 - 2 / 5 - 1 / A - ε) * (Ncount T (2 * T) : ℝ) ≤
          offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) := by
  have hconstant : 1 + Zeta23.ThmD.HD 1 - 2 * (7 / 10 : ℝ) =
      Zeta23.ThmD.HD 1 - 2 / 5 := by ring
  simpa only [hconstant] using critical_proportion_or_simple_offLine_near_line (7 / 10) A hA

end RHTower

#print axioms RHTower.critical_proportion_or_simple_offLine
#print axioms RHTower.critical_proportion_or_simple_offLine_near_line
#print axioms RHTower.seventy_percent_or_simple_offLine_near_line
