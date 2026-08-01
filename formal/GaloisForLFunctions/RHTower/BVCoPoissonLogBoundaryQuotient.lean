import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Collapse of the logarithmic co-Poisson multiplier quotient

The logarithmic boundary space `ℂ e₀ ⊕ ℓ²(ℤ)` is represented isometrically as
`ℓ²(Option ℤ, ℂ)`, with `none` indexing `e₀` and `some j` indexing `eⱼ`.  The exact ideal
vectors exposed by the critical eta seed are `e₀ + eⱼ`.

Their closed complex span is the whole boundary space.  Consequently the ordinary Hilbert quotient
by the completed multiplier ideal is zero, so this topology cannot retain the Route G normal class.
-/

open Complex Set
open scoped ComplexInnerProductSpace lp

namespace RHTower

noncomputable section

/-- `ℂ e₀ ⊕ ℓ²(ℤ)` with the direct-sum Hilbert norm. -/
abbrev LogBoundarySpace := ℓ²(Option ℤ, ℂ)

/-- Boundary class `[uⱼ] = e₀ + eⱼ` of a dyadic multiplier-ideal generator. -/
def logIdealVector (j : ℤ) : LogBoundarySpace :=
  lp.single 2 none 1 + lp.single 2 (some j) 1

def logIdealSpan : Submodule ℂ LogBoundarySpace :=
  Submodule.span ℂ (Set.range logIdealVector)

theorem logIdealSpan_topologicalClosure_eq_top :
    logIdealSpan.topologicalClosure = ⊤ := by
  have hperp : Submodule.orthogonal (𝕜 := ℂ) logIdealSpan.topologicalClosure = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hcoord (j : ℤ) : z (some j) = -z none := by
      have hv : logIdealVector j ∈ logIdealSpan.topologicalClosure :=
        logIdealSpan.le_topologicalClosure (Submodule.subset_span (Set.mem_range_self j))
      have hi := Submodule.inner_right_of_mem_orthogonal hv hz
      rw [logIdealVector, inner_add_left, lp.inner_single_left, lp.inner_single_left] at hi
      have hi' : z none + z (some j) = 0 := by simpa using hi
      exact eq_neg_of_add_eq_zero_right hi'
    have ha : z none = 0 := by
      by_contra hane
      have hs : Summable (fun _ : ℤ => ‖z none‖ ^ (2 : ℝ)) := by
        have hx := ((lp.memℓp z).summable (by norm_num)).comp_injective
          (Option.some_injective ℤ)
        change Summable (fun j : ℤ => ‖z (some j)‖ ^ (2 : ℝ)) at hx
        simpa only [hcoord, norm_neg] using hx
      have hpos : 0 < ‖z none‖ ^ (2 : ℝ) := by positivity
      exact Set.infinite_univ (Set.Finite.of_summable_const hpos hs)
    apply Subtype.ext
    funext i
    cases i with
    | none => exact ha
    | some j => simpa [ha] using hcoord j
  exact Submodule.orthogonal_eq_bot_iff.mp hperp

theorem logIdealSpan_dense : Dense (logIdealSpan : Set LogBoundarySpace) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr logIdealSpan_topologicalClosure_eq_top

end
end RHTower
