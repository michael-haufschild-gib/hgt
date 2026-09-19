import Zeta23.ThmD.Mult
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Montgomery--Taylor density bounds in the native Xi census

The pinned Zeta23 dependency already proves the unconditional multiplicity-
aware Theorem-D bounds used by Lamzouri.  This module avoids duplicating those
proofs and instead transports their simple-critical and distinct counts to the
project's completed-Xi finite census.
-/

namespace RHTower

noncomputable section

/-- Distinct completed-Xi zeros with ordinate in `(0,T]`. -/
def xiPosDistinctZeroCount (T : ℝ) : ℕ :=
  (stripFinsetPos T).card

/-- Zeta23's cumulative distinct count is the native completed-Xi support
cardinality. -/
theorem zeta23_Ndist_zero_eq_xiPosDistinctZeroCount (T : ℝ) :
    Zeta23.Ndist 0 T = xiPosDistinctZeroCount T := by
  classical
  unfold Zeta23.Ndist xiPosDistinctZeroCount
  rw [Set.ncard_eq_toFinset_card _ (Zeta23.zerosIn_finite 0 T)]
  exact congrArg Finset.card (zeta23_zerosIn_zero_toFinset_eq_stripFinsetPos T)

/-- The unconditional Montgomery--Taylor 67.25% simple-critical bound,
transported to the project's Xi census. -/
theorem lamzouri_montgomeryTaylor_simpleCritical_epsilon :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) * (xiPosZeroCount T : ℝ) ≤
        xiSimpleCriticalZeroCount T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_simple_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [zeta23_Ncount_zero_eq_xiPosZeroCount,
    zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ T hT

/-- The unconditional Montgomery--Taylor 83.62% distinct-zero bound,
transported to the project's Xi census. -/
theorem lamzouri_montgomeryTaylor_distinct_epsilon :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.GD 1 - ε) * (xiPosZeroCount T : ℝ) ≤
        xiPosDistinctZeroCount T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_dist_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [zeta23_Ncount_zero_eq_xiPosZeroCount,
    zeta23_Ndist_zero_eq_xiPosDistinctZeroCount] using hT₀ T hT

end

end RHTower
