import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Uniform effectivity of the period-incidence representation

Every nonzero period mode is algebraically invertible, but a continuous inverse over the complete
period family exists exactly when the embedded period group is discrete.  This is the exact
local-to-global attainment boundary needed by the physical-character completion problem.
-/

open Set
open scoped ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- A uniform nonzero-period gap supplies an explicit continuous left inverse to the incidence
multiplier. -/
theorem periodIncidenceMultiplier_hasLeftInverse_of_gap
    (L : Submodule ℤ ℂ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ q : NonzeroPeriod L, ε ≤ ‖(q.1.1 : ℂ)‖) :
    (periodIncidenceMultiplier L).HasLeftInverse := by
  refine ⟨periodIncidenceInverse L ε hε hgap, ?_⟩
  intro x
  apply lp.ext
  funext q
  rw [periodIncidenceInverse_apply, periodIncidenceMultiplier_apply,
    ← mul_assoc, inv_mul_cancel₀ (regularizedPeriodWeight_ne_zero q.2), one_mul]

/-- A discrete period group has uniform bounded source effectivity. -/
theorem periodIncidenceMultiplier_hasLeftInverse_of_discrete
    (L : Submodule ℤ ℂ) [DiscreteTopology L] :
    (periodIncidenceMultiplier L).HasLeftInverse := by
  obtain ⟨ε, hε, hgap⟩ := exists_period_norm_gap_of_discrete L
  exact periodIncidenceMultiplier_hasLeftInverse_of_gap L ε hε hgap

/-- **Uniform character-effectivity phase law.**  The period-incidence multiplier admits a
continuous left inverse exactly when the embedded integral period group is discrete. -/
theorem periodIncidenceMultiplier_hasLeftInverse_iff_discrete
    (L : Submodule ℤ ℂ) :
    (periodIncidenceMultiplier L).HasLeftInverse ↔ DiscreteTopology L := by
  constructor
  · intro hleft
    exact (periodIncidenceMultiplier_isClosed_range_iff_discrete L).mp
      hleft.isClosed_range
  · intro hdiscrete
    letI : DiscreteTopology L := hdiscrete
    exact periodIncidenceMultiplier_hasLeftInverse_of_discrete L

/-- A rationally independent rank-three period source has no continuous global left inverse even
though every finite nonzero diagonal restriction is bijective. -/
theorem rankThreePeriodIncidenceMultiplier_not_hasLeftInverse
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ¬ (periodIncidenceMultiplier
      (Submodule.span ℤ (Set.range v))).HasLeftInverse := by
  rw [periodIncidenceMultiplier_hasLeftInverse_iff_discrete]
  exact GaloisForLFunctions.not_discrete_intSpan_fin_three v hv

end

end GaloisForLFunctions
