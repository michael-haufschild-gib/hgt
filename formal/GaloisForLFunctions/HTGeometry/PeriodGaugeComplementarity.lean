import GaloisForLFunctions.HTGeometry.MeromorphicTranslationFixedField
import GaloisForLFunctions.HTGeometry.PeriodIncidenceUniformEffectivity

/-!
# Period-gauge complementarity

The topological phase of the embedded integral period source controls two apparently different
obstructions in opposite directions.  Nondiscreteness destroys every continuous global left
inverse of the period-incidence representation, but the resulting arbitrarily small periods force
every global meromorphic source-fixed gauge to be constant.  Conversely, a nonconstant fixed gauge
can occur only in the uniformly effective discrete phase.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-- Every nondiscrete integral period source has only constant global meromorphic fixed gauges. -/
theorem exists_constant_of_nondiscrete_translation_fixed
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (z : meroField (Set.univ : Set ℂ))
    (hfix : ∀ q ∈ L, addTranslationMeroEquiv q z = z) :
    ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  exact exists_constant_of_small_translation_fixed z p hp_zero hp_ne
    (fun n => hfix (p n) (hp_mem n))

/-- **Gauge--attainment complementarity.**  Failure of a continuous global incidence inverse
forces maximal meromorphic gauge rigidity: every source-fixed gauge is constant. -/
theorem exists_constant_of_periodIncidenceMultiplier_not_hasLeftInverse
    (L : Submodule ℤ ℂ)
    (hno : ¬ (periodIncidenceMultiplier L).HasLeftInverse)
    (z : meroField (Set.univ : Set ℂ))
    (hfix : ∀ q ∈ L, addTranslationMeroEquiv q z = z) :
    ∃ c : ℂ, algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z := by
  apply exists_constant_of_nondiscrete_translation_fixed L
  · intro hdiscrete
    exact hno ((periodIncidenceMultiplier_hasLeftInverse_iff_discrete L).2 hdiscrete)
  · exact hfix

/-- Contrapositive form: any nonconstant global meromorphic fixed gauge forces uniform incidence
effectivity and hence discreteness of the period source. -/
theorem periodIncidenceMultiplier_hasLeftInverse_of_nonconstant_fixed
    (L : Submodule ℤ ℂ) (z : meroField (Set.univ : Set ℂ))
    (hfix : ∀ q ∈ L, addTranslationMeroEquiv q z = z)
    (hnonconstant : ¬ ∃ c : ℂ,
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) = z) :
    (periodIncidenceMultiplier L).HasLeftInverse := by
  by_contra hno
  exact hnonconstant
    (exists_constant_of_periodIncidenceMultiplier_not_hasLeftInverse L hno z hfix)

end

end GaloisForLFunctions
