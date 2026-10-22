import GaloisForLFunctions.RHTower.Deninger.DeningerBauSubsingleton
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Vanishing of cohomology passes to a retract

The cohomological counterpart of the homological statement.  It matters because the packet's clause
about the cohomology algebra is stated in cohomology, and the arguments that pass to increasing
unions are available only in homology, where a chain has finite support.

* `deningerTrivialResCo` : the comparison of coefficients.
* `deningerIsZero_of_retract_cohomology` : vanishing of cohomology passes to a retract.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [CommRing k] {G E : Type u} [Group G] [Group E]

/-- The comparison of trivial coefficients along a group homomorphism, for cohomology. -/
noncomputable def deningerTrivialResCo (s : G →* E) :
    Rep.res s (Rep.trivial k E k) ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- **Vanishing of cohomology passes to a retract.** -/
theorem deningerIsZero_of_retract_cohomology (π : E →* G) (s : G →* E)
    (hs : π.comp s = MonoidHom.id G) (n : ℕ)
    (hE : IsZero (groupCohomology (Rep.trivial k E k) n)) :
    IsZero (groupCohomology (Rep.trivial k G k) n) := by
  have hcomp : groupCohomology.map π (deningerTrivialResCo k π) n ≫
      groupCohomology.map s (deningerTrivialResCo k s) n = 𝟙 _ := by
    have h1 := groupCohomology.map_comp π s (deningerTrivialResCo k π)
      (deningerTrivialResCo k s) n
    have h2 : groupCohomology.map (π.comp s)
        ((Rep.resFunctor s).map (deningerTrivialResCo k π) ≫ deningerTrivialResCo k s) n =
        groupCohomology.map (MonoidHom.id G) (deningerTrivialResCo k (MonoidHom.id G)) n :=
      groupCohomology.map_congr hs rfl n
    rw [← h1, h2]
    have h3 : groupCohomology.map (MonoidHom.id G) (deningerTrivialResCo k (MonoidHom.id G)) n =
        groupCohomology.map (MonoidHom.id G) (𝟙 (Rep.trivial k G k)) n :=
      groupCohomology.map_congr rfl rfl n
    rw [h3, groupCohomology.map_id]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← hcomp, hE.eq_zero_of_src (groupCohomology.map s (deningerTrivialResCo k s) n), comp_zero]

end RHTower
