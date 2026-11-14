import GaloisForLFunctions.RHTower.Deninger.DeningerOrbitShapiro
import GaloisForLFunctions.HTGeometry.Buildings.ParabolicShears
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Homology of flag orbits and their stabilizers

The permutation module on the orbit of a family of subspaces is induced
from its simultaneous stabilizer. Shapiro identifies all its group
homology with the homology of that stabilizer. For a nested family this
is the corresponding parabolic subgroup.

Shears across a chosen stage lie in this stabilizer whenever every stage
is comparable with that stage. This connects the explicit unipotent
symmetries with the orbit-family construction in Ash--Gunnells,
arXiv:2611.03303, Lemma 4.4 and §6.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory MulAction
open scoped Pointwise

universe u

variable {k K V ι : Type u} [CommRing k] [Field K] [AddCommGroup V] [Module K V]

/-- The simultaneous stabilizer of a family of subspaces; for a flag this is parabolic. -/
abbrev flagFamilyStabilizer (A : ι → Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  stabilizer (V ≃ₗ[K] V) A

/-- Stabilizing the family means preserving every stage separately. -/
theorem mem_flagFamilyStabilizer_iff (A : ι → Submodule K V) (g : V ≃ₗ[K] V) :
    g ∈ flagFamilyStabilizer A ↔ ∀ i, (A i).map g.toLinearMap = A i := by
  change (fun i => g • A i) = A ↔ _
  rw [funext_iff]
  exact forall_congr' (fun i => Submodule.mem_stabilizer_submodule_iff_map_eq)

/-- The orbit module of a flag is induced from its parabolic stabilizer. -/
noncomputable def flagOrbitInducedIso (A : ι → Submodule K V) :
    Rep.ind (flagFamilyStabilizer A).subtype (Rep.trivial k (flagFamilyStabilizer A) k) ≅
      Rep.ofMulAction k (V ≃ₗ[K] V) (orbit (V ≃ₗ[K] V) A) :=
  RHTower.deningerIndOrbitIso A

/-- All homology degrees of the flag orbit reduce to the simultaneous stabilizer. -/
noncomputable def flagOrbitHomologyIso (A : ι → Submodule K V) (n : ℕ) :
    groupHomology (Rep.ofMulAction k (V ≃ₗ[K] V) (orbit (V ≃ₗ[K] V) A)) n ≅
      groupHomology (Rep.trivial k (flagFamilyStabilizer A) k) n :=
  RHTower.deningerOrbitShapiro A n

/-- The exact shear-invariance criterion holds simultaneously at every stage. -/
theorem flagShear_mem_flagFamilyStabilizer_iff (A : ι → Submodule K V)
    (B : Submodule K V) (f : (V ⧸ B) →ₗ[K] B) :
    flagShear B f ∈ flagFamilyStabilizer A ↔
      ∀ i, ∀ x ∈ A i, flagShearDisplacement B f x ∈ A i := by
  rw [mem_flagFamilyStabilizer_iff]
  exact forall_congr' (fun i => flagShear_map_eq_iff B (A i) f)

/-- A shear across a flag stage fixes every other stage comparable with it. -/
theorem flagShear_mem_flagFamilyStabilizer (A : ι → Submodule K V)
    (B : Submodule K V) (f : (V ⧸ B) →ₗ[K] B)
    (h : ∀ i, A i ≤ B ∨ B ≤ A i) : flagShear B f ∈ flagFamilyStabilizer A := by
  rw [mem_flagFamilyStabilizer_iff]
  intro i
  rcases h i with hi | hi
  · exact flagShear_fixes_below B f ⟨A i, hi⟩
  · exact flagShear_fixes_above B f ⟨A i, hi⟩

/-- Every monotone family is fixed by a shear across any of its stages. -/
theorem flagShear_mem_monotoneFlagStabilizer [LinearOrder ι]
    (A : ι →o Submodule K V) (j : ι) (f : (V ⧸ A j) →ₗ[K] A j) :
    flagShear (A j) f ∈ flagFamilyStabilizer (fun i => A i) := by
  apply flagShear_mem_flagFamilyStabilizer
  intro i
  rcases le_total i j with h | h
  · exact Or.inl (A.monotone h)
  · exact Or.inr (A.monotone h)

end GaloisForLFunctions.HTGeometry
