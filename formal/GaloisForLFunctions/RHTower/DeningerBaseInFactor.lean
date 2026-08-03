import GaloisForLFunctions.RHTower.DeningerAmalgamTwo

/-!
# The base group inside a factor

Inside an amalgam, an element of a factor lies in the base group exactly when it lies in the image
of the structure map of that factor.  So the base group, seen inside a factor, is that image, and
the index of the base group in the factor is computed in the factor itself.

* `deningerMem_baseRange_iff` : the characterization.
* `deningerSubgroupOf_map` : the base group inside a factor is the image of the structure map.
* `deningerIndex_subgroupOf` : the index of the base group in a factor is computed in the factor.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

variable {ι : Type u} {G : ι → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **An element of a factor lies in the base group exactly when it is in the image of the
structure map.** -/
theorem deningerMem_baseRange_iff (hφ : ∀ i, Function.Injective (φ i)) (i : ι) (x : G i) :
    PushoutI.of (φ := φ) i x ∈ (PushoutI.base φ).range ↔ x ∈ (φ i).range := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, PushoutI.of_injective hφ i ?_⟩
    rw [PushoutI.of_apply_eq_base, hh]
  · rintro ⟨h, rfl⟩
    exact ⟨h, (PushoutI.of_apply_eq_base φ i h).symm⟩

/-- **The base group inside a factor is the image of the structure map.** -/
theorem deningerSubgroupOf_map (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    Subgroup.map (MonoidHom.ofInjective (PushoutI.of_injective hφ i)).symm.toMonoidHom
        (((PushoutI.base φ).range).subgroupOf ((PushoutI.of (φ := φ) i).range)) =
      (φ i).range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy : (y : PushoutI φ) ∈ (PushoutI.base φ).range := hy
    have hyx : (y : PushoutI φ) = PushoutI.of (φ := φ) i
        ((MonoidHom.ofInjective (PushoutI.of_injective hφ i)).symm y) := by
      have := (MonoidHom.ofInjective (PushoutI.of_injective hφ i)).apply_symm_apply y
      exact congrArg (Subtype.val) this.symm
    rw [hyx] at hy
    exact (deningerMem_baseRange_iff hφ i _).1 hy
  · intro hx
    refine ⟨⟨PushoutI.of (φ := φ) i x, ⟨x, rfl⟩⟩, ?_, ?_⟩
    · show (PushoutI.of (φ := φ) i x) ∈ (PushoutI.base φ).range
      exact (deningerMem_baseRange_iff hφ i x).2 hx
    · exact (MonoidHom.ofInjective (PushoutI.of_injective hφ i)).symm_apply_eq.2 rfl

/-- **The index of the base group in a factor is computed inside the factor.** -/
theorem deningerIndex_subgroupOf (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    (((PushoutI.base φ).range).subgroupOf ((PushoutI.of (φ := φ) i).range)).index =
      ((φ i).range).index := by
  set e := (MonoidHom.ofInjective (PushoutI.of_injective hφ i)).symm with he
  have hcomap : ((PushoutI.base φ).range).subgroupOf ((PushoutI.of (φ := φ) i).range) =
      ((φ i).range).comap e.toMonoidHom := by
    rw [← deningerSubgroupOf_map hφ i, Subgroup.comap_map_eq_self_of_injective e.injective]
  rw [hcomap, Subgroup.index_comap_of_surjective _ e.surjective]

end RHTower
