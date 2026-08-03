import GaloisForLFunctions.RHTower.DeningerTreeHomologyMono
import GaloisForLFunctions.RHTower.DeningerAmalgamCyclic

/-!
# Degree two for a root adjunction

For an amalgam of a group with an infinite cyclic group over an infinite cyclic base of finite
index, the second homology vanishes as soon as it vanishes for the group.  The vertex homology
vanishes in degree two, and the comparison map one degree down is injective because the base group
sits in the infinite cyclic factor with finite index.

* `deningerAmalgam_isZero_two` : degree two for a two factor amalgam over an infinite cyclic base.
-/

namespace RHTower

open Monoid Monoid.PushoutI CategoryTheory CategoryTheory.Limits

universe u

variable {G : ULift.{u} Bool → Type u} {H : Type u} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Degree two for a two factor amalgam over an infinite cyclic base.** -/
theorem deningerAmalgam_isZero_two (k : Type u) [Field k] [DecidableEq (PushoutI φ)]
    (hφ : ∀ i, Function.Injective (φ i))
    (eH : H ≃* Multiplicative ℤ) (eF : G (ULift.up false) ≃* Multiplicative ℤ)
    [Fintype (↥(PushoutI.of (φ := φ) (ULift.up false)).range ⧸
      ((PushoutI.base φ).range).subgroupOf ((PushoutI.of (φ := φ) (ULift.up false)).range))]
    (hcard : (Fintype.card (↥(PushoutI.of (φ := φ) (ULift.up false)).range ⧸
      ((PushoutI.base φ).range).subgroupOf
        ((PushoutI.of (φ := φ) (ULift.up false)).range)) : k) ≠ 0)
    (hA : IsZero (groupHomology (Rep.trivial k (G (ULift.up true)) k) 2)) :
    IsZero (groupHomology (Rep.trivial k (PushoutI φ) k) 2) := by
  classical
  have hbase : (PushoutI.base φ).range ≃* H :=
    (MonoidHom.ofInjective (PushoutI.base_injective hφ)).symm
  have hfalse : (PushoutI.of (φ := φ) (ULift.up false)).range ≃* G (ULift.up false) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  have htrue : (PushoutI.of (φ := φ) (ULift.up true)).range ≃* G (ULift.up true) :=
    (MonoidHom.ofInjective (PushoutI.of_injective hφ _)).symm
  refine deningerAmalgam_isZero_of_mono k hφ 2 1 rfl ?_ ?_
  · refine IsZero.of_iso (deningerIsZero_biprod ?_ (deningerIsZero_biprod ?_ ?_))
      (deningerTreeVertexHomologyIso k 2)
    · exact IsZero.of_iso (deningerZ_isZero k eH 0) (deningerTrivialHomologyIso hbase k 2)
    · exact IsZero.of_iso hA (deningerTrivialHomologyIso htrue k 2)
    · exact IsZero.of_iso (deningerZ_isZero k eF 0) (deningerTrivialHomologyIso hfalse k 2)
  · exact deningerMono_map_proj (deningerBaseRange_le φ (ULift.up false)) k hcard
      (hbase.trans eH) (hfalse.trans eF)

end RHTower
