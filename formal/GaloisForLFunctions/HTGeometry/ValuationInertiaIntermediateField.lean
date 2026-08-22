import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex
import Mathlib.FieldTheory.Galois.Basic

/-!
# Inertia along an intermediate field

The stabiliser of a sheet inside the inertia group of the base field is the inertia group of the
field that sheet generates.  This module proves that in the form the orbit count needs.

```text
mem_inertiaSubgroup_iff       g is inertial ⟺ g • y − y ∈ 𝔪_W for every y : W
decompositionRestrict         scalar restriction of a decomposition-group element
mem_inertiaSubgroup_decompositionRestrict
natCard_inertiaSubgroup_intermediate
    ** |W.inertiaSubgroup M| = #{ g inertial over F : g fixes M pointwise } **
```

Everything rests on one `rfl`: the pointwise action of `g : L ≃ₐ[M] L` on a valuation subring of `L`
is the action of `g.restrictScalars F`, because the action only reads the underlying ring map.  The
same is true of the action on `W` itself, so the two inertia conditions are literally the same
condition.

Surjectivity is `IntermediateField.fixingSubgroupEquiv` written out: an `F`-algebra equivalence
fixing `M` pointwise *is* an `M`-algebra equivalence, and rebuilding it from its ring equivalence
changes nothing.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing
open scoped Pointwise

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable (W : ValuationSubring L)

/-- Membership in the inertia subgroup, in terms of the action on the ring itself. -/
theorem mem_inertiaSubgroup_iff {g : W.decompositionSubgroup F} :
    g ∈ W.inertiaSubgroup F ↔ ∀ y : W, g • y - y ∈ maximalIdeal W := by
  constructor
  · intro hg y
    exact smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W hg y
  · intro h
    refine MonoidHom.mem_ker.2 (RingEquiv.ext ?_)
    refine (IsLocalRing.residue_surjective (R := W)).forall.2 fun a => ?_
    change g • IsLocalRing.residue W a = IsLocalRing.residue W a
    rw [← IsLocalRing.ResidueField.residue_smul (R := W) (W.decompositionSubgroup F) g a,
      ← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (h a)

variable (M : IntermediateField F L)

/-- Scalar restriction of a decomposition-group element of an intermediate field. -/
def decompositionRestrict (g : W.decompositionSubgroup M) : W.decompositionSubgroup F :=
  ⟨(g : L ≃ₐ[M] L).restrictScalars F, g.property⟩

@[simp] theorem coe_decompositionRestrict (g : W.decompositionSubgroup M) :
    ((decompositionRestrict W M g : W.decompositionSubgroup F) : L ≃ₐ[F] L)
      = (g : L ≃ₐ[M] L).restrictScalars F := rfl

theorem decompositionRestrict_smul (g : W.decompositionSubgroup M) (y : W) :
    decompositionRestrict W M g • y = g • y := rfl

theorem mem_inertiaSubgroup_decompositionRestrict {g : W.decompositionSubgroup M} :
    decompositionRestrict W M g ∈ W.inertiaSubgroup F ↔ g ∈ W.inertiaSubgroup M := by
  rw [mem_inertiaSubgroup_iff, mem_inertiaSubgroup_iff]
  simp only [decompositionRestrict_smul]

/-- **The inertia group of an intermediate field is the part of the inertia group of the base that
fixes it.** -/
theorem natCard_inertiaSubgroup_intermediate :
    Nat.card (W.inertiaSubgroup M)
      = Nat.card {g : W.inertiaSubgroup F //
          ∀ x : M, ((g : W.decompositionSubgroup F) : L ≃ₐ[F] L) (x : L) = (x : L)} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => (⟨⟨decompositionRestrict W M g,
        (mem_inertiaSubgroup_decompositionRestrict W M).mpr g.property⟩,
      fun x => (g : L ≃ₐ[M] L).commutes x⟩ :
        {g : W.inertiaSubgroup F //
          ∀ x : M, ((g : W.decompositionSubgroup F) : L ≃ₐ[F] L) (x : L) = (x : L)}))
    ⟨?_, ?_⟩)
  · intro a b hab
    have h1 := congrArg
      (fun z : {g : W.inertiaSubgroup F //
          ∀ x : M, ((g : W.decompositionSubgroup F) : L ≃ₐ[F] L) (x : L) = (x : L)} =>
        (((z : W.inertiaSubgroup F) : W.decompositionSubgroup F) : L ≃ₐ[F] L)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact AlgEquiv.restrictScalars_injective F h1
  · rintro ⟨⟨⟨g, hgd⟩, hgi⟩, hfix⟩
    refine ⟨⟨⟨{ g.toRingEquiv with commutes' := fun x => hfix x }, hgd⟩, ?_⟩, ?_⟩
    · exact (mem_inertiaSubgroup_decompositionRestrict W M).mp hgi
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact AlgEquiv.ext fun x => rfl

end

end ValuationInertia
end GaloisForLFunctions.HTGeometry
