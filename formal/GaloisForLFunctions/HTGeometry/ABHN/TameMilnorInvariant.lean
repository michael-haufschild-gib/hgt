/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.Specification
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldMilnorResidue

/-!
# Tame local Milnor invariants

Every finite cyclic additive group embeds in `ℚ/ℤ` by sending an integer class modulo its order
to that integer divided by the order.  Applied to the finite cyclic tame Milnor quotient of a
nonarchimedean local field, this gives a faithful tame local invariant.  Its kernel on `K₂ᴹ` is
exactly the tame-residue kernel.  It is not a Brauer-group invariant: the Milnor--Brauer
comparison remains separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped ValuativeRel

/-- The additive map from integers to `ℚ/ℤ` that sends `z` to the class of `z / n`. -/
noncomputable def intDivNatRatModIntAddHom (n : ℕ) : ℤ →+ RatModInt where
  toFun z := QuotientAddGroup.mk ((z : ℚ) / (n : ℚ))
  map_zero' := by
    change QuotientAddGroup.mk ((0 : ℚ) / (n : ℚ)) = QuotientAddGroup.mk 0
    rw [zero_div]
  map_add' x y := by
    change QuotientAddGroup.mk (((x + y : ℤ) : ℚ) / (n : ℚ)) =
      QuotientAddGroup.mk ((x : ℚ) / (n : ℚ) + (y : ℚ) / (n : ℚ))
    rw [Int.cast_add, add_div]

/-- The standard faithful inclusion of `ℤ/nℤ` into `ℚ/ℤ`, for nonzero `n`. -/
noncomputable def zmodRatModIntAddHom (n : ℕ) (hn : n ≠ 0) : ZMod n →+ RatModInt :=
  ZMod.lift n ⟨intDivNatRatModIntAddHom n, by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change ((n : ℚ) / (n : ℚ)) ∈ AddSubgroup.zmultiples (1 : ℚ)
    rw [div_self]
    · exact ⟨1, by simp⟩
    · exact_mod_cast hn⟩

/-- The standard inclusion of `ℤ/nℤ` into `ℚ/ℤ` is injective. -/
theorem zmodRatModIntAddHom_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (zmodRatModIntAddHom n hn) := by
  apply (ZMod.lift_injective n).mpr
  intro m hm
  change QuotientAddGroup.mk ((m : ℚ) / (n : ℚ)) = 0 at hm
  rw [QuotientAddGroup.eq_zero_iff] at hm
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  rw [zsmul_one] at hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd m n).mpr
  refine ⟨z, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : (z : ℚ) * (n : ℚ) = (m : ℚ) := (eq_div_iff hnq).mp hz
  rw [mul_comm] at hq
  exact_mod_cast hq.symm

/-- A finite cyclic additive group has a chosen faithful additive invariant in `ℚ/ℤ`. -/
noncomputable def finiteAddCyclicRatModIntAddHom (G : Type*) [AddGroup G] [Finite G]
    (h : IsAddCyclic G) : G →+ RatModInt :=
  let hn : Nat.card G ≠ 0 := Nat.ne_of_gt Nat.card_pos
  (zmodRatModIntAddHom (Nat.card G) hn).comp (zmodAddCyclicAddEquiv h).symm.toAddMonoidHom

/-- The chosen `ℚ/ℤ`-valued invariant of a finite cyclic additive group is injective. -/
theorem finiteAddCyclicRatModIntAddHom_injective (G : Type*) [AddGroup G] [Finite G]
    (h : IsAddCyclic G) : Function.Injective (finiteAddCyclicRatModIntAddHom G h) := by
  let hn : Nat.card G ≠ 0 := Nat.ne_of_gt Nat.card_pos
  exact (zmodRatModIntAddHom_injective (Nat.card G) hn).comp
    (zmodAddCyclicAddEquiv h).symm.injective

/-- The faithful `ℚ/ℤ`-valued invariant of the finite tame Milnor quotient of a nonarchimedean
local field. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorInvariant
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MilnorKDeg K 2 ⧸ (nonarchimedeanLocalFieldTameMilnorResidue K).ker →+ RatModInt :=
  finiteAddCyclicRatModIntAddHom _
    (nonarchimedeanLocalFieldTameMilnorResidueQuotient_isAddCyclic K)

/-- The tame Milnor invariant of a nonarchimedean local field is injective on its quotient. -/
theorem nonarchimedeanLocalFieldTameMilnorInvariant_injective
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Injective (nonarchimedeanLocalFieldTameMilnorInvariant K) :=
  finiteAddCyclicRatModIntAddHom_injective _
    (nonarchimedeanLocalFieldTameMilnorResidueQuotient_isAddCyclic K)

/-- The `ℚ/ℤ`-valued tame invariant on raw local Milnor `K₂`. -/
noncomputable def nonarchimedeanLocalFieldTameMilnorInvariantRaw
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : MilnorKDeg K 2 →+ RatModInt :=
  (nonarchimedeanLocalFieldTameMilnorInvariant K).comp
    (QuotientAddGroup.mk' (nonarchimedeanLocalFieldTameMilnorResidue K).ker)

/-- The raw tame Milnor invariant has precisely the tame-residue kernel. -/
theorem nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (nonarchimedeanLocalFieldTameMilnorInvariantRaw K).ker =
      (nonarchimedeanLocalFieldTameMilnorResidue K).ker := by
  ext x
  constructor
  · intro hx
    change nonarchimedeanLocalFieldTameMilnorInvariant K (QuotientAddGroup.mk x) = 0 at hx
    have hq : QuotientAddGroup.mk x = 0 :=
      nonarchimedeanLocalFieldTameMilnorInvariant_injective K
        (hx.trans (nonarchimedeanLocalFieldTameMilnorInvariant K).map_zero.symm)
    exact (QuotientAddGroup.eq_zero_iff _).mp hq
  · intro hx
    change nonarchimedeanLocalFieldTameMilnorInvariant K (QuotientAddGroup.mk x) = 0
    rw [(QuotientAddGroup.eq_zero_iff _).mpr hx,
      (nonarchimedeanLocalFieldTameMilnorInvariant K).map_zero]

/-- The raw tame invariant is exact after inclusion of the tame-residue kernel.  This is the
local Milnor exactness component that later comparison maps must preserve to yield a Brauer
local invariant. -/
theorem nonarchimedeanLocalFieldTameMilnorInvariantRaw_exact
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Exact
      ((nonarchimedeanLocalFieldTameMilnorResidue K).ker).subtype
      (nonarchimedeanLocalFieldTameMilnorInvariantRaw K) := by
  rw [AddMonoidHom.exact_iff, nonarchimedeanLocalFieldTameMilnorInvariantRaw_ker,
    AddSubgroup.range_subtype]

end

end GaloisForLFunctions.HTGeometry.ABHN
