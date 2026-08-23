/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.TameMilnorInvariant

/-!
# Finite torsion levels in `ℚ/ℤ`

The standard map `ℤ/nℤ → ℚ/ℤ`, sending an integer class to that integer divided by `n`, has image
exactly the subgroup killed by `n`.  This supplies the explicit finite-level target for the
cohomological local invariants constructed from unramified cyclic extensions.  It does not compare
those cohomology groups with local Brauer groups.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The subgroup of `ℚ/ℤ` killed by the natural number `n`. -/
def ratModIntNTorsion (n : ℕ) : AddSubgroup RatModInt where
  carrier := { x | n • x = 0 }
  zero_mem' := by simp
  add_mem' hx hy := by
    change n • (_ + _) = 0
    change n • _ = 0 at hx hy
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' hx := by
    change n • (-_) = 0
    change n • _ = 0 at hx
    rw [smul_neg, hx, neg_zero]

/-- The standard `ℤ/nℤ` invariant takes values in the `n`-torsion subgroup of `ℚ/ℤ`. -/
theorem zmodRatModIntAddHom_mem_ratModIntNTorsion (n : ℕ) (hn : n ≠ 0) (x : ZMod n) :
    zmodRatModIntAddHom n hn x ∈ ratModIntNTorsion n := by
  change n • zmodRatModIntAddHom n hn x = 0
  rw [← map_nsmul, show n • x = 0 by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]]
  exact (zmodRatModIntAddHom n hn).map_zero

/-- The image of the standard `ℤ/nℤ` invariant is exactly `ℚ/ℤ[n]`. -/
theorem zmodRatModIntAddHom_range_eq_ratModIntNTorsion (n : ℕ) (hn : n ≠ 0) :
    (zmodRatModIntAddHom n hn).range = ratModIntNTorsion n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact zmodRatModIntAddHom_mem_ratModIntNTorsion n hn x
  · rintro x hx
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
    change n • (QuotientAddGroup.mk q : RatModInt) = 0 at hx
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hx
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [nsmul_eq_mul, zsmul_one] at hz
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hq : q = (z : ℚ) / (n : ℚ) := by
      apply (eq_div_iff hnq).mpr
      simpa [mul_comm] using hz.symm
    refine ⟨(z : ZMod n), ?_⟩
    rw [zmodRatModIntAddHom, ZMod.lift_coe]
    change QuotientAddGroup.mk ((z : ℚ) / (n : ℚ)) = QuotientAddGroup.mk q
    rw [hq]

/-- Composing the standard invariant with any additive equivalence onto `ℤ/nℤ` has exactly the
`n`-torsion subgroup of `ℚ/ℤ` as image. -/
theorem zmodRatModIntAddHom_comp_addEquiv_range_eq_ratModIntNTorsion
    {G : Type*} [AddGroup G] (n : ℕ) (hn : n ≠ 0) (e : G ≃+ ZMod n) :
    ((zmodRatModIntAddHom n hn).comp e.toAddMonoidHom).range = ratModIntNTorsion n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact zmodRatModIntAddHom_mem_ratModIntNTorsion n hn (e x)
  · rw [← zmodRatModIntAddHom_range_eq_ratModIntNTorsion n hn]
    rintro _ ⟨x, rfl⟩
    exact ⟨e.symm x, by simp⟩

/-- The standard `ℤ/nℤ` invariant with codomain restricted to the `n`-torsion of `ℚ/ℤ`. -/
noncomputable def zmodRatModIntAddHomToNTorsion (n : ℕ) (hn : n ≠ 0) :
    ZMod n →+ ratModIntNTorsion n :=
  AddMonoidHom.codRestrict (zmodRatModIntAddHom n hn) (ratModIntNTorsion n)
    (zmodRatModIntAddHom_mem_ratModIntNTorsion n hn)

/-- The torsion-valued standard invariant is injective. -/
theorem zmodRatModIntAddHomToNTorsion_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (zmodRatModIntAddHomToNTorsion n hn) := by
  intro x y hxy
  apply zmodRatModIntAddHom_injective n hn
  exact congrArg Subtype.val hxy

/-- The finite cyclic group `ℤ/nℤ` is canonically the `n`-torsion subgroup of `ℚ/ℤ`. -/
noncomputable def zmodRatModIntAddEquivNTorsion (n : ℕ) (hn : n ≠ 0) :
    ZMod n ≃+ ratModIntNTorsion n :=
  AddEquiv.ofBijective (zmodRatModIntAddHomToNTorsion n hn)
    ⟨zmodRatModIntAddHomToNTorsion_injective n hn, by
      intro x
      have hx : (x : RatModInt) ∈ (zmodRatModIntAddHom n hn).range := by
        rw [zmodRatModIntAddHom_range_eq_ratModIntNTorsion]
        exact x.property
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, Subtype.ext hy⟩⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
