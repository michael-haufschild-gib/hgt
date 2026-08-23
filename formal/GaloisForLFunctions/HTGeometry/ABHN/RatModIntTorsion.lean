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

/-- Every `ℚ/ℤ` class is killed by a positive finite denominator.  Thus the finite torsion
levels exhaust the local-invariant target before any local Brauer comparison is imposed. -/
theorem ratModInt_exists_nonzero_nsmul_eq_zero (x : RatModInt) :
    ∃ n : ℕ, n ≠ 0 ∧ x ∈ ratModIntNTorsion n := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨q.den, q.den_nz, ?_⟩
  change q.den • (QuotientAddGroup.mk q : RatModInt) = 0
  rw [← QuotientAddGroup.mk_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change q.den • q ∈ AddSubgroup.zmultiples (1 : ℚ)
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  refine ⟨q.num, ?_⟩
  change q.num • (1 : ℚ) = q.den • q
  rw [zsmul_one, nsmul_eq_mul]
  change (q.num : ℚ) = (q.den : ℚ) * q
  have hq : q = (q.num : ℚ) / (q.den : ℚ) := q.num_div_den.symm
  conv_rhs => arg 2; rw [hq]
  exact (mul_div_cancel₀ _ hden).symm

/-- `ℚ/ℤ` is the union of its finite torsion levels. -/
theorem iUnion_ratModIntNTorsion :
    ⋃ n : ℕ, (ratModIntNTorsion n : Set RatModInt) = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨n, _, hx⟩ := ratModInt_exists_nonzero_nsmul_eq_zero x
    exact Set.mem_iUnion.mpr ⟨n, hx⟩

/-- Torsion-level inclusion follows divisibility of denominators. -/
theorem ratModIntNTorsion_mono {m n : ℕ} (hmn : m ∣ n) :
    ratModIntNTorsion m ≤ ratModIntNTorsion n := by
  rintro x hx
  rcases hmn with ⟨k, rfl⟩
  change (m * k) • x = 0
  rw [mul_nsmul, hx, nsmul_zero]

/-- A finite collection of `ℚ/ℤ` values has one positive common torsion denominator. -/
theorem finset_exists_nonzero_common_ratModIntTorsion (s : Finset RatModInt) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ s, x ∈ ratModIntNTorsion n := by
  classical
  choose d hdne hdmem using (fun x : RatModInt => ratModInt_exists_nonzero_nsmul_eq_zero x)
  refine ⟨∏ x ∈ s, d x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x hx
    exact hdne x
  · intro x hx
    apply ratModIntNTorsion_mono (Finset.dvd_prod_of_mem d hx)
    exact hdmem x

/-- Every finite-support `ℚ/ℤ` profile lands in one positive torsion layer.  This reduces a
restricted ABHN invariant profile to a single finite denominator, while leaving the local
Brauer realization at that denominator as a separate question. -/
theorem finsupp_exists_nonzero_common_ratModIntTorsion
    {ι : Type*} (x : ι →₀ RatModInt) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ i, x i ∈ ratModIntNTorsion n := by
  classical
  obtain ⟨n, hn, htorsion⟩ :=
    finset_exists_nonzero_common_ratModIntTorsion (x.support.image fun i => x i)
  refine ⟨n, hn, ?_⟩
  intro i
  by_cases hi : i ∈ x.support
  · apply htorsion (x i)
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · have hzero : x i = 0 := by
      by_contra hne
      exact hi (Finsupp.mem_support_iff.mpr hne)
    rw [hzero]
    exact (ratModIntNTorsion n).zero_mem

end

end GaloisForLFunctions.HTGeometry.ABHN
