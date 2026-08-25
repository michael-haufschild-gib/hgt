/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisNormQuotientTransition
import Mathlib.Data.ZMod.Units

/-!
# Compatible coordinates on nested finite cyclic subgroups

An inclusion between cyclic groups of orders `m` and `m * r` can be coordinatized by the
canonical `ZMod` transition.  The key arithmetic statement says every order-`m` element of
`ZMod (m * r)` is a unit multiple of the canonical transition generator `r`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

theorem zmod_exists_unit_mul_transition_generator {m n r : ℕ}
    (hm : m ≠ 0) (hr : r ≠ 0) (hmr : m * r = n)
    (y : ZMod n) (hy : addOrderOf y = m) :
    ∃ u : (ZMod n)ˣ, (u : ZMod n) * (r : ZMod n) = y := by
  have hn : n ≠ 0 := by rw [← hmr]; exact mul_ne_zero hm hr
  letI : NeZero n := ⟨hn⟩
  have hy' : n / n.gcd y.val = m := by
    have hcast := ZMod.addOrderOf_coe y.val hn
    rw [ZMod.natCast_zmod_val] at hcast
    exact hcast.symm.trans hy
  have hng : n.gcd y.val * m = n := by
    rw [← hy']
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left n y.val)
  have hgr : n.gcd y.val = r := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm)
    rw [mul_comm, hng, hmr]
  have hry : r ∣ y.val := hgr ▸ Nat.gcd_dvd_right n y.val
  let q := y.val / r
  have hyval : r * q = y.val := Nat.mul_div_cancel' hry
  have hcop' : m.Coprime q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgcd : (r * m).gcd (r * q) = r := by
      rw [mul_comm r m, hmr, hyval, ← hgr]
    rw [Nat.gcd_mul_left] at hgcd
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (by simpa using hgcd)
  have hcop : q.Coprime m := hcop'.symm
  have hmn : m ∣ n := ⟨r, hmr.symm⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hmn (ZMod.unitOfCoprime q hcop)
  refine ⟨u, ?_⟩
  have hmod : (u : ZMod n).val ≡ q [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hv := congrArg Units.val hu
    change ((u : ZMod n).cast : ZMod m) = (q : ZMod m) at hv
    simpa only [ZMod.natCast_val] using hv
  rw [← ZMod.natCast_zmod_val y]
  conv_lhs =>
    lhs
    rw [← ZMod.natCast_zmod_val (u : ZMod n)]
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  let a : ℕ := (u : ZMod n).val
  have hmoda : a ≡ q [MOD m] := hmod
  have hscaled' : a * r ≡ q * r [MOD n] := by
    rw [Nat.ModEq] at hmoda ⊢
    rw [← hmr, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, hmoda]
  have hscaled : (u : ZMod n).val * r ≡ q * r [MOD n] := hscaled'
  rw [← hyval]
  simpa [mul_comm] using hscaled

def zmodUnitMulAddEquiv {n : ℕ} (u : (ZMod n)ˣ) : ZMod n ≃+ ZMod n where
  toEquiv := u.mulLeft
  map_add' x y := mul_add (u : ZMod n) x y

@[simp] theorem zmodUnitMulAddEquiv_apply {n : ℕ} (u : (ZMod n)ˣ) (x : ZMod n) :
    zmodUnitMulAddEquiv u x = (u : ZMod n) * x := rfl

theorem addOrderOf_addSubgroup_inclusion_eq_of_eq {A : Type*} [AddGroup A]
    (S T : AddSubgroup A) (hST : S ≤ T) (x : S) {m : ℕ}
    (hm : 0 < m) (hx : addOrderOf x = m) :
    addOrderOf (AddSubgroup.inclusion hST x) = m := by
  obtain ⟨hxzero, hxmin⟩ := (addOrderOf_eq_iff hm).mp hx
  apply (addOrderOf_eq_iff hm).mpr
  constructor
  · rw [← map_nsmul, hxzero, map_zero]
  · intro k hkm hkpos hkzero
    apply hxmin k hkm hkpos
    apply AddSubgroup.inclusion_injective hST
    simpa only [map_nsmul, map_zero] using hkzero

theorem exists_zmod_addEquiv_of_subgroup_extension
    {A : Type*} [AddGroup A] (S T : AddSubgroup A) (hST : S ≤ T)
    {m n r : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hr : r ≠ 0) (hmr : m * r = n)
    (eS : ZMod m ≃+ S) (eT₀ : ZMod n ≃+ T) :
    ∃ eT : ZMod n ≃+ T,
      (AddSubgroup.inclusion hST).comp eS.toAddMonoidHom =
        eT.toAddMonoidHom.comp (zmodRatModIntTransition hm hn ⟨r, hmr.symm⟩) := by
  let y : ZMod n := eT₀.symm (AddSubgroup.inclusion hST (eS 1))
  have hy : addOrderOf y = m := by
    rw [eT₀.symm.addOrderOf_eq]
    apply addOrderOf_addSubgroup_inclusion_eq_of_eq S T hST (eS 1)
      (Nat.pos_of_ne_zero hm)
    rw [eS.addOrderOf_eq, ZMod.addOrderOf_one]
  obtain ⟨u, hu⟩ := zmod_exists_unit_mul_transition_generator hm hr hmr y hy
  let eT := (zmodUnitMulAddEquiv u).trans eT₀
  refine ⟨eT, ?_⟩
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  change AddSubgroup.inclusion hST (eS (z : ZMod m)) =
    eT (zmodRatModIntTransition hm hn ⟨r, hmr.symm⟩ (z : ZMod m))
  rw [zmodRatModIntTransition_intCast hm hn hmr]
  change AddSubgroup.inclusion hST (eS (z : ZMod m)) =
    eT₀ (zmodUnitMulAddEquiv u ((((r : ℤ) * z : ℤ) : ZMod n)))
  rw [show (((r : ℤ) * z : ℤ) : ZMod n) = z • (r : ZMod n) by simp [mul_comm]]
  rw [map_zsmul, zmodUnitMulAddEquiv_apply, hu, map_zsmul]
  rw [show eT₀ y = AddSubgroup.inclusion hST (eS 1) by
    dsimp [y]
    rw [eT₀.apply_symm_apply]]
  rw [show (z : ZMod m) = z • (1 : ZMod m) by simp, map_zsmul, map_zsmul]

end

end GaloisForLFunctions.HTGeometry.ABHN
