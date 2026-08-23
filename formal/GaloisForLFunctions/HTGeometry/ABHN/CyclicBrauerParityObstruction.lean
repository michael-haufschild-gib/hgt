import GaloisForLFunctions.HTGeometry.ABHN.TameMilnorInvariant

/-!
# Cubic local invariants cannot enter a parity-valued additive receiver

Finite cyclic degree-three local invariants take values in `ZMod 3`, while the reflection-Tate
receiver used by the current conormal RH endpoint is parity-valued.  This file isolates the exact
algebraic obstruction: an additive map from `ZMod 3` to `ZMod 2` is necessarily zero.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- An additive parity-valued receiver annihilates every cubic cyclic invariant. -/
theorem zmod_three_to_zmod_two_addHom_eq_zero (f : ZMod 3 →+ ZMod 2) : f = 0 := by
  have hthree : (3 : ℤ) • f 1 = 0 := by
    calc
      (3 : ℤ) • f 1 = f ((3 : ℤ) • (1 : ZMod 3)) :=
        (f.map_zsmul 3 (1 : ZMod 3)).symm
      _ = f 0 := by congr
      _ = 0 := f.map_zero
  have hone : f 1 = 0 := by
    have htwo : (2 : ℤ) • f 1 = 0 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, add_zsmul, one_zsmul]
      calc
        f 1 + f 1 = (2 : ZMod 2) * f 1 := (two_mul _).symm
        _ = 0 := by
          have hchar : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
          rw [hchar, zero_mul]
    calc
      f 1 = (1 : ℤ) • f 1 := (one_zsmul _).symm
      _ = (3 : ℤ) • f 1 := by
        rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, htwo, add_zero]
      _ = 0 := hthree
  apply AddMonoidHom.ext
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  rw [show (m : ZMod 3) = m • (1 : ZMod 3) by exact (zsmul_one m).symm]
  rw [f.map_zsmul, hone, zsmul_zero]
  simp

/-- An additive parity-valued receiver annihilates every finite cyclic invariant of odd order.
Consequently an odd-primary local Brauer sector cannot feed the current parity-valued
Reflection--Tate endpoint without first changing its target. -/
theorem zmod_odd_to_zmod_two_addHom_eq_zero
    {n : ℕ} (hn : Odd n) (f : ZMod n →+ ZMod 2) : f = 0 := by
  rcases hn with ⟨k, rfl⟩
  have hnsmul : (2 * k + 1) • f 1 = 0 := by
    calc
      (2 * k + 1) • f 1 = f ((2 * k + 1) • (1 : ZMod (2 * k + 1))) :=
        (f.map_nsmul (2 * k + 1) (1 : ZMod (2 * k + 1))).symm
      _ = f 0 := by congr; rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      _ = 0 := f.map_zero
  have hEven : (2 * k) • f 1 = 0 := by
    rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self]
    simp
  have hone : f 1 = 0 := by
    calc
      f 1 = 1 • f 1 := (one_nsmul _).symm
      _ = 0 + 1 • f 1 := by simp
      _ = (2 * k) • f 1 + 1 • f 1 := by rw [hEven]
      _ = (2 * k + 1) • f 1 := (add_nsmul _ _ _).symm
      _ = 0 := hnsmul
  apply AddMonoidHom.ext
  intro z
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  rw [show (m : ZMod (2 * k + 1)) = m • (1 : ZMod (2 * k + 1)) by
    exact (zsmul_one m).symm]
  rw [f.map_zsmul, hone, zsmul_zero]
  simp

/-- No additive parity receiver can faithfully retain all `ℚ/ℤ` local-invariant values: its
restriction to the order-three sector is zero.  Thus a `ZMod 2` endpoint can at most encode
the two-primary shadow of ABHN local data. -/
theorem not_injective_ratModInt_to_zmod_two_addHom (f : RatModInt →+ ZMod 2) :
    ¬ Function.Injective f := by
  intro hf
  let g : ZMod 3 →+ RatModInt := zmodRatModIntAddHom 3 (Nat.succ_ne_zero 2)
  have hg : f.comp g = 0 := zmod_three_to_zmod_two_addHom_eq_zero (f.comp g)
  have hfg : Function.Injective (f.comp g) := hf.comp
    (zmodRatModIntAddHom_injective 3 (Nat.succ_ne_zero 2))
  have h01 : (0 : ZMod 3) = 1 := hfg (by rw [hg]; rfl)
  exact zero_ne_one h01

end GaloisForLFunctions.HTGeometry.ABHN
