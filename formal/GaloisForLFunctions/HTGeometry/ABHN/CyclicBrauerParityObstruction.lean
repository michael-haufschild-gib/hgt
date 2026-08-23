import Mathlib

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

end GaloisForLFunctions.HTGeometry.ABHN
