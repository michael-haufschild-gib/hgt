import GaloisForLFunctions.RHTower.DeningerMilnorRealShape
import GaloisForLFunctions.HTGeometry.MilnorNumberFieldDegreeDrop

/-!
# The real Milnor group of a number field vanishes above its degree

Bass and Tate's degree drop, applied over `ℚ`, makes `K_m^M(F)` torsion for every number field `F`
and every `m ≥ [F : ℚ] + 1`, hence its realification zero.  This is the part of the vanishing
`K_q^M(F) ⊗ ℝ = 0` that needs no input about the tame kernel: it is unconditional, but it leaves the
degrees `2 ≤ m ≤ [F : ℚ]` open.

* `deningerNumberFieldMilnorRealVanishing` : **`K_m^M(F) ⊗ ℝ = 0` for `m ≥ [F : ℚ] + 1`.**
-/

namespace RHTower

open scoped TensorProduct
open GaloisForLFunctions.HTGeometry

/-- **The real Milnor group of a number field vanishes above its degree.** -/
theorem deningerNumberFieldMilnorRealVanishing {F : Type*} [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] (m : ℕ) (hm : Module.finrank ℚ F + 1 ≤ m)
    (t : MilnorKDeg F m ⊗[ℤ] ℝ) : t = 0 :=
  deningerTorsionModule_tensorReal_eq_zero
    (fun x => milnorKDeg_numberField_torsion m hm x) t

/-- Over `ℚ` itself the bound is degree two, which is the known statement. -/
theorem deningerRationalMilnorRealVanishing_of_degreeDrop (m : ℕ) (hm : 2 ≤ m)
    (t : MilnorKDeg ℚ m ⊗[ℤ] ℝ) : t = 0 :=
  deningerTorsionModule_tensorReal_eq_zero (fun x => milnorKDeg_rat_torsion m hm x) t

/-- **The real Milnor group vanishes above the tower bound.**  A tower `ℚ ⊆ E ⊆ L` costs only
`(E : ℚ) − 1` plus `(L : E) − 1`, so a number field with subfields is reached far below its own
degree. -/
theorem deningerMilnorRealVanishing_tower {E L : Type*} [Field E] [Field L]
    [Algebra ℚ E] [Algebra ℚ L] [Algebra E L] [IsScalarTower ℚ E L]
    [FiniteDimensional ℚ E] [FiniteDimensional E L]
    (m : ℕ) (hm : 2 + (Module.finrank ℚ E - 1) + (Module.finrank E L - 1) ≤ m)
    (t : MilnorKDeg L m ⊗[ℤ] ℝ) : t = 0 :=
  deningerTorsionModule_tensorReal_eq_zero (fun x => milnorKDeg_torsion_tower m hm x) t

end RHTower
