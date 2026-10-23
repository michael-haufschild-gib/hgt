import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterExtension

/-!
# The multiplicative rank of an algebraically closed field of characteristic zero

`deningerAleph0_le_rank` and `deningerMk_le_rank` assume `C^× ≠ μ(C)`; in characteristic zero
`deningerExists_notMem_torsion_charZero` proves it.  With `deningerRank_unitSpace_le` this gives
Deninger's dimension formula `dim_ℚ ((C^× / μ(C)) ⊗ ℚ) = #C`.
-/

namespace RHTower

open Cardinal

/-- `(C^× / μ(C)) ⊗ ℚ` is infinite dimensional for `C` algebraically closed of characteristic
zero. -/
theorem deningerAleph0_le_rank_of_charZero (C : Type*) [Field C] [IsAlgClosed C] [CharZero C] :
    ℵ₀ ≤ Module.rank ℚ (DeningerUnitSpace C) :=
  deningerAleph0_le_rank C (deningerExists_notMem_torsion_charZero C)

/-- **Deninger, Lemma 4.3, dimension.**  `dim_ℚ ((C^× / μ(C)) ⊗ ℚ) = #C` for `C` algebraically
closed of characteristic zero. -/
theorem deningerRank_unitSpace_eq_of_charZero (C : Type*) [Field C] [IsAlgClosed C]
    [CharZero C] :
    Module.rank ℚ (DeningerUnitSpace C) = #C :=
  le_antisymm (deningerRank_unitSpace_le C)
    (deningerMk_le_rank C (deningerExists_notMem_torsion_charZero C))

end RHTower
