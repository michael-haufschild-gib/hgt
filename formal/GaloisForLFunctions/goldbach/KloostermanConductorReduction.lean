import GaloisForLFunctions.RHTower.KloostermanComposite
import GaloisForLFunctions.RHTower.QuadraticGaussSumFourthPower
import GaloisForLFunctions.RHTower.WeilKloostermanArtinSchreier
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-!
# Removing a common factor from a Kloosterman phase

Unit reduction has constant fibres. A phase whose two coefficients share
the modulus factor descends to the smaller modulus, with exactly that
fibre multiplicity. Quotient labels bound the multiplicity by the factor.
-/

namespace GaloisForLFunctions.Goldbach

open Finset RHTower.Sieve
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Reduction from the product modulus to its first positive factor. -/
def kloostermanUnitReduction (q d : ℕ+) :
    (ZMod ((q : ℕ) * (d : ℕ)))ˣ →* (ZMod (q : ℕ))ˣ :=
  ZMod.unitsMap (dvd_mul_right (q : ℕ) (d : ℕ))

/-- The exact multiplicity of a unit lifted through modulus reduction. -/
def kloostermanLiftMultiplicity (q d : ℕ+) : ℕ :=
  Fintype.card (kloostermanUnitReduction q d).ker

theorem kloostermanUnitReduction_surjective (q d : ℕ+) :
    Function.Surjective (kloostermanUnitReduction q d) :=
  ZMod.unitsMap_surjective (dvd_mul_right (q : ℕ) (d : ℕ))

/-- A lifted unit is determined by its residue and its quotient label. -/
theorem kloostermanLiftMultiplicity_le (q d : ℕ+) :
    kloostermanLiftMultiplicity q d ≤ (d : ℕ) := by
  let N : ℕ := (q : ℕ) * (d : ℕ)
  let f : (kloostermanUnitReduction q d).ker → Fin (d : ℕ) := fun u =>
    ⟨((u.1 : ZMod N).val / (q : ℕ)),
      Nat.div_lt_of_lt_mul (ZMod.val_lt (u.1 : ZMod N))⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hquot : (u.1 : ZMod N).val / (q : ℕ) =
        (v.1 : ZMod N).val / (q : ℕ) := congrArg Fin.val huv
    have hred : kloostermanUnitReduction q d u.1 =
        kloostermanUnitReduction q d v.1 := u.2.trans v.2.symm
    have hcast : (((u.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) =
        (((v.1 : ZMod N).val : ℕ) : ZMod (q : ℕ)) := by
      have hval := congrArg Units.val hred
      change ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (u.1 : ZMod N) =
        ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ))
          (v.1 : ZMod N) at hval
      rwa [← ZMod.natCast_zmod_val (u.1 : ZMod N),
        ← ZMod.natCast_zmod_val (v.1 : ZMod N), map_natCast, map_natCast] at hval
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ (q : ℕ)).mp hcast
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective
    rw [← Nat.mod_add_div (u.1 : ZMod N).val (q : ℕ),
      ← Nat.mod_add_div (v.1 : ZMod N).val (q : ℕ), hquot, hmod]
  simpa only [kloostermanLiftMultiplicity, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Multiplying the phase by the second modulus factor removes that factor. -/
theorem stdAddChar_factor_reduction (q d : ℕ+)
    (z : ZMod ((q : ℕ) * (d : ℕ))) :
    ZMod.stdAddChar ((d : ℕ) * z) =
      ZMod.stdAddChar
        (ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ)) (ZMod (q : ℕ)) z) := by
  have h := RHTower.HalfWeight.stdAddChar_intCast_mul
    (N := (q : ℕ) * (d : ℕ)) (d := (q : ℕ)) (e := (d : ℕ))
    (by push_cast; rfl) (z.val : ℤ)
  have hz : ZMod.castHom (dvd_mul_right (q : ℕ) (d : ℕ))
      (ZMod (q : ℕ)) z = (z.val : ZMod (q : ℕ)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [hz]
  simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm] using h

end
end GaloisForLFunctions.Goldbach
