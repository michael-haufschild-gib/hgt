import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentRotation

/-!
# Tame symbols of power-series units

The Laurent tame symbol of a power-series unit and any Laurent unit is the
constant coefficient raised to the latter's integer valuation. In particular,
principal units pair trivially with every Laurent unit. These formulas control
the splitting over the positive loop subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

@[simp] theorem laurentTameSymbol_one_left (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F 1 a = 1 := by
  apply Additive.ofMul.injective
  rw [← laurentTameHom_symbol, milnorSym2_one_left, map_zero]
  rfl

@[simp] theorem laurentTameSymbol_one_right (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a 1 = 1 := by
  apply Additive.ofMul.injective
  rw [← laurentTameHom_symbol, milnorSym2_one_right, map_zero]
  rfl

theorem laurentTameSymbol_mul_left (a b c : (LaurentSeries F)ˣ) :
    laurentTameSymbol F (a * b) c = laurentTameSymbol F a c * laurentTameSymbol F b c := by
  apply Additive.ofMul.injective
  change Additive.ofMul (laurentTameSymbol F (a * b) c) =
    Additive.ofMul (laurentTameSymbol F a c) + Additive.ofMul (laurentTameSymbol F b c)
  rw [← laurentTameHom_symbol, ← laurentTameHom_symbol, ← laurentTameHom_symbol,
    milnorSym2_mul_left, map_add]

theorem laurentTameSymbol_mul_right (a b c : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a (b * c) = laurentTameSymbol F a b * laurentTameSymbol F a c := by
  apply Additive.ofMul.injective
  change Additive.ofMul (laurentTameSymbol F a (b * c)) =
    Additive.ofMul (laurentTameSymbol F a b) + Additive.ofMul (laurentTameSymbol F a c)
  rw [← laurentTameHom_symbol, ← laurentTameHom_symbol, ← laurentTameHom_symbol,
    milnorSym2_mul_right, map_add]

theorem laurentTameSymbol_inv_left (a b : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a⁻¹ b = (laurentTameSymbol F a b)⁻¹ := by
  apply Additive.ofMul.injective
  change Additive.ofMul (laurentTameSymbol F a⁻¹ b) = -Additive.ofMul (laurentTameSymbol F a b)
  rw [← laurentTameHom_symbol, ← laurentTameHom_symbol, milnorSym2_inv_left, map_neg]

theorem laurentTameSymbol_inv_right (a b : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a b⁻¹ = (laurentTameSymbol F a b)⁻¹ := by
  apply Additive.ofMul.injective
  change Additive.ofMul (laurentTameSymbol F a b⁻¹) = -Additive.ofMul (laurentTameSymbol F a b)
  rw [← laurentTameHom_symbol, ← laurentTameHom_symbol, milnorSym2_inv_right, map_neg]

theorem laurentTameSymbol_antisymm (a b : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a b = (laurentTameSymbol F b a)⁻¹ := by
  apply Additive.ofMul.injective
  change Additive.ofMul (laurentTameSymbol F a b) = -Additive.ofMul (laurentTameSymbol F b a)
  rw [← laurentTameHom_symbol, ← laurentTameHom_symbol, milnorSym2_antisymm, map_neg]

@[simp] theorem laurentTameSymbol_neg_self (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a (-a) = 1 := by
  apply Additive.ofMul.injective
  rw [← laurentTameHom_symbol, milnorSym2_neg_self, map_zero]
  rfl

/-- A Steinberg pair has trivial Laurent tame symbol. -/
theorem laurentTameSymbol_add_eq_one (a b : (LaurentSeries F)ˣ)
    (hab : (a : LaurentSeries F) + (b : LaurentSeries F) = 1) :
    laurentTameSymbol F a b = 1 := by
  have ha : (a : LaurentSeries F) ≠ 1 := by
    intro ha
    apply b.ne_zero
    linear_combination hab - ha
  have hb : b = oneSubUnit ha := by
    apply Units.ext
    change (b : LaurentSeries F) = 1 - (a : LaurentSeries F)
    linear_combination hab
  apply Additive.ofMul.injective
  rw [hb, ← laurentTameHom_symbol, milnorSym2_steinberg, map_zero]
  rfl

/-- Embed a power-series unit into the Laurent field. -/
def powerSeriesLaurentUnit : (PowerSeries F)ˣ →* (LaurentSeries F)ˣ :=
  Units.map (HahnSeries.ofPowerSeries ℤ F).toMonoidHom

/-- The invertible constant coefficient of a power-series unit. -/
def powerSeriesResidueUnit : (PowerSeries F)ˣ →* Fˣ :=
  Units.map (PowerSeries.constantCoeff (R := F)).toMonoidHom

@[simp] theorem coe_powerSeriesLaurentUnit (p : (PowerSeries F)ˣ) :
    (powerSeriesLaurentUnit F p : LaurentSeries F) =
      ((p : PowerSeries F) : LaurentSeries F) := rfl

@[simp] theorem coe_powerSeriesResidueUnit (p : (PowerSeries F)ˣ) :
    (powerSeriesResidueUnit F p : F) = PowerSeries.constantCoeff (p : PowerSeries F) := rfl

theorem powerSeriesLaurentUnit_mem_kernel (p : (PowerSeries F)ˣ) :
    powerSeriesLaurentUnit F p ∈ (tameValHom (laurentValuation F)).ker := by
  rw [tameValHom_mem_ker_iff, coe_powerSeriesLaurentUnit]
  exact laurent_valuation_coe_powerSeries_eq_one_of_constantCoeff_ne_zero F
    (powerSeriesResidueUnit F p).ne_zero

private theorem tameResidue_powerSeriesUnit (p : (PowerSeries F)ˣ) :
    Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom
      (tameResHom (laurentValuation F)
        ⟨powerSeriesLaurentUnit F p, powerSeriesLaurentUnit_mem_kernel F p⟩) =
      powerSeriesResidueUnit F p := by
  apply Units.ext
  rw [Units.coe_map, tameResHom_val]
  change ABHN.laurentSeriesResidueFieldEquiv F
    (IsLocalRing.residue _
      (ABHN.laurentPowerSeriesEquivValuedInteger F (p : PowerSeries F))) =
        PowerSeries.constantCoeff (p : PowerSeries F)
  exact ABHN.laurentSeriesResidueFieldEquiv_residue_powerSeries F _

/-- Only the constant coefficient of a power-series unit enters the tame symbol. -/
theorem laurentTameSymbol_powerSeriesUnit_left
    (p : (PowerSeries F)ˣ) (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F (powerSeriesLaurentUnit F p) a =
      powerSeriesResidueUnit F p ^ (tameDataOfValuation (laurentValuation F)).v a := by
  rw [laurentTameSymbol,
    (tameDataOfValuation (laurentValuation F)).tame_of_mem_ker_left
      (powerSeriesLaurentUnit_mem_kernel F p)]
  exact (map_zpow (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom)
    _ _).trans (congrArg (fun u : Fˣ => u ^ (tameDataOfValuation (laurentValuation F)).v a)
      (tameResidue_powerSeriesUnit F p))

/-- Power-series units pair trivially with one another. -/
theorem laurentTameSymbol_powerSeriesUnits (p q : (PowerSeries F)ˣ) :
    laurentTameSymbol F (powerSeriesLaurentUnit F p) (powerSeriesLaurentUnit F q) = 1 := by
  rw [laurentTameSymbol,
    (tameDataOfValuation (laurentValuation F)).tame_eq_one_of_mem_ker
      (powerSeriesLaurentUnit_mem_kernel F p) (powerSeriesLaurentUnit_mem_kernel F q)]
  exact map_one (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom)

/-- A unit with constant coefficient one is invisible to every tame pairing. -/
theorem laurentTameSymbol_principalUnit_left
    (p : (PowerSeries F)ˣ) (hp : powerSeriesResidueUnit F p = 1)
    (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F (powerSeriesLaurentUnit F p) a = 1 := by
  rw [laurentTameSymbol_powerSeriesUnit_left, hp, one_zpow]

theorem laurentTameSymbol_principalUnit_right
    (p : (PowerSeries F)ˣ) (hp : powerSeriesResidueUnit F p = 1)
    (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a (powerSeriesLaurentUnit F p) = 1 := by
  rw [laurentTameSymbol_antisymm, laurentTameSymbol_principalUnit_left F p hp, inv_one]

/-- Right-slot tame values depend only on the nonzero constant coefficient. -/
theorem laurentTameSymbol_eq_of_residue_eq
    (p q : (PowerSeries F)ˣ) (hpq : powerSeriesResidueUnit F p = powerSeriesResidueUnit F q)
    (a : (LaurentSeries F)ˣ) :
    laurentTameSymbol F a (powerSeriesLaurentUnit F p) =
      laurentTameSymbol F a (powerSeriesLaurentUnit F q) := by
  rw [laurentTameSymbol_antisymm F a, laurentTameSymbol_antisymm F a,
    laurentTameSymbol_powerSeriesUnit_left, laurentTameSymbol_powerSeriesUnit_left, hpq]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
