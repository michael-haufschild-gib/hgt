import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentTameNormalization
import GaloisForLFunctions.HTGeometry.SkewLaurentCoefficientTrace

/-!
# Degree scaling on the Laurent field

The coefficientwise automorphism `X ↦ qX` preserves the Laurent valuation and
the residue of every integral series. These are the two invariants entering
the tame central extension.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {F : Type*} [Field F]

/-- The canonical Laurent valuation, with its value group made explicit. -/
abbrev laurentValuation (F : Type*) [Field F] :
    Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)) := Valued.v

/-- Rotate the Laurent variable by a coefficient unit. -/
def laurentRotation (q : Fˣ) : LaurentSeries F ≃+* LaurentSeries F :=
  quantumLaurentScaleAut q

@[simp] theorem laurentRotation_coeff (q : Fˣ) (f : LaurentSeries F) (n : ℤ) :
    (laurentRotation q f).coeff n = (↑(q ^ n) : F) * f.coeff n := rfl

/-- Scaling a variable preserves its Laurent valuation. -/
theorem laurentRotation_valuation (q : Fˣ) (f : LaurentSeries F) :
    laurentValuation F (laurentRotation q f) = laurentValuation F f := by
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero]
  have hsf : laurentRotation q f ≠ 0 := by
    intro h
    exact hf ((laurentRotation q).injective (h.trans (map_zero (laurentRotation q)).symm))
  have hvf := (Valuation.ne_zero_iff (laurentValuation F)).2 hf
  have hvs := (Valuation.ne_zero_iff (laurentValuation F)).2 hsf
  apply le_antisymm
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvf).2
    intro n hn
    rw [laurentRotation_coeff,
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvf).1 le_rfl n hn,
      mul_zero]
  · apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvs).2
    intro n hn
    have hz := (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F hvs).1 le_rfl n hn
    rw [laurentRotation_coeff] at hz
    exact (mul_eq_zero.mp hz).resolve_left (q ^ n).ne_zero

/-- Reduction to the coefficient field through the canonical residue equivalence. -/
def laurentResidue (f : (laurentValuation F).integer) : F :=
  ABHN.laurentSeriesResidueFieldEquiv F (IsLocalRing.residue _ f)

/-- The residue of any integral Laurent series is its coefficient of degree zero. -/
theorem laurentResidue_eq_coeff_zero (f : (laurentValuation F).integer) :
    laurentResidue f = (f : LaurentSeries F).coeff 0 := by
  obtain ⟨p, hp⟩ := (LaurentSeries.val_le_one_iff_eq_coe F (f : LaurentSeries F)).1 f.property
  have he : f = ABHN.laurentPowerSeriesEquivValuedInteger F p := Subtype.ext hp.symm
  rw [he]
  change ABHN.laurentSeriesResidueFieldEquiv F
    (IsLocalRing.residue _ (ABHN.laurentPowerSeriesEquivValuedInteger F p)) =
      ((HahnSeries.ofPowerSeries ℤ F) p).coeff 0
  rw [ABHN.laurentSeriesResidueFieldEquiv_residue_powerSeries]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero] using
    (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) p 0).symm

/-- Rotate an invertible Laurent series. -/
def laurentUnitRotation (q : Fˣ) : (LaurentSeries F)ˣ →* (LaurentSeries F)ˣ :=
  Units.map (laurentRotation q).toMonoidHom

@[simp] theorem coe_laurentUnitRotation (q : Fˣ) (a : (LaurentSeries F)ˣ) :
    (laurentUnitRotation q a : LaurentSeries F) = laurentRotation q (a : LaurentSeries F) := rfl

/-- The integer valuation used in the tame symbol is rotation-invariant. -/
theorem laurentUnitRotation_tameVal (q : Fˣ) (a : (LaurentSeries F)ˣ) :
    (tameDataOfValuation (laurentValuation F)).v (laurentUnitRotation q a) =
      (tameDataOfValuation (laurentValuation F)).v a := by
  have hu : tameUnzero (laurentValuation F) (laurentUnitRotation q a) =
      tameUnzero (laurentValuation F) a := by
    apply WithZero.coe_inj.mp
    rw [coe_tameUnzero, coe_tameUnzero, coe_laurentUnitRotation, laurentRotation_valuation]
  change Multiplicative.toAdd (tameValHom (laurentValuation F) (laurentUnitRotation q a)) =
    Multiplicative.toAdd (tameValHom (laurentValuation F) a)
  rw [tameValHom_toAdd, tameValHom_toAdd, hu]

private theorem tameResidue_coe_eq_coeff_zero (a : (LaurentSeries F)ˣ)
    (ha : a ∈ (tameValHom (laurentValuation F)).ker) :
    (Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom
      (tameResHom (laurentValuation F) ⟨a, ha⟩) : F) = (a : LaurentSeries F).coeff 0 := by
  change laurentResidue
    (⟨(a : LaurentSeries F), tame_mem_valuationSubring (laurentValuation F) ha⟩ :
      (laurentValuation F).integer) = (a : LaurentSeries F).coeff 0
  exact laurentResidue_eq_coeff_zero _

/-- The tame symbol is the degree-zero coefficient of its valuation-zero unit. -/
theorem laurentTameSymbol_coe_eq_coeff_zero (a b : (LaurentSeries F)ˣ) :
    (laurentTameSymbol F a b : F) =
      (((tameDataOfValuation (laurentValuation F)).symbolUnit a b :
        (LaurentSeries F)ˣ) : LaurentSeries F).coeff 0 :=
  tameResidue_coe_eq_coeff_zero _
    ((tameDataOfValuation (laurentValuation F)).symbolUnit_mem a b)

@[simp] theorem laurentUnitRotation_neg_one (q : Fˣ) :
    laurentUnitRotation q (-1) = -1 := by
  apply Units.ext
  change laurentRotation q (-1) = -1
  rw [map_neg, map_one]

private theorem symbolUnit_rotation (q : Fˣ) (a b : (LaurentSeries F)ˣ) :
    (tameDataOfValuation (laurentValuation F)).symbolUnit
        (laurentUnitRotation q a) (laurentUnitRotation q b) =
      laurentUnitRotation q ((tameDataOfValuation (laurentValuation F)).symbolUnit a b) := by
  simp only [TameData.symbolUnit, laurentUnitRotation_tameVal, map_mul, map_zpow,
    laurentUnitRotation_neg_one]

/-- Degree rotation preserves the actual tame symbol. -/
theorem laurentTameSymbol_rotation (q : Fˣ) (a b : (LaurentSeries F)ˣ) :
    laurentTameSymbol F (laurentUnitRotation q a) (laurentUnitRotation q b) =
      laurentTameSymbol F a b := by
  apply Units.ext
  rw [laurentTameSymbol_coe_eq_coeff_zero, laurentTameSymbol_coe_eq_coeff_zero,
    symbolUnit_rotation, coe_laurentUnitRotation, laurentRotation_coeff]
  simp only [zpow_zero, Units.val_one, one_mul]

@[simp] theorem laurentRotation_one (f : LaurentSeries F) : laurentRotation 1 f = f := by
  exact congrArg (fun e : RingAut (LaurentSeries F) => e f)
    (map_one (quantumLaurentScaleHom (F := F)))

theorem laurentRotation_mul (q r : Fˣ) (f : LaurentSeries F) :
    laurentRotation (q * r) f = laurentRotation q (laurentRotation r f) := by
  exact congrArg (fun e : RingAut (LaurentSeries F) => e f)
    (map_mul (quantumLaurentScaleHom (F := F)) q r)

@[simp] theorem laurentRotation_inv_apply (q : Fˣ) (f : LaurentSeries F) :
    laurentRotation q⁻¹ (laurentRotation q f) = f := by
  rw [← laurentRotation_mul, inv_mul_cancel, laurentRotation_one]

@[simp] theorem laurentRotation_apply_inv (q : Fˣ) (f : LaurentSeries F) :
    laurentRotation q (laurentRotation q⁻¹ f) = f := by
  rw [← laurentRotation_mul, mul_inv_cancel, laurentRotation_one]

/-- A degree-`n` monomial acquires precisely the factor `q^n`. -/
theorem laurentRotation_single (q : Fˣ) (n : ℤ) (a : F) :
    laurentRotation q (HahnSeries.single n a) =
      HahnSeries.single n ((↑(q ^ n) : F) * a) := by
  ext k
  by_cases hk : k = n
  · subst k
    simp [laurentRotation_coeff]
  · simp [laurentRotation_coeff, hk]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
