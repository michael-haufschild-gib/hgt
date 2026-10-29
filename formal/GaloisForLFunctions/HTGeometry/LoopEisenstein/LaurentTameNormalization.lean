import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentSL2Extension
import GaloisForLFunctions.HTGeometry.LaurentSeriesNormalization

/-!
# Constants and the Laurent uniformizer in the central extension

The tame symbol of a constant unit and `X` is that constant. Consequently the
commutator of their diagonal lifts is its inverse square. This identifies the
central-extension normalization on the actual Laurent monomial.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- A coefficient unit embedded as a constant Laurent series. -/
def laurentConstantUnit (a : Fˣ) : (LaurentSeries F)ˣ :=
  Units.map ((HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C).toMonoidHom a

@[simp] theorem coe_laurentConstantUnit (a : Fˣ) :
    (laurentConstantUnit F a : LaurentSeries F) =
      ((PowerSeries.C (a : F) : PowerSeries F) : LaurentSeries F) := rfl

/-- The actual Laurent monomial `X`, as a field unit. -/
def laurentXUnit : (LaurentSeries F)ˣ :=
  Units.mk0 (HahnSeries.single (1 : ℤ) (1 : F)) (HahnSeries.single_ne_zero one_ne_zero)

@[simp] theorem coe_laurentXUnit :
    (laurentXUnit F : LaurentSeries F) = HahnSeries.single (1 : ℤ) (1 : F) := rfl

private theorem constant_mem_valuation_kernel (a : Fˣ) :
    laurentConstantUnit F a ∈
      (tameValHom (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).ker := by
  rw [tameValHom_mem_ker_iff, coe_laurentConstantUnit]
  exact laurent_valuation_coe_powerSeries_eq_one_of_constantCoeff_ne_zero F
    (by simpa only [PowerSeries.constantCoeff_C] using a.ne_zero)

private theorem tameVal_X :
    (tameDataOfValuation
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).v
        (laurentXUnit F) = 1 := by
  have hcoe : ((tameUnzero
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
      (laurentXUnit F) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero, coe_laurentXUnit]
    exact LaurentSeries.valuation_single_zpow F 1
  have hu := WithZero.coe_inj.mp hcoe
  change Multiplicative.toAdd (tameValHom
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
      (laurentXUnit F)) = 1
  rw [tameValHom_toAdd, hu]
  rfl

private theorem residue_constant (a : Fˣ) :
    Units.map (ABHN.laurentSeriesResidueFieldEquiv F).toMonoidHom
      (tameResHom
        (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
        ⟨laurentConstantUnit F a, constant_mem_valuation_kernel F a⟩) = a := by
  apply Units.ext
  rw [Units.coe_map, tameResHom_val]
  change ABHN.laurentSeriesResidueFieldEquiv F
    (IsLocalRing.residue _
      (ABHN.laurentPowerSeriesEquivValuedInteger F (PowerSeries.C (a : F)))) = (a : F)
  rw [ABHN.laurentSeriesResidueFieldEquiv_residue_powerSeries, PowerSeries.constantCoeff_C]

/-- The tame symbol of a constant and `X` is the constant itself. -/
theorem laurentTameSymbol_constant_X (a : Fˣ) :
    laurentTameSymbol F (laurentConstantUnit F a) (laurentXUnit F) = a := by
  rw [laurentTameSymbol,
    (tameDataOfValuation
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))).tame_of_mem_ker_left
        (constant_mem_valuation_kernel F a), tameVal_X, zpow_one]
  exact residue_constant F a

/-- Every coefficient unit is attained by the Laurent tame homomorphism. -/
theorem laurentTameHom_surjective : Function.Surjective (laurentTameHom F) := by
  intro z
  refine ⟨milnorSym2 (LaurentSeries F) (laurentConstantUnit F z.toMul) (laurentXUnit F), ?_⟩
  rw [laurentTameHom_symbol, laurentTameSymbol_constant_X]
  rfl

/-- Constant and degree coroot lifts have the expected inverse-square commutator. -/
theorem constant_X_diagonal_commutator (a : Fˣ) :
    LoopSL2.diagonalSection F (laurentConstantUnit F a) *
      LoopSL2.diagonalSection F (laurentXUnit F) *
      (LoopSL2.diagonalSection F (laurentConstantUnit F a))⁻¹ *
      (LoopSL2.diagonalSection F (laurentXUnit F))⁻¹ =
      LoopSL2.centralEmbedding F (a⁻¹ * a⁻¹) := by
  rw [LoopSL2.diagonalSection_commutator, laurentTameSymbol_constant_X]

/-- The constant/degree commutator vanishes exactly for coefficient units of square one. -/
theorem constant_X_diagonal_commutator_eq_one_iff (a : Fˣ) :
    LoopSL2.diagonalSection F (laurentConstantUnit F a) *
      LoopSL2.diagonalSection F (laurentXUnit F) *
      (LoopSL2.diagonalSection F (laurentConstantUnit F a))⁻¹ *
      (LoopSL2.diagonalSection F (laurentXUnit F))⁻¹ = 1 ↔ a * a = 1 := by
  rw [constant_X_diagonal_commutator]
  constructor
  · intro h
    have hi : a⁻¹ * a⁻¹ = 1 := LoopSL2.centralEmbedding_injective F
      (h.trans (map_one (LoopSL2.centralEmbedding F)).symm)
    simpa using congrArg (fun u : Fˣ => u⁻¹) hi
  · intro h
    have hi : a⁻¹ * a⁻¹ = 1 := by
      simpa using congrArg (fun u : Fˣ => u⁻¹) h
    rw [hi, map_one]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
