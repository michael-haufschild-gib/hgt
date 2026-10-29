import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Coroots
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2Rotation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PowerSeriesTameSymbol

/-!
# Monomial translations in the central loop torus

The tame pairing of a constant and `X^n` is the constant to the power `n`.
Consequently monomial diagonal lifts have explicit central commutators, and
degree rotation produces a quadratic central factor. These are identities
inside the constructed loop group, rather than an abstract root datum.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The Laurent tame pairing as a homomorphism in its second argument. -/
def laurentTameRightHom (a : (LaurentSeries F)ˣ) : (LaurentSeries F)ˣ →* Fˣ where
  toFun := laurentTameSymbol F a
  map_one' := laurentTameSymbol_one_right F a
  map_mul' := laurentTameSymbol_mul_right F a

theorem laurentTameSymbol_zpow_right (a b : (LaurentSeries F)ˣ) (n : ℤ) :
    laurentTameSymbol F a (b ^ n) = laurentTameSymbol F a b ^ n :=
  map_zpow (laurentTameRightHom F a) b n

/-- Constants pair with monomials by their exact integer degree. -/
theorem laurentTameSymbol_constant_X_zpow (a : Fˣ) (n : ℤ) :
    laurentTameSymbol F (laurentConstantUnit F a) (laurentXUnit F ^ n) = a ^ n := by
  rw [laurentTameSymbol_zpow_right, laurentTameSymbol_constant_X]

theorem laurentTameSymbol_X_zpow_constant (n : ℤ) (a : Fˣ) :
    laurentTameSymbol F (laurentXUnit F ^ n) (laurentConstantUnit F a) = a ^ (-n) := by
  rw [laurentTameSymbol_antisymm, laurentTameSymbol_constant_X_zpow, zpow_neg]

@[simp] theorem laurentConstantUnit_zpow (a : Fˣ) (n : ℤ) :
    laurentConstantUnit F (a ^ n) = laurentConstantUnit F a ^ n :=
  map_zpow (Units.map ((HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C).toMonoidHom) a n

@[simp] theorem laurentUnitRotation_constant (q a : Fˣ) :
    laurentUnitRotation q (laurentConstantUnit F a) = laurentConstantUnit F a := by
  apply Units.ext
  change laurentRotation q ((HahnSeries.ofPowerSeries ℤ F) (PowerSeries.C (a : F))) =
    (HahnSeries.ofPowerSeries ℤ F) (PowerSeries.C (a : F))
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, laurentRotation_single]
  simp only [zpow_zero, Units.val_one, one_mul]

theorem laurentUnitRotation_X (q : Fˣ) :
    laurentUnitRotation q (laurentXUnit F) = laurentConstantUnit F q * laurentXUnit F := by
  apply Units.ext
  change laurentRotation q (HahnSeries.single (1 : ℤ) (1 : F)) =
    (HahnSeries.ofPowerSeries ℤ F) (PowerSeries.C (q : F)) * HahnSeries.single (1 : ℤ) (1 : F)
  rw [laurentRotation_single, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.single_mul_single]
  simp only [zpow_one, zero_add, mul_one]

/-- Rotation multiplies an integer monomial by the corresponding constant power. -/
theorem laurentUnitRotation_X_zpow (q : Fˣ) (n : ℤ) :
    laurentUnitRotation q (laurentXUnit F ^ n) =
      laurentConstantUnit F (q ^ n) * laurentXUnit F ^ n := by
  rw [map_zpow, laurentUnitRotation_X, mul_zpow, laurentConstantUnit_zpow]

namespace LoopSL2

/-- Conjugation of one diagonal lift by another records the inverse-square tame pairing. -/
theorem diagonalSection_conj (a b : (LaurentSeries F)ˣ) :
    diagonalSection F a * diagonalSection F b * (diagonalSection F a)⁻¹ =
      centralEmbedding F ((laurentTameSymbol F a b)⁻¹ * (laurentTameSymbol F a b)⁻¹) *
        diagonalSection F b := by
  have h := congrArg (fun g : LoopSL2 F => g * diagonalSection F b)
    (diagonalSection_commutator F a b)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- A representative of the affine Weyl translation indexed by `m`. -/
def translationLift (m : ℤ) : LoopSL2 F := diagonalSection F (laurentXUnit F ^ (-m))

/-- Monomial translation shifts the central coordinate of the finite coroot. -/
theorem translationLift_conj_finiteCoroot (m : ℤ) (a : Fˣ) :
    translationLift F m * finiteCoroot F a * (translationLift F m)⁻¹ =
      centralEmbedding F (a ^ (-2 * m)) * finiteCoroot F a := by
  rw [finiteCoroot_apply, translationLift, diagonalSection_conj,
    laurentTameSymbol_X_zpow_constant, neg_neg, ← zpow_neg, ← zpow_add,
    show -m + -m = -2 * m by ring]

/-- Rotation of any diagonal section is the section of its rotated Laurent unit. -/
theorem rotation_diagonalSection (q : Fˣ) (a : (LaurentSeries F)ˣ) :
    rotation q (diagonalSection F a) = diagonalSection F (laurentUnitRotation q a) := by
  apply SL2SymbolExtension.ext
  · change sl2Rotation q (sl2Diagonal a) = sl2Diagonal (laurentUnitRotation q a)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Rotation_apply, sl2Diagonal, laurentUnitRotation]
  · rfl

@[simp] theorem rotation_finiteCoroot (q a : Fˣ) :
    rotation q (finiteCoroot F a) = finiteCoroot F a := by
  rw [finiteCoroot_apply, rotation_diagonalSection, laurentUnitRotation_constant]

/-- Separating a constant from a monomial exposes its central degree factor. -/
theorem diagonalSection_constant_mul_X_zpow (a : Fˣ) (n : ℤ) :
    diagonalSection F (laurentConstantUnit F a * laurentXUnit F ^ n) =
      centralEmbedding F (a ^ n) * finiteCoroot F a * diagonalSection F (laurentXUnit F ^ n) := by
  symm
  rw [finiteCoroot_apply, mul_assoc, diagonalSection_mul,
    laurentTameSymbol_constant_X_zpow, ← mul_assoc, ← map_mul,
    mul_inv_cancel, map_one, one_mul]

/-- The square of the translation index is forced by the tame torus defect. -/
theorem rotation_translationLift (q : Fˣ) (m : ℤ) :
    rotation q (translationLift F m) =
      centralEmbedding F (q ^ (m * m)) * finiteCoroot F (q ^ (-m)) * translationLift F m := by
  rw [translationLift, rotation_diagonalSection, laurentUnitRotation_X_zpow,
    diagonalSection_constant_mul_X_zpow, ← zpow_mul, neg_mul_neg]

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
