import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveBorelCoordinates
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2DiagonalRescaling

/-!
# Constant and affine coefficient-field matrices

Constant matrices embed in the positive-loop splitting. Rescaling the two
off-diagonal entries by inverse powers of `X` gives the matrix projection
of the affine simple rank-one subgroup.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The actual coefficient-field homomorphism into the Laurent field. -/
def laurentConstantRingHom : F →+* LaurentSeries F :=
  (HahnSeries.ofPowerSeries ℤ F).comp PowerSeries.C

/-- Constant matrices in the positive-loop matrix group. -/
def constantPowerSeriesSL2Map : SL2 F →* PowerSeriesSL2 F :=
  Matrix.SpecialLinearGroup.map (PowerSeries.C : F →+* PowerSeries F)

@[simp] theorem constantPowerSeriesSL2Map_apply (g : SL2 F) (i j : Fin 2) :
    constantPowerSeriesSL2Map F g i j = PowerSeries.C (g i j) := rfl

theorem constantPowerSeriesSL2Map_injective : Function.Injective (constantPowerSeriesSL2Map F) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h' := congrArg (fun p : PowerSeriesSL2 F => PowerSeries.constantCoeff (p i j)) he
  simpa only [constantPowerSeriesSL2Map_apply, PowerSeries.constantCoeff_C] using h'

/-- Constant coefficient-field matrices in the Laurent matrix group. -/
def constantLaurentSL2Map : SL2 F →* SL2 (LaurentSeries F) :=
  (powerSeriesSL2Map F).comp (constantPowerSeriesSL2Map F)

@[simp] theorem constantLaurentSL2Map_apply (g : SL2 F) (i j : Fin 2) :
    constantLaurentSL2Map F g i j = laurentConstantRingHom F (g i j) := rfl

theorem constantLaurentSL2Map_injective : Function.Injective (constantLaurentSL2Map F) :=
  (powerSeriesSL2Map_injective F).comp (constantPowerSeriesSL2Map_injective F)

@[simp] theorem constantLaurentSL2Map_upper (s : F) :
    constantLaurentSL2Map F (sl2Upper s) = sl2Upper (laurentConstantRingHom F s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [constantLaurentSL2Map_apply, sl2Upper]

@[simp] theorem constantLaurentSL2Map_lower (s : F) :
    constantLaurentSL2Map F (sl2Lower s) = sl2Lower (laurentConstantRingHom F s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [constantLaurentSL2Map_apply, sl2Lower]

@[simp] theorem constantLaurentSL2Map_diagonal (a : Fˣ) :
    constantLaurentSL2Map F (sl2Diagonal a) = sl2Diagonal (laurentConstantUnit F a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [constantLaurentSL2Map_apply, sl2Diagonal, laurentConstantUnit, laurentConstantRingHom]

/-- Odd-degree rescaling realizes the affine simple SL₂ at the matrix level. -/
def affineConstantSL2Map : SL2 F →* SL2 (LaurentSeries F) :=
  (sl2Rescale (laurentXUnit F)⁻¹).comp (constantLaurentSL2Map F)

theorem affineConstantSL2Map_injective : Function.Injective (affineConstantSL2Map F) :=
  (sl2Rescale_injective _).comp (constantLaurentSL2Map_injective F)

@[simp] theorem affineConstantSL2Map_zero_zero (g : SL2 F) :
    affineConstantSL2Map F g 0 0 = laurentConstantRingHom F (g 0 0) := rfl

@[simp] theorem affineConstantSL2Map_zero_one (g : SL2 F) :
    affineConstantSL2Map F g 0 1 =
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        laurentConstantRingHom F (g 0 1) := rfl

@[simp] theorem affineConstantSL2Map_one_zero (g : SL2 F) :
    affineConstantSL2Map F g 1 0 =
      (laurentXUnit F : LaurentSeries F) * laurentConstantRingHom F (g 1 0) := by
  change ((((laurentXUnit F)⁻¹)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * _ = _
  rw [inv_inv, constantLaurentSL2Map_apply]

@[simp] theorem affineConstantSL2Map_one_one (g : SL2 F) :
    affineConstantSL2Map F g 1 1 = laurentConstantRingHom F (g 1 1) := rfl

/-- The upper parameter has degree minus one in the affine rank-one copy. -/
def affineUpperParameter (s : F) : LaurentSeries F :=
  (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * laurentConstantRingHom F s

/-- The lower parameter has degree one in the affine rank-one copy. -/
def affineLowerParameter (s : F) : LaurentSeries F :=
  (laurentXUnit F : LaurentSeries F) * laurentConstantRingHom F s

@[simp] theorem affineConstantSL2Map_upper (s : F) :
    affineConstantSL2Map F (sl2Upper s) = sl2Upper (affineUpperParameter F s) := by
  change sl2Rescale (laurentXUnit F)⁻¹ (constantLaurentSL2Map F (sl2Upper s)) = _
  rw [constantLaurentSL2Map_upper, sl2Rescale_upper]
  rfl

@[simp] theorem affineConstantSL2Map_lower (s : F) :
    affineConstantSL2Map F (sl2Lower s) = sl2Lower (affineLowerParameter F s) := by
  change sl2Rescale (laurentXUnit F)⁻¹ (constantLaurentSL2Map F (sl2Lower s)) = _
  rw [constantLaurentSL2Map_lower, sl2Rescale_lower, inv_inv]
  rfl

@[simp] theorem affineConstantSL2Map_diagonal (a : Fˣ) :
    affineConstantSL2Map F (sl2Diagonal a) = sl2Diagonal (laurentConstantUnit F a) := by
  change sl2Rescale (laurentXUnit F)⁻¹ (constantLaurentSL2Map F (sl2Diagonal a)) = _
  rw [constantLaurentSL2Map_diagonal, sl2Rescale_diagonal]

namespace LoopSL2

/-- The actual finite simple rank-one subgroup, via the positive-loop splitting. -/
def finiteSL2Embedding : SL2 F →* LoopSL2 F :=
  (positiveEmbedding F).comp (constantPowerSeriesSL2Map F)

theorem finiteSL2Embedding_injective : Function.Injective (finiteSL2Embedding F) :=
  (positiveEmbedding_injective F).comp (constantPowerSeriesSL2Map_injective F)

@[simp] theorem projection_finiteSL2Embedding (g : SL2 F) :
    projection F (finiteSL2Embedding F g) = constantLaurentSL2Map F g :=
  projection_positiveEmbedding F _

theorem finiteSL2Embedding_upper (s : F) :
    finiteSL2Embedding F (sl2Upper s) =
      upperRoot F (Multiplicative.ofAdd (laurentConstantRingHom F s)) := by
  change positiveEmbedding F
    (Matrix.SpecialLinearGroup.map (PowerSeries.C : F →+* PowerSeries F) (FiniteRingSl2.upper s)) = _
  rw [FiniteRingSl2.map_upper, positiveEmbedding_upper]
  rfl

theorem finiteSL2Embedding_lower (s : F) :
    finiteSL2Embedding F (sl2Lower s) =
      lowerRoot F (Multiplicative.ofAdd (laurentConstantRingHom F s)) := by
  change positiveEmbedding F
    (Matrix.SpecialLinearGroup.map (PowerSeries.C : F →+* PowerSeries F) (FiniteRingSl2.lower s)) = _
  rw [FiniteRingSl2.map_lower, positiveEmbedding_lower]
  rfl

theorem finiteSL2Embedding_diagonal (a : Fˣ) :
    finiteSL2Embedding F (sl2Diagonal a) = finiteCoroot F a := by
  have h : constantPowerSeriesSL2Map F (sl2Diagonal a) =
      powerSeriesDiagonal F (powerSeriesConstantUnit F a) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [constantPowerSeriesSL2Map_apply, sl2Diagonal, powerSeriesDiagonal, powerSeriesConstantUnit]
  change positiveEmbedding F (constantPowerSeriesSL2Map F (sl2Diagonal a)) = _
  rw [h]
  exact positiveEmbedding_iwahoriFiniteCoroot F a

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
