import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentRotation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1Roots
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Degree rotation on the central loop group

Entrywise Laurent scaling lifts to the tame central extension and fixes its
center. The lift acts on a degree-`n` real-root parameter by multiplication
by `q^n`.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable {F : Type*} [Field F]

/-- Apply degree rotation to each entry of a Laurent special-linear matrix. -/
def sl2Rotation (q : Fˣ) : SL2 (LaurentSeries F) →* SL2 (LaurentSeries F) :=
  Matrix.SpecialLinearGroup.map (laurentRotation q).toRingHom

@[simp] theorem sl2Rotation_apply (q : Fˣ) (g : SL2 (LaurentSeries F)) (i j : Fin 2) :
    sl2Rotation q g i j = laurentRotation q (g i j) := rfl

/-- Field injectivity preserves the two branches of the Bruhat coordinate. -/
theorem kubotaUnit_rotation (q : Fˣ) (g : SL2 (LaurentSeries F)) :
    kubotaUnit (sl2Rotation q g) = laurentUnitRotation q (kubotaUnit g) := by
  apply Units.ext
  rw [coe_kubotaUnit, coe_laurentUnitRotation, coe_kubotaUnit]
  classical
  by_cases hg : g 1 0 = 0
  · have hsg : sl2Rotation q g 1 0 = 0 := by rw [sl2Rotation_apply, hg, map_zero]
    simp only [kubotaX, hg, hsg, if_true, sl2Rotation_apply]
  · have hsg : laurentRotation q (g 1 0) ≠ 0 := by
      intro hz
      apply hg
      apply (laurentRotation q).injective
      exact hz.trans (map_zero (laurentRotation q)).symm
    simp only [kubotaX, sl2Rotation_apply, hg, hsg, if_false]

/-- The image of the Kubota cocycle under the actual tame map is rotation-invariant. -/
theorem tame_kubotaCocycle_rotation (q : Fˣ) (g h : SL2 (LaurentSeries F)) :
    laurentTameHom F (kubotaCocycle (sl2Rotation q g) (sl2Rotation q h)) =
      laurentTameHom F (kubotaCocycle g h) := by
  simp only [kubotaCocycle, laurentTameHom_symbol]
  rw [← (sl2Rotation q).map_mul g h, kubotaUnit_rotation, kubotaUnit_rotation, kubotaUnit_rotation,
    ← map_div, ← map_div, laurentTameSymbol_rotation]

namespace LoopSL2

/-- Degree rotation on the central extension fixes the central coordinate. -/
def rotation (q : Fˣ) : LoopSL2 F ≃* LoopSL2 F where
  toFun g := ⟨sl2Rotation q g.base, g.centralCoord⟩
  invFun g := ⟨sl2Rotation q⁻¹ g.base, g.centralCoord⟩
  left_inv g := by
    apply SL2SymbolExtension.ext
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact laurentRotation_inv_apply q (g.base i j)
    · rfl
  right_inv g := by
    apply SL2SymbolExtension.ext
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact laurentRotation_apply_inv q (g.base i j)
    · rfl
  map_mul' g h := by
    apply SL2SymbolExtension.ext
    · exact (sl2Rotation q).map_mul g.base h.base
    · change g.centralCoord + h.centralCoord + laurentTameHom F (kubotaCocycle g.base h.base) =
        g.centralCoord + h.centralCoord +
          laurentTameHom F (kubotaCocycle (sl2Rotation q g.base) (sl2Rotation q h.base))
      rw [tame_kubotaCocycle_rotation]

@[simp] theorem rotation_base (q : Fˣ) (g : LoopSL2 F) :
    (rotation q g).base = sl2Rotation q g.base := rfl

@[simp] theorem rotation_centralCoord (q : Fˣ) (g : LoopSL2 F) :
    (rotation q g).centralCoord = g.centralCoord := rfl

@[simp] theorem rotation_centralEmbedding (q a : Fˣ) :
    rotation q (centralEmbedding F a) = centralEmbedding F a := by
  apply SL2SymbolExtension.ext
  · exact map_one (sl2Rotation q)
  · rfl

/-- The coefficient units act by actual automorphisms of the central loop group. -/
def rotationAction : Fˣ →* MulAut (LoopSL2 F) where
  toFun := rotation
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply SL2SymbolExtension.ext
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact laurentRotation_one (g.base i j)
    · rfl
  map_mul' q r := by
    apply MulEquiv.ext
    intro g
    apply SL2SymbolExtension.ext
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      exact laurentRotation_mul q r (g.base i j)
    · rfl

private theorem sl2Rotation_upper (q : Fˣ) (s : LaurentSeries F) :
    sl2Rotation q (sl2Upper s) = sl2Upper (laurentRotation q s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sl2Rotation_apply, sl2Upper]

private theorem sl2Rotation_lower (q : Fˣ) (s : LaurentSeries F) :
    sl2Rotation q (sl2Lower s) = sl2Lower (laurentRotation q s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sl2Rotation_apply, sl2Lower]

theorem rotation_upperRoot (q : Fˣ) (s : LaurentSeries F) :
    rotation q (upperRoot F (Multiplicative.ofAdd s)) =
      upperRoot F (Multiplicative.ofAdd (laurentRotation q s)) := by
  apply SL2SymbolExtension.ext
  · exact sl2Rotation_upper q s
  · rfl

theorem rotation_lowerRoot (q : Fˣ) (s : LaurentSeries F) :
    rotation q (lowerRoot F (Multiplicative.ofAdd s)) =
      lowerRoot F (Multiplicative.ofAdd (laurentRotation q s)) := by
  apply SL2SymbolExtension.ext
  · exact sl2Rotation_lower q s
  · rfl

/-- The actual root-group element for either string of affine real roots. -/
def realRootElement (β : AffineA1.Root) (a : F) : LoopSL2 F :=
  match β with
  | .plus n => upperRoot F (Multiplicative.ofAdd (HahnSeries.single n a))
  | .minus n => lowerRoot F (Multiplicative.ofAdd (HahnSeries.single n a))

/-- Rotation acts with the degree prescribed by the affine root datum. -/
theorem rotation_realRootElement (q : Fˣ) (β : AffineA1.Root) (a : F) :
    rotation q (realRootElement β a) =
      realRootElement β ((↑(q ^ β.corootZero) : F) * a) := by
  cases β with
  | plus n =>
    exact (rotation_upperRoot q (HahnSeries.single n a)).trans
      (congrArg (fun s => upperRoot F (Multiplicative.ofAdd s)) (laurentRotation_single q n a))
  | minus n =>
    exact (rotation_lowerRoot q (HahnSeries.single n a)).trans
      (congrArg (fun s => lowerRoot F (Multiplicative.ofAdd s)) (laurentRotation_single q n a))

end LoopSL2

/-- The central loop group together with its degree-rotation factor. -/
abbrev ExtendedLoopSL2 (F : Type*) [Field F] :=
  SemidirectProduct (LoopSL2 F) Fˣ LoopSL2.rotationAction

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
