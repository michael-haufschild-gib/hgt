import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.RHTower.DeningerMultiplicativeGreenTransgression
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesMellinResponse
import GaloisForLFunctions.RHTower.DeningerStationaryKahlerGerm

noncomputable section

namespace RHTower

/-- Multiplication by logarithmic weight as a complex-linear endomorphism. -/
def deningerLogWeightEnd : Module.End ℂ (ℝ → ℂ) where
  toFun := deningerLogWeight
  map_add' F G := by
    funext x
    simp [deningerLogWeight, add_mul]
  map_smul' c F := by
    funext x
    simp [deningerLogWeight, mul_assoc]

/-- Multiplicative inversion as a complex-linear endomorphism. -/
def deningerMultInversionEnd : Module.End ℂ (ℝ → ℂ) where
  toFun := deningerMultInversion
  map_add' F G := by
    funext x
    simp [deningerMultInversion, mul_add]
  map_smul' c F := by
    funext x
    simp [deningerMultInversion]
    ring

/-- Logarithmic weight and multiplicative inversion form a split supertranslation sector. -/
def deningerMultiplicativeReflectionD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℂ (ℝ → ℂ)) :=
  SuperPoincare.D1N2Split.ofEqNeg
    deningerLogWeightEnd deningerMultInversionEnd (by
      apply LinearMap.ext
      intro F
      funext x
      exact deningerLogWeight_reflection F x)

/-- Squared multiplicative inversion is identity off zero and kills the singular point. -/
theorem deningerMultiplicativeReflection_momentum1_apply
    (F : ℝ → ℂ) (x : ℝ) :
    deningerMultiplicativeReflectionD1N2Split.momentum1 F x =
      if x = 0 then 0 else F x := by
  change deningerMultInversion (deningerMultInversion F) x = _
  by_cases hx : x = 0
  · simp [hx, deningerMultInversion]
  · rw [if_neg hx]
    simp [deningerMultInversion, hx]

/-- Critical Gamma-sewn Stokes frequency and prime-lattice reflection form split supercharges. -/
def gammaStokesReflectionD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℂ DeningerHeightKothe) :=
  SuperPoincare.D1N2Split.ofEqNeg
    (gammaSewnMobiusApertureStokesKotheOperator 1 (by norm_num))
    deningerHeightReflect (by
      apply LinearMap.ext
      intro a
      exact gammaSewnMobiusApertureStokesKotheOperator_reflect
        (by norm_num) a)

/-- Prime-lattice reflection generates identity momentum. -/
theorem gammaStokesReflection_momentum1_eq_one :
    gammaStokesReflectionD1N2Split.momentum1 = 1 := by
  apply LinearMap.ext
  exact deningerHeightReflect_involutive

/-- Leaf-orientation sign as a real-linear endomorphism. -/
def deningerGermSigmaOneEnd : Module.End ℝ (ℝ × ℝ) where
  toFun := deningerGermSigmaOne
  map_add' a b := by
    rcases a with ⟨a0, a1⟩
    rcases b with ⟨b0, b1⟩
    ext <;> simp [deningerGermSigmaOne, add_comm]
  map_smul' c a := by
    rcases a with ⟨a0, a1⟩
    ext <;> simp [deningerGermSigmaOne]

/-- Leafwise Hodge star as a real-linear endomorphism. -/
def deningerLeafStarEnd : Module.End ℝ (ℝ × ℝ) where
  toFun := deningerLeafStar
  map_add' a b := by
    rcases a with ⟨a0, a1⟩
    rcases b with ⟨b0, b1⟩
    ext <;> simp [deningerLeafStar, add_comm]
  map_smul' c a := by
    rcases a with ⟨a0, a1⟩
    ext <;> simp [deningerLeafStar]

/-- Leaf orientation and Hodge star form a split sector with opposite signed momenta. -/
def deningerGermHodgeD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℝ (ℝ × ℝ)) :=
  SuperPoincare.D1N2Split.ofEqNeg
    deningerGermSigmaOneEnd deningerLeafStarEnd (by
      apply LinearMap.ext
      exact deningerGermSigmaOne_star)

/-- Orientation sign generates positive unit momentum. -/
theorem deningerGermHodge_momentum0_eq_one :
    deningerGermHodgeD1N2Split.momentum0 = 1 := by
  apply LinearMap.ext
  exact deningerGermSigmaOne_involutive

/-- Leafwise Hodge star generates negative unit momentum. -/
theorem deningerGermHodge_momentum1_eq_neg_one :
    deningerGermHodgeD1N2Split.momentum1 = -1 := by
  apply LinearMap.ext
  exact deningerLeafStar_star

end RHTower
