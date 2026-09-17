import GaloisForLFunctions.RHTower.SelbergMaassRationalMackeyBlockSource
import GaloisForLFunctions.RHTower.SelbergMaassGLAutomorphicIntertwiner

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- Integral common cover of a principal source and one rationally conjugated
source. This is the source group on which both legs of a rational Hecke
correspondence can be represented by quotient `L²` spaces. -/
def rationalHeckeIntegralIntersection (N : ℕ) (g : GL (Fin 2) ℚ) :
    Subgroup SL2Z :=
  CongruenceSubgroup.Gamma (N + 1) ⊓
    (rationalConjugateGroup N g).comap (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The common integral cover has finite index in `SL(2, ℤ)`. -/
theorem rationalHeckeIntegralIntersection_finiteIndex (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalHeckeIntegralIntersection N g).FiniteIndex := by
  letI : NeZero (N + 1) := ⟨Nat.succ_ne_zero N⟩
  letI : (rationalConjugateGroup N g).IsArithmetic :=
    rationalConjugateGroup_isArithmetic N g
  letI : ((rationalConjugateGroup N g).comap
      (Matrix.SpecialLinearGroup.mapGL ℝ)).FiniteIndex :=
    Subgroup.IsArithmetic.finiteIndex_comap _
  change (CongruenceSubgroup.Gamma (N + 1) ⊓
    (rationalConjugateGroup N g).comap (Matrix.SpecialLinearGroup.mapGL ℝ)).FiniteIndex
  exact inferInstance

/-- The common cover is a finite deck over the principal source. -/
theorem rationalHeckeIntegralIntersection_isFiniteRelIndex_principal
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  letI : (rationalHeckeIntegralIntersection N g).FiniteIndex :=
    rationalHeckeIntegralIntersection_finiteIndex N g
  exact inferInstance

private theorem integralSL2ToReal_toGL_eq_mapGL_commonCover (x : SL2Z) :
    Matrix.SpecialLinearGroup.toGL (integralSL2ToReal x) =
      Matrix.SpecialLinearGroup.mapGL ℝ x := by
  have hcast : Int.castRingHom ℝ = algebraMap ℤ ℝ := by
    ext n
    rfl
  rw [integralSL2ToReal, hcast]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congr_fun
    (congr_fun (Matrix.SpecialLinearGroup.mapGL_coe_matrix (S := ℝ) x).symm i) j

/-- On real points, the common integral cover is exactly the intersection of
principal and rational-conjugate source groups. -/
theorem realImage_rationalHeckeIntegralIntersection (N : ℕ) (g : GL (Fin 2) ℚ) :
    realImage (rationalHeckeIntegralIntersection N g) =
      realImage (CongruenceSubgroup.Gamma (N + 1)) ⊓
        (rationalConjugateGroup N g).comap Matrix.SpecialLinearGroup.toGL := by
  ext x
  constructor
  · rintro ⟨a, ⟨haGamma, haRational⟩, rfl⟩
    constructor
    · exact ⟨a, haGamma, rfl⟩
    · change Matrix.SpecialLinearGroup.toGL (integralSL2ToReal a) ∈
        rationalConjugateGroup N g
      rw [integralSL2ToReal_toGL_eq_mapGL_commonCover]
      exact haRational
  · rintro ⟨⟨a, haGamma, haEq⟩, hxRational⟩
    refine ⟨a, ⟨haGamma, ?_⟩, haEq⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ a ∈ rationalConjugateGroup N g
    rw [← integralSL2ToReal_toGL_eq_mapGL_commonCover, haEq]
    exact hxRational

end

end GaloisForLFunctions.RHTower
