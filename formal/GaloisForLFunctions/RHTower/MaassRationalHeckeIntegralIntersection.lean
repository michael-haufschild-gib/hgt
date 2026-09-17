import GaloisForLFunctions.RHTower.SelbergMaassRationalMackeyBlockSource
import GaloisForLFunctions.RHTower.SelbergMaassGLAutomorphicIntertwiner

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The determinant-one subgroup underlying a rationally conjugated principal
source. -/
def rationalConjugateSL2Group (N : ℕ) (g : GL (Fin 2) ℚ) : Subgroup SL2R :=
  (rationalConjugateGroup N g).comap Matrix.SpecialLinearGroup.toGL

/-- The determinant-one source recovers the whole rationally conjugated group
under the standard embedding into `GL(2, ℝ)`. -/
theorem rationalConjugateSL2Group_map_toGL (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateSL2Group N g).map Matrix.SpecialLinearGroup.toGL =
      rationalConjugateGroup N g := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    let x' : rationalConjugateGroup N g := ⟨x, hx⟩
    have hdet : (x : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      have h := congrArg Units.val (rationalConjugateGroup_det_eq_one N g x')
      norm_num at h
      exact h
    let y : SL2R := ⟨x.val, hdet⟩
    have hy : Matrix.SpecialLinearGroup.toGL y = x := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl
    refine ⟨y, ?_, hy⟩
    change Matrix.SpecialLinearGroup.toGL y ∈ rationalConjugateGroup N g
    rw [hy]
    exact hx

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
        rationalConjugateSL2Group N g := by
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
