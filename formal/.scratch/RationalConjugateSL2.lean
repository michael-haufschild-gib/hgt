import GaloisForLFunctions.RHTower.SelbergMaassGLAutomorphicIntertwiner

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The determinant-one `SL(2,ℝ)` subgroup underlying a rationally conjugated
principal `GL(2,ℝ)` group. -/
def rationalConjugateSL2Group (N : ℕ) (g : GL (Fin 2) ℚ) : Subgroup SL2R :=
  (rationalConjugateGroup N g).comap sl2ToGL

/-- The determinant-one rational conjugate has no elements outside its
canonical `SL(2,ℝ)` preimage. -/
theorem rationalConjugateSL2Group_map_sl2ToGL (N : ℕ) (g : GL (Fin 2) ℚ) :
    (rationalConjugateSL2Group N g).map sl2ToGL = rationalConjugateGroup N g := by
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
    have hy : sl2ToGL y = x := by
      apply GeneralLinearGroup.ext
      intro i j
      rfl
    refine ⟨y, ?_, hy⟩
    change sl2ToGL y ∈ rationalConjugateGroup N g
    rw [hy]
    exact hx

end
end GaloisForLFunctions.RHTower
