import GaloisForLFunctions.RHTower.GaussUniformTranslationL2

/-!
# The rotation multiplier is translation

On the Fourier side, translation by `δ` is the unitary diagonal `e_(-j)(δ)`.  The two descriptions
are identified here, so the moving target of equation (9) can be handled either coefficientwise —
which is how the estimate is proved — or pointwise, which is how the iterated principal action of
§4 composes it with the multiplication operators.
-/

namespace RHTower

open Filter Topology MeasureTheory

noncomputable section

/-- Translation by `δ` on `L²(ℝ/ℤ)`, as a linear isometry. -/
def gaussTranslationBlock (δ : AddCircle (1 : ℝ)) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →ₗᵢ[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : AddCircle (1 : ℝ) => z - δ)
    (measurePreserving_sub_right AddCircle.haarAddCircle δ)

theorem coeFn_gaussTranslationBlock (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ((gaussTranslationBlock δ u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => (u : AddCircle (1 : ℝ) → ℂ) (z - δ) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right AddCircle.haarAddCircle δ)

theorem fourierCoeff_gaussTranslationBlock (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    fourierCoeff ((gaussTranslationBlock δ u :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j
      = fourier (-j) δ * fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j := by
  rw [fourierCoeff_congr_ae (coeFn_gaussTranslationBlock δ u) j]
  exact GaloisForLFunctions.fourierCoeff_comp_sub ((u : AddCircle (1 : ℝ) → ℂ)) j δ

/-- **The rotation multiplier is translation.** -/
theorem gaussRotationBlock_eq_translation (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussRotationBlock δ u = gaussTranslationBlock δ u := by
  refine (fourierBasis (T := (1 : ℝ))).repr.injective ?_
  refine lp.ext (funext fun j => ?_)
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_gaussRotationBlock,
    fourierCoeff_gaussTranslationBlock]

theorem fourier_neg_neg (j : ℤ) (δ : AddCircle (1 : ℝ)) :
    fourier (-j) (-δ) = fourier j δ := by
  rw [fourier_apply, fourier_apply, neg_smul_neg]

/-- The inverse rotation is translation by `-δ`. -/
theorem gaussRotationBlockInv_eq_translation (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussRotationBlockInv δ u = gaussTranslationBlock (-δ) u := by
  refine (fourierBasis (T := (1 : ℝ))).repr.injective ?_
  refine lp.ext (funext fun j => ?_)
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_gaussRotationBlockInv,
    fourierCoeff_gaussTranslationBlock, fourier_neg_neg]

end

end RHTower
