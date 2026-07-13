import Mathlib

/-!
# Parseval's identity for a Hilbert basis and the Fourier basis

`hilbertBasis_norm_sq` is Parseval's identity `‖f‖² = ∑ᵢ ‖(repr f) i‖²` for any Hilbert basis,
and `fourier_parseval` is its specialization to the Fourier basis of `L²` of the unit additive
circle: `‖f‖² = ∑ₙ ‖fourierCoeff f n‖²`.  This is the `L²` norm–coefficient bridge used to obtain
`L²` boundary values of Hardy `H²` functions.
-/

open scoped ENNReal
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Parseval's identity.**  For a Hilbert basis `b`, the squared norm is the sum of the squared
moduli of the coordinates. -/
theorem hilbertBasis_norm_sq {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 E) (f : E) :
    ‖f‖ ^ 2 = ∑' i, ‖b.repr f i‖ ^ 2 := by
  have h2 := lp.norm_rpow_eq_tsum (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) (b.repr f)
  simp only [ENNReal.toReal_ofNat] at h2
  rw [show ‖f‖ = ‖b.repr f‖ from (b.repr.norm_map f).symm]
  simp only [← Real.rpow_natCast, Nat.cast_ofNat]
  exact h2

/-- **Parseval's identity for the Fourier basis** of `L²` of the unit additive circle:
`‖f‖² = ∑ₙ ‖fourierCoeff f n‖²`. -/
theorem fourier_parseval
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle 1 ⟨one_pos⟩)) :
    ‖f‖ ^ 2 = ∑' n : ℤ, ‖fourierCoeff (⇑f) n‖ ^ 2 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [hilbertBasis_norm_sq fourierBasis f]
  refine tsum_congr (fun n => ?_)
  rw [fourierBasis_repr]

/-- **`L²` distance equals `ℓ²` coefficient distance.**  The squared `L²` distance between two
Fourier synthesis functions is the `ℓ²` distance of their coefficient sequences.  With one sequence
a radial dilate of the other this yields the boundary convergence of Hardy `H²` functions. -/
theorem norm_sub_repr_symm_sq (a b : lp (fun _ : ℤ => ℂ) 2) :
    ‖(fourierBasis.repr.symm a : Lp ℂ 2 (@AddCircle.haarAddCircle 1 ⟨one_pos⟩))
        - fourierBasis.repr.symm b‖ ^ 2 = ∑' n : ℤ, ‖a n - b n‖ ^ 2 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [hilbertBasis_norm_sq fourierBasis]
  refine tsum_congr (fun n => ?_)
  rw [map_sub, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    lp.coeFn_sub, Pi.sub_apply]

end GaloisForLFunctions.HTGeometry
