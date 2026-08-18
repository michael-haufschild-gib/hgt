import GaloisForLFunctions.HTGeometry.FourierCircleTruncation

/-!
# The inner product is dominated by the `ℓ¹` pairing of Fourier coefficients

For two square-integrable functions on the circle the inner product is the `ℓ²` pairing of their
Fourier coefficients, hence bounded by the (possibly larger) `ℓ¹` pairing of their moduli.  This is
the estimate a *pairing* argument needs: it converts a statement about one distinguished linear
functional into a coefficientwise sum, where a two-piece amplitude profile can be inserted.
-/

namespace GaloisForLFunctions

open MeasureTheory

/-- **The inner product is bounded coefficientwise.** -/
theorem norm_inner_le_tsum_fourierCoeff (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖(inner ℂ u v : ℂ)‖ ≤ ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
      * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖ := by
  have hexp : (inner ℂ u v : ℂ)
      = ∑' j : ℤ, (inner ℂ (fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)
          (fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j) : ℂ) := by
    rw [← (fourierBasis (T := (1 : ℝ))).repr.inner_map_map u v, lp.inner_eq_tsum]
    exact tsum_congr fun j => by rw [fourierBasis_repr, fourierBasis_repr]
  have hsummable : Summable fun j : ℤ =>
      (inner ℂ (fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)
        (fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j) : ℂ) := by
    have h := lp.summable_inner (𝕜 := ℂ) (G := fun _ : ℤ => ℂ)
      ((fourierBasis (T := (1 : ℝ))).repr u) ((fourierBasis (T := (1 : ℝ))).repr v)
    refine h.congr fun j => ?_
    rw [fourierBasis_repr, fourierBasis_repr]
  have hnormeq : ∀ j : ℤ,
      ‖(inner ℂ (fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j)
        (fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j) : ℂ)‖
        = ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
          * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖ := by
    intro j
    rw [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]
  rw [hexp]
  exact le_trans (norm_tsum_le_tsum_norm hsummable.norm) (le_of_eq (tsum_congr hnormeq))

/-- The same bound in `ℝ≥0∞`, in the form a vanishing-`tsum` argument consumes. -/
theorem ofReal_norm_inner_le_tsum_fourierCoeff
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ENNReal.ofReal ‖(inner ℂ u v : ℂ)‖
      ≤ ∑' j : ℤ, ENNReal.ofReal (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
        * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖) := by
  classical
  have hsummable : Summable fun j : ℤ =>
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
        * ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖ := by
    have h := lp.summable_inner (𝕜 := ℂ) (G := fun _ : ℤ => ℂ)
      ((fourierBasis (T := (1 : ℝ))).repr u) ((fourierBasis (T := (1 : ℝ))).repr v)
    refine (h.norm).congr fun j => ?_
    rw [fourierBasis_repr, fourierBasis_repr, RCLike.inner_apply, norm_mul, RCLike.norm_conj,
      mul_comm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_tsum_fourierCoeff u v)

end GaloisForLFunctions
