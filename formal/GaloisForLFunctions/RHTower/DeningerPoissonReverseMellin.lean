import GaloisForLFunctions.RHTower.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.DeningerPoissonCokernel

/-!
# The reverse Mellin estimate on a line far to the right

On the line `Re s = 2` the zeta function is bounded below by `1/4`, so the factorization
`M(Zf) = ζ·M(f)` can be inverted there: the Mellin transform of a member of Meyer's space is
bounded by four times that of its Poisson sum.

This is the half of strictness that needs no information about the zeros of `ζ`: to the right of
the Euler product region the multiplier is invertible for elementary reasons.  The remaining half
lives on a line to the left of the critical strip, where the functional equation converts the same
elementary bound into a lower bound with polynomial loss.

* `norm_mellin_le_of_two_le_re` : **`‖M(f)(s)‖ ≤ 4‖M(Zf)(s)‖` for `Re s ≥ 2`.**
* `norm_mellin_le_radial` : the same against the radial presentation of `Zf`.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-- **The reverse Mellin estimate**: to the right of the Euler product region the Poisson sum
controls the function. -/
theorem norm_mellin_le_of_two_le_re (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖mellin (f : ℝ → ℂ) s‖ ≤ 4 * ‖mellin (deningerPoissonValue f) s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hfac := mellin_deningerPoissonValue f hs1
  have hzeta := norm_riemannZeta_ge_of_two_le_re hs
  have hnorm : ‖mellin (deningerPoissonValue f) s‖
      = ‖riemannZeta s‖ * ‖mellin (f : ℝ → ℂ) s‖ := by
    rw [hfac, norm_mul]
  have hnn : 0 ≤ ‖mellin (f : ℝ → ℂ) s‖ := norm_nonneg _
  have hstep : (1 : ℝ) / 4 * ‖mellin (f : ℝ → ℂ) s‖
      ≤ ‖riemannZeta s‖ * ‖mellin (f : ℝ → ℂ) s‖ :=
    mul_le_mul_of_nonneg_right hzeta hnn
  rw [hnorm]
  linarith

/-- The reverse estimate against the radial presentation of the image. -/
theorem norm_mellin_le_radial (f : DeningerMeyerCap) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖mellin ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s‖
      ≤ 4 * ‖mellin (deningerRadialValue (deningerPoissonLM f)) s‖ := by
  rw [mellin_deningerRadialValue_poisson f s]
  exact norm_mellin_le_of_two_le_re (f : 𝓢(ℝ, ℂ)) hs

end RHTower

end
