import GaloisForLFunctions.RHTower.VectorFourierPlancherelIntegral
import GaloisForLFunctions.HTGeometry.FourierFirstOrderWeight
import GaloisForLFunctions.RHTower.WallBlockSliceProfile

/-!
# Multiplication by the frequency is differentiation of the profile

In the angular convention the Fourier weight identity carries no constant:

`|z| · ‖ĥ(z)‖ = ‖(h′)^(z)‖`.

On a block slice the differentiated profile is the weighted corrected derivative
`e^{-Ls}(g′(L) − s g(L))`: the Laplace weight contributes its own `−s`.  That is the exact reason
the derivative statement costs one power of the block's `H¹` norm *and* one power of the Laplace
variable — the second of which the accretive semigroup absorbs.
-/

open MeasureTheory Real
open scoped FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Multiplication by the frequency is differentiation of the profile.**  In the angular
convention the constant is exactly one. -/
theorem norm_freq_smul_vectorAngularTransform_eq {h : ℝ → H} (hh : Integrable h)
    (hh' : Differentiable ℝ h) (hdh : Integrable (deriv h)) (z : ℝ) :
    |z| * ‖vectorAngularTransform h z‖ = ‖vectorAngularTransform (deriv h) z‖ := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbase := GaloisForLFunctions.HTGeometry.norm_freq_smul_fourier_eq hh hh' hdh
    (z / (2 * Real.pi))
  rw [vectorAngularTransform_eq_fourier, vectorAngularTransform_eq_fourier]
  have habs : |z / (2 * Real.pi)| = |z| / (2 * Real.pi) := by
    rw [abs_div, abs_of_pos hpi]
  rw [habs] at hbase
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  field_simp at hbase ⊢
  linarith [hbase]

omit [CompleteSpace H] in
/-- The weighted block profile is differentiable, with the weighted corrected derivative. -/
theorem hasDerivAt_blockWeighted {g g' : ℝ → H} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L) (s L : ℝ) :
    HasDerivAt (blockWeighted g s) (blockWeighted (fun M => g' M - s • g M) s L) L := by
  have hexp : HasDerivAt (fun M : ℝ => Real.exp (-(M * s))) (-s * Real.exp (-(L * s))) L := by
    have h := (((hasDerivAt_id L).mul_const s).neg).exp
    refine h.congr_deriv ?_
    simp
    ring
  have h := hexp.smul (hg L)
  refine h.congr_deriv ?_
  rw [blockWeighted, smul_sub, smul_smul]
  ring_nf
  module

omit [CompleteSpace H] in
/-- The derivative of the weighted block profile, as a function. -/
theorem deriv_blockWeighted {g g' : ℝ → H} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L) (s : ℝ) :
    deriv (blockWeighted g s) = blockWeighted (fun M => g' M - s • g M) s := by
  funext L
  exact (hasDerivAt_blockWeighted hg s L).deriv

omit [CompleteSpace H] in
/-- **Multiplication by the frequency on a block slice.** -/
theorem norm_freq_smul_blockSlice_eq {g g' : ℝ → H} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    {s : ℝ} (hint : Integrable (blockWeighted g s))
    (hdint : Integrable (blockWeighted (fun M => g' M - s • g M) s)) (x : ℝ) :
    |x| * ‖blockSlice g s x‖ = ‖blockSlice (fun M => g' M - s • g M) s x‖ := by
  have hdiff : Differentiable ℝ (blockWeighted g s) := fun L =>
    (hasDerivAt_blockWeighted hg s L).differentiableAt
  have hderiv : Integrable (deriv (blockWeighted g s)) := by
    rw [deriv_blockWeighted hg s]
    exact hdint
  have h := norm_freq_smul_vectorAngularTransform_eq hint hdiff hderiv x
  rw [blockSlice, blockSlice, h, deriv_blockWeighted hg s]

end GaloisForLFunctions.RHTower
