import GaloisForLFunctions.HTGeometry.FourierCircleTruncation
import GaloisForLFunctions.HTGeometry.FourierCircleTranslation
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# A bounded multiplier on a finite Fourier truncation

Multiplication by a bounded symbol `c` mixes frequencies, and in general the coefficients of
`c · w` are an infinite convolution.  On a *truncation* the sum is finite and needs no convergence
argument at all:

`(c · w_S)^(l) = ∑_{j ∈ S} ŵ(j) ĉ(l - j)`.

If `S` and `l` are separated — the situation in every far-band estimate — every kernel entry
`ĉ(l - j)` is uniformly small, and the whole coefficient is bounded by that uniform size times the
`ℓ¹` mass of the truncated coefficients.  This is the substitute for a convolution theorem in the
band-split estimates.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions

noncomputable section

variable {c : AddCircle (1 : ℝ) → ℂ}

/-- Multiplying an exponential monomial by a bounded symbol shifts the symbol's index. -/
theorem fourierCoeff_lpBoundedMulCLM_fourierLp (hc : Measurable c) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖c x‖ ≤ C) (j l : ℤ) :
    fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC
        (fourierLp (T := (1 : ℝ)) 2 j) : AddCircle (1 : ℝ) → ℂ)) l
      = fourierCoeff c (l - j) := by
  have hae : ((MeasureTheory.lpBoundedMulCLM (p := 2)
      (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC
      (fourierLp (T := (1 : ℝ)) 2 j) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => fourier j z * c z := by
    filter_upwards [MeasureTheory.lpBoundedMulCLM_coeFn hc hC0 hC
      (fourierLp (T := (1 : ℝ)) 2 j), coeFn_fourierLp (T := (1 : ℝ)) 2 j] with z h1 h2
    rw [h1, h2, mul_comm]
  rw [fourierCoeff_congr_ae hae, fourierCoeff_fourier_mul c l j]

/-- **The coefficients of a multiplied truncation form a finite sum.** -/
theorem fourierCoeff_lpBoundedMulCLM_fourierTruncate (hc : Measurable c) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖c x‖ ≤ C) (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC
        (fourierTruncate S w) : AddCircle (1 : ℝ) → ℂ)) l
      = ∑ j ∈ S, fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j * fourierCoeff c (l - j) := by
  rw [fourierTruncate, map_sum, ← inner_fourierLp_eq_fourierCoeff, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_lpBoundedMulCLM_fourierLp hc hC0 hC j l]

/-- **The far-band coefficient bound.**  When every kernel entry over the truncation set is at
most `K`, the multiplied truncation has coefficients at most `K` times the `ℓ¹` mass. -/
theorem norm_fourierCoeff_lpBoundedMulCLM_fourierTruncate_le (hc : Measurable c) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖c x‖ ≤ C) (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) {K : ℝ}
    (hK : ∀ j ∈ S, ‖fourierCoeff c (l - j)‖ ≤ K) :
    ‖fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC
        (fourierTruncate S w) : AddCircle (1 : ℝ) → ℂ)) l‖
      ≤ K * ∑ j ∈ S, ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ := by
  rw [fourierCoeff_lpBoundedMulCLM_fourierTruncate hc hC0 hC S w l, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK j hj) (norm_nonneg _)

end

end GaloisForLFunctions
