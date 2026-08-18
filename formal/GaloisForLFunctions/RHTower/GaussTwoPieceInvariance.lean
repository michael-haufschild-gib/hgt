import GaloisForLFunctions.RHTower.SpikeBandConvolution
import GaloisForLFunctions.RHTower.GaussConvolutionCoefficient

/-!
# The two-piece amplitude class is invariant under the symbol algebra

Multiplication by a bounded real symbol whose Fourier coefficients decay harmonically is, on the
Fourier side, convolution with a harmonic kernel.  Such a convolution carries the two-piece class
into itself: the bulk part is transferred at any exponent below the original one, and the spike
part is transferred as a spike of the *same* exponent whose height pays only a logarithm, plus a
bulk term whose height is `spikeConvBulkConst · K · B · n^γ`.
-/

namespace RHTower

open MeasureTheory

/-- **The two-piece class is stable under multiplication by a symbol.** -/
theorem TwoPieceAmplitude.mul_symbol {A θ γ c B K Cb : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hθ1 : θ ≤ 1) (hγ0 : 0 < γ) (hγθ : γ < θ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n)
    {sym : AddCircle (1 : ℝ) → ℂ} (hsym : Measurable sym) (hCb0 : 0 ≤ Cb)
    (hCb : ∀ x, ‖sym x‖ ≤ Cb) (hreal : ∀ x, starRingEnd ℂ (sym x) = sym x)
    (hK : ∀ x : ℤ, ‖fourierCoeff sym x‖ ≤ K / (1 + (x.natAbs : ℝ)))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hu : TwoPieceAmplitude A θ B c n
      (fun l => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) l)) :
    TwoPieceAmplitude
      (K * A * (2 ^ γ * (2 * (∑' x : ℤ,
          GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
        + spikeConvBulkConst c (bandRadius n) * K * B * (n : ℝ) ^ γ)
      γ (3 * K * spikeConvConst c (bandRadius n) * B) c n
      (fun j => fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hsym hCb0 hCb u :
          AddCircle (1 : ℝ) → ℂ)) j) := by
  have hK0 : 0 ≤ K := by
    have h0 := hK 0
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  intro j
  refine le_trans (norm_fourierCoeff_lpBoundedMulCLM_le hsym hCb0 hCb hreal hK u j) ?_
  exact tsum_harmonic_two_piece_le hc0 hc1 hθ1 hγ0 hγθ hK0 hA hB hn hu j

end RHTower
