import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Complex-analytic continuation of the prime-Laplace channel

The Euler-region complex continuation of the von Mangoldt prime channel of
`ccm-polar-prime-critical-mellin-defect-law`.  The card's resolved real channel
`vonMangoldtPrimeLaplaceChannel : ℝ → ℂ` equals `-ζ'/ζ(s+1)` for `s > 0`
(`vonMangoldtPrimeLaplaceChannel_eq_logDeriv`); its natural complex extension is

`vonMangoldtPrimeChannelComplex s = -ζ'(s+1)/ζ(s+1)`,

which agrees with the real channel on `s > 0` and is **holomorphic on the whole right half-plane
`Re s > 0`** (from `differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re`, since `Re(s+1) > 1` puts
`s+1` in `ζ`'s zero-free absolute-convergence region).  This is the analytic backbone of the card's
open "full complex continuation" — the holomorphic Euler-region piece; continuation past `Re s = 0`
(across the critical line) is the distributional/autocorrelation Stieltjes layer that remains open.
-/

namespace RHTower

/-- The complex extension of the von Mangoldt prime-Laplace channel: `-ζ'(s+1)/ζ(s+1)`. -/
noncomputable def vonMangoldtPrimeChannelComplex (s : ℂ) : ℂ :=
  -deriv riemannZeta (s + 1) / riemannZeta (s + 1)

/-- The complex channel agrees with the card's resolved real channel on `s > 0`. -/
theorem vonMangoldtPrimeChannelComplex_eq_channel {s : ℝ} (hs : 0 < s) :
    vonMangoldtPrimeChannelComplex (s : ℂ) = vonMangoldtPrimeLaplaceChannel s := by
  rw [vonMangoldtPrimeChannelComplex, vonMangoldtPrimeLaplaceChannel_eq_logDeriv hs]
  push_cast
  ring_nf

/-- **The prime channel is holomorphic at every `s` with `Re s > 0`** — `-ζ'/ζ(s+1)` with `s+1` in the
Euler region `Re > 1`. -/
theorem vonMangoldtPrimeChannelComplex_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ vonMangoldtPrimeChannelComplex s := by
  have hre : 1 < (s + 1).re := by rw [Complex.add_re]; simp; linarith
  exact (differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re hre).comp s
    (differentiableAt_id.add_const 1)

/-- **The prime channel is holomorphic on the right half-plane `Re s > 0`.** -/
theorem vonMangoldtPrimeChannelComplex_differentiableOn :
    DifferentiableOn ℂ vonMangoldtPrimeChannelComplex {s : ℂ | 0 < s.re} :=
  fun _ hs => (vonMangoldtPrimeChannelComplex_differentiableAt hs).differentiableWithinAt

end RHTower
