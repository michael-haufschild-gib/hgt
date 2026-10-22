import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilFrakPLaplace
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilZeroSeries

/-!
# Suzuki's Proposition 3.1: the two Laplace transforms agree

`SuzukiWeilFrakPLaplace` computes the Laplace transform of the prime--archimedean expression
`𝔓_t(z)` of Suzuki eq. (1.6); `SuzukiWeilZeroSeries` computes the Laplace transform of the
Xi-zero series `P_t(z)` of eq. (3.2).  This module identifies the two closed forms, which is the
analytic core of Suzuki, *On the Hilbert space derived from the Weil distribution*
(arXiv:2301.00421v3), Proposition 3.1:

```text
∫_0^∞ 𝔓_t(z) e^{-σt} dt = ∫_0^∞ P_t(z) e^{-σt} dt
```

for every real `σ` above `max(1/2, 1 + max(Im z, 0))`, at every `z ≠ 0` off the Xi divisor with
`Im z > -1/2` and `1/2 - iz ≠ 1`.  The bridge is the corpus's Guinand--Weil explicit formula
`continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace`, evaluated at the two base
points `-iσ` and `-z`, together with the elementary identity `iσ - z = i(σ + iz)`.

Everything here is unconditional.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- Off the Xi divisor and inside the right half-plane, `ζ` does not vanish at Suzuki's
coordinate `1/2 - iz`. -/
theorem riemannZeta_ne_zero_of_XiC_ne_zero {z : ℂ} (hz : XiC z ≠ 0)
    (hs0 : (1 : ℂ) / 2 - I * z ≠ 0) (hs1 : (1 : ℂ) / 2 - I * z ≠ 1)
    (hre : 0 < ((1 : ℂ) / 2 - I * z).re) :
    riemannZeta ((1 : ℂ) / 2 - I * z) ≠ 0 := by
  intro h
  apply hz
  rw [← XiC_neg]
  change xi (1 / 2 + (-z) * Complex.I) = 0
  have hcast : (1 : ℂ) / 2 + (-z) * Complex.I = 1 / 2 - I * z := by ring
  rw [hcast, xi_eq_archFactor_mul_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hre), h, mul_zero]

/-- The Xi relative resolvent trace at Suzuki's base point, in prime and archimedean terms. -/
theorem xiRelativeResolventTrace_neg_eq {z : ℂ} (hz : XiC z ≠ 0)
    (hs0 : (1 : ℂ) / 2 - I * z ≠ 0) (hs1 : (1 : ℂ) / 2 - I * z ≠ 1)
    (hre : 0 < ((1 : ℂ) / 2 - I * z).re) :
    xiRelativeResolventTrace (-z)
      = I * (logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)
          + logDeriv archFactor ((1 : ℂ) / 2 - I * z)) := by
  have hcast : (1 : ℂ) / 2 + (-z) * Complex.I = 1 / 2 - I * z := by ring
  have hzeta := riemannZeta_ne_zero_of_XiC_ne_zero hz hs0 hs1 hre
  rw [← continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (z := -z) (by rw [hcast]; exact hre) (by rw [hcast]; exact hs1) (by rw [hcast]; exact hzeta)]
  rw [continuedPrimeArchSourceRelativeTrace, hcast, infinitePrimeFlux]
  ring

/-- The Xi relative resolvent trace at the purely imaginary base point `-iσ`. -/
theorem xiRelativeResolventTrace_neg_I_mul {σ : ℝ} (hσ : 1 / 2 < σ) :
    xiRelativeResolventTrace (-(I * (σ : ℂ)))
      = I * (logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ)
          + logDeriv archFactor (((σ + 1 / 2 : ℝ)) : ℂ)) := by
  have hcast : (1 : ℂ) / 2 + (-(I * (σ : ℂ))) * Complex.I = (((σ + 1 / 2 : ℝ)) : ℂ) := by
    push_cast
    linear_combination (-(σ : ℂ)) * Complex.I_sq
  have hre : (1 : ℝ) < ((((σ + 1 / 2 : ℝ)) : ℂ)).re := by
    simpa using (by linarith : (1 : ℝ) < σ + 1 / 2)
  have hzeta : riemannZeta ((((σ + 1 / 2 : ℝ)) : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  have hne1 : (((σ + 1 / 2 : ℝ)) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [← continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (z := -(I * (σ : ℂ))) (by rw [hcast]; linarith) (by rw [hcast]; exact hne1)
    (by rw [hcast]; exact hzeta)]
  rw [continuedPrimeArchSourceRelativeTrace, hcast, infinitePrimeFlux]
  ring


theorem re_half_sub_I_mul {z : ℂ} : ((1 : ℂ) / 2 - I * z).re = 1 / 2 + z.im := by
  simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  norm_num

theorem re_quarter_sub_I_mul {z : ℂ} : ((1 : ℂ) / 4 - I * z / 2).re = 1 / 4 + z.im / 2 := by
  simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  norm_num
  ring

/-- **The two Laplace transforms agree.**  This is the analytic core of Suzuki's Proposition 3.1:
the prime--archimedean expression `𝔓_t(z)` and the Xi-zero series `P_t(z)` have the same Laplace
transform in `t` for every large real `σ`. -/
theorem integral_suzukiFrakP_laplace_eq_zeroSeries {σ : ℝ} {z : ℂ} (hz0 : z ≠ 0)
    (hσ1 : 1 / 2 < σ) (hσ2 : 1 + max z.im 0 < σ) (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re)
    (hs1 : (1 : ℂ) / 2 - I * z ≠ 1) (hXi : XiC z ≠ 0) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakP t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ∫ t in Ioi (0 : ℝ), suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
  rw [re_quarter_sub_I_mul] at hw
  have hre : 0 < ((1 : ℂ) / 2 - I * z).re := by rw [re_half_sub_I_mul]; linarith
  have hs0 : (1 : ℂ) / 2 - I * z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hzim : z.im < σ := lt_of_le_of_lt (le_max_left _ _) (by linarith [le_max_right z.im 0])
  have hzσ : I * (σ : ℂ) - z ≠ 0 := by
    intro h
    have him : (I * (σ : ℂ) - z).im = σ - z.im := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [h] at him
    simp at him
    linarith
  have hwq : 0 < ((1 : ℂ) / 4 - I * z / 2).re := by rw [re_quarter_sub_I_mul]; linarith
  rw [integral_suzukiFrakP_laplace hz0 hσ1 hσ2 hwq hs0 hs1,
    integral_suzukiPtZeroSum_laplace hσ1 hXi hzσ,
    xiRelativeResolventTrace_neg_I_mul hσ1, xiRelativeResolventTrace_neg_eq hXi hs0 hs1 hre]
  have hσC : ((σ : ℂ)) ≠ 0 := by
    simpa using ne_of_gt (show (0 : ℝ) < σ by linarith)
  have hsum : ((σ : ℂ)) + I * z ≠ 0 := by
    intro h
    have hre' : (((σ : ℂ)) + I * z).re = σ - z.im := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub]
      ring
    rw [h] at hre'
    simp at hre'
    linarith
  have hden : (σ : ℂ) * (I * (σ : ℂ) - z) = I * ((σ : ℂ) * ((σ : ℂ) + I * z)) := by
    linear_combination (-(σ : ℂ) * z) * Complex.I_sq
  rw [hden]
  rw [show I * (logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ)
        + logDeriv archFactor (((σ + 1 / 2 : ℝ)) : ℂ))
      - I * (logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)
        + logDeriv archFactor ((1 : ℂ) / 2 - I * z))
      = I * (logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ)
        + logDeriv archFactor (((σ + 1 / 2 : ℝ)) : ℂ)
        - logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)
        - logDeriv archFactor ((1 : ℂ) / 2 - I * z)) by ring]
  rw [mul_div_mul_left _ _ Complex.I_ne_zero]

end
end RHTower
