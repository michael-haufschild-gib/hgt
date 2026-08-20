import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent

/-!
# The Euler-safe boundary density is a Poisson orbit of the centred divisor

On the absolute-Euler line `Re w = a > 1/2` the boundary density of the completed logarithmic
derivative is `h_a (t) = Re L (a + i t)`.  The paired Hadamard expansion `L w = ∑' α, A_w α` and the
Hardy splitting `A_w = (1/2) [1/(w - iα) + 1/(w + iα)]` turn each resolvent into a half-plane
Poisson kernel: writing `α = ρ + i ν`,

```
Re (1/(w - i α)) = pi * P_(Re w + nu) (Im w - rho),
Re (1/(w + i α)) = pi * P_(Re w - nu) (Im w + rho),
```

so `h_a` is an explicit convergent divisor sum of Poisson kernels at heights `a ± ν`, all positive
because the unconditional critical-strip width gives `|ν| ≤ 1/2 < a`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace RHTower

/-! ### Resolvents are Poisson kernels -/

theorem re_inv_sub_I_mul (w z : ℂ) :
    (1 / (w - Complex.I * z)).re
      = Real.pi * halfPlanePoisson (w.re + z.im) (w.im - z.re) := by
  have hre : (w - Complex.I * z).re = w.re + z.im := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, sub_neg_eq_add]
  have him : (w - Complex.I * z).im = w.im - z.re := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add]
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him, halfPlanePoisson]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rcases eq_or_ne ((w.re + z.im) ^ 2 + (w.im - z.re) ^ 2) 0 with h0 | h0
  · have h1 : (w.re + z.im) * (w.re + z.im) + (w.im - z.re) * (w.im - z.re) = 0 := by
      nlinarith [h0]
    rw [h1, h0]
    simp
  · field_simp

theorem re_inv_add_I_mul (w z : ℂ) :
    (1 / (w + Complex.I * z)).re
      = Real.pi * halfPlanePoisson (w.re - z.im) (w.im + z.re) := by
  have hre : (w + Complex.I * z).re = w.re - z.im := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    ring
  have him : (w + Complex.I * z).im = w.im + z.re := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add]
  rw [one_div, Complex.inv_re, Complex.normSq_apply, hre, him, halfPlanePoisson]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rcases eq_or_ne ((w.re - z.im) ^ 2 + (w.im + z.re) ^ 2) 0 with h0 | h0
  · have h1 : (w.re - z.im) * (w.re - z.im) + (w.im + z.re) * (w.im + z.re) = 0 := by
      nlinarith [h0]
    rw [h1, h0]
    simp
  · field_simp

/-- **The even channel is a pair of Poisson kernels.** -/
theorem re_weilChannelA {w z : ℂ} (hz : w ^ 2 + z ^ 2 ≠ 0) :
    (weilChannelA w z).re
      = (Real.pi / 2) * (halfPlanePoisson (w.re + z.im) (w.im - z.re)
        + halfPlanePoisson (w.re - z.im) (w.im + z.re)) := by
  rw [weilChannelA_eq_resolvent hz, weilResolventPlus, weilResolventMinus, Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, re_inv_sub_I_mul, re_inv_add_I_mul,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  ring

/-! ### The boundary density -/

/-- The Euler-safe boundary density `h_a (t) = Re L (a + i t)`. -/
def eulerSafeDensity (a t : ℝ) : ℝ :=
  (logDeriv xiCent ((a : ℂ) + (t : ℂ) * Complex.I)).re

theorem re_boundaryPoint (a t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I)).re = a := by
  simp

theorem im_boundaryPoint (a t : ℝ) : (((a : ℂ) + (t : ℂ) * Complex.I)).im = t := by
  simp

/-- The divisor family of Poisson kernels attached to the boundary line `Re w = a`. -/
def boundaryPoissonTerm (a t : ℝ) (q : XiZeroCopy) : ℝ :=
  halfPlanePoisson (a + (xiSpectralPoint q).im) (t - (xiSpectralPoint q).re)
    + halfPlanePoisson (a - (xiSpectralPoint q).im) (t + (xiSpectralPoint q).re)

theorem re_weilChannelA_spectral {a t : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy) :
    (weilChannelA ((a : ℂ) + (t : ℂ) * Complex.I) (xiSpectralPoint q)).re
      = (Real.pi / 2) * boundaryPoissonTerm a t q := by
  have hW : (((a : ℂ) + (t : ℂ) * Complex.I)).re = a := by simp
  have hWim : (((a : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  have hWhalf : 1 / 2 < (((a : ℂ) + (t : ℂ) * Complex.I)).re := by rw [hW]; exact ha
  rw [re_weilChannelA (sq_add_spectral_sq_ne_zero hWhalf q), hW, hWim, boundaryPoissonTerm]

theorem summable_boundaryPoissonTerm {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    Summable (boundaryPoissonTerm a t) := by
  have hW : (((a : ℂ) + (t : ℂ) * Complex.I)).re = a := by simp
  have hWhalf : 1 / 2 < (((a : ℂ) + (t : ℂ) * Complex.I)).re := by rw [hW]; exact ha
  have hsum := summable_channelA hWhalf
  have hre := (hsum.map Complex.reCLM Complex.reCLM.continuous)
  have hpi : (Real.pi / 2) ≠ 0 := by
    have := Real.pi_pos
    positivity
  refine ((hre.div_const (Real.pi / 2)).congr fun q => ?_)
  simp only [Function.comp_def]
  rw [re_weilChannelA_spectral ha q]
  field_simp

/-- **The boundary density is a convergent divisor sum of Poisson kernels.** -/
theorem eulerSafeDensity_eq_tsum {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    eulerSafeDensity a t
      = (Real.pi / 2) * ∑' q : XiZeroCopy,
          (halfPlanePoisson (a + (xiSpectralPoint q).im) (t - (xiSpectralPoint q).re)
            + halfPlanePoisson (a - (xiSpectralPoint q).im) (t + (xiSpectralPoint q).re)) := by
  set W : ℂ := (a : ℂ) + (t : ℂ) * Complex.I with hW
  have hWre : W.re = a := by rw [hW]; simp
  have hWim : W.im = t := by rw [hW]; simp
  have hWhalf : 1 / 2 < W.re := by rw [hWre]; exact ha
  have hsum := summable_channelA hWhalf
  have hre : ∀ q : XiZeroCopy, (weilChannelA W (xiSpectralPoint q)).re
      = (Real.pi / 2) * (halfPlanePoisson (a + (xiSpectralPoint q).im)
            (t - (xiSpectralPoint q).re)
          + halfPlanePoisson (a - (xiSpectralPoint q).im) (t + (xiSpectralPoint q).re)) := by
    intro q
    rw [re_weilChannelA (sq_add_spectral_sq_ne_zero hWhalf q), hWre, hWim]
  rw [eulerSafeDensity, ← hW, logDeriv_xiCent_eq_tsum_channelA hWhalf, Complex.re_tsum hsum,
    tsum_congr hre, tsum_mul_left]

end RHTower
