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
  rcases eq_or_ne ((w.re + z.im) ^ (2 : ℕ) + (w.im - z.re) ^ (2 : ℕ)) 0 with h0 | h0
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
  rcases eq_or_ne ((w.re - z.im) ^ (2 : ℕ) + (w.im + z.re) ^ (2 : ℕ)) 0 with h0 | h0
  · have h1 : (w.re - z.im) * (w.re - z.im) + (w.im + z.re) * (w.im + z.re) = 0 := by
      nlinarith [h0]
    rw [h1, h0]
    simp
  · field_simp

/-- **The even channel is a pair of Poisson kernels.** -/
theorem re_weilChannelA {w z : ℂ} (hz : w ^ (2 : ℕ) + z ^ (2 : ℕ) ≠ 0) :
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
  simp only [Function.comp_def, Complex.reCLM_apply]
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

theorem eulerSafeDensity_eq_tsum_term {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    eulerSafeDensity a t = (Real.pi / 2) * ∑' q : XiZeroCopy, boundaryPoissonTerm a t q :=
  eulerSafeDensity_eq_tsum ha t

/-! ### Equation (12): the Poisson semigroup transports the boundary density -/

theorem abs_im_spectral_lt {a : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy) :
    0 < a + (xiSpectralPoint q).im ∧ 0 < a - (xiSpectralPoint q).im := by
  have hb := abs_le.mp (abs_im_xiSpectralPoint_le q)
  constructor <;> linarith [hb.1, hb.2]

theorem integral_boundaryPoissonTerm {a b : ℝ} (ha : 1 / 2 < a) (hab : a < b) (t : ℝ)
    (q : XiZeroCopy) :
    (∫ s : ℝ, halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q)
      = boundaryPoissonTerm b t q := by
  obtain ⟨hp, hm⟩ := abs_im_spectral_lt ha q
  have hba : 0 < b - a := by linarith
  have h1 : (∫ s : ℝ, halfPlanePoisson (b - a) (t - s)
      * halfPlanePoisson (a + (xiSpectralPoint q).im) (s - (xiSpectralPoint q).re))
      = halfPlanePoisson (b - a + (a + (xiSpectralPoint q).im)) (t - (xiSpectralPoint q).re) :=
    integral_poisson_shift_product hba hp t _
  have h2 : (∫ s : ℝ, halfPlanePoisson (b - a) (t - s)
      * halfPlanePoisson (a - (xiSpectralPoint q).im) (s - (-(xiSpectralPoint q).re)))
      = halfPlanePoisson (b - a + (a - (xiSpectralPoint q).im)) (t - (-(xiSpectralPoint q).re)) :=
    integral_poisson_shift_product hba hm t _
  have hi1 : Integrable fun s : ℝ => halfPlanePoisson (b - a) (t - s)
      * halfPlanePoisson (a + (xiSpectralPoint q).im) (s - (xiSpectralPoint q).re) :=
    integrable_poisson_shift_product hba hp t _
  have hi2 : Integrable fun s : ℝ => halfPlanePoisson (b - a) (t - s)
      * halfPlanePoisson (a - (xiSpectralPoint q).im) (s - (-(xiSpectralPoint q).re)) :=
    integrable_poisson_shift_product hba hm t _
  have hcongr : ∀ s : ℝ, halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q
      = halfPlanePoisson (b - a) (t - s)
          * halfPlanePoisson (a + (xiSpectralPoint q).im) (s - (xiSpectralPoint q).re)
        + halfPlanePoisson (b - a) (t - s)
          * halfPlanePoisson (a - (xiSpectralPoint q).im) (s - (-(xiSpectralPoint q).re)) := by
    intro s
    rw [boundaryPoissonTerm]
    have hsub : s - (-(xiSpectralPoint q).re) = s + (xiSpectralPoint q).re := by ring
    rw [hsub]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_add hi1 hi2, h1, h2, boundaryPoissonTerm]
  have he1 : b - a + (a + (xiSpectralPoint q).im) = b + (xiSpectralPoint q).im := by ring
  have he2 : b - a + (a - (xiSpectralPoint q).im) = b - (xiSpectralPoint q).im := by ring
  have he3 : t - -(xiSpectralPoint q).re = t + (xiSpectralPoint q).re := by ring
  rw [he1, he2, he3]

theorem integrable_poisson_boundaryTerm {a b : ℝ} (ha : 1 / 2 < a) (hab : a < b) (t : ℝ)
    (q : XiZeroCopy) :
    Integrable fun s : ℝ => halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q := by
  obtain ⟨hp, hm⟩ := abs_im_spectral_lt ha q
  have hba : 0 < b - a := by linarith
  have hi1 := integrable_poisson_shift_product hba hp t ((xiSpectralPoint q).re)
  have hi2 := integrable_poisson_shift_product hba hm t (-(xiSpectralPoint q).re)
  refine (hi1.add hi2).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, boundaryPoissonTerm]
  have hsub : s - -(xiSpectralPoint q).re = s + (xiSpectralPoint q).re := by ring
  rw [hsub]
  ring

/-- **Equation (12).**  The boundary densities at all safe offsets form one Poisson semigroup
orbit. -/
theorem eulerSafeDensity_poisson_transport {a b : ℝ} (ha : 1 / 2 < a) (hab : a < b) (t : ℝ) :
    eulerSafeDensity b t
      = ∫ s : ℝ, halfPlanePoisson (b - a) (t - s) * eulerSafeDensity a s := by
  have hb : 1 / 2 < b := lt_trans ha hab
  have hba : 0 < b - a := by linarith
  have hnormeq : ∀ q : XiZeroCopy,
      (∫ s : ℝ, ‖halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q‖)
        = boundaryPoissonTerm b t q := by
    intro q
    obtain ⟨hp, hm⟩ := abs_im_spectral_lt ha q
    rw [← integral_boundaryPoissonTerm ha hab t q]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have h1 := halfPlanePoisson_pos hba (t - s)
    have h2 := halfPlanePoisson_pos hp (s - (xiSpectralPoint q).re)
    have h3 := halfPlanePoisson_pos hm (s + (xiSpectralPoint q).re)
    simp only [boundaryPoissonTerm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hswap : (∑' q : XiZeroCopy,
        ∫ s : ℝ, halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q)
      = ∫ s : ℝ, ∑' q : XiZeroCopy,
          halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q := by
    refine MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun q => integrable_poisson_boundaryTerm ha hab t q) ?_
    exact (summable_boundaryPoissonTerm hb t).congr fun q => (hnormeq q).symm
  have hinner : ∀ s : ℝ, halfPlanePoisson (b - a) (t - s) * eulerSafeDensity a s
      = (Real.pi / 2) * ∑' q : XiZeroCopy,
          halfPlanePoisson (b - a) (t - s) * boundaryPoissonTerm a s q := by
    intro s
    rw [eulerSafeDensity_eq_tsum_term ha s, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun q => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner),
    MeasureTheory.integral_const_mul, ← hswap]
  rw [eulerSafeDensity_eq_tsum_term hb t]
  refine congrArg (fun x => (Real.pi / 2) * x) ?_
  exact (tsum_congr fun q => (integral_boundaryPoissonTerm ha hab t q)).symm

end RHTower
