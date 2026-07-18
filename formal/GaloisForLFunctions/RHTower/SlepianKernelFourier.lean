import GaloisForLFunctions.RHTower.SlepianSmoothKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Slepian kernel is the Gram kernel of the band-limited Fourier characters

The prolate apparatus is built on the sinc kernel `K̃_c(x,y) = sin(c(x−y))/(π(x−y))`, defined
directly as a profile.  The concentration operator whose spectrum the constrained transfer
measures is, by contrast, built from Fourier cutoffs.  The two meet here: the sinc profile *is*
the integral of a Fourier character over the band,

```text
sincSmooth c u = (c/2π) ∫_{−1}^{1} e^{i c u t} dt,
```

so the kernel factors as a Gram kernel of characters,

```text
K̃_c(x,y) = (c/2π) ∫_{−1}^{1} e^{i c x t} · conj(e^{i c y t}) dt.
```

This is the reason the sinc kernel carries the spectral information of a time–band
concentration operator at all: composing a Fourier cutoff with its adjoint produces exactly this
Gram kernel.

The identity also explains, with no power-series bookkeeping, why the profile extends entirely
across the origin: the right-hand side is an integral of a family entire in `u`, and at `u = 0`
it evaluates to `c/π`, which is the `dslope` value.  The removable singularity of `sin(cu)/(πu)`
is an artefact of evaluating the integral, not a property of the kernel.
-/

open intervalIntegral MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-- The symmetric exponential integral over the band. -/
theorem integral_symm_cexp {K : ℂ} (hK : K ≠ 0) :
    ∫ y in (-1 : ℝ)..1, Complex.exp (K * (y : ℂ)) = (Complex.exp K - Complex.exp (-K)) / K := by
  rw [integral_exp_mul_complex hK]
  norm_num

/-- The symmetric integral of a unit character is the sinc profile. -/
theorem integral_symm_cexp_I {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ y in (-1 : ℝ)..1, Complex.exp ((Complex.I * (θ : ℂ)) * (y : ℂ))
      = 2 * (Real.sin θ : ℂ) / (θ : ℂ) := by
  have hθc : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have hK : Complex.I * (θ : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hθc
  rw [integral_symm_cexp hK]
  have he : Complex.exp (Complex.I * (θ : ℂ)) = Complex.cos (θ : ℂ)
      + Complex.sin (θ : ℂ) * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I _
  have he' : Complex.exp (-(Complex.I * (θ : ℂ))) = Complex.cos (θ : ℂ)
      - Complex.sin (θ : ℂ) * Complex.I := by
    have hneg : -(Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
    rw [hneg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [he, he']
  have hsimp : Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I
      - (Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I)
      = 2 * Complex.sin (θ : ℂ) * Complex.I := by ring
  rw [hsimp, ← Complex.ofReal_sin]
  field_simp

/-- The sinc profile at the origin. -/
theorem sincSmooth_zero (c : ℝ) : sincSmooth c 0 = c / π := by
  rw [sincSmooth, dslope_same]
  have hf : HasDerivAt (fun u : ℝ => c * u) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h1 : HasDerivAt (fun u : ℝ => Real.sin (c * u)) (Real.cos (c * 0) * c) 0 := hf.sin
  have h2 := h1.div_const π
  rw [h2.deriv]
  simp

/-- **The sinc profile is the band integral of a Fourier character.**  Valid at the origin too,
where both sides equal `c/π`. -/
theorem sincSmooth_eq_integral (c u : ℝ) (hc : c ≠ 0) :
    ((sincSmooth c u : ℝ) : ℂ)
      = ((c : ℂ) / (2 * (π : ℂ)))
          * ∫ t in (-1 : ℝ)..1, Complex.exp ((Complex.I * ((c * u : ℝ) : ℂ)) * (t : ℂ)) := by
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcc : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rcases eq_or_ne u 0 with rfl | hu
  · have hzero : ((c * 0 : ℝ) : ℂ) = 0 := by norm_num
    rw [hzero]
    have hint' : (∫ t in (-1 : ℝ)..1, Complex.exp ((Complex.I * (0 : ℂ)) * (t : ℂ)))
        = (2 : ℂ) := by
      simp only [mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
      norm_num
    rw [hint', sincSmooth_zero]
    push_cast
    field_simp
  · have hcu : c * u ≠ 0 := mul_ne_zero hc hu
    rw [integral_symm_cexp_I hcu, sincSmooth_eq_off hu, sincScalar]
    have huc : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
    push_cast
    field_simp

/-- **The Slepian kernel is the Gram kernel of the band-limited Fourier characters.**  Composing
a Fourier cutoff with its adjoint produces exactly this kernel, which is why the prolate ODE
apparatus governs a time–band concentration operator. -/
theorem sincKernelSmooth_eq_integral (c x y : ℝ) (hc : c ≠ 0) :
    ((sincKernelSmooth c x y : ℝ) : ℂ)
      = ((c : ℂ) / (2 * (π : ℂ)))
          * ∫ t in (-1 : ℝ)..1, Complex.exp (Complex.I * ((c * x : ℝ) : ℂ) * (t : ℂ))
              * (starRingEnd ℂ) (Complex.exp (Complex.I * ((c * y : ℝ) : ℂ) * (t : ℂ))) := by
  have hkey := sincSmooth_eq_integral c (x - y) hc
  rw [sincKernelSmooth, hkey]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * ((c * y : ℝ) : ℂ) * (t : ℂ)))
      = Complex.exp (-(Complex.I * ((c * y : ℝ) : ℂ) * (t : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The model normalization: the band indicator's Fourier transform -/

/-- The symmetric exponential integral over a band of arbitrary half-width. -/
theorem integral_symm_cexp_width {K : ℂ} (hK : K ≠ 0) (a : ℝ) :
    ∫ t in (-a : ℝ)..a, Complex.exp (K * (t : ℂ))
      = (Complex.exp (K * (a : ℂ)) - Complex.exp (-(K * (a : ℂ)))) / K := by
  rw [integral_exp_mul_complex hK, Complex.ofReal_neg, mul_neg]

/-- **The Fourier character integrated over the band is the Slepian sinc profile**, in the
project's `e^{−2πixy}` normalization: the aperture `[−a,a]` carries the profile parameter
`c = 2πa`.  Valid at `s = 0`, where both sides equal `2a`. -/
theorem integral_symm_fourierChar (a s : ℝ) :
    ∫ t in (-a : ℝ)..a, Complex.exp ((-(2 * π * t * s) : ℝ) * Complex.I)
      = ((sincSmooth (2 * π * a) s : ℝ) : ℂ) := by
  have hrw : ∀ t : ℝ, Complex.exp ((-(2 * π * t * s) : ℝ) * Complex.I)
      = Complex.exp (((-(2 * π * s) : ℝ) * Complex.I) * (t : ℂ)) := by
    intro t
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hrw t)]
  rcases eq_or_ne s 0 with rfl | hs
  · have hzero : ((-(2 * π * 0) : ℝ) : ℂ) * Complex.I = 0 := by norm_num
    have hval : sincSmooth (2 * π * a) 0 = 2 * a := by
      rw [sincSmooth_zero]
      field_simp
    rw [hzero, hval]
    simp only [zero_mul, Complex.exp_zero, intervalIntegral.integral_const, sub_neg_eq_add,
      Complex.real_smul]
    push_cast
    ring
  · have hsc : ((-(2 * π * s) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      have : (2 : ℝ) * π * s ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hs
      simpa using this
    have hK : ((-(2 * π * s) : ℝ) : ℂ) * Complex.I ≠ 0 := mul_ne_zero hsc Complex.I_ne_zero
    rw [integral_symm_cexp_width hK]
    set θ : ℝ := -(2 * π * s) * a with hθ
    have he : Complex.exp (((-(2 * π * s) : ℝ) : ℂ) * Complex.I * (a : ℂ))
        = Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
      have harg : ((-(2 * π * s) : ℝ) : ℂ) * Complex.I * (a : ℂ) = (θ : ℂ) * Complex.I := by
        rw [hθ]
        push_cast
        ring
      rw [harg]
      exact Complex.exp_mul_I _
    have he' : Complex.exp (-(((-(2 * π * s) : ℝ) : ℂ) * Complex.I * (a : ℂ)))
        = Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I := by
      have harg : -(((-(2 * π * s) : ℝ) : ℂ) * Complex.I * (a : ℂ))
          = (-(θ : ℂ)) * Complex.I := by
        rw [hθ]
        push_cast
        ring
      rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    rw [he, he']
    have hsimp : Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I
        - (Complex.cos (θ : ℂ) - Complex.sin (θ : ℂ) * Complex.I)
        = 2 * Complex.sin (θ : ℂ) * Complex.I := by ring
    rw [hsimp, ← Complex.ofReal_sin, sincSmooth_eq_off hs, sincScalar]
    have hsinθ : Real.sin θ = -Real.sin (2 * π * a * s) := by
      rw [hθ]
      have : -(2 * π * s) * a = -(2 * π * a * s) := by ring
      rw [this, Real.sin_neg]
    rw [hsinθ]
    have hpic : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsc' : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    push_cast
    field_simp

/-- **The Slepian kernel as the band Gram kernel in the model's normalization.**  This is the
kernel of the composition of a Fourier cutoff with its adjoint on the aperture `[−a,a]`. -/
theorem integral_symm_fourierChar_gram (a x y : ℝ) :
    ∫ t in (-a : ℝ)..a, Complex.exp ((-(2 * π * x * t) : ℝ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I))
      = ((sincKernelSmooth (2 * π * a) x y : ℝ) : ℂ) := by
  have hrw : ∀ t : ℝ, Complex.exp ((-(2 * π * x * t) : ℝ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I))
      = Complex.exp ((-(2 * π * t * (x - y)) : ℝ) * Complex.I) := by
    intro t
    have hconj : (starRingEnd ℂ) (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I))
        = Complex.exp (-((-(2 * π * y * t) : ℝ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hrw t), integral_symm_fourierChar,
    sincKernelSmooth]

/-- The set-integral form over the aperture, which is how the `L²` model presents the inner
Fourier transform. -/
theorem setIntegral_Icc_fourierChar (a s : ℝ) (ha : 0 ≤ a) :
    ∫ t in Set.Icc (-a) a, Complex.exp ((-(2 * π * t * s) : ℝ) * Complex.I)
      = ((sincSmooth (2 * π * a) s : ℝ) : ℂ) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  rw [← integral_symm_fourierChar a s, intervalIntegral.integral_of_le hle]
  exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm

/-- The set-integral Gram form over the aperture. -/
theorem setIntegral_Icc_fourierChar_gram (a x y : ℝ) (ha : 0 ≤ a) :
    ∫ t in Set.Icc (-a) a, Complex.exp ((-(2 * π * x * t) : ℝ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp ((-(2 * π * y * t) : ℝ) * Complex.I))
      = ((sincKernelSmooth (2 * π * a) x y : ℝ) : ℂ) := by
  have hle : (-a : ℝ) ≤ a := by linarith
  rw [← integral_symm_fourierChar_gram a x y, intervalIntegral.integral_of_le hle]
  exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm

end RHTower

end
