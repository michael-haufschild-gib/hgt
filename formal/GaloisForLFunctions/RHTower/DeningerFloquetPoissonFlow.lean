import GaloisForLFunctions.RHTower.DeningerFloquetPoissonSample
import GaloisForLFunctions.RHTower.DeningerMeyerDilationFlow
import GaloisForLFunctions.RHTower.CCMConnesConsaniZetaCycles

/-!
# The dilation flow modulates the Mellin sample by a critical-line character

Scaling a Meyer test function by `e^{-c}` multiplies its Mellin transform by `e^{cs}`, so on the
critical line it multiplies the Mellin sample of the associated Poisson boundary by the character
`e^{c/2}e^{-2πicξ}`.  Since the explicit Poisson test function has nowhere-vanishing Mellin
transform on the critical line, the Poisson boundaries realize every such character times one fixed
nonvanishing profile.

* `mellin_deningerMeyerCapFlow` : `M(f(e^{-c}·)) = e^{cs} M f`.
* `deningerFloquetSample_capFlow` : **the sample of a scaled Poisson boundary.**
* `deningerFloquetProfile_ne_zero` : **the explicit profile never vanishes on the critical line.**
-/

namespace RHTower

open MeasureTheory Complex SchwartzMap
open scoped FourierTransform

noncomputable section

theorem ofReal_exp_cpow (c : ℝ) (s : ℂ) :
    ((Real.exp c : ℝ) : ℂ) ^ s = Complex.exp ((c : ℂ) * s) := by
  have hne : ((Real.exp c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_ne_zero c)
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos c).le, Real.log_exp]

/-- **Scaling multiplies the Mellin transform by `e^{cs}`.** -/
theorem mellin_deningerMeyerCapFlow (c : ℝ) (f : DeningerMeyerCap) (s : ℂ) :
    mellin (((deningerMeyerCapFlow c f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s
      = Complex.exp ((c : ℂ) * s) * mellin (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s := by
  have hfun : (((deningerMeyerCapFlow c f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun x : ℝ => (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (Real.exp (-c) * x) :=
    funext fun x => deningerMeyerCapFlow_apply c f x
  rw [hfun, mellin_comp_mul_left _ s (Real.exp_pos (-c)), ofReal_exp_cpow, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **The Mellin sample of a scaled Poisson boundary.** -/
theorem deningerFloquetSample_capFlow (c : ℝ) (f : DeningerMeyerCap) (ξ : ℝ) :
    deningerFloquetSample (deningerPoissonSource (deningerMeyerCapFlow c f)) ξ
      = Complex.exp ((c : ℂ) * deningerCriticalLine ξ)
        * (riemannZeta (deningerCriticalLine ξ)
          * mellin (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ)) := by
  rw [deningerFloquetSample_poissonSource, mellin_deningerMeyerCapFlow]
  ring

/-- The explicit Poisson test profile on the critical line. -/
def deningerFloquetProfile (ξ : ℝ) : ℂ :=
  mellin (((meyerPoissonTestSource : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
    (deningerCriticalLine ξ)

/-- **The explicit profile never vanishes on the critical line.** -/
theorem deningerFloquetProfile_ne_zero (ξ : ℝ) : deningerFloquetProfile ξ ≠ 0 := by
  refine mellin_meyerPoissonTestSource_ne_zero ?_ (deningerCriticalLine_ne_one ξ)
  rw [deningerCriticalLine_re]
  norm_num

theorem deningerFloquetSample_profileFlow (c : ℝ) (ξ : ℝ) :
    deningerFloquetSample
        (deningerPoissonSource (deningerMeyerCapFlow c meyerPoissonTestSource)) ξ
      = Complex.exp ((c : ℂ) * deningerCriticalLine ξ)
        * (riemannZeta (deningerCriticalLine ξ) * deningerFloquetProfile ξ) :=
  deningerFloquetSample_capFlow c meyerPoissonTestSource ξ

end

end RHTower
