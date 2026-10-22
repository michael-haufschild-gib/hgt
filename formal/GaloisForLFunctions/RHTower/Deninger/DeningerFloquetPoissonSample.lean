import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetMeasureEnergy
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonMellinFactorization
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonSource

/-!
# The Mellin sample of a Poisson boundary carries the zeta factor

The Mellin sampling map evaluates the two-sided Mellin transform of a source cochain on the
critical line: `𝓕(e^{t/2}h)(ξ) = ∫ e^{(1/2 - 2πiξ)t}h(t)dt`.  Applied to a Poisson boundary this
is the Poisson--Mellin factorization, so the sample of `Z f` is `ζ(1/2-2πiξ)` times the Mellin
transform of `f`.

In particular every Poisson boundary has vanishing sample at the resonant nodes, the frequencies of
the arithmetic lattice at which `ζ` vanishes on the critical line.

* `deningerCriticalLine` : the parameter `s = 1/2 - 2πiξ`.
* `deningerFloquetSample_eq_strongLogMellin` : **the sample is a critical-line Mellin value.**
* `deningerFloquetSample_poissonSource` : **the sample of a Poisson boundary is `ζ · M f`.**
* `deningerFloquetSample_poissonSource_eq_zero` : it vanishes at the resonant nodes.
-/

namespace RHTower

open MeasureTheory Complex SchwartzMap
open scoped FourierTransform RealInnerProductSpace

noncomputable section

/-- The critical-line parameter `s = 1/2 - 2πiξ`. -/
def deningerCriticalLine (ξ : ℝ) : ℂ := 1 / 2 - 2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)

@[simp]
theorem deningerCriticalLine_re (ξ : ℝ) : (deningerCriticalLine ξ).re = 1 / 2 := by
  simp [deningerCriticalLine, Complex.mul_re, Complex.mul_im]

theorem deningerCriticalLine_re_pos (ξ : ℝ) : 0 < (deningerCriticalLine ξ).re := by
  rw [deningerCriticalLine_re]
  norm_num

theorem deningerCriticalLine_ne_one (ξ : ℝ) : deningerCriticalLine ξ ≠ 1 := by
  intro hone
  have hre := congrArg Complex.re hone
  rw [deningerCriticalLine_re] at hre
  norm_num at hre

/-- **The Mellin sample is a critical-line two-sided Mellin value.** -/
theorem deningerFloquetSample_eq_strongLogMellin (h : DeningerExpSchwartz) (ξ : ℝ) :
    deningerFloquetSample h ξ
      = deningerMeyerStrongLogMellin (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
          (deningerCriticalLine ξ) := by
  rw [deningerFloquetSample, Real.fourier_eq', deningerMeyerStrongLogMellin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hinner : (⟪v, ξ⟫ : ℝ) = v * ξ := by
    simp [RCLike.inner_apply, mul_comm]
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul, smul_eq_mul,
    deningerHalfDensityLift_apply, hinner]
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, deningerCriticalLine]
  congr 1
  push_cast
  ring

/-! ## Poisson boundaries -/

theorem deningerPoissonSource_coe_eq_strongLogSum (f : DeningerMeyerCap) :
    (((deningerPoissonSource f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = ((deningerMeyerStrongLogSumLM f : DeningerMeyerStrongLogTarget) : ℝ → ℂ) := by
  funext t
  rw [deningerPoissonSource_apply, deningerMeyerStrongLogSumLM_apply, deningerPoissonLog,
    deningerMeyerSum]

/-- **The Mellin sample of a Poisson boundary is the zeta factor times the Mellin transform.** -/
theorem deningerFloquetSample_poissonSource (f : DeningerMeyerCap) (ξ : ℝ) :
    deningerFloquetSample (deningerPoissonSource f) ξ
      = riemannZeta (deningerCriticalLine ξ)
        * mellin (((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (deningerCriticalLine ξ) := by
  rw [deningerFloquetSample_eq_strongLogMellin, deningerPoissonSource_coe_eq_strongLogSum]
  exact deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin_of_re_pos f
    (deningerCriticalLine_re_pos ξ) (deningerCriticalLine_ne_one ξ)

/-- The resonant nodes: the lattice frequencies at which `ζ` vanishes on the critical line. -/
def deningerFloquetResonance : Set ℝ :=
  {ξ | ξ ∈ deningerFloquetSupport ∧ riemannZeta (deningerCriticalLine ξ) = 0}

/-- **Every Poisson boundary has vanishing sample at every resonant node.** -/
theorem deningerFloquetSample_poissonSource_eq_zero (f : DeningerMeyerCap) {ξ : ℝ}
    (hξ : ξ ∈ deningerFloquetResonance) :
    deningerFloquetSample (deningerPoissonSource f) ξ = 0 := by
  rw [deningerFloquetSample_poissonSource, hξ.2, zero_mul]

end

end RHTower
