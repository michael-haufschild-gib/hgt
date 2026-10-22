import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilLerchBlock
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstGap
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Suzuki's prime--archimedean function `𝔓_t` and its removable central value

This module formalizes equation (1.6) of Suzuki, *On the Hilbert space derived from the Weil
distribution* (arXiv:2301.00421v3),

```text
𝔓_t(z) = 4(e^{t/2}-1)/(1+2iz) + 4(e^{-t/2}-1)/(1-2iz)
       + ((e^{-izt}-1)/(iz)) (ζ'/ζ)(1/2-iz)
       + ∑_{n ≤ e^t} Λ(n) n^{-1/2} (e^{-iz(t-log n)}-1)/(iz)
       - (1/(2iz)) [ψ(1/4-iz/2) - ψ(1/4)]
       - (1/(2iz)) e^{-t/2} [Φ(e^{-2t},1,(1/2)(1/2-iz)) - Φ(e^{-2t},1,1/4)],
```

together with the first half of the unconditional appendix theorem of Section 7:

**`tendsto_suzukiFrakP_zero` — `𝔓_t(0) = -g_ξ(t)`**, in the honest form of a limit through the
punctured neighbourhood of `z = 0`, since `z = 0` is a removable singularity of the printed formula
and the printed formula itself is `0/0` there.

Suzuki's screw function `g_ξ` of equation (4.3) is *not* redefined here: it is the corpus's
`suzukiScrewG = -Ψ`, and `suzukiScrewG_eq_screwFn` records that on `t ≥ 0` it is literally the
corpus's prime--Lerch `screwFn screwLinearCoeff screwLerchConst`.

Two supporting facts are proved on the way and are of independent interest:

* `logDeriv_riemannZeta_half` — `ζ'/ζ(1/2) = (log π - ψ(1/4))/2 = -screwLinearCoeff/2`;
* `continuousAt_logDeriv_riemannZeta_half`.

Everything in this file is unconditional.

## Source defect

The printed proof of (7.1) states the two intermediate limits

```text
lim_{z→0} (1/(iz)) [ψ(1/4-iz/2) - ψ(1/4)]                      =  (1/2) ψ₁(1/4),
lim_{z→0} (1/(iz)) [Φ(e^{-2t},1,(1/2)(1/2-iz)) - Φ(e^{-2t},1,1/4)] = -(1/2) Φ(e^{-2t},2,1/4).
```

Both signs are wrong: differentiating `w ↦ ψ(w)` and `w ↦ Φ(q,1,w)` at `w = 1/4` along
`w = 1/4 - iz/2` produces `-(1/2)ψ₁(1/4)` and `+(1/2)Φ(q,2,1/4)` respectively.  With the corrected
signs the theorem (7.1) is exactly right, which is what is proved here; with the printed signs the
two archimedean contributions would enter `-g_ξ(t)` with the wrong sign.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## The exponential slope -/

/-- The elementary slope limit `(e^{-iza} - 1)/(iz) → -a` as `z → 0`. -/
theorem tendsto_suzukiExpSlope (a : ℂ) :
    Tendsto (fun z : ℂ => (Complex.exp (-(I * z * a)) - 1) / (I * z)) (𝓝[≠] (0 : ℂ)) (𝓝 (-a)) := by
  have hlin : HasDerivAt (fun z : ℂ => -(I * z * a)) (-(I * a)) 0 := by
    have h0 : HasDerivAt (fun z : ℂ => I * z * a) (I * a) 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).const_mul I).mul_const a)
    exact h0.neg
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (-(I * z * a))) (-(I * a)) 0 := by
    simpa using hlin.cexp
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hfun : (fun z : ℂ => (Complex.exp (-(I * z * a)) - 1) / (I * z))
      = fun z : ℂ => slope (fun z : ℂ => Complex.exp (-(I * z * a))) 0 z / I := by
    funext z
    rw [slope_def_field]
    simp only [mul_zero, zero_mul, neg_zero, Complex.exp_zero]
    ring
  rw [hfun]
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have := hslope.div_const I
  have hval : -(I * a) / I = -a := by field_simp
  rwa [hval] at this

/-! ## The central value of `ζ'/ζ` -/

/-- `ζ(1/2) ≠ 0`, from the corpus's real-axis critical-strip nonvanishing. -/
theorem riemannZeta_half_ne_zero : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  have h := riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
  simpa using h

/-- **The central logarithmic derivative.**  `ζ'/ζ(1/2) = (log π - ψ(1/4))/2`, which is exactly
minus one half of Suzuki's archimedean linear coefficient. -/
theorem logDeriv_riemannZeta_half :
    logDeriv riemannZeta (1 / 2 : ℂ) = ((-screwLinearCoeff / 2 : ℝ) : ℂ) := by
  have hpole : ∀ m : ℕ, (1 / 2 : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hpole' : ∀ m : ℕ, ((1 : ℂ) - 1 / 2) / 2 ≠ -(m : ℂ) := by
    intro m h
    have h2 : ((1 : ℂ) - 1 / 2) / 2 = (1 / 2 : ℂ) / 2 := by ring
    rw [h2] at h
    exact hpole m h
  have hz : riemannZeta (1 / 2 : ℂ) ≠ 0 := riemannZeta_half_ne_zero
  have hz' : riemannZeta ((1 : ℂ) - 1 / 2) ≠ 0 := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]; exact hz
  have hrefl := logDeriv_riemannZeta_add_reflect_off_poles hpole hpole' hz hz'
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at hrefl
  rw [show (1 / 2 : ℂ) / 2 = 1 / 4 by ring] at hrefl
  rw [digamma_quarter] at hrefl
  rw [screwLinearCoeff_eq]
  push_cast
  push_cast at hrefl
  linear_combination hrefl / 2

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology
open GaloisForLFunctions.RHTower

/-- **Suzuki eq. (1.6).**  The prime--archimedean expression `𝔓_t(z)`. -/
def suzukiFrakP (t : ℝ) (z : ℂ) : ℂ :=
  4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)
    + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)
    + (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) * logDeriv riemannZeta (1 / 2 - I * z)
    + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z)))
    - (Complex.digamma (1 / 4 - I * z / 2) - Complex.digamma (1 / 4)) / (2 * I * z)
    - (Real.exp (-(t / 2)) : ℂ) * suzukiLerchDiff t (1 / 4 - I * z / 2) / (2 * I * z)

/-- Suzuki's eq. (4.3) function `g_ξ` is the corpus's `suzukiScrewG = -Ψ`: on `t ≥ 0` it is
literally the corpus's prime--Lerch `screwFn` at the published archimedean constants. -/
theorem suzukiScrewG_eq_screwFn {t : ℝ} (ht : 0 ≤ t) :
    suzukiScrewG t = ((screwFn screwLinearCoeff screwLerchConst t : ℝ) : ℂ) := by
  rw [suzukiScrewG, suzukiPsi, abs_of_nonneg ht]
  push_cast
  ring

/-- The pole-free rewriting of `𝔓_t` near `z = 0`: both archimedean blocks lose their `1/(2iz)`. -/
def suzukiFrakPReg (t : ℝ) (z : ℂ) : ℂ :=
  4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)
    + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)
    + (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) * logDeriv riemannZeta (1 / 2 - I * z)
    + (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z)))
    + suzukiLerchKernel 0 (1 / 4 - I * z / 2) / 4
    - (Real.exp (-(t / 2)) : ℂ) * suzukiLerchKernel t (1 / 4 - I * z / 2) / 4

theorem re_quarter_sub {z : ℂ} (hz : ‖z‖ < 1 / 2) : 0 < ((1 : ℂ) / 4 - I * z / 2).re := by
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hre : ((1 : ℂ) / 4 - I * z / 2).re = 1 / 4 + z.im / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
    ring
  rw [hre]
  have := abs_lt.mp (him.trans_lt hz)
  linarith [this.1]

theorem suzukiFrakP_eq_reg_of_re_pos (t : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hwre0 : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    suzukiFrakP t z = suzukiFrakPReg t z := by
  set w : ℂ := 1 / 4 - I * z / 2 with hw
  have hwre : 0 < w.re := hwre0
  have hIz : I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hquarter : (1 : ℂ) / 4 - w = I * z / 2 := by rw [hw]; ring
  have hA : Complex.digamma w - Complex.digamma (1 / 4) = -((I * z / 2) * suzukiLerchKernel 0 w) := by
    rw [digamma_sub_quarter_eq hwre, suzukiLerchDiff_eq hwre, hquarter]
  have hB : suzukiLerchDiff t w = (I * z / 2) * suzukiLerchKernel t w := by
    rw [suzukiLerchDiff_eq hwre, hquarter]
  rw [suzukiFrakP, suzukiFrakPReg, ← hw, hA, hB]
  have e1 : -(((I * z / 2) * suzukiLerchKernel 0 w)) / (2 * I * z)
      = -(suzukiLerchKernel 0 w / 4) := by
    field_simp
    ring
  have e2 : (Real.exp (-(t / 2)) : ℂ) * ((I * z / 2) * suzukiLerchKernel t w) / (2 * I * z)
      = (Real.exp (-(t / 2)) : ℂ) * suzukiLerchKernel t w / 4 := by
    field_simp
    ring
  rw [e1, e2]
  ring

/-- The pole-free rewriting on the small centered disc, where the archimedean argument
`1/4 - iz/2` automatically has positive real part. -/
theorem suzukiFrakP_eq_reg (t : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1 / 2) :
    suzukiFrakP t z = suzukiFrakPReg t z :=
  suzukiFrakP_eq_reg_of_re_pos t hz0 (re_quarter_sub hz)

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology
open GaloisForLFunctions.RHTower

/-- `ζ'/ζ` is continuous at the central point. -/
theorem continuousAt_logDeriv_riemannZeta_half :
    ContinuousAt (logDeriv riemannZeta) (1 / 2 : ℂ) := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) (1 / 2 : ℂ) :=
    differentiableAt_neg_logDeriv_riemannZeta (by norm_num) riemannZeta_half_ne_zero
  have hfun : logDeriv riemannZeta = fun z : ℂ => -(-deriv riemannZeta z / riemannZeta z) := by
    funext z
    rw [logDeriv_apply]
    ring
  rw [hfun]
  exact hd.continuousAt.neg

/-- The Lerch kernel along Suzuki's vertical parametrization is continuous at `z = 0`. -/
theorem tendsto_suzukiLerchKernel_shift {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun z : ℂ => suzukiLerchKernel t (1 / 4 - I * z / 2)) (𝓝 (0 : ℂ))
      (𝓝 (suzukiLerchKernel t (1 / 4))) := by
  have hinner : Tendsto (fun z : ℂ => (1 : ℂ) / 4 - I * z / 2) (𝓝 (0 : ℂ)) (𝓝 ((1 : ℂ) / 4)) := by
    have hc : ContinuousAt (fun z : ℂ => (1 : ℂ) / 4 - I * z / 2) 0 := by fun_prop
    have h2 : Tendsto (fun z : ℂ => (1 : ℂ) / 4 - I * z / 2) (𝓝 (0 : ℂ))
        (𝓝 ((1 : ℂ) / 4 - I * 0 / 2)) := hc
    rw [show (1 : ℂ) / 4 - I * 0 / 2 = 1 / 4 by ring] at h2
    exact h2
  exact Filter.Tendsto.comp
    (show Tendsto (suzukiLerchKernel t) (𝓝 ((1 : ℂ) / 4)) (𝓝 (suzukiLerchKernel t (1 / 4))) from
      continuousAt_suzukiLerchKernel_quarter ht) hinner

/-- `ζ'/ζ` along Suzuki's vertical parametrization is continuous at `z = 0`. -/
theorem tendsto_logDeriv_riemannZeta_shift :
    Tendsto (fun z : ℂ => logDeriv riemannZeta (1 / 2 - I * z)) (𝓝 (0 : ℂ))
      (𝓝 (logDeriv riemannZeta (1 / 2 : ℂ))) := by
  have hinner : Tendsto (fun z : ℂ => (1 : ℂ) / 2 - I * z) (𝓝 (0 : ℂ)) (𝓝 ((1 : ℂ) / 2)) := by
    have hc : ContinuousAt (fun z : ℂ => (1 : ℂ) / 2 - I * z) 0 := by fun_prop
    have h2 : Tendsto (fun z : ℂ => (1 : ℂ) / 2 - I * z) (𝓝 (0 : ℂ))
        (𝓝 ((1 : ℂ) / 2 - I * 0)) := hc
    rw [show (1 : ℂ) / 2 - I * 0 = 1 / 2 by ring] at h2
    exact h2
  exact Filter.Tendsto.comp
    (show Tendsto (logDeriv riemannZeta) (𝓝 ((1 : ℂ) / 2))
      (𝓝 (logDeriv riemannZeta (1 / 2 : ℂ))) from continuousAt_logDeriv_riemannZeta_half) hinner

/-- The finite prime block of `𝔓_t` collapses to `-∑_{n ≤ e^t} Λ(n) n^{-1/2}(t - log n)`. -/
theorem suzukiPrimeSum_cast (t : ℝ) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (screwPrimeWeight n : ℂ) * (-((t : ℂ) - (Real.log n : ℂ))))
      = -((screwPrimeSum t : ℝ) : ℂ) := by
  rw [screwPrimeSum, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- Value of the Lerch kernel at `t = 0`. -/
theorem suzukiLerchKernel_zero_quarter :
    suzukiLerchKernel 0 (1 / 4) = ((4 * screwLerchConst : ℝ) : ℂ) := by
  rw [suzukiLerchKernel_quarter, screwLerchConst]
  norm_num

/-- **Suzuki, appendix eq. (7.1), unconditional.**  The removable value of `𝔓_t` at `z = 0` is
`-g_ξ(t)`. -/
theorem tendsto_suzukiFrakP_zero {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (suzukiFrakP t) (𝓝[≠] (0 : ℂ)) (𝓝 (-suzukiScrewG t)) := by
  have hball : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), ‖z‖ < 1 / 2 := by
    have hb : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), ‖z‖ < 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
      simpa [Complex.dist_eq] using hz
    exact hb.filter_mono nhdsWithin_le_nhds
  have hev : suzukiFrakPReg t =ᶠ[𝓝[≠] (0 : ℂ)] suzukiFrakP t := by
    filter_upwards [hball, self_mem_nhdsWithin] with z hz hz0
    exact (suzukiFrakP_eq_reg t hz0 hz).symm
  refine Tendsto.congr' hev ?_
  have h1 : Tendsto (fun z : ℂ => 4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (4 * ((Real.exp (t / 2) : ℂ) - 1))) := by
    have hc : ContinuousAt (fun z : ℂ => 4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)) 0 := by
      refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
      norm_num
    have hc2 : Tendsto (fun z : ℂ => 4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z))
        (𝓝 (0 : ℂ)) (𝓝 (4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * 0))) := hc
    rw [show (1 : ℂ) + 2 * I * 0 = 1 by ring, div_one] at hc2
    exact hc2.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (4 * ((Real.exp (-(t / 2)) : ℂ) - 1))) := by
    have hc : ContinuousAt
        (fun z : ℂ => 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)) 0 := by
      refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
      norm_num
    have hc2 : Tendsto (fun z : ℂ => 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z))
        (𝓝 (0 : ℂ)) (𝓝 (4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * 0))) := hc
    rw [show (1 : ℂ) - 2 * I * 0 = 1 by ring, div_one] at hc2
    exact hc2.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun z : ℂ =>
        (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) * logDeriv riemannZeta (1 / 2 - I * z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-(t : ℂ) * logDeriv riemannZeta (1 / 2 : ℂ))) :=
    (tendsto_suzukiExpSlope (t : ℂ)).mul
      (tendsto_logDeriv_riemannZeta_shift.mono_left nhdsWithin_le_nhds)
  have h4 : Tendsto (fun z : ℂ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z)))
      (𝓝[≠] (0 : ℂ)) (𝓝 (-((screwPrimeSum t : ℝ) : ℂ))) := by
    rw [← suzukiPrimeSum_cast t]
    refine tendsto_finsetSum _ fun n _ => ?_
    exact (tendsto_suzukiExpSlope _).const_mul _
  have h5 : Tendsto (fun z : ℂ => suzukiLerchKernel 0 (1 / 4 - I * z / 2) / 4)
      (𝓝[≠] (0 : ℂ)) (𝓝 (suzukiLerchKernel 0 (1 / 4) / 4)) :=
    ((tendsto_suzukiLerchKernel_shift (le_refl (0 : ℝ))).mono_left nhdsWithin_le_nhds).div_const 4
  have h6 : Tendsto
      (fun z : ℂ => (Real.exp (-(t / 2)) : ℂ) * suzukiLerchKernel t (1 / 4 - I * z / 2) / 4)
      (𝓝[≠] (0 : ℂ))
      (𝓝 ((Real.exp (-(t / 2)) : ℂ) * suzukiLerchKernel t (1 / 4) / 4)) :=
    (((tendsto_suzukiLerchKernel_shift ht).mono_left nhdsWithin_le_nhds).const_mul
      ((Real.exp (-(t / 2)) : ℂ))).div_const 4
  have hall := ((((h1.add h2).add h3).add h4).add h5).sub h6
  have hval : 4 * ((Real.exp (t / 2) : ℂ) - 1) + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1)
      + -(t : ℂ) * logDeriv riemannZeta (1 / 2 : ℂ) + -((screwPrimeSum t : ℝ) : ℂ)
      + suzukiLerchKernel 0 (1 / 4) / 4
      - (Real.exp (-(t / 2)) : ℂ) * suzukiLerchKernel t (1 / 4) / 4
      = -suzukiScrewG t := by
    rw [logDeriv_riemannZeta_half, suzukiLerchKernel_zero_quarter, suzukiLerchKernel_quarter,
      suzukiScrewG_eq_screwFn ht, screwFn, screwLerchConst]
    have hexp : Complex.exp (-((t : ℂ) / 2)) * Complex.exp ((t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]
      simp
    push_cast
    linear_combination (-(screwLerchTail t : ℂ)) * hexp
  rw [← hval]
  exact hall

end
end RHTower
