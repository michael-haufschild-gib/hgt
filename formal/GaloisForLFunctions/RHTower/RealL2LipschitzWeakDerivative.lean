import GaloisForLFunctions.RHTower.VectorL2WeakDerivativeFourier
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Real Lipschitz `L²` functions as complex weak derivatives

A real globally Lipschitz function in `L²`, whose classical `deriv` is also in `L²`, is an
`H¹` function.  If both endpoints vanish, its real derivative is exactly its distributional
derivative after complexification.  This module proves that fact directly in the tempered-
distribution model used by the CCM Fourier pipeline.

The proof does not assume pointwise differentiability.  Lipschitz regularity gives absolute
continuity on every finite interval; finite-interval integration by parts is then passed to the
whole line through the `L² × L² → L¹` product bound and the vanishing endpoint terms.
-/

open Set MeasureTheory Filter
open scoped ENNReal SchwartzMap LineDeriv

noncomputable section

namespace RHTower

private theorem deriv_re_schwartz (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (fun y : ℝ => (φ y).re) x = (deriv (φ : ℝ → ℂ) x).re := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (φ.hasDerivAt x)).deriv

private theorem deriv_im_schwartz (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (fun y : ℝ => (φ y).im) x = (deriv (φ : ℝ → ℂ) x).im := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (φ.hasDerivAt x)).deriv

private theorem integral_schwartz_re_mul_deriv_eq_neg
    (p : ℝ → ℝ) {C : NNReal} (hpLip : LipschitzWith C p)
    (hp2 : MemLp p 2 (volume : Measure ℝ))
    (hdp2 : MemLp (deriv p) 2 (volume : Measure ℝ))
    (hpTop : Tendsto p atTop (nhds 0)) (hpBot : Tendsto p atBot (nhds 0))
    (φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (φ x).re * deriv p x) =
      -∫ x : ℝ, deriv (fun y : ℝ => (φ y).re) x * p x := by
  let q : ℝ → ℝ := fun x => (φ x).re
  let q' : ℝ → ℝ := fun x => deriv (fun y : ℝ => (φ y).re) x
  have hq2 : MemLp q 2 (volume : Measure ℝ) := by
    exact (φ.memLp 2 (volume : Measure ℝ)).re
  have hq'2 : MemLp q' 2 (volume : Measure ℝ) := by
    let dφ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ
    have hdφ2 : MemLp (dφ : ℝ → ℂ) 2 (volume : Measure ℝ) :=
      dφ.memLp 2 (volume : Measure ℝ)
    apply MemLp.ae_eq _ (MeasureTheory.MemLp.re hdφ2)
    filter_upwards with x
    simp only [q', dφ, SchwartzMap.derivCLM_apply]
    exact (deriv_re_schwartz φ x).symm
  have hleft : Integrable (q * deriv p) (volume : Measure ℝ) :=
    MemLp.integrable_mul hq2 hdp2
  have hright : Integrable (q' * p) (volume : Measure ℝ) :=
    MemLp.integrable_mul hq'2 hp2
  have hqAC (a b : ℝ) : AbsolutelyContinuousOnInterval q a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hqdiff : ContDiff ℝ (⊤ : ℕ∞) q := by
      simpa [q, Function.comp_def] using
        (Complex.reCLM.contDiff.comp (φ.smooth ⊤))
    exact hqdiff.contDiffOn.of_le (by simp)
  have hpAC (a b : ℝ) : AbsolutelyContinuousOnInterval p a b :=
    hpLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hfinite (t : ℝ) :
      (∫ x in (-t)..t, q x * deriv p x) =
        q t * p t - q (-t) * p (-t) - ∫ x in (-t)..t, q' x * p x := by
    simpa [q'] using (hqAC (-t) t).integral_mul_deriv_eq_deriv_mul (hpAC (-t) t)
  have hqTop : Tendsto q atTop (nhds 0) := by
    exact (Complex.continuous_re.tendsto 0).comp
      ((SchwartzMap.tendsto_cocompact φ).mono_left atTop_le_cocompact)
  have hqBot : Tendsto q atBot (nhds 0) := by
    exact (Complex.continuous_re.tendsto 0).comp
      ((SchwartzMap.tendsto_cocompact φ).mono_left atBot_le_cocompact)
  have hboundary : Tendsto (fun t : ℝ => q t * p t - q (-t) * p (-t)) atTop (nhds 0) := by
    have htop : Tendsto (fun t : ℝ => q t * p t) atTop (nhds (0 : ℝ)) := by
      simpa using hqTop.mul hpTop
    have hbotq : Tendsto (fun t : ℝ => q (-t)) atTop (nhds 0) :=
      hqBot.comp tendsto_neg_atTop_atBot
    have hbotp : Tendsto (fun t : ℝ => p (-t)) atTop (nhds 0) :=
      hpBot.comp tendsto_neg_atTop_atBot
    simpa using htop.sub (hbotq.mul hbotp)
  have hleftLim : Tendsto (fun t : ℝ => ∫ x in (-t)..t, q x * deriv p x)
      atTop (nhds (∫ x : ℝ, q x * deriv p x)) :=
    intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id
  have hrightLim : Tendsto (fun t : ℝ => ∫ x in (-t)..t, q' x * p x)
      atTop (nhds (∫ x : ℝ, q' x * p x)) :=
    intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id
  have hrhs : Tendsto
      (fun t : ℝ => q t * p t - q (-t) * p (-t) - ∫ x in (-t)..t, q' x * p x)
      atTop (nhds (-(∫ x : ℝ, q' x * p x))) := by
    simpa using hboundary.sub hrightLim
  have heq : (fun t : ℝ => ∫ x in (-t)..t, q x * deriv p x) =
      fun t : ℝ => q t * p t - q (-t) * p (-t) - ∫ x in (-t)..t, q' x * p x :=
    funext hfinite
  rw [heq] at hleftLim
  have hmain := tendsto_nhds_unique hleftLim hrhs
  simpa [q, q'] using hmain

private theorem integral_schwartz_im_mul_deriv_eq_neg
    (p : ℝ → ℝ) {C : NNReal} (hpLip : LipschitzWith C p)
    (hp2 : MemLp p 2 (volume : Measure ℝ))
    (hdp2 : MemLp (deriv p) 2 (volume : Measure ℝ))
    (hpTop : Tendsto p atTop (nhds 0)) (hpBot : Tendsto p atBot (nhds 0))
    (φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (φ x).im * deriv p x) =
      -∫ x : ℝ, deriv (fun y : ℝ => (φ y).im) x * p x := by
  let ψ : SchwartzMap ℝ ℂ := (-Complex.I) • φ
  have h := integral_schwartz_re_mul_deriv_eq_neg p hpLip hp2 hdp2 hpTop hpBot ψ
  have hψ (x : ℝ) : (ψ x).re = (φ x).im := by
    simp [ψ, Complex.mul_re]
  have hdψ (x : ℝ) : deriv (fun y : ℝ => (ψ y).re) x =
      deriv (fun y : ℝ => (φ y).im) x := by
    congr 1
    funext y
    exact hψ y
  simpa only [hψ, hdψ] using h

private theorem integral_schwartz_mul_deriv_ofReal_eq_neg
    (p : ℝ → ℝ) {C : NNReal} (hpLip : LipschitzWith C p)
    (hp2 : MemLp p 2 (volume : Measure ℝ))
    (hdp2 : MemLp (deriv p) 2 (volume : Measure ℝ))
    (hpTop : Tendsto p atTop (nhds 0)) (hpBot : Tendsto p atBot (nhds 0))
    (φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, φ x * ((deriv p x : ℝ) : ℂ)) =
      -∫ x : ℝ, deriv (φ : ℝ → ℂ) x * (p x : ℂ) := by
  let dφ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ φ
  have hleft : Integrable (fun x : ℝ => φ x * ((deriv p x : ℝ) : ℂ)) :=
    MemLp.integrable_mul (φ.memLp 2 (volume : Measure ℝ)) hdp2.ofReal
  have hright : Integrable (fun x : ℝ => deriv (φ : ℝ → ℂ) x * (p x : ℂ)) := by
    have hdφ2 : MemLp (dφ : ℝ → ℂ) 2 (volume : Measure ℝ) :=
      dφ.memLp 2 (volume : Measure ℝ)
    have hmul := MemLp.integrable_mul hdφ2 hp2.ofReal
    apply hmul.congr
    filter_upwards with x
    simp [dφ, SchwartzMap.derivCLM_apply]
  apply Complex.ext
  · calc
      (∫ x : ℝ, φ x * ((deriv p x : ℝ) : ℂ)).re =
          ∫ x : ℝ, (φ x * ((deriv p x : ℝ) : ℂ)).re := (integral_re hleft).symm
      _ = -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * (p x : ℂ)).re := by
        simpa [Complex.mul_re, ← deriv_re_schwartz] using
          integral_schwartz_re_mul_deriv_eq_neg p hpLip hp2 hdp2 hpTop hpBot φ
      _ = (-∫ x : ℝ, deriv (φ : ℝ → ℂ) x * (p x : ℂ)).re := by
        change -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * (p x : ℂ)).re =
          -(∫ x : ℝ, deriv (φ : ℝ → ℂ) x * (p x : ℂ)).re
        exact congrArg Neg.neg (integral_re hright)
  · calc
      (∫ x : ℝ, φ x * ((deriv p x : ℝ) : ℂ)).im =
          ∫ x : ℝ, (φ x * ((deriv p x : ℝ) : ℂ)).im := (integral_im hleft).symm
      _ = -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * (p x : ℂ)).im := by
        simpa [Complex.mul_im, ← deriv_im_schwartz] using
          integral_schwartz_im_mul_deriv_eq_neg p hpLip hp2 hdp2 hpTop hpBot φ
      _ = (-∫ x : ℝ, deriv (φ : ℝ → ℂ) x * (p x : ℂ)).im := by
        change -∫ x : ℝ, (deriv (φ : ℝ → ℂ) x * (p x : ℂ)).im =
          -(∫ x : ℝ, deriv (φ : ℝ → ℂ) x * (p x : ℂ)).im
        exact congrArg Neg.neg (integral_im hright)

/-- Complex `L²` representative of a real square-integrable function. -/
def realToComplexL2 (p : ℝ → ℝ) (hp : MemLp p 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  hp.ofReal.toLp (fun x => (p x : ℂ))

/-- A real Lipschitz `H¹` function with zero endpoints has its literal classical derivative as
its complex tempered-distribution derivative. -/
theorem realToComplexL2_weakDerivative
    (p : ℝ → ℝ) {C : NNReal} (hpLip : LipschitzWith C p)
    (hp2 : MemLp p 2 (volume : Measure ℝ))
    (hdp2 : MemLp (deriv p) 2 (volume : Measure ℝ))
    (hpTop : Tendsto p atTop (nhds 0)) (hpBot : Tendsto p atBot (nhds 0)) :
    ∂_{(1 : ℝ)}
        (realToComplexL2 p hp2 : 𝓢'(ℝ, ℂ)) =
      (realToComplexL2 (deriv p) hdp2 : 𝓢'(ℝ, ℂ)) := by
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  simp only [MeasureTheory.Lp.toTemperedDistribution_apply]
  let P := realToComplexL2 p hp2
  let D := realToComplexL2 (deriv p) hdp2
  have hPae : (P : ℝ → ℂ) =ᵐ[volume] fun x => (p x : ℂ) := by
    exact hp2.ofReal.coeFn_toLp
  have hDae : (D : ℝ → ℂ) =ᵐ[volume] fun x => ((deriv p x : ℝ) : ℂ) := by
    exact hdp2.ofReal.coeFn_toLp
  calc
    ∫ x : ℝ, (-∂_{(1 : ℝ)} φ) x • (P : ℝ → ℂ) x =
        ∫ x : ℝ, (-deriv (φ : ℝ → ℂ) x) * (p x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hPae] with x hx
      rw [hx]
      change (-((∂_{(1 : ℝ)} φ) x)) * (p x : ℂ) =
        -deriv (φ : ℝ → ℂ) x * (p x : ℂ)
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
    _ = ∫ x : ℝ, φ x * ((deriv p x : ℝ) : ℂ) := by
      rw [integral_schwartz_mul_deriv_ofReal_eq_neg p hpLip hp2 hdp2 hpTop hpBot φ]
      simpa only [neg_mul] using
        (integral_neg (fun x : ℝ => deriv (φ : ℝ → ℂ) x * (p x : ℂ)))
    _ = ∫ x : ℝ, φ x • (D : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hDae] with x hx
      rw [hx]
      rfl

end RHTower

end
