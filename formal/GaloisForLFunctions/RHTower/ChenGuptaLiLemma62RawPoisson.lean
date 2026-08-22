import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62Poisson

/-!
# Chen--Gupta--Li Lemma 6.2: raw Poisson normalization

The pre-existing Poisson representation is normalized by CGL's factor `N/q`.
This module introduces the literal raw additive-character Fourier transform
and records the exact normalization identity needed to state Lemma 6.2 in the
paper's physical normalization.
-/

open Complex
open scoped BigOperators FourierTransform

namespace RHTower

noncomputable section

/-- The raw additive-character Fourier series in CGL equation (6.1), before
the exterior `N/q` normalization used by the Mellin representation. -/
def cglLemma62RawPoissonTransform
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) : ℂ :=
  ∑ a : ZMod Q.value, ∑' m : ℤ,
    χ a * ZMod.stdAddChar (a * (m : ZMod Q.value)) *
      𝓕 (cglSmoothBumpHt w.toCGLSmoothBump t : ℝ → ℂ)
        (cglAffineFourierScale N Q * (m : ℝ))

/-- CGL's normalized Poisson transform is exactly the exterior `N/q` factor
times its literal raw additive-character Fourier series. -/
theorem cglLemma62_normalizedPoisson_eq_scale_mul_raw
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    cglLemma62NormalizedPoissonTransform w N Q χ t =
      (cglAffineFourierScale N Q : ℂ) *
        cglLemma62RawPoissonTransform w N Q χ t := by
  unfold cglLemma62NormalizedPoissonTransform cglLemma62RawPoissonTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  ring

/-- CGL's physical smoothed character sum equals the exterior `N/q` scale
times the literal raw additive-character Fourier series. -/
theorem cglLemma62_smoothedCharacterSum_eq_scale_mul_raw
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (χ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    cglLemma62SmoothedCharacterSum w N Q χ t =
      (cglAffineFourierScale N Q : ℂ) *
        cglLemma62RawPoissonTransform w N Q χ t := by
  rw [cglLemma62_smoothedCharacterSum_eq_normalizedPoissonTransform,
    cglLemma62_normalizedPoisson_eq_scale_mul_raw]

end

end RHTower
