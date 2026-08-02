import GaloisForLFunctions.HTGeometry.HermiteGaussianExponential

/-!
# Completeness of the Hermite system on the Schwartz space

A Schwartz function orthogonal to every Hermite function has vanishing Gaussian moments, hence
vanishing integral against the Gaussian times any complex exponential.  Taking the exponent
imaginary, the Fourier transform of the Gaussian multiple vanishes identically, and Fourier
inversion forces the Gaussian multiple — hence the function itself — to be zero.

So the Hermite coefficient map is injective on the Schwartz space: the Hermite functions are a
complete system there.  This is the injectivity that the nuclearity argument needs.

* `fourier_gaussMul_eq_zero` : the Fourier transform of the Gaussian multiple vanishes.
* `hermiteSchwartz_complete` : **a Schwartz function orthogonal to every Hermite function is
  zero.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- The Gaussian multiple of a Schwartz function, as a Schwartz function. -/
def gaussMul (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := mulS f gaussianSchwartz

@[simp] theorem gaussMul_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    gaussMul f x = f x * ((gaussReal x : ℝ) : ℂ) := by
  rw [gaussMul, mulS_apply, gaussianSchwartz_apply]

/-- **The Fourier transform of the Gaussian multiple vanishes**, for a Schwartz function
orthogonal to every Hermite function: it is the exponential integral at an imaginary exponent. -/
theorem fourier_gaussMul_eq_zero {f : 𝓢(ℝ, ℂ)}
    (hf : ∀ n : ℕ, schwartzPair f (hermiteSchwartz n) = 0) (t : ℝ) :
    𝓕 ((gaussMul f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t = 0 := by
  have hexp := integral_gaussMul_exp_eq_zero hf (-(2 * (π : ℂ) * t) * Complex.I)
  rw [Real.fourier_eq', ← hexp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, gaussMul_apply]
  have hinner : (inner ℝ x t : ℝ) = x * t := Real.inner_apply x t
  rw [hinner]
  have hexpeq : Complex.exp ((((-2 * π * (x * t) : ℝ)) : ℂ) * Complex.I)
      = Complex.exp (-(2 * (π : ℂ) * t) * Complex.I * x) := by
    congr 1
    push_cast
    ring
  rw [hexpeq]
  ring

/-- **The Hermite functions are complete on the Schwartz space**: a Schwartz function orthogonal to
every Hermite function is zero. -/
theorem hermiteSchwartz_complete {f : 𝓢(ℝ, ℂ)}
    (hf : ∀ n : ℕ, schwartzPair f (hermiteSchwartz n) = 0) : f = 0 := by
  set g : 𝓢(ℝ, ℂ) := gaussMul f with hg
  have hFzero : 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = fun _ : ℝ => (0 : ℂ) :=
    funext fun t => fourier_gaussMul_eq_zero hf t
  have hFint : Integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) (volume : Measure ℝ) := by
    rw [hFzero]
    exact integrable_zero _ _ _
  have hinv := g.continuous.fourierInv_fourier_eq g.integrable hFint
  rw [hFzero] at hinv
  have hzeroInv : 𝓕⁻ (fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    show (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) (fun _ : ℝ => (0 : ℂ))) t = 0
    rw [VectorFourier.fourierIntegral]
    simp
  rw [hzeroInv] at hinv
  have hgzero : ∀ x : ℝ, f x * ((gaussReal x : ℝ) : ℂ) = 0 := by
    intro x
    have hx := (congrFun hinv x).symm
    rwa [hg, gaussMul_apply] at hx
  refine SchwartzMap.ext fun x => ?_
  have hgauss : ((gaussReal x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (gaussReal_pos x).ne'
  have hx := hgzero x
  show f x = 0
  exact (mul_eq_zero.mp hx).resolve_right hgauss

end GaloisForLFunctions

end
