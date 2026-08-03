import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain
import GaloisForLFunctions.HTGeometry.L2DecayProfile

/-!
# The real restriction of the centered xi function is Schwartz

The centered xi function restricted to the real axis is the Fourier transform of the theta cusp
Schwartz source, hence itself a Schwartz function.  Consequently every polynomial weight of it is
square integrable, and every polynomial moment of a square-integrable function against it converges
absolutely.  This is the finiteness layer any moment argument on the critical line needs.
-/

open Complex MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- The centered xi function restricted to the real axis, as a Schwartz function: it is the
Fourier transform of the theta cusp source. -/
def xiCSchwartz : 𝓢(ℝ, ℂ) := 𝓕 xiThetaSchwartzSource

@[simp] theorem xiCSchwartz_apply (t : ℝ) : xiCSchwartz t = XiC (t : ℂ) :=
  fourier_xiThetaSchwartzSource t

theorem continuous_XiC_ofReal : Continuous (fun x : ℝ => XiC (x : ℂ)) :=
  continuous_iff_continuousAt.mpr fun x => by
    simpa only [Function.comp_def] using
      (XiC_analytic (x : ℂ) (Set.mem_univ _)).continuousAt.comp
        Complex.continuous_ofReal.continuousAt

/-- **Every polynomial weight of the real restriction of the centered xi function is square
integrable.**  The restriction is a Schwartz function, so it beats every polynomial. -/
theorem memLp_pow_mul_XiC_ofReal (n : ℕ) :
    MemLp (fun x : ℝ => (x : ℂ) ^ n * XiC (x : ℂ)) 2 volume := by
  obtain ⟨C₀, hC₀, hb₀⟩ := xiCSchwartz.decay n 0
  obtain ⟨C₁, hC₁, hb₁⟩ := xiCSchwartz.decay (n + 1) 0
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ n * XiC (x : ℂ)) volume :=
    ((Complex.measurable_ofReal.pow_const n).aestronglyMeasurable).mul
      continuous_XiC_ofReal.aestronglyMeasurable
  refine HTGeometry.memLp_two_of_decayProfile hmeas (C := C₀ + C₁) (fun t => ?_)
  have h0 : |t| ^ n * ‖XiC (t : ℂ)‖ ≤ C₀ := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, xiCSchwartz_apply] using hb₀ t
  have h1 : |t| ^ (n + 1) * ‖XiC (t : ℂ)‖ ≤ C₁ := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, xiCSchwartz_apply] using hb₁ t
  have hnorm : ‖((t : ℂ) ^ n * XiC (t : ℂ))‖ = |t| ^ n * ‖XiC (t : ℂ)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have hkey : |t| ^ n * ‖XiC (t : ℂ)‖ * (1 + |t|) ≤ C₀ + C₁ := by
    have hexp : |t| ^ n * ‖XiC (t : ℂ)‖ * (1 + |t|) =
        |t| ^ n * ‖XiC (t : ℂ)‖ + |t| ^ (n + 1) * ‖XiC (t : ℂ)‖ := by
      rw [pow_succ]; ring
    rw [hexp]
    linarith
  rw [hnorm]
  calc |t| ^ n * ‖XiC (t : ℂ)‖
      = (|t| ^ n * ‖XiC (t : ℂ)‖ * (1 + |t|)) * (1 + |t|)⁻¹ := by
        field_simp
    _ ≤ (C₀ + C₁) * (1 + |t|)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)

/-- **All polynomial moments of a square-integrable function against the real restriction of the
centered xi function converge absolutely.** -/
theorem integrable_mul_pow_mul_XiC {f : ℝ → ℂ} (hf : MemLp f 2 volume) (n : ℕ) :
    Integrable (fun x : ℝ => f x * ((x : ℂ) ^ n * XiC (x : ℂ))) volume :=
  hf.integrable_mul (memLp_pow_mul_XiC_ofReal n)

end RHTower
