import GaloisForLFunctions.RHTower.XiThetaSourceSeam
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import Mathlib.Analysis.MellinInversion

/-!
# The completed critical trace is the cosine trace of the positive theta source

The Mellin transform defining the entire completion becomes an ordinary Fourier transform after
the logarithmic change of variables. On the critical line the Mellin pullback is exactly
xiThetaLogSource, so completedRiemannZeta₀ is one half of its Fourier transform.

The source is the sum of its positive half and its reflection. After proving the required
integrability directly from the strong functional-equation pair, reflection turns the completed
trace into the even part of the positive-half Fourier transform. Since the positive source is real,
the completed trace is exactly its real Fourier component.

This identifies the actual transform exposed by completion. It is Fourier in log x, not Laplace in
x; therefore square-rate Laplace interpolation is not directly a reader of the completed trace.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- On the critical line, the logarithmic Mellin pullback is the completed theta source. -/
theorem criticalMellinPullback_eq (t u : ℝ) :
    Real.exp (-((((1 : ℂ) / 2 + (t : ℂ) * I) / 2).re) * u) •
        modifiedEvenKernel (Real.exp (-u)) =
      xiThetaLogSource u := by
  rw [← xiThetaLogSource_neg u]
  simp only [xiThetaLogSource, neg_div, Complex.div_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  norm_num
  left
  congr 1
  ring

/-- Exact completed critical-line trace in logarithmic Fourier coordinates. -/
theorem completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) =
      𝓕 xiThetaLogSource (t / (4 * π)) / 2 := by
  change mellin modifiedEvenKernel (((1 : ℂ) / 2 + (t : ℂ) * I) / 2) / 2 = _
  rw [mellin_eq_fourier]
  apply congrArg (fun z : ℂ => z / 2)
  let freq : ℝ := ((((1 : ℂ) / 2 + (t : ℂ) * I) / 2).im) / (2 * π)
  have hfun :
      (fun u : ℝ =>
        Real.exp (-((((1 : ℂ) / 2 + (t : ℂ) * I) / 2).re) * u) •
          modifiedEvenKernel (Real.exp (-u))) =
        xiThetaLogSource := by
    funext u
    exact criticalMellinPullback_eq t u
  have hfreq : freq = t / (4 * π) := by
    dsimp [freq]
    norm_num [Complex.div_im, Complex.add_im, Complex.mul_im]
    field_simp
    ring
  change 𝓕 (fun u : ℝ =>
      Real.exp (-((((1 : ℂ) / 2 + (t : ℂ) * I) / 2).re) * u) •
        modifiedEvenKernel (Real.exp (-u))) freq =
    𝓕 xiThetaLogSource (t / (4 * π))
  calc
    𝓕 (fun u : ℝ =>
        Real.exp (-((((1 : ℂ) / 2 + (t : ℂ) * I) / 2).re) * u) •
          modifiedEvenKernel (Real.exp (-u))) freq =
        𝓕 xiThetaLogSource freq :=
      congrArg (fun f : ℝ → ℂ => 𝓕 f freq) hfun
    _ = 𝓕 xiThetaLogSource (t / (4 * π)) := congrArg (𝓕 xiThetaLogSource) hfreq

private theorem xi_rexp_neg_deriv :
    ∀ x ∈ univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem xi_rexp_neg_image : Real.exp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem xi_rexp_neg_injOn : univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem xi_rexp_cexp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

/-- Mellin convergence unconditionally discharges integrability of the logarithmic pullback. -/
theorem integrable_logMellinPullback_of_mellinConvergent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (σ : ℝ) (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← xi_rexp_neg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ xi_rexp_neg_deriv xi_rexp_neg_injOn] at hf
  replace hf :
      Integrable (fun u : ℝ => Complex.exp (-(σ : ℂ) * u) • f (Real.exp (-u))) := by
    simpa [xi_rexp_cexp] using hf
  norm_cast at hf

theorem xiThetaLogSource_integrable : Integrable xiThetaLogSource := by
  have hm : MellinConvergent modifiedEvenKernel (((1 : ℝ) / 4 : ℝ) : ℂ) :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (((1 : ℝ) / 4 : ℝ) : ℂ)).1
  have hi := integrable_logMellinPullback_of_mellinConvergent
    modifiedEvenKernel ((1 : ℝ) / 4) hm
  apply hi.congr
  filter_upwards with u
  convert criticalMellinPullback_eq 0 u using 1
  all_goals norm_num

theorem xiThetaPositiveSource_integrable : Integrable xiThetaPositiveSource := by
  exact xiThetaLogSource_integrable.indicator measurableSet_Ioi

theorem xiThetaReflectedSource_integrable : Integrable xiThetaReflectedSource := by
  change Integrable (xiThetaPositiveSource ∘ fun u : ℝ => -u)
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
    xiThetaPositiveSource_integrable

/-- Reflection of the physical half-source becomes reflection of Fourier frequency. -/
theorem fourier_xiThetaReflectedSource (w : ℝ) :
    𝓕 xiThetaReflectedSource w = 𝓕 xiThetaPositiveSource (-w) := by
  change 𝓕 (xiThetaPositiveSource ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)) w =
    𝓕 xiThetaPositiveSource (-w)
  simpa using Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) xiThetaPositiveSource w

/-- The full completed source trace is the even Fourier part of its positive half. -/
theorem fourier_xiThetaLogSource_split (w : ℝ) :
    𝓕 xiThetaLogSource w =
      𝓕 xiThetaPositiveSource w + 𝓕 xiThetaPositiveSource (-w) := by
  rw [show xiThetaLogSource = xiThetaPositiveSource + xiThetaReflectedSource by
    funext u
    exact xiThetaLogSource_split u]
  calc
    𝓕 (xiThetaPositiveSource + xiThetaReflectedSource) w =
        𝓕 xiThetaPositiveSource w + 𝓕 xiThetaReflectedSource w := by
      rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
      simp only [Pi.add_apply, smul_add]
      rw [integral_add]
      · exact (Real.fourierIntegral_convergent_iff w).2 xiThetaPositiveSource_integrable
      · exact (Real.fourierIntegral_convergent_iff w).2 xiThetaReflectedSource_integrable
    _ = 𝓕 xiThetaPositiveSource w + 𝓕 xiThetaPositiveSource (-w) := by
      rw [fourier_xiThetaReflectedSource]

theorem xiThetaPositiveSource_ofReal_re (u : ℝ) :
    ((xiThetaPositiveSource u).re : ℂ) = xiThetaPositiveSource u := by
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · rw [xiThetaPositiveSource, indicator_of_mem hu,
      xiThetaLogSource_eq_positiveFormula hu]
    simp [xiThetaPositiveFormula]
    left
    convert Complex.ofReal_exp_ofReal_re (u / 4) using 1 <;> push_cast <;> ring
  · simp [xiThetaPositiveSource, indicator_of_notMem hu]

open scoped ComplexConjugate in
theorem conj_fourier_xiThetaPositiveSource (w : ℝ) :
    conj (𝓕 xiThetaPositiveSource w) = 𝓕 xiThetaPositiveSource (-w) := by
  have hsource :
      (fun u : ℝ => ((xiThetaPositiveSource u).re : ℂ)) =
        xiThetaPositiveSource := by
    funext u
    exact xiThetaPositiveSource_ofReal_re u
  rw [← hsource]
  exact conj_fourier_ofReal xiThetaPositiveSource_integrable.re w

/-- The critical trace is the even part of the one-sided Fourier transform. -/
theorem completedRiemannZeta₀_critical_eq_positiveFourierEvenPart (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) =
      (𝓕 xiThetaPositiveSource (t / (4 * π)) +
        𝓕 xiThetaPositiveSource (-(t / (4 * π)))) / 2 := by
  rw [completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource,
    fourier_xiThetaLogSource_split]

/-- Since the positive theta source is real, the completed critical trace is its cosine trace. -/
theorem completedRiemannZeta₀_critical_eq_re_positiveFourier (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) =
      ((𝓕 xiThetaPositiveSource (t / (4 * π))).re : ℂ) := by
  rw [completedRiemannZeta₀_critical_eq_positiveFourierEvenPart,
    ← conj_fourier_xiThetaPositiveSource]
  apply Complex.ext <;> simp

end RHTower
