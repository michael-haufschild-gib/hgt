import GaloisForLFunctions.HTGeometry.ContinuousTestPairing
import GaloisForLFunctions.HTGeometry.FlowMultiplicityMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# A finite spectral measure is determined by its trace pairings

Pairing a weight against the flow characters and integrating over the spectrum is, after Fubini,
the pairing of the weight with the characteristic function of the spectral measure.  Since the
characteristic function of a finite measure is continuous, the fundamental lemma of the calculus
of variations turns equality of all trace pairings into equality of the characteristic functions,
and a finite measure on the line is determined by its characteristic function.

This is Fourier inversion in the form the multiplicity-measure uniqueness needs: on a window,
where the spectral measure is finite, the trace pairings determine it.

* `integral_cWeightTransform_eq_integral_charFun` : the Fubini exchange.
* `measure_eq_of_forall_integral_cWeightTransform_eq` : the uniqueness.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section CharFunUniqueness

/-- The transform of a complex weight at a spectral point. -/
noncomputable def cWeightTransform (phi : ℝ → ℂ) (lam : ℝ) : ℂ :=
  ∫ t, phi t * flowCharacter lam t

theorem cWeightTransform_apply (phi : ℝ → ℂ) (lam : ℝ) :
    cWeightTransform phi lam = ∫ t, phi t * flowCharacter lam t := rfl

theorem flowCharacter_apply (lam t : ℝ) :
    flowCharacter lam t = Complex.exp (Complex.I * ((lam : ℂ) * (t : ℂ))) := rfl

theorem norm_flowCharacter (lam t : ℝ) : ‖flowCharacter lam t‖ = 1 := by
  rw [flowCharacter_apply, Complex.norm_exp]
  have hre : (Complex.I * ((lam : ℂ) * (t : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

theorem continuous_uncurry_flowCharacter :
    Continuous (fun p : ℝ × ℝ => flowCharacter p.1 p.2) := by
  have hmul : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * (p.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_ofReal.comp continuous_snd)
  exact Complex.continuous_exp.comp (continuous_const.mul hmul)

/-- The integrand of the trace pairing is integrable on the product. -/
theorem integrable_uncurry_weight (nu : Measure ℝ) [IsFiniteMeasure nu] {phi : ℝ → ℂ}
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) :
    Integrable (Function.uncurry fun lam t => phi t * flowCharacter lam t)
      (nu.prod MeasureTheory.volume) := by
  have hint : Integrable phi MeasureTheory.volume :=
    hphi.integrable_of_hasCompactSupport hsupp
  have hg : Integrable (fun p : ℝ × ℝ => phi p.2) (nu.prod MeasureTheory.volume) :=
    hint.comp_snd nu
  refine hg.mono ?_ ?_
  · exact (Continuous.aestronglyMeasurable
      ((hphi.comp continuous_snd).mul continuous_uncurry_flowCharacter))
  · refine Filter.Eventually.of_forall fun p => ?_
    show ‖phi p.2 * flowCharacter p.1 p.2‖ ≤ ‖phi p.2‖
    rw [norm_mul, norm_flowCharacter, mul_one]

/-- **The Fubini exchange.**  Integrating the weight transform over a finite spectral measure is
pairing the weight with that measure's characteristic function. -/
theorem integral_cWeightTransform_eq_integral_charFun (nu : Measure ℝ) [IsFiniteMeasure nu]
    {phi : ℝ → ℂ} (hphi : Continuous phi) (hsupp : HasCompactSupport phi) :
    ∫ lam, cWeightTransform phi lam ∂nu = ∫ t, phi t * charFun nu t := by
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun lam t => phi t * flowCharacter lam t)
    (integrable_uncurry_weight nu hphi hsupp)
  simp only [cWeightTransform_apply]
  rw [hswap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ∫ x, phi t * flowCharacter x t ∂nu = phi t * charFun nu t
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [charFun_apply_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun lam => ?_)
  show flowCharacter lam t = Complex.exp ((t : ℂ) * (lam : ℂ) * Complex.I)
  rw [flowCharacter_apply]
  congr 1
  ring

/-- **Uniqueness of a finite spectral measure from its trace pairings.**  Two finite measures on
the line whose weight transforms integrate identically against every continuous compactly
supported weight are equal. -/
theorem measure_eq_of_forall_integral_cWeightTransform_eq (nu mu : Measure ℝ)
    [IsFiniteMeasure nu] [IsFiniteMeasure mu]
    (h : ∀ phi : ℝ → ℂ, Continuous phi → HasCompactSupport phi →
      ∫ lam, cWeightTransform phi lam ∂nu = ∫ lam, cWeightTransform phi lam ∂mu) :
    nu = mu := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  refine eq_of_forall_integral_mul_eq (f := charFun nu) (g := charFun mu)
    continuous_charFun continuous_charFun ?_ t
  intro phi hphi hsupp
  rw [← integral_cWeightTransform_eq_integral_charFun nu hphi hsupp,
    ← integral_cWeightTransform_eq_integral_charFun mu hphi hsupp]
  exact h phi hphi hsupp

end CharFunUniqueness

end GaloisForLFunctions.HTGeometry
