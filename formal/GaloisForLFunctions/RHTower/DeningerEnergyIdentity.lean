import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The completing-the-square energy identity

On one Fourier coefficient the radial energy splits as the boundary term plus the energy of the
deviation from the decaying exponential:

`∫₀^∞ (‖u'‖² + m²‖u‖²) = m ‖u 0‖² + ∫₀^∞ ‖u' + m u‖²`.

The cross term is the total derivative of the squared modulus, which integrates to minus its
boundary value when the coefficient decays.  Equality of the two energies therefore holds exactly
when `u' + m u` vanishes, that is for the Poisson profile.

* `deningerNormSq_hasDerivAt` : the derivative of the squared modulus.
* `deningerEnergy_expand` : the pointwise expansion of the deviation energy.
* `deningerEnergy_identity` : the energy identity.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

section EnergyIdentity

/-- The squared modulus in real coordinates. -/
theorem deningerNormSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

/-- **The derivative of the squared modulus** along a differentiable path. -/
theorem deningerNormSq_hasDerivAt {u : ℝ → ℂ} {v : ℂ} {r : ℝ} (h : HasDerivAt u v r) :
    HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ((starRingEnd ℂ) (u r) * v).re) r := by
  have hre : HasDerivAt (fun s => (u s).re) v.re r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have him : HasDerivAt (fun s => (u s).im) v.im r :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  have hsum := (hre.mul hre).add (him.mul him)
  have hfun : (fun s => ‖u s‖ ^ 2)
      = fun s => (u s).re * (u s).re + (u s).im * (u s).im := by
    funext s
    exact deningerNormSq_eq (u s)
  have hval : 2 * ((starRingEnd ℂ) (u r) * v).re
      = v.re * (u r).re + (u r).re * v.re + (v.im * (u r).im + (u r).im * v.im) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hfun, hval]
  exact hsum

/-- **The pointwise expansion of the deviation energy.** -/
theorem deningerEnergy_expand (m : ℝ) (a b : ℂ) :
    ‖a + (m : ℂ) * b‖ ^ 2
      = ‖a‖ ^ 2 + 2 * m * ((starRingEnd ℂ) b * a).re + m ^ 2 * ‖b‖ ^ 2 := by
  rw [deningerNormSq_eq, deningerNormSq_eq, deningerNormSq_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **The energy identity.**  The radial energy is the boundary term plus the energy of the
deviation from the decaying exponential; the cross term is the total derivative of the squared
modulus, which integrates to minus its boundary value. -/
theorem deningerEnergy_identity {u v : ℝ → ℂ} {m : ℝ}
    (hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt u (v r) r)
    (hcont : ContinuousWithinAt (fun r => ‖u r‖ ^ 2) (Ici (0 : ℝ)) 0)
    (hlim : Tendsto (fun r => ‖u r‖ ^ 2) atTop (𝓝 0))
    (hcross : IntegrableOn (fun r => 2 * ((starRingEnd ℂ) (u r) * v r).re) (Ioi (0 : ℝ))) :
    (∫ r in Ioi (0 : ℝ), 2 * m * ((starRingEnd ℂ) (u r) * v r).re) = -(m * ‖u 0‖ ^ 2) := by
  have hderiv' : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s => ‖u s‖ ^ 2) (2 * ((starRingEnd ℂ) (u r) * v r).re) r :=
    fun r hr => deningerNormSq_hasDerivAt (hderiv r hr)
  have hbase := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv' hcross hlim
  have hfun : (fun r => 2 * m * ((starRingEnd ℂ) (u r) * v r).re)
      = fun r => m * (2 * ((starRingEnd ℂ) (u r) * v r).re) := by
    funext r
    ring
  rw [hfun, integral_const_mul, hbase, zero_sub]
  ring

end EnergyIdentity

end RHTower
