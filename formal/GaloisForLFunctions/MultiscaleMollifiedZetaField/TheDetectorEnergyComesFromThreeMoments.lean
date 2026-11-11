import GaloisForLFunctions.MultiscaleMollifiedZetaField.CauchyJetsOfTheTwistedMoment
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts

/-!
# The three-moment identity for the mollified detector

Polarization removes the mixed coefficient moment. Vertical integration
by parts converts the remaining complex derivative square into the second
displacement derivative and two explicit taper terms.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem taper_ibp {W W₁ u u₁ : ℝ → ℝ}
    (hW : ∀ t, HasDerivAt W (W₁ t) t) (hW₁ : Continuous W₁)
    (hWc : HasCompactSupport W) (hu : ∀ t, HasDerivAt u (u₁ t) t)
    (hu₁ : Continuous u₁) :
    (∫ t, W t * u₁ t) = -(∫ t, W₁ t * u t) := by
  have hW0 : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  have hu0 : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have hW₁c : HasCompactSupport W₁ := by
    have he : W₁ = deriv W := funext fun t => (hW t).deriv.symm
    rw [he]
    exact hWc.deriv
  have hi₁ := (hW₁.mul hu0).integrable_of_hasCompactSupport (μ := volume) hW₁c.mul_right
  have hi₂ := (hW0.mul hu₁).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  change Integrable (fun t => W₁ t * u t) volume at hi₁
  change Integrable (fun t => W t * u₁ t) volume at hi₂
  have he := integral_deriv_eq_zero_of_hasCompactSupport
    (fun t => (hW t).mul (hu t)) ((hW₁.mul hu0).add (hW0.mul hu₁)) hWc.mul_right
  rw [integral_add hi₁ hi₂] at he
  linarith only [he]

private theorem taper_ibp_twice {W W₁ W₂ u u₁ u₂ : ℝ → ℝ}
    (hW : ∀ t, HasDerivAt W (W₁ t) t)
    (hW₁ : ∀ t, HasDerivAt W₁ (W₂ t) t) (hW₂ : Continuous W₂)
    (hWc : HasCompactSupport W)
    (hu : ∀ t, HasDerivAt u (u₁ t) t)
    (hu₁ : ∀ t, HasDerivAt u₁ (u₂ t) t) (hu₂ : Continuous u₂) :
    (∫ t, W t * u₂ t) = ∫ t, W₂ t * u t := by
  have hW₁cont : Continuous W₁ := continuous_iff_continuousAt.mpr fun t => (hW₁ t).continuousAt
  have hu₁cont : Continuous u₁ := continuous_iff_continuousAt.mpr fun t => (hu₁ t).continuousAt
  have hW₁c : HasCompactSupport W₁ := by
    have he : W₁ = deriv W := funext fun t => (hW t).deriv.symm
    rw [he]
    exact hWc.deriv
  rw [taper_ibp hW hW₁cont hWc hu₁ hu₂,
    taper_ibp hW₁ hW₂ hW₁c hu hu₁cont, neg_neg]

/-- The first displacement jet of a squared holomorphic field. -/
def displacementEnergyFirst (f f₁ : ℂ) : ℝ := -2 * (f₁ * conj f).re

/-- The second displacement jet of a squared holomorphic field. -/
def displacementEnergySecond (f f₁ f₂ : ℂ) : ℝ :=
  2 * (f₂ * conj f).re + 2 * ‖f₁‖ ^ 2

private theorem hasDerivAt_im_mul_conj {f g f₁ g₁ : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * f₁ t) t) (hg : HasDerivAt g (I * g₁ t) t) :
    HasDerivAt (fun x => (f x * conj (g x)).im)
      ((f₁ t * conj (g t) - f t * conj (g₁ t)).re) t := by
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hg
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf.mul hc)
  change HasDerivAt (fun x => (f x * conj (g x)).im)
    ((I * f₁ t * conj (g t) + f t * conj (I * g₁ t)).im) t at hh
  apply hh.congr_deriv
  simp only [Complex.add_re, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.sub_re]
  ring

private theorem hasDerivAt_norm_square {f f₁ : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * f₁ t) t) :
    HasDerivAt (fun x => ‖f x‖ ^ 2) (-2 * (f₁ t * conj (f t)).im) t := by
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.mul hc)
  change HasDerivAt (fun x => (f x * conj (f x)).re)
    ((I * f₁ t * conj (f t) + f t * conj (I * f₁ t)).re) t at hh
  have he : (fun x => (f x * conj (f x)).re) = fun x => ‖f x‖ ^ 2 := by
    funext x
    rw [Complex.mul_conj]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [he] at hh
  apply hh.congr_deriv
  simp only [Complex.add_re, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem hasDerivAt_norm_square_first {f f₁ f₂ : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * f₁ t) t) (hf₁ : HasDerivAt f₁ (I * f₂ t) t) :
    HasDerivAt (fun x => -2 * (f₁ x * conj (f x)).im)
      (2 * ‖f₁ t‖ ^ 2 - 2 * (f₂ t * conj (f t)).re) t := by
  have hh := (hasDerivAt_im_mul_conj hf₁ hf).const_mul (-2)
  apply hh.congr_deriv
  rw [Complex.sub_re, Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  ring

/-- Pointwise polarization leaves precisely one vertical second derivative
and one vertical mixed derivative. -/
theorem detectorEnergy_three_moment_algebra (f f₁ f₂ g g₁ : ℂ) (lam : ℝ) :
    ‖f + (lam : ℂ) * f₁ - g‖ ^ 2 =
      ‖f - g‖ ^ 2 - lam / 2 *
        (displacementEnergyFirst f f₁ - displacementEnergyFirst g g₁ +
          displacementEnergyFirst (f - g) (f₁ - g₁)) +
      lam ^ 2 / 4 * displacementEnergySecond f f₁ f₂ -
      lam * (f₁ * conj g - f * conj g₁).re +
      lam ^ 2 / 4 * (2 * ‖f₁‖ ^ 2 - 2 * (f₂ * conj f).re) := by
  simp only [displacementEnergyFirst, displacementEnergySecond,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The exact tapered detector identity for a vertical holomorphic field and
its coefficient correction. All boundary contributions are taper integrals. -/
theorem integral_detectorEnergy_three_moments
    {W W₁ W₂ : ℝ → ℝ} {f f₁ f₂ g g₁ : ℝ → ℂ}
    (hW : ∀ t, HasDerivAt W (W₁ t) t)
    (hW₁ : ∀ t, HasDerivAt W₁ (W₂ t) t) (hW₂ : Continuous W₂)
    (hWc : HasCompactSupport W)
    (hf : ∀ t, HasDerivAt f (I * f₁ t) t)
    (hf₁ : ∀ t, HasDerivAt f₁ (I * f₂ t) t) (hf₂ : Continuous f₂)
    (hg : ∀ t, HasDerivAt g (I * g₁ t) t) (hg₁ : Continuous g₁) (lam : ℝ) :
    (∫ t, W t * ‖f t + (lam : ℂ) * f₁ t - g t‖ ^ 2) =
      (∫ t, W t * ‖f t - g t‖ ^ 2) - lam / 2 *
        (∫ t, W t * (displacementEnergyFirst (f t) (f₁ t) -
          displacementEnergyFirst (g t) (g₁ t) +
          displacementEnergyFirst (f t - g t) (f₁ t - g₁ t))) +
      lam ^ 2 / 4 * (∫ t, W t * displacementEnergySecond (f t) (f₁ t) (f₂ t)) +
      lam * (∫ t, W₁ t * (f t * conj (g t)).im) +
      lam ^ 2 / 4 * (∫ t, W₂ t * ‖f t‖ ^ 2) := by
  have hW0 : Continuous W := continuous_iff_continuousAt.mpr fun t => (hW t).continuousAt
  have hW1 : Continuous W₁ := continuous_iff_continuousAt.mpr fun t => (hW₁ t).continuousAt
  have hf0 : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hf1 : Continuous f₁ := continuous_iff_continuousAt.mpr fun t => (hf₁ t).continuousAt
  have hg0 : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  let a : ℝ → ℝ := fun t => displacementEnergyFirst (f t) (f₁ t) -
    displacementEnergyFirst (g t) (g₁ t) +
    displacementEnergyFirst (f t - g t) (f₁ t - g₁ t)
  let b : ℝ → ℝ := fun t => displacementEnergySecond (f t) (f₁ t) (f₂ t)
  let c : ℝ → ℝ := fun t => (f₁ t * conj (g t) - f t * conj (g₁ t)).re
  let v : ℝ → ℝ := fun t => 2 * ‖f₁ t‖ ^ 2 - 2 * (f₂ t * conj (f t)).re
  have ha : Continuous a := by dsimp only [a, displacementEnergyFirst]; fun_prop
  have hb : Continuous b := by dsimp only [b, displacementEnergySecond]; fun_prop
  have hc : Continuous c := by dsimp only [c]; fun_prop
  have hv : Continuous v := by dsimp only [v]; fun_prop
  have hfirst : (∫ t, W t * c t) = -(∫ t, W₁ t * (f t * conj (g t)).im) :=
    taper_ibp hW hW1 hWc (fun t => hasDerivAt_im_mul_conj (hf t) (hg t)) hc
  have hsecond : (∫ t, W t * v t) = ∫ t, W₂ t * ‖f t‖ ^ 2 :=
    taper_ibp_twice hW hW₁ hW₂ hWc
      (fun t => hasDerivAt_norm_square (hf t))
      (fun t => hasDerivAt_norm_square_first (hf t) (hf₁ t)) hv
  have hH : Integrable (fun t => W t * ‖f t - g t‖ ^ 2) volume :=
    (hW0.mul ((hf0.sub hg0).norm.pow 2)).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  have hA := (hW0.mul ha).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  have hB := (hW0.mul hb).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  have hC := (hW0.mul hc).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  have hV := (hW0.mul hv).integrable_of_hasCompactSupport (μ := volume) hWc.mul_right
  have he : (∫ t, W t * ‖f t + (lam : ℂ) * f₁ t - g t‖ ^ 2) =
      (∫ t, W t * ‖f t - g t‖ ^ 2) - lam / 2 * (∫ t, W t * a t) +
        lam ^ 2 / 4 * (∫ t, W t * b t) - lam * (∫ t, W t * c t) +
        lam ^ 2 / 4 * (∫ t, W t * v t) := by
    calc
      _ = ∫ t, W t * ‖f t - g t‖ ^ 2 - lam / 2 * (W t * a t) +
          lam ^ 2 / 4 * (W t * b t) - lam * (W t * c t) +
          lam ^ 2 / 4 * (W t * v t) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [detectorEnergy_three_moment_algebra]
        dsimp only [a, b, c, v]
        ring
      _ = _ := by
        rw [integral_add
          (f := fun t => W t * ‖f t - g t‖ ^ 2 - lam / 2 * (W t * a t) +
            lam ^ 2 / 4 * (W t * b t) - lam * (W t * c t))
          (g := fun t => lam ^ 2 / 4 * (W t * v t))
          (((hH.sub (hA.const_mul _)).add (hB.const_mul _)).sub (hC.const_mul _))
          (hV.const_mul _),
          integral_sub
            (f := fun t => W t * ‖f t - g t‖ ^ 2 - lam / 2 * (W t * a t) +
              lam ^ 2 / 4 * (W t * b t)) (g := fun t => lam * (W t * c t))
            ((hH.sub (hA.const_mul _)).add (hB.const_mul _)) (hC.const_mul _),
          integral_add
            (f := fun t => W t * ‖f t - g t‖ ^ 2 - lam / 2 * (W t * a t))
            (g := fun t => lam ^ 2 / 4 * (W t * b t))
            (hH.sub (hA.const_mul _)) (hB.const_mul _),
          integral_sub hH (show Integrable (fun t => lam / 2 * (W t * a t)) volume from
            hA.const_mul _)]
        simp only [integral_const_mul]
  rw [he, hfirst, hsecond]
  simp only [a, b, mul_neg, sub_neg_eq_add]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
