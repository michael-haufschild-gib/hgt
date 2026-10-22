/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.CCM.CCMLogarithmicApertureUnitary
import GaloisForLFunctions.RHTower.CCM.CCMTranslationInvariance
import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilMatrix

/-!
# CCM logarithmic Weil-form transport

This file formalizes the remaining exact content of Connes--Consani--Moscovici (2025),
Proposition 3.2(ii), together with the finite-aperture form of the preceding inversion-splitting
lemma for the Weil functional.

It constructs literal complex `L¹(ℝ₊*,d*u)` sources, multiplicative involution and Haar
convolution, proves that logarithm transports the involutive convolution algebra, defines both
two-sided `Ψ` and one-sided `Ψ#` from the published polar, archimedean, and finite von Mangoldt
components, proves `Ψ(H)=Ψ#(H+H∘(-·))`, and derives
`QW(κf,κg)=Ψ#(q(f,g)∘log)` for bundled interval sources.  No RH or spectral premise is used.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace RHTower

/-- Literal complex `L¹(ℝ₊*,d*u)` source. -/
structure CCMMultiplicativeL1Source where
  toFun : MellinL2.PosReal → ℂ
  integrable : Integrable toFun MellinL2.multiplicativeHaar

instance : CoeFun CCMMultiplicativeL1Source
    (fun _ => MellinL2.PosReal → ℂ) := ⟨CCMMultiplicativeL1Source.toFun⟩

/-- Transport `L¹(ℝ,dx)` to `L¹(ℝ₊*,d*u)` by the logarithm. -/
def ccmMultiplicativeLogPush (f : CCML1Source) : CCMMultiplicativeL1Source where
  toFun u := f (MellinL2.expMeasurableEquiv.symm u)
  integrable :=
    MellinL2.exp_measurePreserving.symm.integrable_comp_of_integrable f.integrable

/-- Multiplicative involution `F*(u)=conj(F(u⁻¹))`. -/
def ccmPosInv (u : MellinL2.PosReal) : MellinL2.PosReal :=
  ⟨(u : ℝ)⁻¹, by
    simpa only [Set.mem_Ioi] using inv_pos.mpr u.property⟩

def ccmPosMul (u v : MellinL2.PosReal) : MellinL2.PosReal :=
  ⟨(u : ℝ) * (v : ℝ), by
    simpa only [Set.mem_Ioi] using mul_pos u.property v.property⟩

def ccmMultiplicativeL1Involution (f : CCMMultiplicativeL1Source)
    (u : MellinL2.PosReal) : ℂ :=
  conj (f (ccmPosInv u))

/-- Haar convolution on `ℝ₊*`. -/
def ccmMultiplicativeL1Convolution
    (f g : MellinL2.PosReal → ℂ) (u : MellinL2.PosReal) : ℂ :=
  ∫ x : MellinL2.PosReal, f x * g (ccmPosMul (ccmPosInv x) u)
    ∂MellinL2.multiplicativeHaar

/-- Literal multiplicative source correlation `(F* * G)(u)`. -/
def ccmMultiplicativeStarConvolution
    (f g : CCMMultiplicativeL1Source) (u : MellinL2.PosReal) : ℂ :=
  ccmMultiplicativeL1Convolution (ccmMultiplicativeL1Involution f) g u

theorem expMeasurableEquiv_symm_inv_exp (t : ℝ) :
    MellinL2.expMeasurableEquiv.symm
      (ccmPosInv (MellinL2.expMeasurableEquiv t)) = -t := by
  apply MellinL2.expMeasurableEquiv.injective
  apply Subtype.ext
  rw [MellinL2.expMeasurableEquiv.apply_symm_apply]
  change (Real.exp t)⁻¹ = Real.exp (-t)
  exact (Real.exp_neg t).symm

theorem expMeasurableEquiv_symm_inv_mul_exp (t y : ℝ) :
    MellinL2.expMeasurableEquiv.symm
      (ccmPosMul (ccmPosInv (MellinL2.expMeasurableEquiv t))
        (MellinL2.expMeasurableEquiv y)) = y - t := by
  apply MellinL2.expMeasurableEquiv.injective
  apply Subtype.ext
  rw [MellinL2.expMeasurableEquiv.apply_symm_apply]
  change (Real.exp t)⁻¹ * Real.exp y = Real.exp (y - t)
  rw [show (Real.exp t)⁻¹ = Real.exp (-t) from (Real.exp_neg t).symm,
    ← Real.exp_add]
  congr 1
  ring

/-- `log : ℝ₊* → ℝ` transports the literal involutive convolution algebra. -/
theorem ccmMultiplicativeStarConvolution_logPush
    (f g : CCML1Source) (y : ℝ) :
    ccmMultiplicativeStarConvolution
        (ccmMultiplicativeLogPush f) (ccmMultiplicativeLogPush g)
        (MellinL2.expMeasurableEquiv y) =
      ccmStarConvolution f g y := by
  unfold ccmMultiplicativeStarConvolution ccmMultiplicativeL1Convolution
    ccmMultiplicativeL1Involution ccmMultiplicativeLogPush
    ccmStarConvolution ccmL1Convolution ccmL1Involution
  rw [← MellinL2.exp_measurePreserving.integral_comp']
  apply integral_congr_ae
  filter_upwards with t
  rw [expMeasurableEquiv_symm_inv_exp,
    expMeasurableEquiv_symm_inv_mul_exp]

/-! ### Exact finite-aperture Weil distributions -/

/-- Complex one-sided archimedean distribution `W_ℝ#` in logarithmic coordinates. -/
def ccmRestrictedArchimedeanSharp (a : ℝ) (F : ℝ → ℂ) : ℂ :=
  F 0 / 2 * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ) +
    ∫ h in Ioc (0 : ℝ) (2 * a),
      ((Real.exp (h / 2) : ℂ) * F h - F 0) /
        (Real.exp h - Real.exp (-h) : ℝ)

/-- Literal complex `Ψ# = W₀,₂# - W_ℝ# - ΣW_p#` on the finite logarithmic aperture.  The
polar and finite von Mangoldt terms are the existing critical-Mellin Stieltjes pairing. -/
def ccmRestrictedWeilSharp (a : ℝ) (F : ℝ → ℂ) : ℂ :=
  criticalMellinStieltjesPairing a F - ccmRestrictedArchimedeanSharp a F

/-- Two-sided polar/prime part of the finite-aperture Weil functional. -/
def ccmRestrictedPolarPrimeFull (a : ℝ) (H : ℝ → ℂ) : ℂ :=
  (∫ h in Ioc (0 : ℝ) (2 * a),
      (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)) -
    ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      (criticalMellinAtomWeight k : ℂ) *
        (H (Real.log k) + H (-Real.log k))

/-- Two-sided archimedean part of the finite-aperture Weil functional. -/
def ccmRestrictedArchimedeanFull (a : ℝ) (H : ℝ → ℂ) : ℂ :=
  H 0 * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ) +
    ∫ h in Ioc (0 : ℝ) (2 * a),
      ((Real.exp (h / 2) : ℂ) * (H h + H (-h)) - 2 * H 0) /
        (Real.exp h - Real.exp (-h) : ℝ)

/-- Literal two-sided finite-aperture Weil functional `Ψ`. -/
def ccmRestrictedWeilFull (a : ℝ) (H : ℝ → ℂ) : ℂ :=
  ccmRestrictedPolarPrimeFull a H - ccmRestrictedArchimedeanFull a H

theorem ccmRestrictedPolarPrimeFull_eq_sharp_evenization
    (a : ℝ) (H : ℝ → ℂ) :
    ccmRestrictedPolarPrimeFull a H =
      criticalMellinStieltjesPairing a (fun h => H h + H (-h)) := by
  unfold ccmRestrictedPolarPrimeFull criticalMellinStieltjesPairing
  congr 1

theorem ccmRestrictedArchimedeanFull_eq_sharp_evenization
    (a : ℝ) (H : ℝ → ℂ) :
    ccmRestrictedArchimedeanFull a H =
      ccmRestrictedArchimedeanSharp a (fun h => H h + H (-h)) := by
  unfold ccmRestrictedArchimedeanFull ccmRestrictedArchimedeanSharp
  simp only [neg_zero]
  congr 1
  · ring
  · apply integral_congr_ae
    filter_upwards with h
    ring

/-- CCM Lemma 3.1 (`wsharp`) on a finite aperture, for the literal complex Weil components. -/
theorem ccmRestrictedWeilFull_eq_sharp_evenization
    (a : ℝ) (H : ℝ → ℂ) :
    ccmRestrictedWeilFull a H =
      ccmRestrictedWeilSharp a (fun h => H h + H (-h)) := by
  rw [ccmRestrictedWeilFull, ccmRestrictedWeilSharp,
    ccmRestrictedPolarPrimeFull_eq_sharp_evenization,
    ccmRestrictedArchimedeanFull_eq_sharp_evenization]

/-- An actual source function on `[0,2 log λ]`, extended by zero, with integrability bundled. -/
structure CCMIntervalL1Source (lam : CCMApertureParameter) where
  source : CCML1Source
  zero_outside : ∀ x : ℝ, x ∉ ccmAdditiveAperture lam → source x = 0

instance (lam : CCMApertureParameter) : CoeFun (CCMIntervalL1Source lam)
    (fun _ => ℝ → ℂ) := ⟨fun f => f.source⟩

/-- Source formula `κ(f)(u)=f(log(λu))`, implemented as logarithmic pushforward of translation by
`-log λ`. -/
def ccmMultiplicativeKappa (lam : CCMApertureParameter)
    (f : CCMIntervalL1Source lam) : CCMMultiplicativeL1Source :=
  ccmMultiplicativeLogPush (f.source.translate (-Real.log (lam : ℝ)))

theorem ccmMultiplicativeKappa_exp
    (lam : CCMApertureParameter) (f : CCMIntervalL1Source lam) (t : ℝ) :
    ccmMultiplicativeKappa lam f (MellinL2.expMeasurableEquiv t) =
      f (t + Real.log (lam : ℝ)) := by
  simp [ccmMultiplicativeKappa, ccmMultiplicativeLogPush,
    CCML1Source.translate]

/-- Literal multiplicative Weil form `QW(F,G)=Ψ(F* * G)` in logarithmic coordinates. -/
def ccmRestrictedMultiplicativeWeilForm (a : ℝ)
    (f g : CCMMultiplicativeL1Source) : ℂ :=
  ccmRestrictedWeilFull a (fun y =>
    ccmMultiplicativeStarConvolution f g (MellinL2.expMeasurableEquiv y))

/-- CCM Proposition 3.2(ii): on the exact logarithmic aperture,
`QW(κf,κg)=Ψ#(q(f,g)∘log)`.  All source conditions are bundled; there is no RH or operator
premise. -/
theorem ccmRestrictedMultiplicativeWeilForm_kappa
    (lam : CCMApertureParameter) (f g : CCMIntervalL1Source lam) :
    ccmRestrictedMultiplicativeWeilForm (Real.log (lam : ℝ))
        (ccmMultiplicativeKappa lam f) (ccmMultiplicativeKappa lam g) =
      ccmRestrictedWeilSharp (Real.log (lam : ℝ))
        (ccmEvenHermitianCorrelation f.source g.source) := by
  rw [ccmRestrictedMultiplicativeWeilForm,
    ccmRestrictedWeilFull_eq_sharp_evenization]
  congr 1
  funext y
  rw [ccmMultiplicativeKappa, ccmMultiplicativeKappa,
    ccmMultiplicativeStarConvolution_logPush,
    ccmMultiplicativeStarConvolution_logPush]
  unfold ccmEvenHermitianCorrelation
  rw [ccmStarConvolution_translate, ccmStarConvolution_translate]

end RHTower
