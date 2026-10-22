import GaloisForLFunctions.RHTower.Deninger.DeningerPreimageL1
import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The Möbius–Fourier commutator

The even extension of the canonical Möbius preimage is an integrable function of the line, hence a
tempered distribution.  Comparing its Fourier transform with the preimage of the exchanged collar
gives the source-defined off-diagonal operator

`𝔖_μ h = ℱ(E f_h) - E f_{Jh}`,

which needs no zeta zero, no divisor, no quotient and no Hilbert completion — only the `L¹` datum of
the preimage and the involution `J`.

Squaring the Fourier transform reflects the line, and every canonical preimage is even, so the
square acts trivially on the distributions in play.  With `J² = 1` this gives the exact
Fourier covariance of the commutator: exchanging the collars acts on the target by `-ℱ`.

* `deningerFourierSq_apply` : `ℱ²g = g ∘ (-·)` on Schwartz functions.
* `deningerEvenDistribution_fourierSq` : `ℱ²` is trivial on an even `L¹` distribution.
* `deningerPreimageDistribution` : the even preimage, as a tempered distribution.
* `deningerMobiusCommutator` : **the commutator `𝔖_μ`.**
* `deningerMobiusCommutator_fourier_covariance` : **`𝔖_μ(Jh) = -ℱ(𝔖_μ h)`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform

noncomputable section

/-! ## The square of the Fourier transform -/

/-- **The square of the Fourier transform reflects the line.** -/
theorem deningerFourierSq_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) : (𝓕 (𝓕 g)) x = g (-x) := by
  have h1 := SchwartzMap.fourierInv_apply_eq (𝓕 g)
  have h2 : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := fourierInv_fourier_eq g
  have h3 : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) (-x) = (𝓕 (𝓕 g) : 𝓢(ℝ, ℂ)) (-(-x)) := by
    rw [h1]
    rfl
  rw [h2, neg_neg] at h3
  exact h3.symm

/-! ## Even integrable functions as tempered distributions -/

/-- The tempered distribution of an integrable function of the line. -/
def deningerL1Distribution {F : ℝ → ℂ} (hF : Integrable F) : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (MeasureTheory.Integrable.toL1 F hF)

theorem deningerL1Distribution_apply {F : ℝ → ℂ} (hF : Integrable F) (g : 𝓢(ℝ, ℂ)) :
    deningerL1Distribution hF g = ∫ x : ℝ, g x • F x := by
  rw [deningerL1Distribution, MeasureTheory.Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Integrable.coeFn_toL1 (f := F) hF] with x hx
  rw [hx]

/-- **The square of the Fourier transform is trivial on an even `L¹` distribution.** -/
theorem deningerEvenDistribution_fourierSq {F : ℝ → ℂ} (hF : Integrable F)
    (hev : ∀ x : ℝ, F (-x) = F x) :
    𝓕 (𝓕 (deningerL1Distribution hF)) = deningerL1Distribution hF := by
  ext g
  have hstep : (𝓕 (𝓕 (deningerL1Distribution hF))) g
      = deningerL1Distribution hF (𝓕 (𝓕 g)) := rfl
  rw [hstep, deningerL1Distribution_apply, deningerL1Distribution_apply]
  have hrefl : ∀ x : ℝ, (𝓕 (𝓕 g)) x • F x = g (-x) • F (-(-x)) := by
    intro x
    rw [deningerFourierSq_apply, neg_neg]
  calc (∫ x : ℝ, (𝓕 (𝓕 g)) x • F x)
      = ∫ x : ℝ, (fun y : ℝ => g y • F (-y)) (-x) := integral_congr_ae
          (Filter.Eventually.of_forall hrefl)
    _ = ∫ y : ℝ, g y • F (-y) :=
        integral_neg_eq_self (fun y : ℝ => g y • F (-y)) volume
    _ = ∫ y : ℝ, g y • F y := integral_congr_ae
          (Filter.Eventually.of_forall fun y => by
            show g y • F (-y) = g y • F y
            rw [hev y])

/-! ## The commutator -/

/-- The even extension of the canonical Möbius preimage, as a tempered distribution. -/
def deningerPreimageDistribution (h : DeningerExpSchwartz) : 𝓢'(ℝ, ℂ) :=
  deningerL1Distribution (deningerEvenPreimage_integrable h.2)

theorem deningerPreimageDistribution_fourierSq (h : DeningerExpSchwartz) :
    𝓕 (𝓕 (deningerPreimageDistribution h)) = deningerPreimageDistribution h :=
  deningerEvenDistribution_fourierSq _ (deningerEvenPreimage_even _)

/-- **The Möbius–Fourier commutator** `𝔖_μ h = ℱ(E f_h) - E f_{Jh}`. -/
def deningerMobiusCommutator (h : DeningerExpSchwartz) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerPreimageDistribution h) -
    deningerPreimageDistribution (deningerCollarExchange h)

/-- The Fourier transform of tempered distributions is additive on differences. -/
theorem deningerFourier_sub (A B : 𝓢'(ℝ, ℂ)) : 𝓕 (A - B) = 𝓕 A - 𝓕 B := by
  ext g
  rfl

/-- **The exact Fourier covariance of the commutator.**  Exchanging the two collars acts on the
target by `-ℱ`: the involution `J` squares to the identity, and the Fourier square is trivial on
the even preimage distributions. -/
theorem deningerMobiusCommutator_fourier_covariance (h : DeningerExpSchwartz) :
    deningerMobiusCommutator (deningerCollarExchange h)
      = -(𝓕 (deningerMobiusCommutator h)) := by
  rw [deningerMobiusCommutator, deningerCollarExchange_involutive,
    deningerMobiusCommutator, deningerFourier_sub,
    deningerPreimageDistribution_fourierSq, neg_sub]

end

end RHTower
