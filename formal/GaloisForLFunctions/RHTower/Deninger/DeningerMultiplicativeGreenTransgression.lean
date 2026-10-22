import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The multiplicative Green cocycle and its transgression

The Green form of a commutative convolution algebra with a derivation and a trace that kills
derivations is antisymmetric: applying the trace to the derivation of a product gives the two terms
of the Leibniz rule, and their sum vanishes.

For the multiplicative Schwartz algebra the derivation is multiplication by `log`, the trace is
evaluation at `1`, and the trace does kill the derivation because `log 1 = 0`.  In the additive
model the Leibniz rule for the convolution is the splitting `x = t + (x - t)` under the integral.
Multiplicative inversion anticommutes with the derivation, so it reverses the Green orientation.

Cutoff independence is the algebraic remark that a commutator is additive in its first slot: if the
trace kills the commutator built from the difference of two cutoffs, the two cutoffs give the same
value.

* `deningerGreenForm_antisymm` : the antisymmetry `(3)`.
* `deningerMultTrace_logWeight` : the trace kills the derivation.
* `deningerLogWeight_convolution_leibniz` : the Leibniz rule in the additive model.
* `deningerLogWeight_reflection` : the reflection law `(4)`.
* `deningerGreenTransgression_cutoff_independent` : independence of the cutoff.
-/

namespace RHTower

section AbstractGreenForm

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The multiplicative Green form `ω(F, G) = τ(F ⋆ ∂G)`. -/
def deningerGreenForm (D : A →ₗ[R] A) (tau : A →ₗ[R] R) (a b : A) : R := tau (a * D b)

/-- **Antisymmetry of the Green form `(3)`.**  The derivation of a product has two terms, the trace
kills the derivation, and the algebra is commutative. -/
theorem deningerGreenForm_antisymm (D : A →ₗ[R] A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b)
    (tau : A →ₗ[R] R) (htau : ∀ a : A, tau (D a) = 0) (a b : A) :
    deningerGreenForm D tau a b = -deningerGreenForm D tau b a := by
  have h := htau (a * b)
  rw [hD a b, map_add] at h
  have hcomm : tau (D a * b) = tau (b * D a) := by
    rw [mul_comm (D a) b]
  rw [hcomm] at h
  show tau (a * D b) = -tau (b * D a)
  exact eq_neg_of_add_eq_zero_right h

/-- **Cutoff independence.**  A commutator is additive in its first slot, so if the trace kills the
commutator built from the difference of two cutoffs, both cutoffs give the same transgression. -/
theorem deningerGreenTransgression_cutoff_independent (tau : A →ₗ[R] R) (F G phi phi' : A)
    (h : tau (F * ((phi - phi') * G - G * (phi - phi'))) = 0) :
    tau (F * (phi * G - G * phi)) = tau (F * (phi' * G - G * phi')) := by
  have hexp : F * ((phi - phi') * G - G * (phi - phi'))
      = F * (phi * G - G * phi) - F * (phi' * G - G * phi') := by
    ring
  rw [hexp, map_sub] at h
  exact sub_eq_zero.mp h

end AbstractGreenForm

section MultiplicativeModel

/-- The derivation of the multiplicative Schwartz algebra: multiplication by the logarithm. -/
noncomputable def deningerLogWeight (F : ℝ → ℂ) (x : ℝ) : ℂ := F x * (Real.log x : ℂ)

/-- The trace of the multiplicative Schwartz algebra: evaluation at the unit. -/
def deningerMultTrace (F : ℝ → ℂ) : ℂ := F 1

/-- Multiplicative inversion. -/
noncomputable def deningerMultInversion (F : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ)⁻¹ * F x⁻¹

/-- **The trace kills the derivation.**  The logarithm vanishes at the unit. -/
theorem deningerMultTrace_logWeight (F : ℝ → ℂ) : deningerMultTrace (deningerLogWeight F) = 0 := by
  show F 1 * (Real.log 1 : ℂ) = 0
  rw [Real.log_one]
  norm_num

/-- **The reflection law `(4)`.**  Multiplicative inversion anticommutes with the derivation, so it
reverses the Green orientation. -/
theorem deningerLogWeight_reflection (F : ℝ → ℂ) (x : ℝ) :
    deningerLogWeight (deningerMultInversion F) x
      = -deningerMultInversion (deningerLogWeight F) x := by
  show (x : ℂ)⁻¹ * F x⁻¹ * (Real.log x : ℂ)
      = -((x : ℂ)⁻¹ * (F x⁻¹ * (Real.log x⁻¹ : ℂ)))
  rw [Real.log_inv]
  push_cast
  ring

end MultiplicativeModel

section ConvolutionLeibniz

open MeasureTheory

/-- **The Leibniz rule of the derivation for the convolution**, in the additive model where the
derivation is multiplication by the coordinate: the splitting `x = t + (x - t)` under the integral
turns the weight of a convolution into the sum of the two weighted convolutions. -/
theorem deningerLogWeight_convolution_leibniz (f g : ℝ → ℂ) (x : ℝ)
    (h1 : Integrable fun t : ℝ => (t : ℂ) * (f t * g (x - t)))
    (h2 : Integrable fun t : ℝ => ((x - t : ℝ) : ℂ) * (f t * g (x - t))) :
    (x : ℂ) * ∫ t : ℝ, f t * g (x - t)
      = (∫ t : ℝ, (t : ℂ) * (f t * g (x - t)))
        + ∫ t : ℝ, ((x - t : ℝ) : ℂ) * (f t * g (x - t)) := by
  rw [← integral_add h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  push_cast
  ring

end ConvolutionLeibniz

end RHTower
