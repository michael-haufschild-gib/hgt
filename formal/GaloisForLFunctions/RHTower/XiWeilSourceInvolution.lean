import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.HedenmalmThetaEigenTransform

/-!
# The source-side involution realizes the critical-line sharp operation

The time-side composition operator `f ↦ (x ↦ conj (f (-x)))` is an involution whose induced
action on the `e^{-izx}` source transform is exactly the divisor-side sharp operation
`(sharp F) z = conj (F (conj z))` of the Xi Weil polarization.

The identity is literal at the level of Bochner integrals and needs no integrability
hypothesis: complex conjugation is an isometric ring involution and reflection is
measure-preserving, so integrability transfers along both and the junk values of
non-integrable cases agree as well.

Consequently the Hermitian (sharp) slot of the Xi Weil polarization has an exact source-side
realization by a composition operator.  Positivity of the resulting pairing is not addressed
here and does not follow from this identity.
-/

namespace RHTower

noncomputable section

open MeasureTheory Complex

/-- Time-side source involution: complex conjugation composed with reflection. -/
def sourceInvolution (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (starRingEnd ℂ) (f (-x))

@[simp] theorem sourceInvolution_apply (f : ℝ → ℂ) (x : ℝ) :
    sourceInvolution f x = (starRingEnd ℂ) (f (-x)) := rfl

/-- The source involution is an involution. -/
theorem sourceInvolution_involutive : Function.Involutive sourceInvolution := by
  intro f
  funext x
  simp [sourceInvolution]

/-- The `e^{-izx}` source transform, in the eigen-transform normalization of the corpus. -/
def sourceFourier (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-I * z * (x : ℂ))

/-- The Hedenmalm theta eigen transform is the source transform of the causal Volterra flow. -/
theorem hedenmalmThetaEigenTransform_eq_sourceFourier (α z : ℂ) :
    hedenmalmThetaEigenTransform α z = sourceFourier (hedenmalmCausalVolterra α) z := rfl

/-- Pointwise conjugation-reflection identity for the transform integrand. -/
theorem sourceInvolution_mul_exp (f : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    sourceInvolution f x * Complex.exp (-I * z * (x : ℂ)) =
      (starRingEnd ℂ)
        (f (-x) * Complex.exp (-I * (starRingEnd ℂ) z * ((-x : ℝ) : ℂ))) := by
  rw [sourceInvolution_apply, map_mul, ← Complex.exp_conj]
  congr 2
  push_cast
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **The source involution realizes the sharp operation on transforms.**  A literal
Bochner-level identity with no hypotheses: reflection is measure-preserving and conjugation is
an isometric involution, so both sides agree in the integrable and non-integrable cases
alike. -/
theorem sourceFourier_sourceInvolution (f : ℝ → ℂ) (z : ℂ) :
    sourceFourier (sourceInvolution f) z = xiWeilSharp (sourceFourier f) z := by
  have hcong :
      (fun x : ℝ => sourceInvolution f x * Complex.exp (-I * z * (x : ℂ))) =
        fun x : ℝ =>
          (starRingEnd ℂ)
            ((fun u : ℝ => f u * Complex.exp (-I * (starRingEnd ℂ) z * (u : ℂ))) (-x)) := by
    funext x
    exact sourceInvolution_mul_exp f z x
  calc
    sourceFourier (sourceInvolution f) z
        = ∫ x : ℝ,
            (starRingEnd ℂ)
              ((fun u : ℝ => f u * Complex.exp (-I * (starRingEnd ℂ) z * (u : ℂ))) (-x)) := by
          rw [sourceFourier, hcong]
    _ = (starRingEnd ℂ)
          (∫ x : ℝ,
            (fun u : ℝ => f u * Complex.exp (-I * (starRingEnd ℂ) z * (u : ℂ))) (-x)) :=
        integral_conj
    _ = (starRingEnd ℂ)
          (∫ u : ℝ, f u * Complex.exp (-I * (starRingEnd ℂ) z * (u : ℂ))) := by
        rw [integral_neg_eq_self
          (fun u : ℝ => f u * Complex.exp (-I * (starRingEnd ℂ) z * (u : ℂ))) volume]
    _ = xiWeilSharp (sourceFourier f) z := rfl

/-- Function-level form: the sharp slot of the polarization is the transform of the
source involution. -/
theorem xiWeilSharp_sourceFourier (f : ℝ → ℂ) :
    xiWeilSharp (sourceFourier f) = sourceFourier (sourceInvolution f) := by
  funext z
  exact (sourceFourier_sourceInvolution f z).symm

end

end RHTower
