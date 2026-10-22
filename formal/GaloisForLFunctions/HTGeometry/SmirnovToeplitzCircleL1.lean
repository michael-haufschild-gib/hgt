import GaloisForLFunctions.HTGeometry.BoundedPhaseHardyHalfToeplitz
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzKernel

/-!
# Circle `L¹` integrability of the reflected side of a Smirnov Toeplitz kernel element

Almost-everywhere equality transfers from the real line to the unit circle through the Cayley
map: if two a.e.-measurable circle functions agree a.e. after composition with the Cayley
parametrization, they agree a.e. for circle Lebesgue measure. For an element of the Smirnov
Toeplitz kernel with unimodular real-line symbol `U`, the reflected boundary function has the same
modulus as the forward one a.e., so the reflected circle boundary is integrable whenever the
forward circle boundary is.

## Main results

- `circle_eventuallyEq_of_line_eventuallyEq_ae`: a.e. equality along the Cayley parametrization
  implies a.e. equality on the circle, for a.e.-measurable functions.
- `SmirnovToeplitzKernelElement.integrable_reflected_circleBoundary`: assuming `|U| = 1` a.e. and
  circle integrability of the forward boundary, the reflected boundary is circle integrable.

## Hypotheses

Unconditional apart from the explicit inputs: a.e.-measurability in the transfer lemma, and in
the integrability theorem the unimodularity `‖U x‖ = 1` for a.e. `x` and integrability of the
forward circle boundary.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- If a.e.-measurable `f g : Circle → β` agree a.e. on `ℝ` after composing with the Cayley map,
then `f = g` almost everywhere for circle Lebesgue measure. -/
theorem circle_eventuallyEq_of_line_eventuallyEq_ae
    {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    {f g : Circle → β}
    (hf : AEMeasurable f circleLebesgue)
    (hg : AEMeasurable g circleLebesgue)
    (h : (fun x => f (circleCayley x)) =ᵐ[volume]
      fun x => g (circleCayley x)) :
    f =ᵐ[circleLebesgue] g := by
  have hpull {u v : Circle → β} (huv : u =ᵐ[circleLebesgue] v) :
      (fun x => u (circleCayley x)) =ᵐ[volume]
        fun x => v (circleCayley x) := by
    have hweighted := huv.comp_tendsto
      circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
    exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp hweighted
  have hfLine := hpull hf.ae_eq_mk
  have hgLine := hpull hg.ae_eq_mk
  have hmkLine :
      (fun x => hf.mk f (circleCayley x)) =ᵐ[volume]
        fun x => hg.mk g (circleCayley x) :=
    hfLine.symm.trans (h.trans hgLine)
  have hmk : hf.mk f =ᵐ[circleLebesgue] hg.mk g :=
    circle_eventuallyEq_of_line_eventuallyEq (β := β)
      hf.measurable_mk hg.measurable_mk hmkLine
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

/-- For a Smirnov Toeplitz kernel element with symbol `U`, assuming `|U| = 1` a.e. on `ℝ` and that
the forward circle boundary is integrable, the reflected circle boundary is integrable. -/
theorem SmirnovToeplitzKernelElement.integrable_reflected_circleBoundary
    {U : ℝ → ℂ} (K : SmirnovToeplitzKernelElement U)
    (hU : ∀ᵐ x ∂volume, ‖U x‖ = 1)
    (hforward : Integrable K.forward.circleBoundary circleLebesgue) :
    Integrable K.reflected.circleBoundary circleLebesgue := by
  have hline :
      (fun x => ‖K.reflected.circleBoundary (circleCayley x)‖) =ᵐ[volume]
        fun x => ‖K.forward.circleBoundary (circleCayley x)‖ := by
    filter_upwards [K.boundary_relation, hU,
      K.forward.boundary_eq_circleBoundary_cayley_ae,
      K.reflected.boundary_eq_circleBoundary_cayley_ae]
        with x hrel hunit hforwardCircle hreflectedCircle
    rw [← hreflectedCircle, ← hforwardCircle, hrel, norm_mul, norm_conj,
      norm_conj, hunit, one_mul]
  have hcircle :
      (fun z => ‖K.reflected.circleBoundary z‖) =ᵐ[circleLebesgue]
        fun z => ‖K.forward.circleBoundary z‖ :=
    circle_eventuallyEq_of_line_eventuallyEq_ae
      K.reflected.aestronglyMeasurable_circleBoundary.norm.aemeasurable
      K.forward.aestronglyMeasurable_circleBoundary.norm.aemeasurable
      hline
  exact hforward.norm.mono'
    K.reflected.aestronglyMeasurable_circleBoundary
    (hcircle.mono fun _ hz => hz.le)

end

end GaloisForLFunctions.HTGeometry
