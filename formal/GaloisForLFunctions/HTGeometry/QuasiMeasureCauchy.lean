import GaloisForLFunctions.HTGeometry.QuasiMeasureIntegral
import GaloisForLFunctions.HTGeometry.QuasiCauchyComplex

/-!
# The Nevanlinna identity for the quadrature measure

Combining the identification of the quadrature Cauchy transform with the finite node sum and the
complex finite-level identity gives the Nevanlinna relation for the level-`n` *measure*:

`P(z)·∫(x − z)⁻¹ d(quasiMeasure) = −s₀·(R_{n+1}(z) + t·Rₙ(z))`.

Everything here is finite: the measure has `n+1` atoms and the identity is polynomial.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The Nevanlinna identity for the level-`n` quadrature measure.** -/
theorem quasiMeasure_cauchy_identity (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℂ}
    (hz : ∀ ξ ∈ quasiNodes s n t, ((ξ : ℝ) : ℂ) ≠ z) :
    Polynomial.aeval z (quasiOrtho s n t) *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(quasiMeasure s n t)
      = -((s 0 : ℝ) : ℂ) *
          (secondKindC s (n + 1) z + ((t : ℝ) : ℂ) * secondKindC s n z) := by
  rw [integral_cauchy_quasiMeasure h n t z]
  have hconv : ∑ ξ ∈ quasiNodes s n t,
      ((quasiWeight s n t ξ : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) - z)⁻¹
      = ∑ ξ ∈ quasiNodes s n t,
          ((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z) := by
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [div_eq_mul_inv]
  rw [hconv]
  exact quasiCauchy_identity_complex h n t hz

/-- The nodes avoid every non-real point, so the identity holds throughout the upper and lower
half-planes. -/
theorem quasiNodes_ne_of_im_ne_zero (n : ℕ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∀ ξ ∈ quasiNodes s n t, ((ξ : ℝ) : ℂ) ≠ z := by
  intro ξ _ hc
  apply hz
  rw [← hc]
  simp

/-- **The Nevanlinna identity off the real axis.** -/
theorem quasiMeasure_cauchy_identity_of_im_ne_zero (h : PositiveMomentForm s) (n : ℕ) (t : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) :
    Polynomial.aeval z (quasiOrtho s n t) *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(quasiMeasure s n t)
      = -((s 0 : ℝ) : ℂ) *
          (secondKindC s (n + 1) z + ((t : ℝ) : ℂ) * secondKindC s n z) :=
  quasiMeasure_cauchy_identity h n t (quasiNodes_ne_of_im_ne_zero n t hz)

end HTGeometry
