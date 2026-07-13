import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion

/-!
# Infinite-support prime--archimedean moment representations imply RH

This module closes the consumer end shared by probabilistic and measure-producing detours.  If one
positive real measure with genuinely infinite support represents every canonical normalized
prime--archimedean moment, the general strict Hankel theorem makes every source determinant
positive.  The existing exact determinant criterion then gives RH.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- A single positive real measure represents the complete canonical prime--archimedean moment
tower and is not carried by any finite set. -/
def PrimeArchInfiniteSupportMomentRepresentation : Prop :=
  ∃ μ : Measure ℝ,
    (∀ k, normalizedPrimeArchMoment k = ∫ x, (x : ℝ) ^ k ∂μ) ∧
    (∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) ∧
    (∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F})

/-- An infinite-support representing measure makes every canonical source Hankel determinant
strictly positive. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_infiniteSupportRepresentation
    (hrep : PrimeArchInfiniteSupportMomentRepresentation) :
    PrimeArchSourceMomentHankelDeterminantsPositive := by
  obtain ⟨μ, hmom, hint, hinf⟩ := hrep
  intro n
  have hmatrix :
      primeArchSourceMomentHankelMatrix n =
        HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n := by
    ext i j
    rfl
  rw [hmatrix]
  exact HTGeometry.det_momentHankelMatrix_pos_of_infiniteSupport
    normalizedPrimeArchMoment hmom hint hinf n

/-- **Measure-representation capstone.**  Constructing one source-defined infinite-support positive
measure for the complete normalized prime--archimedean moment tower proves RH. -/
theorem riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation
    (hrep : PrimeArchInfiniteSupportMomentRepresentation) :
    RiemannHypothesis :=
  primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
    (primeArchSourceMomentHankelDeterminantsPositive_of_infiniteSupportRepresentation hrep)

end

end RHTower
