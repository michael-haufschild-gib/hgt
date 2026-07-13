import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion

/-!
# Positive prime--archimedean moment representations imply RH

This module closes the consumer end shared by probabilistic and measure-producing detours.  Any
positive real measure representing every canonical normalized prime--archimedean moment makes the
complete source Hankel form nonnegative and therefore proves RH.  Infinite support is needed only
for the stronger conclusion that every leading Hankel determinant is strictly positive; it is not
needed for RH itself.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- One positive real measure represents the complete canonical prime--archimedean moment tower.
No support-size or determinacy hypothesis is imposed. -/
def PrimeArchMomentRepresentation : Prop :=
  ∃ μ : Measure ℝ,
    (∀ k, normalizedPrimeArchMoment k = ∫ x, (x : ℝ) ^ k ∂μ) ∧
    ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ

/-- The real part of the canonical prime--Gamma trace-Hankel value is exactly the abstract moment
functional evaluated on the square of the same polynomial. -/
theorem re_primeArchSourceTraceHankel_eq_momentFunctional_sq (p : Polynomial ℝ) :
    (primeArchSourceTraceHankel p).re =
      HTGeometry.momentFunctional normalizedPrimeArchMoment (p ^ 2) := by
  rw [primeArchSourceTraceHankel, HTGeometry.momentFunctional_eq_support_sum]
  have hmap : p.map (algebraMap ℝ ℂ) ^ 2 =
      (p ^ 2).map (algebraMap ℝ ℂ) := by
    exact (Polynomial.map_pow (p := p) (algebraMap ℝ ℂ) 2).symm
  rw [hmap]
  rw [Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective (algebraMap ℝ ℂ))]
  have hrange := (p ^ 2).sum_over_range
    (f := fun k c => c * normalizedPrimeArchMoment k) (by simp)
  rw [Polynomial.sum_def] at hrange
  rw [hrange]
  simp [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm]
  apply Finset.sum_congr rfl
  intro k _
  rw [hmap, Polynomial.coeff_map]
  simp

/-- An arbitrary positive representing measure already supplies every integer-polynomial source
Hankel inequality.  Infinite support is unnecessary for this non-strict cone. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_momentRepresentation
    (hrep : PrimeArchMomentRepresentation) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  obtain ⟨μ, hmom, hint⟩ := hrep
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg
    normalizedPrimeArchMoment hmom hint _

/-- **Weak measure-representation capstone.**  Constructing any positive representing measure for
the complete normalized prime--archimedean moment tower proves RH. -/
theorem riemannHypothesis_of_primeArchMomentRepresentation
    (hrep : PrimeArchMomentRepresentation) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_momentRepresentation hrep)

/-- A single positive real measure represents the complete canonical prime--archimedean moment
tower and is not carried by any finite set. -/
def PrimeArchInfiniteSupportMomentRepresentation : Prop :=
  ∃ μ : Measure ℝ,
    (∀ k, normalizedPrimeArchMoment k = ∫ x, (x : ℝ) ^ k ∂μ) ∧
    (∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ) ∧
    (∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F})

/-- The old infinite-support interface strictly strengthens the representation needed for RH. -/
theorem primeArchMomentRepresentation_of_infiniteSupport
    (hrep : PrimeArchInfiniteSupportMomentRepresentation) :
    PrimeArchMomentRepresentation := by
  obtain ⟨μ, hmom, hint, _⟩ := hrep
  exact ⟨μ, hmom, hint⟩

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
