import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import GaloisForLFunctions.HTGeometry.MomentCharacterisation
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

/-- RH makes the canonical prime--archimedean moment form positive definite on every nonzero real
polynomial.  This closes the finite-coordinate bridge from the existing source Hankel hierarchy to
the abstract Hamburger moment machinery. -/
theorem positiveMomentForm_normalizedPrimeArchMoment_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    HTGeometry.PositiveMomentForm normalizedPrimeArchMoment := by
  refine ⟨fun p hp => ?_⟩
  let n := p.natDegree + 1
  let a : Fin n → ℝ := Polynomial.toFn n p
  have hpof : Polynomial.ofFn n a = p := by
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
  have ha : a ≠ 0 := by
    intro ha
    apply hp
    rw [← hpof, ha, Polynomial.ofFn_zero]
  have hpos : (HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n).PosDef := by
    change (primeArchSourceMomentHankelMatrix n).PosDef
    rw [primeArchSourceMomentHankelMatrix_eq_xiCentralMomentHankelMatrix]
    exact (xiCentralMomentHankelPosDef_iff_riemannHypothesis.mpr hRH) n
  have hquad := hpos.dotProduct_mulVec_pos ha
  rw [star_trivial, HTGeometry.dotProduct_mulVec_momentHankelMatrix, hpof,
    ← HTGeometry.momentInner_self] at hquad
  exact hquad

/-- Positive definiteness of the canonical moment form constructs, rather than assumes, an exact
finite representing measure with infinite support. -/
theorem primeArchInfiniteSupportMomentRepresentation_of_positiveMomentForm
    (hpos : HTGeometry.PositiveMomentForm normalizedPrimeArchMoment) :
    PrimeArchInfiniteSupportMomentRepresentation := by
  obtain ⟨ν, _, hmom, hinf⟩ :=
    (HTGeometry.positiveMomentForm_iff_exists_representing
      normalizedPrimeArchMoment).mp hpos
  exact ⟨ν, fun k => (hmom k).2.symm, fun k => (hmom k).1, hinf⟩

/-- RH constructs an exact infinite-support Hamburger representation of every canonical
prime--archimedean moment. -/
theorem primeArchInfiniteSupportMomentRepresentation_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchInfiniteSupportMomentRepresentation :=
  primeArchInfiniteSupportMomentRepresentation_of_positiveMomentForm
    (positiveMomentForm_normalizedPrimeArchMoment_of_riemannHypothesis hRH)

/-- Infinite-support representation is not an additional producer hypothesis: for the canonical
prime--archimedean moment tower it is exactly RH. -/
theorem primeArchInfiniteSupportMomentRepresentation_iff_riemannHypothesis :
    PrimeArchInfiniteSupportMomentRepresentation ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation
  · exact primeArchInfiniteSupportMomentRepresentation_of_riemannHypothesis

/-- RH also constructs the weaker unrestricted positive moment representation. -/
theorem primeArchMomentRepresentation_of_riemannHypothesis
    (hRH : RiemannHypothesis) : PrimeArchMomentRepresentation :=
  primeArchMomentRepresentation_of_infiniteSupport
    (primeArchInfiniteSupportMomentRepresentation_of_riemannHypothesis hRH)

/-- An unrestricted positive measure represents all canonical prime--archimedean moments exactly
if and only if RH holds. -/
theorem primeArchMomentRepresentation_iff_riemannHypothesis :
    PrimeArchMomentRepresentation ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_primeArchMomentRepresentation
  · exact primeArchMomentRepresentation_of_riemannHypothesis

end

end RHTower
