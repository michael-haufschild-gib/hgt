import GaloisForLFunctions.HTGeometry.CompleteCauchyGermClosure
import GaloisForLFunctions.HTGeometry.FAndMRieszSchurConsequences

/-!
# Moment-fiber boundary splitting, Pick phases, and Schur condensation

The repository already contains the concrete Nevanlinna boundary simplex/retract, residual maximal
translation phase, spectral singular-continuous phase, complete Cauchy-germ separation, and
Bernstein--Szegő condensation.  This file supplies the common Hilbert projection algebra and the
finite Pick-defect/Xi assembly used by the remaining cards.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set Topology
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-- A self-adjoint idempotent linear map, the exact Hilbert-space interface supplied by conditional
expectation onto the projective support label. -/
structure BoundaryConditionalProjection (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  projector : H →ₗ[ℂ] H
  idempotent : ∀ x, projector (projector x) = projector x
  selfAdjoint : ∀ x y, ⟪projector x, y⟫_ℂ = ⟪x, projector y⟫_ℂ

/-- Every state splits exactly into horizontal and vertical components, and the two components are
orthogonal. -/
theorem BoundaryConditionalProjection.orthogonal_decomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : BoundaryConditionalProjection H) (x : H) :
    x = P.projector x + (x - P.projector x) ∧
      P.projector (P.projector x) = P.projector x ∧
      P.projector (x - P.projector x) = 0 ∧
      ⟪P.projector x, x - P.projector x⟫_ℂ = 0 := by
  have hvertical : P.projector (x - P.projector x) = 0 := by
    rw [map_sub, P.idempotent]
    exact sub_self _
  refine ⟨by abel, P.idempotent x, hvertical, ?_⟩
  rw [P.selfAdjoint, hvertical]
  simp

/-- If conditional expectation sends a polynomial to its common moment constant, then the centered
polynomial lies in the vertical kernel. -/
theorem BoundaryConditionalProjection.centeredPolynomial_vertical
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : BoundaryConditionalProjection H)
    (one polynomial : H) (moment : ℂ)
    (hone : P.projector one = one)
    (hpoly : P.projector polynomial = moment • one) :
    P.projector (polynomial - moment • one) = 0 := by
  rw [map_sub, map_smul, hpoly, hone, sub_self]

/-- Every vertical vector is orthogonal to every horizontal fixed vector.  This is exact
polynomial blindness once centered polynomials are routed through the preceding theorem. -/
theorem BoundaryConditionalProjection.horizontal_orthogonal_vertical
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : BoundaryConditionalProjection H)
    (horizontal vertical : H)
    (hhorizontal : P.projector horizontal = horizontal)
    (hvertical : P.projector vertical = 0) :
    ⟪horizontal, vertical⟫_ℂ = 0 := by
  rw [← hhorizontal, P.selfAdjoint, hvertical]
  simp

/-- Complete resolvent data separate finite measures at every nonreal node.  This capstone exposes
the arbitrary-node theorem next to the projection splitting used by the moment cards. -/
theorem momentBoundary_completeResolvent_separates
    {mu nu : Measure ℝ} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (a : ℂ) (ha : a.im ≠ 0)
    (hjet : ∀ k,
      iteratedDeriv k (resolventTransform mu) a =
        iteratedDeriv k (resolventTransform nu) a) :
    mu = nu :=
  measure_eq_of_completeCauchyJet_eq mu nu ha hjet

/-- The classical confluent Pick input at one finite selector level.  `singular` is uniqueness of
the interpolant; `freePhase` is the positive-defect Schur-parameter phase. -/
structure FinitePickDefectPhaseInput where
  defect : ℝ
  singular : Prop
  freePhase : Prop
  defect_nonnegative : 0 ≤ defect
  singular_iff : singular ↔ defect = 0
  freePhase_iff : freePhase ↔ 0 < defect

/-- Every nonnegative finite Pick defect lies in exactly one of the singular and free phases. -/
theorem finitePickDefect_singular_or_free_exclusive
    (input : FinitePickDefectPhaseInput) :
    (input.singular ∨ input.freePhase) ∧
      ¬(input.singular ∧ input.freePhase) := by
  constructor
  · by_cases hzero : input.defect = 0
    · exact Or.inl (input.singular_iff.mpr hzero)
    · exact Or.inr (input.freePhase_iff.mpr (lt_of_le_of_ne
        input.defect_nonnegative (Ne.symm hzero)))
  · rintro ⟨hsingular, hfree⟩
    have hz := input.singular_iff.mp hsingular
    have hp := input.freePhase_iff.mp hfree
    linarith

/-- A selector that excludes the free maximal-translation phase must land on the singular Pick
locus.  Thus universal finite selection is forced to destroy a finite jet aperture. -/
theorem finitePickSelector_forces_singular
    (input : FinitePickDefectPhaseInput)
    (selected : Prop) (hexcludesFree : selected → ¬ input.freePhase) :
    selected → input.singular := by
  intro hselected
  rcases (finitePickDefect_singular_or_free_exclusive input).1 with hs | hf
  · exact hs
  · exact (hexcludesFree hselected hf).elim

/-- Xi-facing Schur capstone.  Once the source-side RH criterion identifies RH with singularity of
the canonical infinite-support circle law, the checked Riesz-brothers theorem yields strict finite
defects, cofinal metric collapse, exact finite Gram reconstruction, weak atomic condensation, and
all finite superlinear `L^p` blow-up. -/
theorem xiSchur_inverseLimit_atomicCondensation
    (RH : Prop)
    (mu : ProbabilityMeasure Circle)
    (hmu : (mu : Measure Circle).support.Infinite)
    (hRH : RH ↔ (mu : Measure Circle) ⟂ₘ circleLebesgue) :
    RH →
      HasSingularSchurDefectCollapse (mu : Measure Circle) hmu ∧
      HasBernsteinSzegoCofinalApproximation mu hmu := by
  intro h
  exact singularSchurDefect_doubleBoundary mu hmu (hRH.mp h)

end

end GaloisForLFunctions.HTGeometry
