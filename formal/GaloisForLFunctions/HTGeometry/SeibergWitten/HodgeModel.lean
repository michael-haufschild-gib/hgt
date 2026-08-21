import GaloisForLFunctions.HTGeometry.SeibergWitten.Equations
import GaloisForLFunctions.HTGeometry.SeibergWitten.Hodge

/-!
# A nonzero finite Hodge Seiberg--Witten model

This module couples the flat Hodge-star model to the abstract Seiberg--Witten equation interface.
The configuration carrier is a finite spinor space, not an affine space of geometric connections:
it is a closed algebraic test of the nonlinear curvature equation, not a claim about solutions on a
smooth four-manifold.  Its quadratic curvature is `normSq ψ₀` in a self-dual two-form direction,
so it is nonzero at the displayed reference spinor and invariant under every `U(1)` phase.

Consequently the formal equations have a closed nonzero spinor/nonzero self-dual-curvature
solution, whose curvature invariant is constant along the stationary gauge flow.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Finite positive-spinor carrier for the flat Hodge equation model. -/
abbrev FlatHodgePositiveSpinor := Fin 2 → ℂ

/-- Finite negative-spinor carrier for the flat Hodge equation model. -/
abbrev FlatHodgeNegativeSpinor := Fin 2 → ℂ

/-- A phase-invariant quadratic curvature in the first self-dual coordinate direction. -/
def flatHodgeQuadraticMap (psi : FlatHodgePositiveSpinor) : FlatFourTwoForms :=
  flatSelfDualTwoForm (Complex.normSq (psi 0)) 0 0

/-- The finite quadratic curvature is self-dual by construction. -/
theorem flatHodgeQuadraticMap_selfDual (psi : FlatHodgePositiveSpinor) :
    flatFourHodgeStar.toLinearMap (flatHodgeQuadraticMap psi) = flatHodgeQuadraticMap psi := by
  exact flatSelfDualTwoForm_isSelfDual _ _ _

/-- The quadratic curvature is invariant under all unit-complex phases. -/
theorem flatHodgeQuadraticMap_gaugeInvariant (u : Circle) (psi : FlatHodgePositiveSpinor) :
    flatHodgeQuadraticMap ((u : ℂ) • psi) = flatHodgeQuadraticMap psi := by
  unfold flatHodgeQuadraticMap
  congr 1
  change Complex.normSq ((u : ℂ) * psi 0) = Complex.normSq (psi 0)
  rw [Complex.normSq_mul, Circle.normSq_coe, one_mul]

/-- Closed finite data with self-dual quadratic curvature and zero Dirac component. -/
def flatHodgeSeibergWittenData :
    SeibergWittenData FlatHodgePositiveSpinor FlatHodgePositiveSpinor FlatHodgeNegativeSpinor
      FlatFourTwoForms where
  hodgeStar := flatFourHodgeStar
  curvature := flatHodgeQuadraticMap
  dirac := fun _ => 0
  quadraticMap := flatHodgeQuadraticMap
  quadraticMap_selfDual := flatHodgeQuadraticMap_selfDual
  gaugeConnection := fun u connection => (u : ℂ) • connection
  curvatureGaugeInvariant := by
    intro u connection
    unfold HodgeStar.selfDualPart
    rw [flatHodgeQuadraticMap_gaugeInvariant]
  diracGaugeCovariant := by
    intro
    simp
  quadraticMap_gaugeInvariant := flatHodgeQuadraticMap_gaugeInvariant

/-- A closed nonzero reference positive spinor. -/
def flatHodgeReferenceSpinor : FlatHodgePositiveSpinor :=
  ![(1 : ℂ), 0]

/-- The reference spinor is nonzero. -/
theorem flatHodgeReferenceSpinor_ne_zero : flatHodgeReferenceSpinor ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [flatHodgeReferenceSpinor] at h0

/-- Its quadratic self-dual curvature is nonzero. -/
theorem flatHodgeReferenceCurvature_ne_zero :
    flatHodgeQuadraticMap flatHodgeReferenceSpinor ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [flatHodgeQuadraticMap, flatSelfDualTwoForm, flatHodgeReferenceSpinor] at h0

/-- The reference spinor, paired with the matching finite curvature carrier, solves both equations. -/
def flatHodgeSeibergWittenSolution :
    SeibergWittenSolution flatHodgeSeibergWittenData :=
  ⟨(flatHodgeReferenceSpinor, flatHodgeReferenceSpinor), by
    constructor
    · rfl
    · change flatFourHodgeStar.selfDualPart
        (flatHodgeQuadraticMap flatHodgeReferenceSpinor) =
          flatHodgeQuadraticMap flatHodgeReferenceSpinor
      exact flatFourHodgeStar.selfDualPart_eq_of_isSelfDual _
        (flatHodgeQuadraticMap_selfDual flatHodgeReferenceSpinor)⟩

/-- The solution invariant is precisely the nonzero quadratic self-dual curvature. -/
theorem flatHodgeSeibergWittenSolution_invariant :
    seibergWittenSolutionInvariant flatHodgeSeibergWittenData flatHodgeSeibergWittenSolution =
      flatHodgeQuadraticMap flatHodgeReferenceSpinor :=
  flatHodgeSeibergWittenSolution.2.2

/-- Stationary phase flow on the nonzero finite Hodge model. -/
def flatHodgeSeibergWittenGaugeFlow : SeibergWittenGaugeFlow flatHodgeSeibergWittenData where
  phase := fun _ => 1
  phase_zero := rfl
  phase_add := by intro; simp

/-- The nonzero self-dual curvature invariant is constant along the stationary gauge flow. -/
theorem flatHodgeSeibergWittenGaugeFlow_invariant (t : ℝ) :
    seibergWittenSolutionInvariant flatHodgeSeibergWittenData
      (flatHodgeSeibergWittenGaugeFlow.at t flatHodgeSeibergWittenSolution) =
      flatHodgeQuadraticMap flatHodgeReferenceSpinor := by
  rw [flatHodgeSeibergWittenGaugeFlow.at_invariant]
  exact flatHodgeSeibergWittenSolution_invariant

end GaloisForLFunctions.HTGeometry.SeibergWitten
