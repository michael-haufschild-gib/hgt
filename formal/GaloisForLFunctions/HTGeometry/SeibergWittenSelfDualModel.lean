import GaloisForLFunctions.HTGeometry.SeibergWitten.Equations
import GaloisForLFunctions.HTGeometry.SeibergWittenFlatGaugeFlow

/-!
# A nonzero finite self-dual Seiberg--Witten model

This module couples the trace-free self-dual curvature map to the abstract Seiberg--Witten
equation interface.  The configuration's connection carrier is a finite spinor space, so this is
an algebraic model rather than an affine continuum connection space.  Its value is exact: the
north vacuum is a closed nonzero self-dual solution, and the nonstationary phase flow `exp(it)`
preserves its curvature invariant.

The Dirac component is zero.  This construction therefore does not assert a nontrivial continuum
Dirac solution.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Finite coupled data using the trace-free self-dual spinor curvature map. -/
def finiteSelfDualSeibergWittenData :
    SeibergWitten.SeibergWittenData SeibergWittenSpinor SeibergWittenSpinor
      SeibergWittenSpinor SeibergWitten.FlatFourTwoForms where
  hodgeStar := SeibergWitten.flatFourHodgeStar
  curvature := seibergWittenSelfDualCurvature
  dirac := fun _ => 0
  quadraticMap := seibergWittenSelfDualCurvature
  quadraticMap_selfDual := seibergWittenSelfDualCurvature_isSelfDual
  gaugeConnection := fun u connection => u • connection
  curvatureGaugeInvariant := by
    intro u connection
    unfold SeibergWitten.HodgeStar.selfDualPart
    rw [seibergWittenSelfDualCurvature_gaugeInvariant]
  diracGaugeCovariant := by
    intro
    simp
  quadraticMap_gaugeInvariant := seibergWittenSelfDualCurvature_gaugeInvariant

/-- The north finite spinor vacuum solves the coupled finite self-dual equations. -/
def finiteSelfDualSeibergWittenSolution :
    SeibergWitten.SeibergWittenSolution finiteSelfDualSeibergWittenData :=
  ⟨(abelianHiggsSpinorVacuum, abelianHiggsSpinorVacuum), by
    constructor
    · rfl
    · change SeibergWitten.flatFourHodgeStar.selfDualPart
        (seibergWittenSelfDualCurvature abelianHiggsSpinorVacuum) =
          seibergWittenSelfDualCurvature abelianHiggsSpinorVacuum
      exact SeibergWitten.flatFourHodgeStar.selfDualPart_eq_of_isSelfDual _
        (seibergWittenSelfDualCurvature_isSelfDual _)⟩

/-- The solution invariant is its trace-free self-dual curvature. -/
theorem finiteSelfDualSeibergWittenSolution_invariant :
    SeibergWitten.seibergWittenSolutionInvariant finiteSelfDualSeibergWittenData
      finiteSelfDualSeibergWittenSolution =
        seibergWittenSelfDualCurvature abelianHiggsSpinorVacuum :=
  finiteSelfDualSeibergWittenSolution.2.2

/-- The closed self-dual solution has nonzero curvature invariant. -/
theorem finiteSelfDualSeibergWittenSolution_invariant_ne_zero :
    SeibergWitten.seibergWittenSolutionInvariant finiteSelfDualSeibergWittenData
      finiteSelfDualSeibergWittenSolution ≠ 0 := by
  rw [finiteSelfDualSeibergWittenSolution_invariant]
  exact seibergWittenVacuum_selfDualCurvature_ne_zero

/-- Nonstationary `exp(it)` gauge flow on the finite self-dual coupled model. -/
def finiteSelfDualSeibergWittenGaugeFlow :
    SeibergWitten.SeibergWittenGaugeFlow finiteSelfDualSeibergWittenData where
  phase := seibergWittenUnitPhase
  phase_zero := seibergWittenUnitPhase_zero
  phase_add := seibergWittenUnitPhase_add

/-- The nonzero finite self-dual curvature invariant is constant along the phase flow. -/
theorem finiteSelfDualSeibergWittenGaugeFlow_invariant (t : ℝ) :
    SeibergWitten.seibergWittenSolutionInvariant finiteSelfDualSeibergWittenData
      (finiteSelfDualSeibergWittenGaugeFlow.at t finiteSelfDualSeibergWittenSolution) =
    SeibergWitten.seibergWittenSolutionInvariant finiteSelfDualSeibergWittenData
      finiteSelfDualSeibergWittenSolution :=
  finiteSelfDualSeibergWittenGaugeFlow.at_invariant t finiteSelfDualSeibergWittenSolution

end GaloisForLFunctions.HTGeometry
