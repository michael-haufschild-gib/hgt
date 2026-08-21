import GaloisForLFunctions.HTGeometry.SeibergWitten.Models
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor
import GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint

/-!
# Finite Seiberg--Witten bridge to the BRST Hodge--Dirac construction

The existing finite spinor is a coordinate function, whereas the BRST Hodge--Dirac operator
requires a complete inner-product space.  We therefore use `EuclideanSpace ℂ (Fin 2)`, linked to
those coordinates by `EuclideanSpace.equiv`.  Its quadratic curvature map is exactly the existing
finite one after that coordinate isometry.

The closed model below uses the zero BRST charge.  Its Dirac operator is consequently the actual
BRST Hodge--Dirac operator for that charge, and its coupled Seiberg--Witten solution is BRST closed
and coclosed.  This proves an interface compatibility model only: it does not identify the BRST
complex with the geometric spinor complex of a four-manifold.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

open GaloisForLFunctions.HTGeometry

/-- Complete two-component complex Hilbert spinor carrier for the Hodge--Dirac bridge. -/
abbrev HilbertSeibergWittenSpinor := EuclideanSpace ℂ (Fin 2)

/-- The finite quadratic curvature map transported to Hilbert spinor coordinates. -/
def hilbertSeibergWittenQuadraticMap
    (psi : HilbertSeibergWittenSpinor) : SeibergWittenCurvature :=
  seibergWittenQuadraticMap (EuclideanSpace.equiv (Fin 2) ℂ psi)

/-- The transported finite curvature map remains invariant under `U(1)`. -/
theorem hilbertSeibergWittenQuadraticMap_gaugeInvariant
    (u : Circle) (psi : HilbertSeibergWittenSpinor) :
    hilbertSeibergWittenQuadraticMap ((u : ℂ) • psi) =
      hilbertSeibergWittenQuadraticMap psi := by
  unfold hilbertSeibergWittenQuadraticMap
  rw [(EuclideanSpace.equiv (Fin 2) ℂ).map_smul]
  exact seibergWittenQuadraticMap_gaugeInvariant u _

/-- Identity Hodge star on the finite curvature carrier. -/
def finiteHodgeStar : HodgeStar SeibergWittenCurvature where
  toLinearMap := LinearMap.id
  sq := rfl

/-- Every finite curvature is self-dual for the identity Hodge star. -/
theorem finiteHodgeStar_selfDualPart (omega : SeibergWittenCurvature) :
    finiteHodgeStar.selfDualPart omega = omega := by
  change (2 : ℝ)⁻¹ • (omega + omega) = omega
  rw [← two_smul ℝ omega, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- Closed zero BRST charge on the Hilbert spinor carrier. -/
def finiteBrstCharge :
    HilbertSeibergWittenSpinor →L[ℂ] HilbertSeibergWittenSpinor := 0

/-- The closed finite BRST charge is nilpotent. -/
theorem finiteBrstCharge_sq_eq_zero : finiteBrstCharge * finiteBrstCharge = 0 := by
  simp [finiteBrstCharge]

/-- Hodge--Dirac operator associated with the closed finite BRST charge. -/
def finiteBrstHodgeDirac :
    HilbertSeibergWittenSpinor →L[ℂ] HilbertSeibergWittenSpinor :=
  HTGeometry.brstHodgeDiracOperator finiteBrstCharge

/-- This Hodge--Dirac operator is self-adjoint. -/
theorem finiteBrstHodgeDirac_isSelfAdjoint :
    IsSelfAdjoint finiteBrstHodgeDirac :=
  HTGeometry.brstHodgeDiracOperator_isSelfAdjoint finiteBrstCharge

/-- Its square is the BRST Hodge Hamiltonian. -/
theorem finiteBrstHodgeDirac_sq_eq_hamiltonian :
    finiteBrstHodgeDirac * finiteBrstHodgeDirac =
      HTGeometry.brstHodgeHamiltonian finiteBrstCharge :=
  HTGeometry.brstHodgeDiracOperator_sq_eq_hamiltonian finiteBrstCharge
    finiteBrstCharge_sq_eq_zero

/-- Finite coupled data whose Dirac field is the BRST Hodge--Dirac operator. -/
def finiteBrstHodgeSeibergWittenData :
    SeibergWittenData PUnit.{1} HilbertSeibergWittenSpinor HilbertSeibergWittenSpinor
      SeibergWittenCurvature where
  hodgeStar := finiteHodgeStar
  curvature := fun _ => hilbertSeibergWittenQuadraticMap 0
  dirac := fun _ => finiteBrstHodgeDirac
  quadraticMap := hilbertSeibergWittenQuadraticMap
  quadraticMap_selfDual := by intro; rfl
  gaugeConnection := fun _ A => A
  curvatureGaugeInvariant := by intro u A; rfl
  diracGaugeCovariant := by
    intro u A psi
    simp [finiteBrstHodgeDirac, finiteBrstCharge, HTGeometry.brstHodgeDiracOperator]
  quadraticMap_gaugeInvariant := hilbertSeibergWittenQuadraticMap_gaugeInvariant

/-- The coupled Dirac field is definitionally the finite BRST Hodge--Dirac operator. -/
theorem finiteBrstHodgeSeibergWittenData_dirac (A : PUnit.{1}) :
    finiteBrstHodgeSeibergWittenData.dirac A = finiteBrstHodgeDirac := rfl

/-- Closed finite solution of the coupled equation with the BRST Hodge--Dirac field. -/
def finiteBrstHodgeSeibergWittenSolution :
    SeibergWittenSolution finiteBrstHodgeSeibergWittenData :=
  ⟨(PUnit.unit, 0), by
    constructor
    · simp [finiteBrstHodgeSeibergWittenData, finiteBrstHodgeDirac, finiteBrstCharge,
        HTGeometry.brstHodgeDiracOperator]
    · dsimp [finiteBrstHodgeSeibergWittenData]
      exact finiteHodgeStar_selfDualPart _⟩

/-- The coupled Dirac equation of the closed solution is exactly the Hodge--Dirac zero equation. -/
theorem finiteBrstHodgeSeibergWittenSolution_dirac_eq_zero :
    finiteBrstHodgeDirac finiteBrstHodgeSeibergWittenSolution.1.2 = 0 := by
  change finiteBrstHodgeSeibergWittenData.dirac
    finiteBrstHodgeSeibergWittenSolution.1.1
    finiteBrstHodgeSeibergWittenSolution.1.2 = 0
  exact finiteBrstHodgeSeibergWittenSolution.2.1

/-- The closed coupled solution is annihilated by its BRST Hodge Hamiltonian. -/
theorem finiteBrstHodgeSeibergWittenSolution_hamiltonian_eq_zero :
    HTGeometry.brstHodgeHamiltonian finiteBrstCharge
      finiteBrstHodgeSeibergWittenSolution.1.2 = 0 := by
  rw [← finiteBrstHodgeDirac_sq_eq_hamiltonian]
  change finiteBrstHodgeDirac (finiteBrstHodgeDirac
    finiteBrstHodgeSeibergWittenSolution.1.2) = 0
  rw [finiteBrstHodgeSeibergWittenSolution_dirac_eq_zero]
  exact map_zero finiteBrstHodgeDirac

/-- The closed coupled solution is simultaneously BRST closed and coclosed. -/
theorem finiteBrstHodgeSeibergWittenSolution_brst_closed_coclosed :
    finiteBrstCharge finiteBrstHodgeSeibergWittenSolution.1.2 = 0 ∧
      finiteBrstCharge.adjoint finiteBrstHodgeSeibergWittenSolution.1.2 = 0 :=
  (HTGeometry.brstHodgeHamiltonian_apply_eq_zero_iff finiteBrstCharge
    finiteBrstHodgeSeibergWittenSolution.1.2).mp
    finiteBrstHodgeSeibergWittenSolution_hamiltonian_eq_zero

/-- Every `U(1)` phase fixes the closed coupled configuration. -/
theorem finiteBrstHodgeSeibergWittenSolution_gaugeFixed (u : Circle) :
    gaugeTransformSolution finiteBrstHodgeSeibergWittenData u
      finiteBrstHodgeSeibergWittenSolution = finiteBrstHodgeSeibergWittenSolution := by
  apply Subtype.ext
  exact Prod.ext rfl (smul_zero _)

/-- Stationary `U(1)` gauge flow on the finite BRST--Seiberg--Witten model. -/
def finiteBrstHodgeSeibergWittenGaugeFlow :
    SeibergWittenGaugeFlow finiteBrstHodgeSeibergWittenData where
  phase := fun _ => 1
  phase_zero := rfl
  phase_add := by intro; simp

/-- The finite BRST--Seiberg--Witten curvature invariant is constant along its gauge flow. -/
theorem finiteBrstHodgeSeibergWittenGaugeFlow_invariant (t : ℝ) :
    seibergWittenSolutionInvariant finiteBrstHodgeSeibergWittenData
      (finiteBrstHodgeSeibergWittenGaugeFlow.at t finiteBrstHodgeSeibergWittenSolution) =
      seibergWittenSolutionInvariant finiteBrstHodgeSeibergWittenData
        finiteBrstHodgeSeibergWittenSolution :=
  finiteBrstHodgeSeibergWittenGaugeFlow.at_invariant t
    finiteBrstHodgeSeibergWittenSolution

end GaloisForLFunctions.HTGeometry.SeibergWitten
