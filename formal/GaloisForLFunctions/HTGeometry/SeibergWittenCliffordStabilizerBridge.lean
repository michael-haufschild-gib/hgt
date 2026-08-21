import GaloisForLFunctions.HTGeometry.CliffordStabilizerHiggsMechanism
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Clifford-stabilizer bridge to finite Seiberg--Witten invariants

The existing single-qubit Clifford-Higgs system represents each stabilizer vacuum by a pure
two-component density matrix.  Reindexing its `Bool` carrier by `Fin 2` identifies that matrix
exactly with the finite Seiberg--Witten outer-square invariant.  Thus every one of the six closed
stabilizer vacuum records supplies an exact finite `F = q(ψ)` solution.

This is a matrix-level bridge between existing finite theories.  It does not identify a qubit
density matrix with a curvature two-form of a continuum `Spinᶜ` connection.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Reindex a two-component Boolean spinor on the finite Seiberg--Witten carrier. -/
def boolSpinorToSeibergWitten (psi : Bool → ℂ) : SeibergWittenSpinor :=
  fun i => psi (finTwoEquiv i)

/-- Reindex a Boolean-indexed density matrix as a finite Seiberg--Witten curvature record. -/
def boolDensityAsSeibergWittenCurvature (rho : Matrix Bool Bool ℂ) : SeibergWittenCurvature :=
  fun i j => rho (finTwoEquiv i) (finTwoEquiv j)

/-- A reindexed pure qubit density is exactly the finite Seiberg--Witten quadratic map. -/
theorem boolDensityAsSeibergWittenCurvature_pure (psi : Bool → ℂ) :
    boolDensityAsSeibergWittenCurvature (pureQubitDensity psi) =
      seibergWittenQuadraticMap (boolSpinorToSeibergWitten psi) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Reindexing commutes with the common Abelian phase action. -/
theorem boolSpinorToSeibergWitten_gaugeEquivariant (u : Circle) (psi : Bool → ℂ) :
    boolSpinorToSeibergWitten (u • psi) = u • boolSpinorToSeibergWitten psi := by
  funext i
  rfl

/-- The finite Seiberg--Witten spinor carried by a stabilizer state. -/
def cliffordStabilizerSeibergWittenSpinor (t : Fin 6) : SeibergWittenSpinor :=
  boolSpinorToSeibergWitten (boolStabAmp t)

/-- Reindexed density invariant of a Clifford stabilizer vacuum. -/
def cliffordStabilizerSeibergWittenInvariant (t : Fin 6) : SeibergWittenCurvature :=
  boolDensityAsSeibergWittenCurvature (cliffordStabilizerDensity t).val

/-- Every Clifford stabilizer density invariant is the quadratic invariant of its reindexed spinor. -/
theorem cliffordStabilizerSeibergWittenInvariant_eq (t : Fin 6) :
    cliffordStabilizerSeibergWittenInvariant t =
      seibergWittenInvariant (cliffordStabilizerSeibergWittenSpinor t) := by
  change boolDensityAsSeibergWittenCurvature (pureQubitDensity (boolStabAmp t)) =
    seibergWittenQuadraticMap (boolSpinorToSeibergWitten (boolStabAmp t))
  exact boolDensityAsSeibergWittenCurvature_pure _

/-- Each reindexed Clifford stabilizer vacuum solves the finite curvature equation. -/
theorem cliffordStabilizerSeibergWitten_solvesEquation (t : Fin 6) :
    seibergWittenEquation (cliffordStabilizerSeibergWittenInvariant t)
      (cliffordStabilizerSeibergWittenSpinor t) := by
  rw [cliffordStabilizerSeibergWittenInvariant_eq]
  exact seibergWittenEquation_inducedCurvature _

/-- The existing stabilizer density remains a zero-potential Clifford-Higgs vacuum. -/
theorem cliffordStabilizerSeibergWitten_zeroHiggsPotential (t : Fin 6) :
    cliffordHiggsMechanism.potential (cliffordStabilizerDensity t) = 0 :=
  cliffordStabilizerDensity_zeroPotential t

/-- Common phase changes leave the reindexed finite curvature invariant unchanged. -/
theorem boolSpinorSeibergWittenInvariant_gaugeInvariant (u : Circle) (psi : Bool → ℂ) :
    seibergWittenInvariant (boolSpinorToSeibergWitten (u • psi)) =
      seibergWittenInvariant (boolSpinorToSeibergWitten psi) := by
  rw [boolSpinorToSeibergWitten_gaugeEquivariant]
  exact seibergWittenInvariant_gaugeInvariant u _

/-- The stabilizer's finite curvature invariant is constant along every common-phase gauge flow. -/
theorem cliffordStabilizerSeibergWittenGaugeFlow_invariant
  (phase : ℝ → Circle) (s : ℝ) (t : Fin 6) :
    seibergWittenInvariant
      (boolSpinorToSeibergWitten (phase s • boolStabAmp t)) =
      cliffordStabilizerSeibergWittenInvariant t := by
  rw [boolSpinorSeibergWittenInvariant_gaugeInvariant]
  exact (cliffordStabilizerSeibergWittenInvariant_eq t).symm

end GaloisForLFunctions.HTGeometry
