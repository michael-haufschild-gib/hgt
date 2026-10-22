import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliMultichart
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# L2-operator analytic Pauli coordinates on `SU(4)`

The existing fifteen-direction Pauli chart is also real analytic for the
finite-matrix L2 operator norm used by the exponential atlas.  Its derivative
at the identity is the same explicit Pauli tangent map.  This puts the local
rank witness and the global normalized exponential atlas in one analytic
model without transporting between inequivalent norm instances.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampSpecialUnitaryPauliL2ChartDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampSpecialUnitaryPauliL2ChartFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- The terminal `I ⊗ Z` phase matrix is real analytic in the L2 operator norm. -/
theorem analyticAt_terminalPauliPhaseMatrix_l2
    (t : ℝ) : AnalyticAt ℝ terminalPauliPhaseMatrix t := by
  let diagonalCLM : (Bool × Bool → ℂ) →L[ℂ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    (Matrix.diagonalLinearMap (Bool × Bool) ℂ ℂ).toContinuousLinearMap
  have hvector : AnalyticAt ℝ
      (fun s : ℝ => fun x : Bool × Bool => terminalPauliPhaseEigenvalue s x) t := by
    apply AnalyticAt.pi
    intro x
    unfold terminalPauliPhaseEigenvalue
    split
    · let mulNegI : ℂ →L[ℂ] ℂ :=
        (ContinuousLinearMap.lsmul ℂ ℂ) (-Complex.I)
      have hcomplex : AnalyticAt ℂ
          (fun z : ℂ => Complex.exp (-Complex.I * z)) (t : ℂ) := by
        have hlin : AnalyticAt ℂ (fun z : ℂ => mulNegI z) (t : ℂ) :=
          mulNegI.analyticAt _
        simpa [Function.comp_def, mulNegI, smul_eq_mul] using hlin.cexp
      have hreal : AnalyticAt ℝ
          (fun z : ℂ => Complex.exp (-Complex.I * z)) (t : ℂ) :=
        hcomplex.restrictScalars
      have hofReal : AnalyticAt ℝ (fun s : ℝ => (s : ℂ)) t := by
        convert Complex.ofRealCLM.analyticAt t using 1
        ext s
        rfl
      simpa [Function.comp_def] using hreal.comp hofReal
    · let mulI : ℂ →L[ℂ] ℂ :=
        (ContinuousLinearMap.lsmul ℂ ℂ) Complex.I
      have hcomplex : AnalyticAt ℂ
          (fun z : ℂ => Complex.exp (Complex.I * z)) (t : ℂ) := by
        have hlin : AnalyticAt ℂ (fun z : ℂ => mulI z) (t : ℂ) :=
          mulI.analyticAt _
        simpa [Function.comp_def, mulI, smul_eq_mul] using hlin.cexp
      have hreal : AnalyticAt ℝ
          (fun z : ℂ => Complex.exp (Complex.I * z)) (t : ℂ) :=
        hcomplex.restrictScalars
      have hofReal : AnalyticAt ℝ (fun s : ℝ => (s : ℂ)) t := by
        convert Complex.ofRealCLM.analyticAt t using 1
        ext s
        rfl
      simpa [Function.comp_def] using hreal.comp hofReal
  have hdiag : AnalyticAt ℝ (fun v : Bool × Bool → ℂ => diagonalCLM v)
      (fun x : Bool × Bool => terminalPauliPhaseEigenvalue t x) :=
    (diagonalCLM.restrictScalars ℝ).analyticAt _
  have hcomp := hdiag.comp hvector
  convert hcomp using 1
  funext s
  ext x y
  simp [diagonalCLM, terminalPauliPhaseMatrix]

/-- Each conjugated Pauli coordinate path is L2-operator real analytic. -/
theorem analyticAt_boolNonidentityTwoQubitPauliPath_l2
    (pq : boolNonidentityTwoQubitPauliLabel) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ =>
      (boolNonidentityTwoQubitPauliPath pq s :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) t := by
  rw [show (fun s : ℝ =>
      (boolNonidentityTwoQubitPauliPath pq s :
        Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      (fun s : ℝ =>
        (specialUnitaryAdjoint (boolNonidentityTwoQubitPauliTransport pq) :
          Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        terminalPauliPhaseMatrix s *
        (boolNonidentityTwoQubitPauliTransport pq :
          Matrix (Bool × Bool) (Bool × Bool) ℂ)) by
        funext s
        rfl]
  exact (analyticAt_const.mul (analyticAt_terminalPauliPhaseMatrix_l2 t)).mul analyticAt_const

private theorem analyticAt_boolNonidentityTwoQubitPauliPathProduct_l2
    (L : List boolNonidentityTwoQubitPauliLabel)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    AnalyticAt ℝ (boolNonidentityTwoQubitPauliPathProduct L) x := by
  induction L with
  | nil =>
      exact analyticAt_const
  | cons pq L ih =>
      change AnalyticAt ℝ
        (fun y : boolNonidentityTwoQubitPauliLabel → ℝ =>
          (boolNonidentityTwoQubitPauliPath pq (y pq) :
            Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolNonidentityTwoQubitPauliPathProduct L y) x
      have hpath := analyticAt_boolNonidentityTwoQubitPauliPath_l2 pq (x pq)
      let proj : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ] ℝ :=
        ContinuousLinearMap.proj pq
      have hproj : AnalyticAt ℝ
          (fun y : boolNonidentityTwoQubitPauliLabel → ℝ => y pq) x := by
        change AnalyticAt ℝ (fun y => proj y) x
        exact proj.analyticAt x
      have hhead : AnalyticAt ℝ
          (fun y : boolNonidentityTwoQubitPauliLabel → ℝ =>
            (boolNonidentityTwoQubitPauliPath pq (y pq) :
              Matrix (Bool × Bool) (Bool × Bool) ℂ)) x := by
        simpa [Function.comp_def] using
          (AnalyticAt.comp (f := fun y : boolNonidentityTwoQubitPauliLabel → ℝ => y pq)
            (g := fun s : ℝ =>
              (boolNonidentityTwoQubitPauliPath pq s :
                Matrix (Bool × Bool) (Bool × Bool) ℂ)) hpath hproj)
      exact hhead.mul ih

/-- The simultaneous fifteen-coordinate Pauli chart is L2-operator real analytic. -/
theorem analyticAt_boolNonidentityTwoQubitPauliCoordinateChart_l2
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    AnalyticAt ℝ boolNonidentityTwoQubitPauliCoordinateChart x := by
  change AnalyticAt ℝ
    (boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList) x
  exact analyticAt_boolNonidentityTwoQubitPauliPathProduct_l2 Finset.univ.toList x

/-- The actual L2-operator derivative of the simultaneous Pauli chart is its tangent map. -/
theorem hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero_l2 :
    HasFDerivAt boolNonidentityTwoQubitPauliCoordinateChart
      boolNonidentityTwoQubitPauliTangentMap 0 :=
  hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero

/-- The L2-operator Pauli chart has derivative range dimension fifteen at identity. -/
theorem finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart_l2 :
    Module.finrank ℝ
      (fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0).range = 15 :=
  finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart

end

end GaloisForLFunctions.HTGeometry
