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

local instance : DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance : Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

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
      boolNonidentityTwoQubitPauliTangentMap 0 := by
  let f : (boolNonidentityTwoQubitPauliLabel → ℝ) →
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    boolNonidentityTwoQubitPauliCoordinateChart
  have hdiff : DifferentiableAt ℝ f 0 :=
    (analyticAt_boolNonidentityTwoQubitPauliCoordinateChart_l2 0).differentiableAt
  have hfull : HasFDerivAt f (fderiv ℝ f 0) 0 := hdiff.hasFDerivAt
  have haxis (pq : boolNonidentityTwoQubitPauliLabel) :
      (fderiv ℝ f 0) (Pi.single pq (1 : ℝ)) =
        boolNonidentityTwoQubitPauliTangent pq := by
    let singleCLM : ℝ →L[ℝ] (boolNonidentityTwoQubitPauliLabel → ℝ) :=
      ContinuousLinearMap.single ℝ
        (fun _ : boolNonidentityTwoQubitPauliLabel => ℝ) pq
    have hsingle : HasFDerivAt
        (fun t : ℝ => Pi.single pq t) singleCLM 0 := by
      change HasFDerivAt
        (singleCLM : ℝ → (boolNonidentityTwoQubitPauliLabel → ℝ)) singleCLM 0
      exact singleCLM.hasFDerivAt
    have hbase : HasFDerivAt f (fderiv ℝ f 0) (Pi.single pq (0 : ℝ)) := by
      simpa using hfull
    have hcomp := HasFDerivAt.comp
      (f := fun t : ℝ => Pi.single pq t) (g := f) 0 hbase hsingle
    have haxisExact : HasFDerivAt
        (fun t : ℝ => f (Pi.single pq t))
        (ContinuousLinearMap.toSpanSingleton ℝ
          (boolNonidentityTwoQubitPauliTangent pq)) 0 := by
      rw [show (fun t : ℝ => f (Pi.single pq t)) =
          (fun t : ℝ => (boolNonidentityTwoQubitPauliPath pq t :
            Matrix (Bool × Bool) (Bool × Bool) ℂ)) by
          funext t
          exact boolNonidentityTwoQubitPauliCoordinateChart_single pq t]
      exact (entrywiseHasDerivAt_boolNonidentityTwoQubitPauliPath pq).hasFDerivAt
    have hderiv : (fderiv ℝ f 0).comp singleCLM =
        ContinuousLinearMap.toSpanSingleton ℝ
          (boolNonidentityTwoQubitPauliTangent pq) := by
      apply hcomp.unique
      exact haxisExact
    have hvalue := congrArg (fun L : ℝ →L[ℝ]
        Matrix (Bool × Bool) (Bool × Bool) ℂ => L 1) hderiv
    change (fderiv ℝ f 0) (Pi.single pq (1 : ℝ)) = _ at hvalue
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hvalue
  have hmap : fderiv ℝ f 0 = boolNonidentityTwoQubitPauliTangentMap := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      (fderiv ℝ f 0) x =
          (fderiv ℝ f 0) (∑ pq, Pi.single pq (x pq)) := by
            rw [Finset.univ_sum_single]
      _ = ∑ pq, (fderiv ℝ f 0) (Pi.single pq (x pq)) := by rw [map_sum]
      _ = ∑ pq, x pq • boolNonidentityTwoQubitPauliTangent pq := by
        apply Finset.sum_congr rfl
        intro pq _
        have hsingle : Pi.single pq (x pq) = x pq • Pi.single pq (1 : ℝ) := by
          ext q
          by_cases hqp : q = pq
          · subst q
            simp
          · simp [hqp]
        rw [hsingle, map_smul, haxis pq]
      _ = boolNonidentityTwoQubitPauliTangentMap x := by rfl
  rw [show boolNonidentityTwoQubitPauliCoordinateChart = f by rfl]
  exact hfull.congr_fderiv hmap

/-- The L2-operator Pauli chart has derivative range dimension fifteen at identity. -/
theorem finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart_l2 :
    Module.finrank ℝ
      (fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0).range = 15 := by
  let D : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0
  change Module.finrank ℝ D.range = 15
  apply le_antisymm
  · calc
      Module.finrank ℝ D.range ≤
          Module.finrank ℝ (boolNonidentityTwoQubitPauliLabel → ℝ) :=
        LinearMap.finrank_range_le D.toLinearMap
      _ = Fintype.card boolNonidentityTwoQubitPauliLabel := Module.finrank_pi ℝ
      _ = 15 := card_boolNonidentityTwoQubitPauliLabel
  · rw [← card_boolNonidentityTwoQubitPauliLabel]
    have hderiv : D = boolNonidentityTwoQubitPauliTangentMap := by
      exact hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero_l2.fderiv
    rw [hderiv]
    exact finrank_range_ge_boolNonidentityTwoQubitPauliTangentMap

end

end GaloisForLFunctions.HTGeometry
