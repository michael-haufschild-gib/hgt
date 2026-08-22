import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliMultichart
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPhaseAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Analytic observer for the local `SU(4)` Pauli chart

The fifteen simultaneous Pauli coordinates have an explicit analytic
ambient-matrix observer whose derivative at identity is the identity.  This
is the finite-dimensional local-coordinate component required before a Haar
measure chart transfer can be established.
-/

open Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampSpecialUnitaryPauliLocalDiffeomorphDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampSpecialUnitaryPauliLocalDiffeomorphFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- The fifteen-direction Pauli tangent map is injective over the reals. -/
theorem boolNonidentityTwoQubitPauliTangentMap_injective :
    Function.Injective boolNonidentityTwoQubitPauliTangentMap := by
  let D := boolNonidentityTwoQubitPauliTangentMap
  have hLI : LinearIndependent ℝ (fun pq : boolNonidentityTwoQubitPauliLabel =>
      D (Pi.single pq 1)) := by
    simpa [D] using linearIndependent_boolNonidentityTwoQubitPauliTangentMap_single
  have hD : D.toLinearMap = Fintype.linearCombination ℝ
      (fun pq : boolNonidentityTwoQubitPauliLabel => D (Pi.single pq 1)) := by
    apply LinearMap.ext
    intro x
    change (∑ pq, x pq • boolNonidentityTwoQubitPauliTangent pq) = _
    rw [Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro pq _
    rw [boolNonidentityTwoQubitPauliTangentMap_single]
    simp
  rw [show (D : (boolNonidentityTwoQubitPauliLabel → ℝ) →
      Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      Fintype.linearCombination ℝ
        (fun pq : boolNonidentityTwoQubitPauliLabel => D (Pi.single pq 1)) by
          funext x
          exact DFunLike.congr_fun hD x]
  exact hLI.fintypeLinearCombination_injective

/-- A continuous real-linear left inverse to the full local Pauli tangent map. -/
def boolNonidentityTwoQubitPauliTangentLeftInverse :
    Matrix (Bool × Bool) (Bool × Bool) ℂ →L[ℝ]
      (boolNonidentityTwoQubitPauliLabel → ℝ) :=
  boolNonidentityTwoQubitPauliTangentMap.toLinearMap.leftInverse.toContinuousLinearMap

/-- The chosen tangent observer recovers every local Pauli coordinate exactly. -/
theorem boolNonidentityTwoQubitPauliTangentLeftInverse_comp :
    boolNonidentityTwoQubitPauliTangentLeftInverse.comp
      boolNonidentityTwoQubitPauliTangentMap =
      ContinuousLinearMap.id ℝ (boolNonidentityTwoQubitPauliLabel → ℝ) := by
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot_of_injective boolNonidentityTwoQubitPauliTangentMap_injective) x

/-- Each conjugated local Pauli path is real analytic in its coordinate. -/
theorem analyticAt_boolNonidentityTwoQubitPauliPath
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
  exact (analyticAt_const.mul (analyticAt_terminalPauliPhaseMatrix t)).mul analyticAt_const

private theorem analyticAt_boolNonidentityTwoQubitPauliPathProduct
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
      have hpath := analyticAt_boolNonidentityTwoQubitPauliPath pq (x pq)
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

/-- The simultaneous fifteen-coordinate local Pauli chart is real analytic. -/
theorem analyticAt_boolNonidentityTwoQubitPauliCoordinateChart
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    AnalyticAt ℝ boolNonidentityTwoQubitPauliCoordinateChart x := by
  change AnalyticAt ℝ
    (boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList) x
  exact analyticAt_boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList x

/-- Ambient-matrix observer associated to the fifteen-coordinate local Pauli chart. -/
def boolNonidentityTwoQubitPauliObservedMap :
    (boolNonidentityTwoQubitPauliLabel → ℝ) →
      (boolNonidentityTwoQubitPauliLabel → ℝ) :=
  fun x => boolNonidentityTwoQubitPauliTangentLeftInverse
    (boolNonidentityTwoQubitPauliCoordinateChart x)

/-- The local Pauli-coordinate observer is real analytic everywhere. -/
theorem analyticAt_boolNonidentityTwoQubitPauliObservedMap
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    AnalyticAt ℝ boolNonidentityTwoQubitPauliObservedMap x := by
  let L := boolNonidentityTwoQubitPauliTangentLeftInverse
  let C := boolNonidentityTwoQubitPauliCoordinateChart
  have hC : AnalyticAt ℝ C x :=
    analyticAt_boolNonidentityTwoQubitPauliCoordinateChart x
  have hL : AnalyticAt ℝ (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ => L M)
      (C x) := L.analyticAt _
  have h := hL.comp hC
  rw [show boolNonidentityTwoQubitPauliObservedMap = fun z => L (C z) by rfl]
  exact h

/-- The local Pauli-coordinate observer has identity Fréchet derivative at identity. -/
theorem hasFDerivAt_boolNonidentityTwoQubitPauliObservedMap_zero :
    HasFDerivAt boolNonidentityTwoQubitPauliObservedMap
      (ContinuousLinearMap.id ℝ (boolNonidentityTwoQubitPauliLabel → ℝ)) 0 := by
  let D := boolNonidentityTwoQubitPauliTangentMap
  let L := boolNonidentityTwoQubitPauliTangentLeftInverse
  let C := boolNonidentityTwoQubitPauliCoordinateChart
  have hC : HasFDerivAt C D 0 := by
    simpa [C, D] using hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero
  have hL : HasFDerivAt (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ => L M)
      L (C 0) := L.hasFDerivAt
  have hLC := hL.comp 0 hC
  have hLD : L.comp D =
      ContinuousLinearMap.id ℝ (boolNonidentityTwoQubitPauliLabel → ℝ) := by
    exact boolNonidentityTwoQubitPauliTangentLeftInverse_comp
  rw [show boolNonidentityTwoQubitPauliObservedMap = fun z => L (C z) by rfl]
  exact hLC.congr_fderiv hLD

/-- A certified open local inverse domain for the fifteen-coordinate observer. -/
noncomputable def boolNonidentityTwoQubitPauliObservedLocalHomeomorph :
    OpenPartialHomeomorph (boolNonidentityTwoQubitPauliLabel → ℝ)
      (boolNonidentityTwoQubitPauliLabel → ℝ) := by
  let e : (boolNonidentityTwoQubitPauliLabel → ℝ) ≃L[ℝ]
      (boolNonidentityTwoQubitPauliLabel → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (boolNonidentityTwoQubitPauliLabel → ℝ)
  have hcont : ContDiffAt ℝ 1 boolNonidentityTwoQubitPauliObservedMap 0 :=
    (analyticAt_boolNonidentityTwoQubitPauliObservedMap 0).contDiffAt
  have hderiv : HasFDerivAt boolNonidentityTwoQubitPauliObservedMap
      (e : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
        (boolNonidentityTwoQubitPauliLabel → ℝ)) 0 := by
    simpa [e] using hasFDerivAt_boolNonidentityTwoQubitPauliObservedMap_zero
  exact hcont.toOpenPartialHomeomorph boolNonidentityTwoQubitPauliObservedMap hderiv
    (by norm_num)

/-- Identity belongs to the source of the certified observer local inverse. -/
theorem zero_mem_boolNonidentityTwoQubitPauliObservedLocalHomeomorph_source :
    0 ∈ boolNonidentityTwoQubitPauliObservedLocalHomeomorph.source := by
  let e : (boolNonidentityTwoQubitPauliLabel → ℝ) ≃L[ℝ]
      (boolNonidentityTwoQubitPauliLabel → ℝ) :=
    ContinuousLinearEquiv.refl ℝ (boolNonidentityTwoQubitPauliLabel → ℝ)
  have hcont : ContDiffAt ℝ 1 boolNonidentityTwoQubitPauliObservedMap 0 :=
    (analyticAt_boolNonidentityTwoQubitPauliObservedMap 0).contDiffAt
  have hderiv : HasFDerivAt boolNonidentityTwoQubitPauliObservedMap
      (e : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
        (boolNonidentityTwoQubitPauliLabel → ℝ)) 0 := by
    simpa [e] using hasFDerivAt_boolNonidentityTwoQubitPauliObservedMap_zero
  exact hcont.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)

/-- On the inverse-function neighbourhood, the ambient local Pauli chart is injective. -/
theorem boolNonidentityTwoQubitPauliCoordinateChart_injectiveOn_localSource :
    Set.InjOn boolNonidentityTwoQubitPauliCoordinateChart
      boolNonidentityTwoQubitPauliObservedLocalHomeomorph.source := by
  intro x hx y hy hxy
  apply boolNonidentityTwoQubitPauliObservedLocalHomeomorph.injOn hx hy
  change boolNonidentityTwoQubitPauliObservedMap x =
    boolNonidentityTwoQubitPauliObservedMap y
  exact congrArg boolNonidentityTwoQubitPauliTangentLeftInverse hxy

end

end GaloisForLFunctions.HTGeometry
