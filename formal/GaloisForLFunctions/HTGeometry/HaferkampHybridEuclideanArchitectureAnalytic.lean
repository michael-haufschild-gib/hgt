import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryPauliHybridEuclideanProductMeasure
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPhaseAnalytic

/-!
# Analytic global hybrid charts for fixed two-qubit architectures

The finite globally centred `SU(4)` hybrid chart is lifted at every gate of a
fixed architecture.  Its ordered contraction is a literal finite matrix word
and therefore real analytic in all local Euclidean coordinates.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampHybridEuclideanArchitectureAnalyticDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampHybridEuclideanArchitectureAnalyticFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- A reverse ordered finite matrix word is analytic when each local matrix
factor is analytic in its own Euclidean coordinate. -/
theorem analyticAt_reverse_prod_ofFn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n R : ℕ)
    (F : Fin R → E → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (z : Fin R → E)
    (hF : ∀ r x, AnalyticAt ℝ (F r) x) :
    AnalyticAt ℝ
      (fun y => (List.ofFn fun r => F r (y r)).reverse.prod) z := by
  induction R with
  | zero =>
      simpa using (analyticAt_const : AnalyticAt ℝ
        (fun _ : Fin 0 → E =>
          (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) z)
  | succ R ih =>
      let tailProj : (Fin (R + 1) → E) →L[ℝ] (Fin R → E) :=
        ContinuousLinearMap.pi fun j : Fin R =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (R + 1) => E) j.succ
      have htailProj : AnalyticAt ℝ (fun y : Fin (R + 1) → E => Fin.tail y) z := by
        change AnalyticAt ℝ (tailProj : (Fin (R + 1) → E) → Fin R → E) z
        exact tailProj.analyticAt _
      have htail : AnalyticAt ℝ
          (fun y : Fin (R + 1) → E =>
            (List.ofFn fun r : Fin R => F r.succ (Fin.tail y r)).reverse.prod) z :=
        AnalyticAt.comp
          (f := fun y : Fin (R + 1) → E => Fin.tail y)
          (g := fun w : Fin R → E =>
            (List.ofFn fun r : Fin R => F r.succ (w r)).reverse.prod)
          (ih (fun r => F r.succ) (Fin.tail z) (fun r x => hF r.succ x)) htailProj
      have hheadProj : AnalyticAt ℝ (fun y : Fin (R + 1) → E => y 0) z := by
        exact (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (R + 1) => E) 0).analyticAt _
      have hhead : AnalyticAt ℝ
          (fun y : Fin (R + 1) → E => F 0 (y 0)) z :=
        AnalyticAt.comp (f := fun y : Fin (R + 1) → E => y 0)
          (g := F 0) (hF 0 (z 0)) hheadProj
      rw [show (fun y : Fin (R + 1) → E =>
        (List.ofFn fun r => F r (y r)).reverse.prod) =
        (fun y =>
          (List.ofFn fun r : Fin R => F r.succ (Fin.tail y r)).reverse.prod * F 0 (y 0)) by
          funext y
          have hfun : (fun r : Fin (R + 1) => F r (y r)) =
              Fin.cons (F 0 (y 0)) (fun r : Fin R => F r.succ (Fin.tail y r)) := by
            funext r
            refine Fin.cases ?_ (fun i => ?_) r
            · rfl
            · rfl
          rw [hfun, List.ofFn_cons, List.reverse_cons, List.prod_append]
          simp]
      exact htail.mul hhead

namespace TwoQubitArchitecture

/-- The architecture contraction in one global hybrid Euclidean coordinate
space per gate, written as an ambient matrix word. -/
def hybridEuclideanContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    (Fin R → boolTwoQubitHybridEuclideanCoordinates N) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun z => (List.ofFn fun r => twoQubitLiftMatrix
    (A.sites r).1 (A.sites r).2 (A.distinct r)
    (boolTwoQubitHybridEuclideanChart N (z r))).reverse.prod

/-- The finite architecture hybrid-coordinate contraction is real analytic at
every gate-coordinate assignment. -/
theorem analyticAt_hybridEuclideanContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N) :
    AnalyticAt ℝ (A.hybridEuclideanContraction N) z := by
  unfold hybridEuclideanContraction
  refine analyticAt_reverse_prod_ofFn n R
    (fun r w => twoQubitLiftMatrix (A.sites r).1 (A.sites r).2 (A.distinct r)
      (boolTwoQubitHybridEuclideanChart N w)) z ?_
  intro r x
  exact ((twoQubitLiftMatrixCLM (A.sites r).1 (A.sites r).2
    (A.distinct r)).restrictScalars ℝ).analyticAt _ |>.comp
      (analyticAt_boolTwoQubitHybridEuclideanChart N x)

/-- The ambient hybrid-coordinate contraction agrees exactly with the original
`SU(4)` architecture contraction. -/
theorem hybridEuclideanContraction_eq_contraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N) :
    A.hybridEuclideanContraction N z =
      (A.contraction (fun r => boolTwoQubitHybridEuclideanGate N (z r)) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  unfold hybridEuclideanContraction TwoQubitArchitecture.contraction
  rw [← List.map_coe_unitary_reverse_prod]
  congr 1
  apply congrArg List.reverse
  rw [List.map_ofFn]
  congr 1

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
