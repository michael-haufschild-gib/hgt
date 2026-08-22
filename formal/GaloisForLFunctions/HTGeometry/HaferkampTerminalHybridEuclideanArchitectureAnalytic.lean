import GaloisForLFunctions.HTGeometry.HaferkampTerminalHybridEuclideanAtlas

/-!
# Architecture contractions in terminal-phase augmented hybrid coordinates

Every gate receives the literal augmented Euclidean chart.  The resulting
finite ordered matrix word is analytic and still agrees exactly with the
underlying `SU(4)` architecture contraction.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampTerminalHybridEuclideanArchitectureAnalyticDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampTerminalHybridEuclideanArchitectureAnalyticFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

namespace TwoQubitArchitecture

/-- The fixed architecture contraction in terminal-phase augmented local
Euclidean coordinates, represented as an ambient matrix word. -/
def terminalHybridEuclideanContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ) :
    (Fin R → terminalHybridEuclideanCoordinates N) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun z => (List.ofFn fun r => twoQubitLiftMatrix
    (A.sites r).1 (A.sites r).2 (A.distinct r)
    (terminalHybridEuclideanGate N (z r))).reverse.prod

/-- The terminal-phase augmented coordinate contraction is real analytic at
every finite gate-coordinate assignment. -/
theorem analyticAt_terminalHybridEuclideanContraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → terminalHybridEuclideanCoordinates N) :
    AnalyticAt ℝ (A.terminalHybridEuclideanContraction N) z := by
  unfold terminalHybridEuclideanContraction
  refine analyticAt_reverse_prod_ofFn n R
    (fun r w => twoQubitLiftMatrix (A.sites r).1 (A.sites r).2 (A.distinct r)
      (terminalHybridEuclideanGate N w)) z ?_
  intro r x
  exact ((twoQubitLiftMatrixCLM (A.sites r).1 (A.sites r).2
    (A.distinct r)).restrictScalars ℝ).analyticAt _ |>.comp
      (analyticAt_terminalHybridEuclideanGate_coe N x)

/-- At zero terminal phase coordinates, the augmented contraction is the
original hybrid contraction at the projected local coordinates. -/
theorem terminalHybridEuclideanContraction_zeroPhase_eq_hybridEuclideanContraction
    {n R : ℕ} (A : TwoQubitArchitecture n R) (N : ℕ)
    (z : Fin R → boolTwoQubitHybridEuclideanCoordinates N) :
    A.terminalHybridEuclideanContraction N
      (fun r => terminalHybridEuclideanEmbed N 0 (z r)) =
      A.hybridEuclideanContraction N z := by
  unfold terminalHybridEuclideanContraction hybridEuclideanContraction
  congr 1
  apply congrArg List.reverse
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.get_ofFn]
    simp [terminalHybridEuclideanGate]
    rw [boolTwoQubitHybridEuclideanGate_coe]

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
