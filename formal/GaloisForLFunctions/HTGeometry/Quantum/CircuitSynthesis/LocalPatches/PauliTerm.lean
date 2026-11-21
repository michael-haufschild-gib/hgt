import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.PathOverlap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors

/-! # Single-gate evolutions of individual path interactions -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where

/-- Skew-adjoint real-time generator for one onsite or bond Pauli coefficient. -/
def pathTermGenerator {n : ℕ} (u : PathShell n) (l : PathLabel n) : Reg (n+2) :=
  (-Complex.I) • ((u l : ℂ) • finitePauliMatrix (pathWord l))

/-- Each path term has coefficient norm and its flow needs one physical gate. -/
theorem pathTerm_properties {n : ℕ} (u : PathShell n) (l : PathLabel n) :
    let x := pathTermGenerator u l
    ‖x‖ = |u l| ∧ x ∈ skewAdjoint (Reg (n+2)) ∧ ∀ t : ℝ,
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount = 1 ∧
        exp (t • x) = c • (C.eval : Reg (n+2)) := by
  let P : PauliTracelessLabel (n+2) 2 :=
    ⟨pathWord l,pathWord_support_card_le_two l,pathWord_ne_identity l⟩
  let B := finitePauliSelfAdjointBasis (Fin (n+2))
  let H := u l • B (pathWord l)
  have hc : realPauliCoefficient H P.val = u l := by
    change B.repr (u l • B (pathWord l)) (pathWord l) = u l
    simp
  have he : pathTermGenerator u l = twoLocalSkewGenerator H P := by
    unfold twoLocalSkewGenerator; rw [hc]; rfl
  dsimp only
  rw [he]
  refine ⟨(twoLocalSkewGenerator_norm _ _).trans (congrArg abs hc),
    twoLocalSkewGenerator_mem_skewAdjoint _ _,?_⟩
  intro t
  have hn : 2 ≤ n+2 := by omega
  obtain ⟨c,hc',G,hG⟩ := exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn H P t
  exact ⟨c,hc',TwoQubitCircuit.singleOn _ _ (P.coveringPair_distinct hn) G,rfl,
    by rwa [TwoQubitCircuit.singleOn_eval]⟩
end
end GaloisForLFunctions.HTGeometry.LocalPatches
