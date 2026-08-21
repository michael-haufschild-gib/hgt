import GaloisForLFunctions.HTGeometry.HaferkampBlockPrefixTransport
import GaloisForLFunctions.HTGeometry.HaferkampTerminalBlockData

/-!
# One step of the Appendix-B block-prefix induction

Given a Clifford prefix and a fresh Pauli direction, transport that direction
through the prefix, construct a terminal-aware BLC block for the transported
label, and retain the exact reverse identity required for Jacobian rank.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- One compatible BLC block selected after a Clifford prefix. -/
structure TerminalBlockPrefixStep
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root)
    (pre : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (P : Fin n → Option (Fin 3)) where
  transportedLabel : Fin n → Option (Fin 3)
  prefixCoeff : ℂ
  prefixCoeff_ne_zero : prefixCoeff ≠ 0
  prefix_transport :
    (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
      Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      prefixCoeff • finitePauliMatrix transportedLabel
  block : TerminalBlockData cone transportedLabel
  stripped_coordinate :
    Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Matrix.conjTranspose
          (edgeListBlockContraction edges block.gates :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
        (edgeListBlockContraction edges block.gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (block.transportCoeff * prefixCoeff)⁻¹ • finitePauliMatrix P

/-- The base contraction of a bundled terminal-aware block remains a finite
Pauli Clifford, so it can become the prefix for the next recursive step. -/
theorem TerminalBlockData.contraction_isFinitePauliClifford
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    IsFinitePauliClifford (edgeListBlockContraction edges block.gates) := by
  change IsFinitePauliClifford
    (haferkampGateWordReverseProduct totalTwoQubitLift edges block.gates)
  exact haferkampGateWordReverseProduct_isFinitePauliClifford edges block.gates
    block.gates_length cone.edge_distinct block.gates_clifford

/-- The next rank direction always admits a compatible terminal-aware BLC
block after any finite Pauli-Clifford prefix. -/
theorem exists_terminalBlockPrefixStep
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (pre : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hpre : IsFinitePauliClifford pre)
    (P : Fin n → Option (Fin 3)) (hP : P ≠ fun _ => none) :
    Nonempty (TerminalBlockPrefixStep cone pre P) := by
  obtain ⟨a, R, ha, hR, htransport⟩ :=
    hpre.exists_transport_of_nonidentity P hP
  have hRsupport : ∃ q, R q ≠ none := by
    by_contra h
    push Not at h
    apply hR
    funext q
    exact h q
  obtain ⟨block⟩ := cone.exists_terminalBlockData hn R hRsupport
  refine ⟨⟨R, a, ha, htransport, block, ?_⟩⟩
  exact reverse_block_prefix_transport pre
    (edgeListBlockContraction edges block.gates)
    P R (Function.update (fun _ => none) root (some 2))
    a block.transportCoeff ha block.transportCoeff_ne_zero
    htransport block.transport

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
