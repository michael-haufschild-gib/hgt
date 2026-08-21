import GaloisForLFunctions.HTGeometry.KnotTheory.RMatrix

/-!
# Closed Markov-compatible phase quantum trace

The existing phase braid has a framed character `I ^ writhe`.  Its writhe correction cancels the
two stabilization phases exactly.  The resulting trace is closed under the Markov moves represented
by this braid-word layer: cyclic permutation and positive or negative stabilization.

For this particular `i • SWAP` braiding the normalized trace is identically `1`.  Thus this is
honest closed Markov infrastructure, but not a nontrivial Jones polynomial.  A nontrivial result
requires a Hecke/Temperley--Lieb representation and a quantum trace beyond the present phase braid.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

noncomputable section

/-- Writhe-normalized trace of the concrete phase braid. -/
def phaseQuantumTrace (w : BraidWord n) : ℂ :=
  Complex.I ^ (-braidWrithe w) * framedMarkovTrace w

/-- The phase normalization cancels its framed character. -/
theorem phaseQuantumTrace_eq_one (w : BraidWord n) : phaseQuantumTrace w = 1 := by
  unfold phaseQuantumTrace framedMarkovTrace
  rw [← zpow_add₀ Complex.I_ne_zero]
  simp

/-- Closed traces respect the Markov moves implemented by the present braid-word layer. -/
structure MarkovCompatibleQuantumTrace where
  trace : ∀ {n : ℕ}, BraidWord n → ℂ
  trace_empty : ∀ {n : ℕ}, trace ([] : BraidWord n) = 1
  trace_append : ∀ {n : ℕ} (w v : BraidWord n),
    trace (w ++ v) = trace w * trace v
  trace_cyclic : ∀ {n : ℕ} (w v : BraidWord n),
    trace (w ++ v) = trace (v ++ w)
  trace_stabilize : ∀ {n : ℕ} (s : CrossingSign) (w : BraidWord n),
    trace (stabilizeBraid s w) = trace w

theorem phaseQuantumTrace_empty : phaseQuantumTrace ([] : BraidWord n) = 1 :=
  phaseQuantumTrace_eq_one []

theorem phaseQuantumTrace_append (w v : BraidWord n) :
    phaseQuantumTrace (w ++ v) = phaseQuantumTrace w * phaseQuantumTrace v := by
  rw [phaseQuantumTrace_eq_one, phaseQuantumTrace_eq_one, phaseQuantumTrace_eq_one]
  simp

theorem phaseQuantumTrace_cyclic (w v : BraidWord n) :
    phaseQuantumTrace (w ++ v) = phaseQuantumTrace (v ++ w) := by
  rw [phaseQuantumTrace_eq_one, phaseQuantumTrace_eq_one]

theorem phaseQuantumTrace_stabilize (s : CrossingSign) (w : BraidWord n) :
    phaseQuantumTrace (stabilizeBraid s w) = phaseQuantumTrace w := by
  rw [phaseQuantumTrace_eq_one, phaseQuantumTrace_eq_one]

/-- The concrete `i • SWAP` braid carries a closed Markov-compatible quantum trace. -/
def phaseQuantumMarkovTrace : MarkovCompatibleQuantumTrace where
  trace := fun {_} => phaseQuantumTrace
  trace_empty := fun {_} => phaseQuantumTrace_empty
  trace_append := fun w v => phaseQuantumTrace_append w v
  trace_cyclic := fun w v => phaseQuantumTrace_cyclic w v
  trace_stabilize := fun s w => phaseQuantumTrace_stabilize s w

end

end GaloisForLFunctions.HTGeometry.KnotTheory
