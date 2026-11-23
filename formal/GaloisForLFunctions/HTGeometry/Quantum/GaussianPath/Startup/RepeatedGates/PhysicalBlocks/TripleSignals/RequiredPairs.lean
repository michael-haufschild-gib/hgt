import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PauliPacket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.CausalSupport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho

/-! # Stability of a three-site exchange against exterior dynamics -/
open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
open Temporal
noncomputable section
variable {n : ℕ}
private abbrev Reg := Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ

theorem tripleGenerator_selfAdjoint (e f : Fin (n+1)) : IsSelfAdjoint (tripleGenerator e f) := by
  unfold tripleGenerator mix
  change star (((1/sqrt 2:ℝ):ℂ) • (_+_))=_
  rw [star_smul,star_add,(finitePauliMatrix_isHermitian _).isSelfAdjoint.star_eq,
    (finitePauliMatrix_isHermitian _).isSelfAdjoint.star_eq,Complex.star_def,Complex.conj_ofReal]

private theorem probe_supported (i : Fin (n+2)) (a : Fin 3) :
    IsSiteSupported {i} (finitePauliMatrix (onsiteWord i a)) := by
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro j hj
  simp only [onsiteWord,if_neg (show j≠i from fun h => hj (mem_singleton.mpr h))]

/-- Multiplying the reference rotation by any exterior unitary leaves
its six signals unchanged. A circuit within 3/8 of this reference
must transmit between all three pairs in both directions. -/
theorem triple_required_pairs {e f : Fin (n+1)} (hm : e.succ=f.castSucc)
    (E : unitaryGroup (Fin (n+2)→Bool) ℂ) (hE : IsSiteSupported (tripleSites e f)ᶜ E.val)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1)
    (hfit : ‖E.val*unitaryEvolution (tripleGenerator e f) (π/2)-z • C.eval.val‖ ≤ 3/8) :
    ∀ i ∈ tripleSites e f, ∀ j ∈ tripleSites e f, i ∈ inputs (circuitWord C) j := by
  intro i hi j hj
  by_cases hij : i=j
  · exact hij ▸ knows_self _ _
  by_contra hmiss
  let V : unitaryGroup (Fin (n+2)→Bool) ℂ :=
    ⟨unitaryEvolution (tripleGenerator e f) (π/2),unitaryEvolution_mem_unitary (tripleGenerator_selfAdjoint e f) _⟩
  let P := finitePauliMatrix (onsiteWord i (tripleAxis e i))
  let Q := finitePauliMatrix (onsiteWord j (tripleAxis e j))
  have hsup := probe_supported i (tripleAxis e i)
  have hPQ := commute_of_absent C i j hmiss P Q hsup (probe_supported j _)
  have hb := SpanningDensity.missing_signal_bound C (E*V) z hz P Q
    (norm_finitePauliMatrix _).le (norm_finitePauliMatrix _).le hPQ
  have hcom : Commute E.val P := commute_of_isSiteSupported_disjoint
    (Finset.disjoint_singleton_right.mpr (fun h => Finset.mem_compl.mp h hi)) hE hsup
  have he : star (E.val*V.val)*P*(E.val*V.val)=star V.val*P*V.val := by
    calc _ = star V.val*(star E.val*(P*E.val))*V.val := by rw [star_mul]; simp only [mul_assoc]
         _ = _ := by rw [←hcom.eq,←mul_assoc (star E.val) E.val,E.property.1,one_mul]
  change ‖(star (E.val*V.val)*P*(E.val*V.val))*Q-Q*(star (E.val*V.val)*P*(E.val*V.val))‖ ≤
    4*‖E.val*V.val-z • C.eval.val‖ at hb
  rw [he] at hb
  have hs : ‖(star V.val*P*V.val)*Q-Q*(star V.val*P*V.val)‖=2 := triple_pair_signal hm hi hj hij
  rw [hs] at hb
  change ‖E.val*V.val-z • C.eval.val‖ ≤ 3/8 at hfit
  linarith only [hb,hfit]

#print axioms triple_required_pairs
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
