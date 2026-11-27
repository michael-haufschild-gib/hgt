import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.LocalTest
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality.PacketFamily

/-! # A fitting circuit admits at most order sin(t)⁻⁴ independent packet tests -/
open Matrix Finset Real GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section
variable {n m : ℕ}

/-- A local quadratic transfer is amplified in the Choi overlap even when
each individual packet signal is weaker than the physical fitting error. -/
theorem compatible_count (e f : Fin m→Fin (n+1)) (x y : Fin m→Fin (n+2))
    (hadj : ∀ i, (e i).succ=(f i).castSucc)
    (hd : ∀ i j, i≠j → Disjoint (tripleSites (e i) (f i)) (tripleSites (e j) (f j)))
    (hx : ∀ i, x i∈tripleSites (e i) (f i)) (hy : ∀ i, y i∈tripleSites (e i) (f i))
    (C : TwoQubitCircuit (n+2)) (hm : ∀ i, x i∉inputs (circuitWord C) (y i))
    (hc : ∀ i j, i≠j → ¬conflicting (circuitWord C) x y i j)
    (u : PathShell n) (t δ : ℝ) (hδ : 0≤δ) (hs : 0 < (sin t)^2)
    (hcoup : ∀ i l, l∈(tripleSites (e i) (f i)).biUnion pathIncidentLabels →
      |u l-tripleField (e i) (f i) (1/sqrt 2) l|≤δ)
    (herr : 126* |t| * δ≤(sin t)^2/4) (z : ℂ) (hz : ‖z‖=1)
    (he : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    (m:ℝ)*(sin t)^4≤16 := by
  let K i := packetTest (e i) (f i) (x i) t
  have hmean (i) : (sin t)^2≤‖(K i).trace/(Fintype.card (Fin (n+2)→Bool):ℂ)‖ := by
    have hne : x i≠y i := fun h => hm i (h ▸ knows_self _ _)
    rw [show (K i).trace/_=(sin t:ℂ)^2 from packet_transfer (hadj i) (hx i) (hy i) hne t,
      ←Complex.ofReal_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.le]
  have h := compatible_reporter_count e f x y (fun i => tripleSites (e i) (f i)) hadj
    (fun _ => fun _ h => h) hd hx hy C hm hc _ (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t)
    K _ hs (fun i => (CStarRing.norm_of_mem_unitary (packetTest_unitary (hadj i) (x i) t)).le)
    (fun i => packetTest_supported (hadj i) (hx i) t) hmean
    (fun i => (packetTest_local_error (hadj i) (hx i) u hδ t (hcoup i)).trans herr) z hz he
  exact (show (m:ℝ)*(sin t)^4=(m:ℝ)*((sin t)^2)^2 by ring).trans_le h

#print axioms compatible_count
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
