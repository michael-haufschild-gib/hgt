import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.ForestPacking.QuarticCost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.DisjointPackets

/-! # Repeated gate calls forced by a family of fixed-width triples -/
open Finset Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback
noncomputable section

/-- A family of disjoint enlarged triples with controlled local
perturbations forces a number of nonmerging calls proportional to its
size times sin(t)⁸. The perturbation threshold is independent of t. -/
theorem fixed_triples_force_calls {n : ℕ} {ι : Type*} [Fintype ι] (e f : ι→Fin (n+1))
    (hadj : ∀ a, (e a).succ=(f a).castSucc) (u : PathShell n)
    (C : TwoQubitCircuit (n+2)) {t : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (z : ℂ) (hz : ‖z‖=1) (he : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    let S a := tripleSites (e a) (f a)
    let N a := incidentSites (S a)
    let d a := ‖pathHamiltonian (packetPerturbation (e a) (f a) u)‖
    let E a := ∑ l∈(N a).biUnion pathIncidentLabels, |u l|
    (∀ a b, a≠b → Disjoint (N a) (N b)) → (∀ a, 4*d a*(2*E a+d a)≤1/256) →
      (Fintype.card ι:ℝ)*(sin t)^8≤8736*((redundant (circuitWord C):ℝ)+1) := by
  intro S N d E hd hcal
  have h := fixed_triples_fourth_power e f hadj u C ht z hz he hd hcal
  have hs := (half_pos ht.1).trans_le (short_sine ht)
  have hp : (sin t)^8≤(sin t)^4 := pow_le_pow_of_le_one hs.le (sin_le_one _) (by decide)
  have hR : 0≤(redundant (circuitWord C):ℝ) := Nat.cast_nonneg _
  linarith only [h,mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Fintype.card ι)),hR]

#print axioms fixed_triples_force_calls
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
