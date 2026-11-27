import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LocalTests.ProjectiveTrace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.LocalContraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Orthogonality
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.DisjointPackets

/-! # Quadratic precision forces every directed link on a calibrated triple -/
open Finset Matrix Real Set RHTower GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback SpanningDensity
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
variable {n : ℕ}

/-- A missing input makes the circuit trace exactly zero. At quadratic
precision this contradicts the single physical triple signal. -/
theorem quadratic_required_pairs {e f : Fin (n+1)} (hm : e.succ=f.castSucc)
    (u : PathShell n) (t : ℝ) (ht : t∈Set.Ioc (0:ℝ) 1) (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1)
    (hfit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤t^2/64) :
    let d := ‖pathHamiltonian (packetPerturbation e f u)‖
    let S := incidentSites (tripleSites e f)
    let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
    4*d*(2*E+d)≤1/256 → ∀ i∈tripleSites e f, ∀ j∈tripleSites e f, i∈inputs (circuitWord C) j := by
  intro d S E hcal i hi j hj
  by_contra hmiss
  have hij : i≠j := fun hh => hmiss (hh ▸ knows_self _ _)
  let U := unitaryEvolution (pathHamiltonian u) t
  let P := packetProbe e i
  let B := packetImage e f i
  let Q := packetProbe e j
  let X := star U*P*U*B
  let D : ℂ := Fintype.card (Fin (n+2)→Bool)
  have hc := commute_of_absent C i j hmiss P Q (probe_supported _ _) (probe_supported _ _)
  have hzero := trace_zero_of_flip (star C.eval.val*P*C.eval.val) B Q hc (finitePauliMatrix_mul_self _)
    (packetImage_flip hm hi hj hij)
  have hu := missing_trace_bound U C.eval.val (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t)
    C.eval.2 P B (norm_finitePauliMatrix _).le (CStarRing.norm_of_mem_unitary (packetImage_unitary hm i)).le z hz hzero
  change ‖X.trace/D‖≤_ at hu
  obtain ⟨K,_,_,hmean,herr⟩ := fixed_width_reporter hm hi hj hij u ht hcal
  change ‖X-K‖≤_ at herr
  have hle := (norm_normalizedTrace_sub_le_l2OpNorm K X).trans ((norm_sub_rev K X).le.trans herr)
  have hdiff := norm_sub_norm_le (D⁻¹*K.trace) (D⁻¹*X.trace)
  change (sin t)^2/2≤‖K.trace/D‖ at hmean
  rw [div_eq_mul_inv K.trace D,mul_comm K.trace] at hmean
  rw [div_eq_mul_inv,mul_comm X.trace] at hu
  have hsin := pow_le_pow_left₀ (half_pos ht.1).le (short_sine ht) 2
  change ‖D⁻¹*K.trace-D⁻¹*X.trace‖≤_ at hle
  linarith only [hmean,hdiff,hle,hu,hfit,hsin,sq_pos_of_pos ht.1]

/-- Each disjoint calibrated triple consumes one endpoint of a nonmerging
call, independently of the number of connected components. -/
theorem quadratic_required_calls {ι : Type*} [Fintype ι] (e f : ι→Fin (n+1))
    (ha : ∀ i, (e i).succ=(f i).castSucc) (u : PathShell n) (t : ℝ) (ht : t∈Set.Ioc (0:ℝ) 1)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1)
    (hf : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤t^2/64) :
    let S i := tripleSites (e i) (f i)
    let N i := incidentSites (S i)
    (∀ i j, i≠j → Disjoint (N i) (N j)) →
    (∀ i, let d := ‖pathHamiltonian (packetPerturbation (e i) (f i) u)‖
          let E := ∑ l∈(N i).biUnion pathIncidentLabels, |u l|
          4*d*(2*E+d)≤1/256) → Fintype.card ι≤2*redundant (circuitWord C) := by
  classical
  intro S N hdis hcal
  have hs (i : ι) : S i⊆N i := subset_union_left
  obtain ⟨T,_,x,y,hmiss,_,hnum⟩ := packet_selection (circuitWord C) univ S
    (fun i _ => by rw [show (S i).card=3 from tripleSites_card (ha i)]; decide)
    (fun i _ j _ hij => (hdis i j hij).mono (hs i) (hs j))
  have hT : T=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi =>
    (hmiss i hi).2.2 (quadratic_required_pairs (ha i) u t ht C z hz hf (hcal i)
      (x i) (hmiss i hi).1 (y i) (hmiss i hi).2.1)
  simpa only [hT,Finset.card_empty,card_univ,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using hnum

#print axioms quadratic_required_calls
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
