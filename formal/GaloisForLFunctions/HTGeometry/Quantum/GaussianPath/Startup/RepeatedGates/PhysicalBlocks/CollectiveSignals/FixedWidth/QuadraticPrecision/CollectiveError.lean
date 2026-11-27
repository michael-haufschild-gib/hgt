import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.LocalTests.Choi.LocalizedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.QuadraticPrecision.RequiredCalls
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.Packets.Unmarked

/-! # Squared-error charge for missing signals on all unmarked triples -/
open Matrix Set Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
open Temporal Feedback SpanningDensity
open private probe_supported from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.RequiredPairs
noncomputable section
variable {n : ℕ}

/-- At error at most t/8, every triple beyond two per nonmerging call
costs at least t⁴/4096 in squared projective fitting error. -/
theorem collective_error_charge {ι : Type*} [Fintype ι] (e f : ι→Fin (n+1))
    (ha : ∀ i, (e i).succ=(f i).castSucc) (u : PathShell n) (t : ℝ) (ht : t∈Ioc (0:ℝ) 1)
    (C : TwoQubitCircuit (n+2)) (z : ℂ) (hz : ‖z‖=1) {ε : ℝ} (hε : ε≤t/8)
    (hf : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤ε) :
    let S i := tripleSites (e i) (f i)
    let N i := incidentSites (S i)
    (∀ i j, i≠j → Disjoint (N i) (N j)) →
    (∀ i, let d := ‖pathHamiltonian (packetPerturbation (e i) (f i) u)‖
          let E := ∑ l∈(N i).biUnion pathIncidentLabels, |u l|
          4*d*(2*E+d)≤1/256) →
      (Fintype.card ι:ℝ)*t^4≤2*(redundant (circuitWord C):ℝ)*t^4+4096*ε^2 := by
  classical
  intro S N hd hcal
  let U := unitaryEvolution (pathHamiltonian u) t
  let V := z • C.eval.val
  have hs (i : ι) : S i⊆N i := subset_union_left
  obtain ⟨T,_,x,y,hmiss,hnum⟩ := unmarked_missing_pairs (circuitWord C) univ S
    (fun i _ => by rw [show (S i).card=3 from tripleSites_card (ha i)]; decide)
    (fun i _ j _ hij => (hd i j hij).mono (hs i) (hs j))
  let P (i : T) := packetProbe (e i) (x i)
  let B (i : T) := packetImage (e i) (f i) (x i)
  have hne (i : T) : x i≠y i := fun h => (hmiss i i.2).2.2 (h ▸ knows_self _ _)
  have hrep (i : T) := fixed_width_reporter (ha i) (hmiss i i.2).1 (hmiss i i.2).2.1
    (hne i) u ht (hcal i)
  choose K hS hK hm he using hrep
  have hz' (i : T) : (star V*P i*V*B i).trace=0 := by
    let Q := packetProbe (e i) (y i)
    have hcomm := commute_of_absent C (x i) (y i) (hmiss i i.2).2.2 (P i) Q
      (probe_supported _ _) (probe_supported _ _)
    have hphase : star V*P i*V=star C.eval.val*P i*C.eval.val := by
      simp only [V,star_smul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
      rw [show z*star z=1 by simp [Complex.mul_conj',hz],one_smul]
    rw [hphase]
    exact trace_zero_of_flip _ (B i) Q hcomm (finitePauliMatrix_mul_self _)
      (packetImage_flip (ha i) (hmiss i i.2).1 (hmiss i i.2).2.1 (hne i))
  let r := (sin t)^2/2
  have hsin := pow_le_pow_left₀ (half_pos ht.1).le (short_sine ht) 2
  have hr : 0<r := half_pos (sq_pos_of_pos ((half_pos ht.1).trans_le (short_sine ht)))
  have hε₀ := (norm_nonneg _).trans hf
  have hε2 := pow_le_pow_left₀ hε₀ hε 2
  have hcharge := localized_missing_count (fun i : T => N i) U V
    (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t) P B K
    (fun i => finitePauliMatrix_isHermitian _) (fun i => packetImage_hermitian _ _ _)
    (fun i => (norm_finitePauliMatrix _).le) (fun i => (CStarRing.norm_of_mem_unitary (packetImage_unitary (ha i) _)).le)
    hK hS (fun i j hij => hd i j (fun h => hij (Subtype.ext h))) hr hf hm he hz'
    (by dsimp only [r]; linarith) (by linarith only [hε,ht.2]) (by dsimp only [r]; linarith only [hε2,hsin])
  have hscale : t^2/64≤r/8 := by dsimp only [r]; linarith only [hsin]
  have hcost := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale 2)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card T))
  have hnum' := (Nat.cast_le (α:=ℝ)).mpr hnum
  rw [Finset.card_univ] at hnum'
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hnum'
  rw [Fintype.card_coe] at hcharge hcost
  linarith only [mul_le_mul_of_nonneg_right hnum' (pow_nonneg ht.1.le 4),hcost,hcharge]

#print axioms collective_error_charge
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
