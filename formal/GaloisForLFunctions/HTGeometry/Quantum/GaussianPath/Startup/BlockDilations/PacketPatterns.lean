import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.LongitudinalTest
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection

/-! # Independent tests of disjoint packet rotations on a common baseline -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Evolution under the sum of the selected internal packet generators,
followed on the right by the common baseline. -/
def idealPattern (R : I→Finset (Fin (n+2))) (u : PathShell n) (x : I→Bool) (h : ℝ) (W : Reg (n+2)) :=
  unitaryEvolution (∑ i, if x i then pathHamiltonianOnSites (R i) u else 0) h * W

/-- A packet's test depends only on its own bit, even when the
baseline entangles it with all other packets. -/
theorem pattern_fit_iff (R : I→Finset (Fin (n+2))) (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (u : PathShell n) (x : I→Bool) (h : ℝ) (W : Reg (n+2)) (i : I) (r : ℕ) (ε : ℝ) :
    packetFit (R i) r ε (idealPattern R u x h W) ↔
      packetFit (R i) r ε (if x i then unitaryEvolution (pathHamiltonianOnSites (R i) u) h*W else W) := by
  let B := fun j => if x j then pathHamiltonianOnSites (R j) u else 0
  have hs (j) : IsSiteSupported (R j) (B j) := by
    dsimp only [B]; split
    · exact pathHamiltonianOnSites_isSiteSupported _ _
    · exact IsSiteSupported.zero _
  have hsa (j) : IsSelfAdjoint (B j) := by
    dsimp only [B]; split
    · exact isSelfAdjoint_pathHamiltonianOnSites _ _
    · exact IsSelfAdjoint.zero _
  let T := univ.erase i
  let J := ∑ j ∈ T, B j
  have hJ : IsSiteSupported (R i)ᶜ J := by
    apply Finset.sum_induction _ (IsSiteSupported (R i)ᶜ)
      (fun _ _ => IsSiteSupported.add) (IsSiteSupported.zero _)
    intro j hj
    exact (hs j).mono (fun v hv => mem_compl.mpr fun hi =>
      Finset.disjoint_left.mp (hR (ne_of_mem_erase hj)) hv hi)
  have hJsa : IsSelfAdjoint J := (selfAdjoint _).sum_mem fun j _ => hsa j
  let U : unitaryGroup (Fin (n+2)→Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary hJsa h⟩
  have hU : IsSiteSupported (R i)ᶜ U.val := isSiteSupported_unitaryEvolution hJ h
  have hsum : J+B i=∑ j, B j := sum_erase_add _ _ (mem_univ i)
  have hF := unitaryEvolution_add_of_isSiteSupported_disjoint disjoint_compl_left hJ (hs i) h
  change packetFit (R i) r ε (unitaryEvolution (∑ j, B j) h*W) ↔ _
  rw [←hsum,hF,mul_assoc,packetFit_exterior U hU]
  cases hi : x i <;> simp [B,hi,unitaryEvolution,NormedSpace.exp_zero]

omit [Fintype I] [DecidableEq I] in
/-- A single circuit pays at least one wire for each requested wire in
a disjoint collection of failed packet tests. -/
theorem failed_packets_cost {N : ℕ} (R : I→Finset (Fin N))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j))) (T : Finset I)
    (r s : ℕ) (ε : ℝ) (X : Reg N) (hf : HasProjectiveCircuitApproximation N ε s X)
    (hT : ∀ i∈T, ¬packetFit (R i) r ε X) : T.card*(r+1)≤2*s := by
  obtain ⟨z,hz,C,hC,he⟩ := hf
  let S := C.touchedSites
  have hz' : star z*z=1 := conj_mul_self_of_norm_eq_one hz
  have hA : z • C.eval.val∈Matrix.unitaryGroup (Fin N→Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,star_smul,smul_mul_smul_comm,mul_comm z,hz',one_smul]
    exact C.eval.property.2
  let A : unitaryGroup (Fin N→Bool) ℂ := ⟨_,hA⟩
  have hS : IsSiteSupported S A.val := C.isSiteSupported_touchedSites.complex_smul z
  have hr (i) (hi : i∈T) : r+1≤(R i∩S).card := by
    apply Nat.succ_le_of_lt
    exact lt_of_not_ge fun h => hT i hi ⟨S,A,h,hS,he⟩
  have hd : (T : Set I).PairwiseDisjoint (fun i => R i∩S) := by
    intro i _ j _ hij
    exact (hR hij).mono inter_subset_left inter_subset_left
  calc
    _ = ∑ _i ∈ T, (r+1) := by simp
    _ ≤ ∑ i ∈ T, (R i∩S).card := sum_le_sum hr
    _ = (T.biUnion fun i => R i∩S).card := (card_biUnion hd).symm
    _ ≤ S.card := card_le_card (fun v hv => by obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv; exact (mem_inter.mp hi).2)
    _ ≤ 2*s := C.card_touchedSites_le.trans (Nat.mul_le_mul_left _ hC)

#print axioms pattern_fit_iff
#print axioms failed_packets_cost
end
end GaloisForLFunctions.HTGeometry.BlockDilations
