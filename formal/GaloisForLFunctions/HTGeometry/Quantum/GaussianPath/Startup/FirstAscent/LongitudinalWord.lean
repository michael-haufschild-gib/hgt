import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord

/-! # Exact gate count upper bound for a sparse longitudinal packet -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private def fieldAt {n : ℕ} (q : ℝ) (s : Fin (n+2)) : Reg (n+2) :=
  (q:ℂ) • finitePauliMatrix (onsiteWord s 2)

private theorem packet_sum {n : ℕ} (S : Finset (Fin (n+2))) (q : ℝ) :
    pathHamiltonian (longitudinalPacket S q)=∑ s ∈ S, fieldAt q s := by
  classical
  have hE (e : Fin (n+1)) : edgePart (longitudinalPacket S q) e=0 := by
    simp [edgePart,longitudinalPacket]
  rw [pathHamiltonian]
  simp only [hE,Finset.sum_const_zero,add_zero,onsitePart,Fintype.sum_prod_type]
  have hrow (s : Fin (n+2)) : (∑ a : Fin 3,
      ((longitudinalPacket S q (.inl (s,a)):ℝ):ℂ) • finitePauliMatrix (onsiteWord s a))=
      if s∈S then fieldAt q s else 0 := by
    by_cases hs : s∈S
    · rw [if_pos hs,Finset.sum_eq_single (2:Fin 3)]
      · simp [longitudinalPacket,hs,fieldAt]
      · intro a _ ha
        simp [longitudinalPacket,ha]
      · exact fun h => (h (Finset.mem_univ _)).elim
    · simp [longitudinalPacket,hs]
  simp only [hrow,Finset.sum_ite_mem,Finset.univ_inter]

private theorem field_supported {n : ℕ} (q : ℝ) (s : Fin (n+2)) :
    IsSiteSupported {s} (fieldAt q s) := by
  apply IsSiteSupported.complex_smul
  apply finitePauliMatrix_isSiteSupported_of_eq_none
  intro j hj
  have h : j≠s := fun e => hj (Finset.mem_singleton.mpr e)
  simp [onsiteWord,h]

/-- Each selected longitudinal field costs one gate. The full commuting
packet is exact, at every strength and every signed time. -/
theorem longitudinal_word {n : ℕ} (S : Finset (Fin (n+2))) (q t : ℝ) :
    HasProjectiveCircuitApproximation (n+2) 0 S.card
      (unitaryEvolution (pathHamiltonian (longitudinalPacket S q)) t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [packet_sum,Finset.sum_empty]
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    simp [unitaryEvolution,TwoQubitCircuit.one_eval]
  | @insert v S hv ih =>
    let K := pathHamiltonian (longitudinalPacket S q)
    have hK : IsSiteSupported S K := by
      change IsSiteSupported S (pathHamiltonian _)
      rw [←longitudinalPacket_restriction S q]
      exact pathHamiltonianOnSites_isSiteSupported _ _
    have he := (LocalPatches.pathTerm_properties (longitudinalPacket {v} q) (.inl (v,2))).2.2 t
    obtain ⟨z,hz,C,hc,hf⟩ := he
    have hf' : unitaryEvolution (fieldAt q v) t=z • (C.eval : Reg (n+2)) := by
      simpa only [unitaryEvolution,fieldAt,LocalPatches.pathTermGenerator,pathWord,longitudinalPacket,
        WithLp.ofLp_toLp,Finset.mem_singleton,eq_self,and_self,ite_true] using hf
    have h₁ : HasProjectiveCircuitApproximation (n+2) 0 1 (unitaryEvolution (fieldAt q v) t) :=
      ⟨z,hz,C,hc.le,by rw [hf',sub_self,norm_zero]⟩
    rw [packet_sum,Finset.sum_insert hv,←packet_sum S q,
      unitaryEvolution_add_of_isSiteSupported_disjoint (Finset.disjoint_singleton_left.mpr hv)
        (field_supported q v) hK t]
    have hx := LocalPatches.approx_product (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) t) h₁ ih
    simpa only [zero_add,Finset.card_insert_of_notMem hv,Nat.add_comm 1] using hx

#print axioms longitudinal_word
end
end GaloisForLFunctions.HTGeometry.FirstAscent
