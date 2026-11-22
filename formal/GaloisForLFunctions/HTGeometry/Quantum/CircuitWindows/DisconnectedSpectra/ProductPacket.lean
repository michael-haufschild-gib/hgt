import GaloisForLFunctions.HTGeometry.FiniteMomentDivisorReconstruction
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Spectral multiplicities of a tensor product from scalar power traces -/
open Matrix Finset
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section

private theorem packet_relabel {I : Type*} [Fintype I] (f g : I→ℂ)
    (h : ∀ k : ℕ, ∑ i, f i^k=∑ i, g i^k) :
    ∃ e : Equiv.Perm I, ∀ i, g (e i)=f i := by
  classical
  have hmulti : univ.val.map f=univ.val.map g := by
    apply multiset_eq_of_powerSum_eq_le (by simp)
    intro k _
    simp only [Multiset.map_map]
    exact h k
  have hc (z : ℂ) : Fintype.card {i // f i=z}=Fintype.card {i // g i=z} := by
    have hh := congrArg (Multiset.count z) hmulti
    rw [Multiset.count_map,Multiset.count_map] at hh
    change (univ.filter (fun i => z=f i)).card=(univ.filter (fun i => z=g i)).card at hh
    have sym (w : ℂ) : (z=w)=(w=z) := propext eq_comm
    simpa only [Fintype.card_subtype,sym] using hh
  let e (z : ℂ) := Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩

/-- Every diagonal packet unitarily conjugate to A⊗B can be relabelled
as a rectangular table of products of scalar factors. Schur diagonals
give the two factors. Power traces preserve every multiplicity. -/
theorem tensor_product_packet {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) (f : Fin m × Fin n→ℂ)
    (V : Matrix.unitaryGroup (Fin m × Fin n) ℂ)
    (he : A ⊗ₖ B=V.val*diagonal f*star V.val) :
    ∃ (a : Fin m→ℂ) (b : Fin n→ℂ) (p : Equiv.Perm (Fin m × Fin n)), ∀ i j, f (p (i,j))=a i*b j := by
  obtain ⟨U,T,hU,hU',hT,hA⟩ := exists_schur_triangulation m A
  obtain ⟨W,S,hW,hW',hS,hB⟩ := exists_schur_triangulation n B
  let e (i : Fin m × Fin n) := T i.1 i.1*S i.2 i.2
  have hv := Unitary.mem_iff.mp V.2
  have hconj (k : ℕ) : (A ⊗ₖ B)^k=V.val*diagonal (fun i => f i^k)*star V.val := by
    induction k with
    | zero => simp only [pow_zero,Matrix.diagonal_one,mul_one,hv.2]
    | succ k ih =>
      rw [pow_succ,ih,he]
      calc _ = V.val*((diagonal (fun i => f i^k)*diagonal f))*star V.val := by
               simp only [mul_assoc]
               rw [←mul_assoc (star V.val) V.val,hv.1,one_mul]
           _ = _ := by simp only [Matrix.diagonal_mul_diagonal,pow_succ]
  have hkron (k : ℕ) : (A ⊗ₖ B)^k=(A^k) ⊗ₖ (B^k) := by
    induction k with
    | zero => simp only [pow_zero,one_kronecker_one]
    | succ k ih => rw [pow_succ,ih,←mul_kronecker_mul,pow_succ A,pow_succ B]
  have htrace (k : ℕ) : ∑ i, e i^k=∑ i, f i^k := by
    have h := congrArg Matrix.trace ((hkron k).symm.trans (hconj k))
    rw [Matrix.trace_kronecker,trace_pow_eq_sum_diag hU hU' hT hA,trace_pow_eq_sum_diag hW hW' hS hB,
      Matrix.trace_mul_comm _ (star V.val),←mul_assoc,hv.1,one_mul,Matrix.trace_diagonal] at h
    calc _ = (∑ i, T i i^k)*(∑ j, S j j^k) := by
               rw [Finset.sum_mul]
               simp only [e,Fintype.sum_prod_type,mul_pow,Finset.mul_sum]
         _ = _ := h
  obtain ⟨p,hp⟩ := packet_relabel e f htrace
  exact ⟨fun i => T i i,fun j => S j j,p,fun i j => hp (i,j)⟩

#print axioms tensor_product_packet
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
