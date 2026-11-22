import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.DisconnectedSpectra.CircuitCut

/-! # Information missing after a disconnected prefix and sparse suffix -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section
abbrev Register (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

/-- Cut a time-ordered physical circuit immediately after its p-th gate. -/
theorem split_circuit {N p q : ℕ} (C : TwoQubitCircuit N) (hc : C.gateCount=p+q) :
    ∃ P Q : TwoQubitCircuit N, P.gateCount=p ∧ Q.gateCount=q ∧ C.eval=Q.eval*P.eval := by
  rcases C with ⟨k,A,g⟩
  change k=p+q at hc
  subst k
  let lo (i : Fin p) := i.castAdd q
  let hi (i : Fin q) := i.natAdd p
  let P : TwoQubitCircuit N := ⟨p,⟨A.sites ∘ lo,fun i => A.distinct (lo i)⟩,g ∘ lo⟩
  let Q : TwoQubitCircuit N := ⟨q,⟨A.sites ∘ hi,fun i => A.distinct (hi i)⟩,g ∘ hi⟩
  refine ⟨P,Q,rfl,rfl,?_⟩
  let f (i : Fin (p+q)) := A.gateLift i (g i)
  have e : f=Fin.append (f ∘ lo) (f ∘ hi) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [lo,hi]
  change (List.ofFn f).reverse.prod=(List.ofFn (f ∘ hi)).reverse.prod*(List.ofFn (f ∘ lo)).reverse.prod
  conv_lhs => rw [e,List.ofFn_fin_append,List.reverse_append,List.prod_append]

/-- A suffix missing output i cannot transfer to it a signal from an
input j separated from i throughout the prefix. -/
theorem cut_suffix_commute {N : ℕ} (P Q : TwoQubitCircuit N) (S : Finset (Fin N))
    (hcut : ∀ k : Fin P.gateCount, (P.architecture.sites k).1 ∈ S ↔ (P.architecture.sites k).2 ∈ S)
    {i j : Fin N} (hi : i ∉ Q.touchedSites) (hs : i ∈ S) (hj : j ∉ S)
    (A B : Register N) (hA : IsSiteSupported {i} A) (hB : IsSiteSupported {j} B) :
    Commute (star (Q.eval.val*P.eval.val)*A*(Q.eval.val*P.eval.val)) B := by
  have hAQ := commute_of_isSiteSupported_disjoint (Finset.disjoint_singleton_left.mpr hi)
    hA Q.isSiteSupported_touchedSites
  have hfixed : star Q.eval.val*A*Q.eval.val=A := by
    rw [mul_assoc,hAQ.eq,←mul_assoc,(Unitary.mem_iff.mp Q.eval.property).1,one_mul]
  have he : star (Q.eval.val*P.eval.val)*A*(Q.eval.val*P.eval.val)=
      star P.eval.val*(star Q.eval.val*A*Q.eval.val)*P.eval.val := by simp only [star_mul,mul_assoc]
  rw [he,hfixed]
  exact commute_of_isSiteSupported_disjoint (Finset.disjoint_singleton_right.mpr hj)
    (SpanningDensity.circuit_conjugate_supported P S hcut A (hA.mono (Finset.singleton_subset_iff.mpr hs))) hB

/-- If every input can signal to every output, a prefix reaching all
wires must precede the final floor((N−1)/2) gates. -/
theorem missing_ordered_pair {N : ℕ} (hN : 2 ≤ N) (C : TwoQubitCircuit N)
    (hc : C.gateCount < N-1+(N-1)/2) :
    ∃ i j : Fin N, i ≠ j ∧ ∀ A B : Register N, IsSiteSupported {i} A → IsSiteSupported {j} B →
      Commute (star C.eval.val*A*C.eval.val) B := by
  classical
  let q := min C.gateCount ((N-1)/2)
  let p := C.gateCount-q
  have hp : p+1 < N := by dsimp [p,q]; omega
  have hq : 2*q < N := by dsimp [q]; omega
  obtain ⟨P,Q,hP,hQ,he⟩ := split_circuit (p:=p) (q:=q) C (by dsimp [p,q]; omega)
  obtain ⟨S,hS,hT,hcut⟩ := DisconnectedSpectra.circuit_cut P (by rwa [hP])
  have hsize := Q.card_touchedSites_le.trans_lt (by rwa [hQ] : 2*Q.gateCount < N)
  obtain ⟨i,hi⟩ : ∃ i : Fin N, i ∉ Q.touchedSites := by
    by_contra! h
    rw [Finset.eq_univ_of_forall h,Finset.card_univ,Fintype.card_fin] at hsize
    exact hsize.false
  by_cases hmem : i ∈ S
  · obtain ⟨j,hj'⟩ := hT
    have hj := Finset.mem_compl.mp hj'
    refine ⟨i,j,fun h => hj (h ▸ hmem),?_⟩
    rw [he]
    exact cut_suffix_commute P Q S hcut hi hmem hj
  · obtain ⟨j,hj⟩ := hS
    refine ⟨i,j,fun h => hmem (h ▸ hj),?_⟩
    rw [he]
    exact cut_suffix_commute P Q Sᶜ (fun k => by simpa only [Finset.mem_compl] using (hcut k).not)
      hi (Finset.mem_compl.mpr hmem) (fun h => Finset.mem_compl.mp h hj)

#print axioms missing_ordered_pair
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
