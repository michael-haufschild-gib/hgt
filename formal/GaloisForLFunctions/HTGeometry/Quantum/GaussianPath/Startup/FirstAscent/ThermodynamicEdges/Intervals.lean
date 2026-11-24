import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BlockTransport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BlockLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.IntervalLabels

/-! # Width of an embedded block of the frozen Gaussian path -/

open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section
variable {n m B : ℕ}

private theorem translate_word (h : B+(m+2)≤n+2) (l : PathLabel m) :
    finitePauliMatrix (pathWord (translateLabel h l)) =
      Subregister.place (numberWires h) (finitePauliMatrix (pathWord l)) := by
  rw [place_pauli]
  apply congrArg finitePauliMatrix
  funext v
  by_cases hv : v∈intervalWires (n+2) B (m+2)
  · let e := numberWires h
    obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
    rw [extendPacketPauliLabel_mem _ _ hv,Function.comp_apply,←hi,e.symm_apply_apply,
      ←show (e i).val=v from congrArg Subtype.val hi]
    rcases l with ⟨s,a⟩|⟨s,p⟩ <;>
      simp [pathWord,translateLabel,onsiteWord,couplingWord,e,numberWires,Fin.ext_iff,Nat.add_assoc]
  · rw [extendPacketPauliLabel_notMem _ _ hv]
    have hn : ¬(B≤v.val ∧ v.val<B+(m+2)) := fun hh => hv (mem_filter.mpr ⟨mem_univ _,hh⟩)
    rcases l with ⟨s,a⟩|⟨s,p⟩
    · have hne : v.val≠B+s.val := by have := s.isLt; omega
      simp [pathWord,translateLabel,onsiteWord,numberWires,Fin.ext_iff,hne]
    · have h₁ : v.val≠B+s.val := by have := s.isLt; omega
      have h₂ : v.val≠B+s.val+1 := by have := s.isLt; omega
      simp [pathWord,translateLabel,couplingWord,Fin.ext_iff,h₁,h₂]

private theorem place_sum {ι : Type*} [Fintype ι] (h : B+(m+2)≤n+2) (A : ι→Register (m+2)) :
    Subregister.place (numberWires h) (∑ i,A i)=∑ i,Subregister.place (numberWires h) (A i) := by
  unfold Subregister.place
  rw [map_sum]
  exact map_sum (liftLocalMatrixLinear (fun _ : Fin (n+2) => Bool) _) _ _

/-- A full block of the physical Hamiltonian has exactly its independent row-block width. -/
theorem width_full_piece (ω : PathPauliDisorder) (b : Fin (n+2))
    (h : b.val*(m+2)+(m+2)≤n+2) :
    circuitHamiltonianSpectralWidth (shellOperator (piece (m+2) (pathPauliDisorderShell ω n) b)) =
      blockWidth m (readBlock m ω b.val) := by
  apply place_width _ (numberWires h)
  change pathHamiltonian _=Subregister.place _ (pathHamiltonian _)
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum,place_sum]
  let u := pathPauliDisorderShell ω n
  let summand (l : PathLabel n) := ((u l : ℝ):ℂ) • finitePauliMatrix (pathWord l)
  have hc : (∑ l, ((piece (m+2) u b l:ℝ):ℂ) • finitePauliMatrix (pathWord l)) =
      ∑ l ∈ labels (m+2) (some b), summand l := by
    rw [labels,sum_filter]
    apply sum_congr rfl
    intro l _
    by_cases ho : owner (m+2) l=some b <;> simp [summand,piece,ho]
  rw [hc,eq_comm]
  apply sum_bij (fun l _ => translateLabel h l)
  · intro l _
    exact mem_filter.mpr ⟨mem_univ _,owned_translate b h l⟩
  · exact fun _ _ _ _ eq => translateLabel_injective h eq
  · intro l hl
    obtain ⟨k,hk⟩ := translate_covers b h l (mem_filter.mp hl).2
    exact ⟨k,mem_univ _,hk⟩
  · intro l _
    rw [Subregister.place_smul,←translate_word]
    have hc' : readBlock m ω b.val l=u (translateLabel h l) := by cases l <;> rfl
    change ((readBlock m ω b.val l:ℝ):ℂ) • _=((u (translateLabel h l):ℝ):ℂ) • _
    rw [hc']

#print axioms width_full_piece
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
