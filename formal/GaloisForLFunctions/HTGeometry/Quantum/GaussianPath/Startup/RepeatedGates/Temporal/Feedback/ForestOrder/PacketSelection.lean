import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ForestOrder.ForestCertificates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.IndependentTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.Packets.Unmarked

/-! # Linear-size compatible families within a feedback class -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
open private reduced_inputs_subset from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ThreeSenders
variable {J V : Type*} [DecidableEq J] [DecidableEq V] [Fintype V] [Nonempty V]

/-- Color by the reduced forest and the output's feedback profile.
Any cross-connection between two missing pairs of a common profile
survives in the forest. The largest joint color therefore suffices. -/
theorem linear_missing_signals (w : List (V×V)) (x y : J→V) (A : Finset J)
    (hm : ∀ i∈A, x i∉inputs w (y i)) :
    ∃ S⊆A, (∀ i∈S, ∀ j∈S, ¬conflicting w x y i j) ∧
      A.card≤(1+2*redundant w)*(4*S.card) := by
  classical
  obtain ⟨c,hc⟩ := forest_four_colors (mergingWord w) (redundant_mergingWord w)
    (fun i : A => x i) (fun i : A => y i)
    (fun i h => hm _ i.2 (reduced_inputs_subset w _ h))
  let P (i : J) : Finset ℕ × (Bool×Bool) :=
    (profile w (y i),if h : i∈A then c ⟨i,h⟩ else (false,false))
  let D := (univ.image (profile w)) ×ˢ (univ : Finset (Bool×Bool))
  have hd : D.Nonempty := (univ_nonempty.image _).product univ_nonempty
  let F (p : Finset ℕ × (Bool×Bool)) := A.filter fun i => P i=p
  obtain ⟨p,_,hmax⟩ := exists_max_image D (fun q => (F q).card) hd
  refine ⟨F p,filter_subset ..,?_,?_⟩
  · intro i hi j hj hconf
    obtain ⟨hiA,hip⟩ := mem_filter.mp hi
    obtain ⟨hjA,hjp⟩ := mem_filter.mp hj
    have he := hip.trans hjp.symm
    have hprof := congrArg Prod.fst he
    have hcolor : c ⟨i,hiA⟩=c ⟨j,hjA⟩ := by simpa only [P,dif_pos hiA,dif_pos hjA] using congrArg Prod.snd he
    exact hc _ _ hcolor ⟨cross_connection_in_forest w (hm i hiA) hprof.symm hconf.1,
      cross_connection_in_forest w (hm j hjA) hprof hconf.2⟩
  · have hcov : A⊆D.biUnion F := fun i hi => mem_biUnion.mpr ⟨P i,
        mem_product.mpr ⟨mem_image_of_mem _ (mem_univ _),mem_univ _⟩,mem_filter.mpr ⟨hi,rfl⟩⟩
    have hnum : D.card≤(1+2*redundant w)*4 := by
      simpa [D,Fintype.card_prod] using Nat.mul_le_mul_right 4 (number_of_profiles w)
    calc
      A.card ≤ ∑ q∈D, (F q).card := (card_le_card hcov).trans card_biUnion_le
      _ ≤ ∑ _q∈D, (F p).card := sum_le_sum fun q hq => hmax q hq
      _ = D.card*(F p).card := by simp
      _ ≤ _ := (Nat.mul_le_mul_right _ hnum).trans_eq (Nat.mul_assoc ..)

/-- Every disjoint family of triples pays at most two packets per
nonmerging call plus four compatible-family sizes per feedback class. -/
theorem linear_packet_selection (w : List (V×V)) (F : Finset J) (S : J→Finset V)
    (hs : ∀ i∈F, 2<(S i).card) (hd : ∀ i∈F, ∀ j∈F, i≠j → Disjoint (S i) (S j)) :
    ∃ T⊆F, ∃ x y : J→V, (∀ i∈T, x i∈S i ∧ y i∈S i ∧ x i∉inputs w (y i)) ∧
      (∀ i∈T, ∀ j∈T, i≠j → ¬conflicting w x y i j) ∧
      F.card≤2*redundant w+(1+2*redundant w)*(4*T.card) := by
  obtain ⟨A,hA,x,y,hxy,hnum⟩ := unmarked_missing_pairs w F S hs hd
  obtain ⟨T,hT,hw,hcount⟩ := linear_missing_signals w x y A (fun i hi => (hxy i hi).2.2)
  exact ⟨T,hT.trans hA,x,y,fun i hi => hxy i (hT hi),fun i hi j hj _ => hw i hi j hj,by omega⟩

#print axioms linear_packet_selection
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback.ForestOrder
