import GaloisForLFunctions.HTGeometry.Lattices.IntegralRootCartanGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The induced leaf inequality for integral Cartan graphs

For every nonempty set of simple roots there is a vertex whose full degree
plus its degree inside the set is at most three. Weight the set by two and
its exterior neighbors by one. Strict positivity of the Cartan form forces
a deficit inside the set. Singletons exclude degree four, induced subsets
exclude cycles, and paths exclude two branching endpoints.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {J : Type*} [Fintype J] (Q : Form J) (hQ : Q.PosDef)

def neighbors (i : Vertex Q hQ) : Finset (Vertex Q hQ) := by
  classical
  exact univ.filter ((cartanGraph Q hQ).Adj i)

theorem mem_neighbors (i j : Vertex Q hQ) : j∈neighbors Q hQ i ↔ (cartanGraph Q hQ).Adj i j := by
  classical
  simp [neighbors]

def degreeIn (S : Finset (Vertex Q hQ)) (i : Vertex Q hQ) : ℕ := by
  classical
  exact ((neighbors Q hQ i).filter (·∈S)).card

private theorem row_energy (a : Vertex Q hQ → ℤ) (i : Vertex Q hQ) :
    ∑ j, a i*a j*cartanEntry Q hQ i j = a i*(2*a i-∑ j ∈ neighbors Q hQ i, a j) := by
  classical
  simp only [cartanEntry,mul_sub,sum_sub_distrib,mul_ite,mul_zero,mul_one,neighbors,sum_filter,mul_sum]
  rw [sum_ite_eq,if_pos (mem_univ i)]
  ring

/-- Every nonnegative nonzero weight has a positive vertex where the
neighbor weight is strictly less than twice the vertex weight. -/
theorem weighted_leaf (a : Vertex Q hQ → ℤ) (h : ∀ i, 0≤a i) (ha : a≠0) :
    ∃ i, 0<a i ∧ (∑ j ∈ neighbors Q hQ i, a j)<2*a i := by
  classical
  have pos := cartan_energy_pos Q hQ a ha
  simp_rw [row_energy] at pos
  by_contra! none
  apply (not_le_of_gt pos)
  apply sum_nonpos
  intro i _
  rcases eq_or_lt_of_le (h i) with hz|hp
  · rw [← hz,zero_mul]
  · exact mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (none i hp))

private def indicator (S : Finset (Vertex Q hQ)) (i : Vertex Q hQ) : ℤ := by
  classical
  exact if i∈S then 1 else 0

private theorem sum_indicator (S : Finset (Vertex Q hQ)) (i : Vertex Q hQ) :
    ∑ j ∈ neighbors Q hQ i, indicator Q hQ S j=(degreeIn Q hQ S i:ℤ) := by
  classical
  have eq : (neighbors Q hQ i).filter (·∈S)=neighbors Q hQ i ∩ S := by
    ext j
    simp
  simp [indicator,degreeIn,eq]

/-- Every nonempty set contains a vertex with combined full and induced
degree at most three. This uses only integral test weights. -/
theorem induced_leaf (S : Finset (Vertex Q hQ)) (hS : S.Nonempty) :
    ∃ i∈S, (neighbors Q hQ i).card+degreeIn Q hQ S i≤3 := by
  classical
  let B := univ.filter fun v => v∈S ∨ ((neighbors Q hQ v).filter (·∈S)).Nonempty
  have inside {i} (hi : i∈S) : i∈B := mem_filter.mpr ⟨mem_univ _,Or.inl hi⟩
  have allNear {i} (hi : i∈S) : neighbors Q hQ i ⊆ B := by
    intro j hj
    have rev := ((mem_neighbors Q hQ i j).mp hj).symm
    exact mem_filter.mpr ⟨mem_univ _,Or.inr ⟨i,mem_filter.mpr ⟨(mem_neighbors Q hQ _ _).mpr rev,hi⟩⟩⟩
  let a := fun i => indicator Q hQ S i+indicator Q hQ B i
  have nonneg (i) : 0≤a i := by simp only [a,indicator]; split_ifs <;> norm_num
  have ha : a≠0 := by
    obtain ⟨i,hi⟩ := hS
    intro he
    have hz := congrFun he i
    simp [a,indicator,hi,inside hi] at hz
  obtain ⟨i,hi,deficit⟩ := weighted_leaf Q hQ a nonneg ha
  have sum : ∑ j ∈ neighbors Q hQ i, a j = (degreeIn Q hQ S i:ℤ)+degreeIn Q hQ B i := by
    simp only [a,sum_add_distrib,sum_indicator]
  rw [sum] at deficit
  by_cases hs : i∈S
  · have e : degreeIn Q hQ B i=(neighbors Q hQ i).card := by
      unfold degreeIn
      rw [filter_true_of_mem (fun j hj => allNear hs hj)]
    simp only [a,indicator,if_pos hs,if_pos (inside hs),e] at deficit
    exact ⟨i,hs,by omega⟩
  · have hb : i∈B := by
      by_contra hn
      simp [a,indicator,hs,hn] at hi
    obtain ⟨j,hj⟩ := ((mem_filter.mp hb).2).resolve_left hs
    obtain ⟨edge,mem⟩ := mem_filter.mp hj
    have hp : 0<degreeIn Q hQ S i := card_pos.mpr ⟨j,hj⟩
    have hq : 0<degreeIn Q hQ B i := card_pos.mpr ⟨j,mem_filter.mpr ⟨edge,inside mem⟩⟩
    simp only [a,indicator,if_neg hs,if_pos hb] at deficit
    omega

theorem degree_le_three (i : Vertex Q hQ) : (neighbors Q hQ i).card≤3 := by
  classical
  obtain ⟨j,h,he⟩ := induced_leaf Q hQ {i} (singleton_nonempty _)
  obtain rfl := mem_singleton.mp h
  omega

/-- Every nonempty induced subgraph has a vertex of degree zero or one. -/
theorem induced_degree_le_one (S : Finset (Vertex Q hQ)) (hS : S.Nonempty) :
    ∃ i∈S, degreeIn Q hQ S i≤1 := by
  obtain ⟨i,hi,he⟩ := induced_leaf Q hQ S hS
  have le : degreeIn Q hQ S i≤(neighbors Q hQ i).card := card_filter_le _ _
  exact ⟨i,hi,by omega⟩

/-- No finite spine can have trivalent endpoints and two internal neighbors
at every other vertex. This rules out two branching vertices on one path. -/
theorem no_branch_spine (S : Finset (Vertex Q hQ)) (hS : S.Nonempty) :
    ¬∀ i∈S, 2≤degreeIn Q hQ S i ∨ (1≤degreeIn Q hQ S i ∧ 3≤(neighbors Q hQ i).card) := by
  intro h
  obtain ⟨i,hi,he⟩ := induced_leaf Q hQ S hS
  have le : degreeIn Q hQ S i≤(neighbors Q hQ i).card := card_filter_le _ _
  rcases h i hi with inn|⟨inn,deg⟩ <;> omega

/-- Every injective graph copy inherits a vertex of degree at most one,
with a simultaneous bound involving its degree in the full Cartan graph. -/
theorem copy_leaf {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (f : SimpleGraph.Copy H (cartanGraph Q hQ)) :
    ∃ i, H.degree i≤1 ∧ H.degree i+(neighbors Q hQ (f i)).card≤3 := by
  classical
  let S := univ.image f
  have mem (i : V) : f i∈S := mem_image_of_mem _ (mem_univ i)
  obtain ⟨v,hv,h⟩ := induced_leaf Q hQ S ⟨f (Classical.arbitrary V),mem _⟩
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  let N := (neighbors Q hQ (f i)).filter (·∈S)
  let F (j : H.neighborSet i) : N :=
    ⟨f j.val,mem_filter.mpr ⟨(mem_neighbors Q hQ _ _).mpr (f.toHom.map_rel' j.property),mem _⟩⟩
  have inj : Function.Injective F := fun _ _ he => Subtype.ext (f.injective (congrArg Subtype.val he))
  have le : H.degree i≤degreeIn Q hQ S (f i) := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe,N,degreeIn] using
      Fintype.card_le_of_injective F inj
  have ambient : degreeIn Q hQ S (f i)≤(neighbors Q hQ (f i)).card := card_filter_le _ _
  exact ⟨i,by omega,by omega⟩

/-- No cycle embeds in the simple-root graph; every component is a tree. -/
theorem cartan_acyclic : (cartanGraph Q hQ).IsAcyclic := by
  classical
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  rintro n hn ⟨f⟩
  obtain ⟨k,rfl⟩ : ∃ k, n=k+3 := ⟨n-3,by omega⟩
  obtain ⟨i,small,_⟩ := copy_leaf Q hQ _ f
  rw [SimpleGraph.cycleGraph_degree_three_le] at small
  omega

private theorem lower_degree {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {u v w : V} (a : H.Adj u v) (b : H.Adj u w) (ne : v≠w) : 2≤H.degree u := by
  classical
  have h : ({v,w} : Finset V) ⊆ H.neighborFinset u := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact (H.mem_neighborFinset _ _).mpr a
    · obtain rfl := mem_singleton.mp hz
      exact (H.mem_neighborFinset _ _).mpr b
  have c := card_le_card h
  simpa only [card_pair ne,SimpleGraph.degree] using c

/-- A nontrivial path cannot join two trivalent vertices of the Cartan graph. -/
theorem trivalent_unique_in_component (u v : Vertex Q hQ) (path : (cartanGraph Q hQ).Reachable u v)
    (hu : 3≤(neighbors Q hQ u).card) (hv : 3≤(neighbors Q hQ v).card) : u=v := by
  classical
  by_contra ne
  obtain ⟨w,hw⟩ := path.exists_isPath
  have len : 0<w.length := by
    by_contra! he
    exact ne (SimpleGraph.Walk.eq_of_length_eq_zero (p:=w) (by omega))
  let f := hw.pathGraphCopy
  have atIdx (k : Fin (w.length+1)) : f k=w.getVert k.val := by
    change w.support[k.val]'(by simpa using k.isLt)=_
    exact w.support_getElem_eq_getVert _
  obtain ⟨i,low,bound⟩ := copy_leaf Q hQ (SimpleGraph.pathGraph _) f
  by_cases left : i.val=0
  · have edge : (SimpleGraph.pathGraph (w.length+1)).Adj i ⟨1,by omega⟩ :=
      SimpleGraph.pathGraph_adj.mpr (Or.inl (by simp [left]))
    have pos : 0<(SimpleGraph.pathGraph _).degree i := Finset.card_pos.mpr
      ⟨_,((SimpleGraph.pathGraph _).mem_neighborFinset _ _).mpr edge⟩
    rw [atIdx,left,w.getVert_zero] at bound
    omega
  · by_cases right : i.val=w.length
    · have edge : (SimpleGraph.pathGraph (w.length+1)).Adj i ⟨w.length-1,by omega⟩ :=
        SimpleGraph.pathGraph_adj.mpr (Or.inr (by dsimp; omega))
      have pos : 0<(SimpleGraph.pathGraph _).degree i := Finset.card_pos.mpr
        ⟨_,((SimpleGraph.pathGraph _).mem_neighborFinset _ _).mpr edge⟩
      rw [atIdx,right,w.getVert_length] at bound
      omega
    · let j : Fin (w.length+1) := ⟨i.val-1,by omega⟩
      let k : Fin (w.length+1) := ⟨i.val+1,by omega⟩
      have a : (SimpleGraph.pathGraph _).Adj i j := SimpleGraph.pathGraph_adj.mpr (Or.inr (by dsimp [j]; omega))
      have b : (SimpleGraph.pathGraph _).Adj i k := SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
      have d := lower_degree _ a b (fun eq => by have e := congrArg Fin.val eq; dsimp [j,k] at e; omega)
      omega

#print axioms copy_leaf
#print axioms cartan_acyclic
#print axioms trivalent_unique_in_component
#print axioms weighted_leaf
#print axioms induced_leaf
#print axioms degree_le_three
#print axioms induced_degree_le_one
#print axioms no_branch_spine
end GaloisForLFunctions.HTGeometry.IntegralRootShell
