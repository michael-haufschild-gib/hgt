import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.ThreeSenders
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Selecting simultaneous signal tests from a circuit's missing pairs -/
open Finset
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
variable {J V : Type*} [DecidableEq J] [DecidableEq V]

/-- Two missing signals conflict when each source enters the other cone. -/
def conflicting (w : List (V×V)) (x y : J→V) (i j : J) : Prop :=
  x i∈inputs w (y j) ∧ x j∈inputs w (y i)

private theorem maximum_family (A : Finset J) (R : J→J→Prop) :
    ∃ S⊆A, (∀ i∈S, ∀ j∈S, i≠j → ¬R i j) ∧
      ∀ T⊆A, (∀ i∈T, ∀ j∈T, i≠j → ¬R i j) → T.card≤S.card := by
  classical
  let F := A.powerset.filter fun T => ∀ i∈T, ∀ j∈T, i≠j → ¬R i j
  have hn : F.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp⟩⟩
  obtain ⟨S,hS,he⟩ := exists_mem_eq_sup' hn card
  have hh := mem_filter.mp hS
  refine ⟨S,mem_powerset.mp hh.1,hh.2,fun T hT h => ?_⟩
  exact (le_sup' card (mem_filter.mpr ⟨mem_powerset.mpr hT,h⟩ : T∈F)).trans_eq he

/-- In a triangle-free class an independent set of maximum size m covers
all vertices by its closed neighborhoods, each of size at most m+1. -/
private theorem independent_square (A : Finset J) (R : J→J→Prop) (hs : Symmetric R)
    (ht : ∀ i∈A, ∀ j∈A, ∀ k∈A, R i j → R i k → j≠k → ¬R j k) :
    ∃ S⊆A, (∀ i∈S, ∀ j∈S, i≠j → ¬R i j) ∧ A.card≤S.card*(S.card+1) := by
  classical
  obtain ⟨S,hS,hi,hmax⟩ := maximum_family A R
  let B (i : J) := A.filter (R i)
  have hsize (i : J) (h : i∈S) : (B i).card≤S.card :=
    hmax _ (filter_subset ..) fun j hj k hk hne => ht i (hS h) j (mem_filter.mp hj).1
      k (mem_filter.mp hk).1 (mem_filter.mp hj).2 (mem_filter.mp hk).2 hne
  have cover : A⊆S.biUnion (fun i => insert i (B i)) := by
    intro i h
    by_cases hin : i∈S
    · exact mem_biUnion.mpr ⟨i,hin,mem_insert_self ..⟩
    by_contra hn
    have hb (j : J) (hj : j∈S) : ¬R j i := fun hh =>
      hn (mem_biUnion.mpr ⟨j,hj,mem_insert_of_mem (mem_filter.mpr ⟨h,hh⟩)⟩)
    have hh := hmax (insert i S) (insert_subset h hS) (by
      intro j hj k hk hne
      rcases mem_insert.mp hj with rfl|hj <;> rcases mem_insert.mp hk with rfl|hk
      · exact (hne rfl).elim
      · exact fun h => hb k hk (hs h)
      · exact hb j hj
      · exact hi j hj k hk hne)
    rw [card_insert_of_notMem hin] at hh
    omega
  refine ⟨S,hS,hi,(card_le_card cover).trans (card_biUnion_le.trans ?_)⟩
  calc
    (∑ i ∈ S, (insert i (B i)).card) ≤ ∑ _i ∈ S, S.card+1 :=
      sum_le_sum fun i hi => (card_insert_le ..).trans (Nat.succ_le_succ (hsize i hi))
    _ = _ := by rw [sum_const,nsmul_eq_mul]

/-- Among any finite family of L missing signals one can choose m tests
with no mutual cross-connections, where L ≤ (2r+1)m(m+1) and r is the
actual number of nonmerging calls. Input or output labels may repeat. -/
theorem independent_missing_signals [Fintype V] (w : List (V×V)) (x y : J→V) (A : Finset J)
    (hm : ∀ i∈A, x i∉inputs w (y i)) :
    ∃ S⊆A, (∀ i∈S, ∀ j∈S, i≠j → ¬conflicting w x y i j) ∧
      A.card≤(1+2*redundant w)*(S.card*(S.card+1)) := by
  classical
  let R := conflicting w x y
  let P (i : J) := profile w (y i)
  let F (p : Finset ℕ) := A.filter fun i => P i=p
  obtain ⟨S,hS,hi,hmax⟩ := maximum_family A R
  have hsize (p : Finset ℕ) : (F p).card≤S.card*(S.card+1) := by
    have ht (i) (hi : i∈F p) (j) (hj : j∈F p) (k) (hk : k∈F p) (hij : R i j) (hik : R i k)
        (_ : j≠k) (hjk : R j k) : False := by
      let a : Fin 3→J := ![i,j,k]
      have hmem (l : Fin 3) : a l∈F p := by fin_cases l <;> first | exact hi | exact hj | exact hk
      apply three_missing_pairs_exclude_mutual_cross w (x ∘ a) (y ∘ a)
        (fun l => hm _ (mem_filter.mp (hmem l)).1)
        (fun l => (mem_filter.mp (hmem l)).2.trans (mem_filter.mp (hmem 0)).2.symm)
      intro l m hne
      fin_cases l <;> fin_cases m <;> first | exact (hne rfl).elim | exact hij.1 | exact hij.2 |
        exact hik.1 | exact hik.2 | exact hjk.1 | exact hjk.2
    obtain ⟨T,hT,ht',hcard⟩ := independent_square (F p) R (fun _ _ h => And.symm h) ht
    have hh := hmax T (hT.trans (filter_subset ..)) ht'
    exact hcard.trans (Nat.mul_le_mul hh (Nat.succ_le_succ hh))
  have cover : A ⊆ (A.image P).biUnion F :=
    fun i h => mem_biUnion.mpr ⟨P i,mem_image_of_mem _ h,mem_filter.mpr ⟨h,rfl⟩⟩
  have hsub : A.image P ⊆ univ.image (profile w) := by
    rintro _ h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact mem_image_of_mem _ (mem_univ (y i))
  refine ⟨S,hS,hi,(card_le_card cover).trans (card_biUnion_le.trans ?_)⟩
  calc
    (∑ p ∈ A.image P, (F p).card) ≤ ∑ _p ∈ A.image P, S.card*(S.card+1) := sum_le_sum fun p _ => hsize p
    _ = (A.image P).card*(S.card*(S.card+1)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ ((card_le_card hsub).trans (number_of_profiles w))

#print axioms independent_missing_signals
end GaloisForLFunctions.HTGeometry.RepeatedGates.Temporal.Feedback
