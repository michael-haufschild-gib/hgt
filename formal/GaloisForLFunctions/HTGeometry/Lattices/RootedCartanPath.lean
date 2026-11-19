import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Find

/-!
# Numbering a finite connected graph from a leaf

In a connected graph of maximum degree two, a path starting at a
prescribed leaf and of maximal length contains every vertex. Its
indices give all adjacencies, including the one-vertex case.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.CartanPath
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem only_neighbor {i a b : V} (degree : G.degree i ≤ 1)
    (ha : G.Adj i a) (hb : G.Adj i b) : a=b := by
  classical
  by_contra ne
  have h : ({a,b} : Finset V) ⊆ G.neighborFinset i := by
    intro c hc
    rcases mem_insert.mp hc with rfl|hc
    · exact (G.mem_neighborFinset _ _).mpr ha
    · obtain rfl := mem_singleton.mp hc
      exact (G.mem_neighborFinset _ _).mpr hb
  have le := card_le_card h
  rw [card_pair ne] at le
  exact (by omega : ¬2≤G.degree i) le

private theorem either_neighbor {i a b c : V} (degree : G.degree i ≤ 2)
    (ne : a≠b) (ha : G.Adj i a) (hb : G.Adj i b) (hc : G.Adj i c) : c=a ∨ c=b := by
  classical
  by_contra! h
  have incl : insert c ({a,b} : Finset V) ⊆ G.neighborFinset i := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact (G.mem_neighborFinset _ _).mpr hc
    rcases mem_insert.mp hz with rfl|hz
    · exact (G.mem_neighborFinset _ _).mpr ha
    · obtain rfl := mem_singleton.mp hz
      exact (G.mem_neighborFinset _ _).mpr hb
  have le := card_le_card incl
  rw [card_insert_of_notMem (by simp [h.1,h.2]),card_pair ne] at le
  exact (by omega : ¬2+1≤G.degree i) le

/-- Finite initial segment of an injective walk, with arbitrary values beyond its end. -/
private structure Segment (root : V) (n : ℕ) where
  vertex : ℕ → V
  start : vertex 0=root
  distinct : ∀ i≤n, ∀ j≤n, vertex i=vertex j → i=j
  step : ∀ i<n, G.Adj (vertex i) (vertex (i+1))

private def singleton (root : V) : Segment G root 0 where
  vertex _ := root
  start := rfl
  distinct := by omega
  step := by omega

private def extend {root : V} {n : ℕ} (p : Segment G root n) (z : V)
    (hz : G.Adj (p.vertex n) z) (fresh : ∀ i≤n, p.vertex i≠z) : Segment G root (n+1) where
  vertex i := if i=n+1 then z else p.vertex i
  start := by simpa using p.start
  distinct i hi j hj := by
    by_cases a : i=n+1 <;> by_cases b : j=n+1
    · exact fun _ => a.trans b.symm
    · simp only [a,b,if_true,if_false]
      exact fun he => (fresh j (by omega) he.symm).elim
    · simp only [a,b,if_true,if_false]
      exact fun he => (fresh i (by omega) he).elim
    · simpa only [a,b,if_false] using p.distinct i (by omega) j (by omega)
  step i hi := by
    by_cases last : i=n
    · subst i
      simpa using hz
    · simpa only [if_neg (by omega : i≠n+1),if_neg (by omega : i+1≠n+1)] using p.step i (by omega)

private theorem segment_bound {root : V} {n : ℕ} (p : Segment G root n) : n+1≤Fintype.card V := by
  have inj : Function.Injective (fun i : Fin (n+1) => p.vertex i.val) :=
    fun i j he => Fin.ext (p.distinct _ (by omega) _ (by omega) he)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ inj

private theorem edge_closed {S : Set V} (all : G.Preconnected)
    (closed : ∀ i∈S, ∀ j, G.Adj i j → j∈S) {r : V} (hr : r∈S) : ∀ v, v∈S := by
  intro v
  obtain ⟨w⟩ := all r v
  suffices travel : ∀ {i j}, (p : G.Walk i j) → i∈S → j∈S from travel w hr
  intro i j p
  induction p with
  | nil => exact id
  | cons e _ ih => exact fun h => ih (closed _ h _ e)

/-- Number the vertices from any prescribed vertex of degree at most one.
Consecutive indices describe every edge. -/
theorem rooted_numbering (root : V) (connected : G.Preconnected) (leaf : G.degree root≤1)
    (bound : ∀ i, G.degree i≤2) :
    ∃ n, ∃ e : Fin (n+1) ≃ V, e 0=root ∧
      ∀ i j, G.Adj (e i) (e j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  classical
  let P := fun n => Nonempty (Segment G root n)
  let n := Nat.findGreatest P (Fintype.card V)
  obtain ⟨p⟩ : P n := Nat.findGreatest_spec (Nat.zero_le _) ⟨singleton G root⟩
  have last (v : V) (adj : G.Adj (p.vertex n) v) : ∃ j≤n, p.vertex j=v := by
    by_contra! fresh
    let q := extend G p v adj fresh
    have card := segment_bound G q
    have hn : n+1≤n := Nat.le_findGreatest (by omega : n+1≤Fintype.card V) (show P (n+1) from ⟨q⟩)
    omega
  have earlier (i : ℕ) (hi : i<n) (v : V) (h : G.Adj (p.vertex i) v) :
      v=p.vertex (i+1) ∨ (0<i ∧ v=p.vertex (i-1)) := by
    by_cases zero : i=0
    · subst i
      exact Or.inl (only_neighbor G (by rwa [p.start]) h (p.step _ hi))
    · have pred : i-1+1=i := by omega
      have hp := (p.step (i-1) (by omega)).symm
      rw [pred] at hp
      have ne : p.vertex (i+1)≠p.vertex (i-1) :=
        fun he => (by omega : i+1≠i-1) (p.distinct _ (by omega) _ (by omega) he)
      exact (either_neighbor G (bound _) ne (p.step _ hi) hp h).imp_right (fun e => ⟨by omega,e⟩)
  let f := fun i : Fin (n+1) => p.vertex i.val
  have fi : Function.Injective f := fun i j he => Fin.ext (p.distinct _ (by omega) _ (by omega) he)
  have fs : Function.Surjective f := by
    refine edge_closed G (S:=Set.range f) connected ?_ (r:=root) ⟨0,p.start⟩
    rintro _ ⟨i,rfl⟩ v h
    by_cases top : i.val=n
    · change G.Adj (p.vertex i.val) v at h
      rw [top] at h
      obtain ⟨j,hj,eq⟩ := last v h
      exact ⟨⟨j,by omega⟩,eq⟩
    · rcases earlier i.val (by omega) v h with a|⟨_,a⟩
      · exact ⟨⟨i.val+1,by omega⟩,a.symm⟩
      · exact ⟨⟨i.val-1,by omega⟩,a.symm⟩
  refine ⟨n,Equiv.ofBijective f ⟨fi,fs⟩,p.start,fun i j => ?_⟩
  change G.Adj (p.vertex i.val) (p.vertex j.val) ↔ _
  have forward (i j : Fin (n+1)) (lt : i.val<j.val) (h : G.Adj (p.vertex i.val) (p.vertex j.val)) :
      i.val+1=j.val := by
    rcases earlier i.val (by omega) _ h with he|⟨_,he⟩
    · exact (p.distinct _ (by omega) _ (by omega) he).symm
    · have eq := p.distinct _ (by omega) _ (by omega) he
      omega
  constructor
  · intro h
    rcases lt_trichotomy i.val j.val with lt|eq|gt
    · exact Or.inl (forward i j lt h)
    · exact (G.loopless.irrefl _ (by simpa only [eq] using h)).elim
    · exact Or.inr (forward j i gt h.symm)
  · rintro (a|a)
    · simpa only [a] using p.step i.val (by omega)
    · simpa only [a] using (p.step j.val (by omega)).symm

#print axioms rooted_numbering
end GaloisForLFunctions.HTGeometry.CartanPath
