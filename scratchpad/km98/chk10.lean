import Mathlib.Topology.Order.Lattice
open Set

example (X ι : Type) [TopologicalSpace X] (s : Set X) (t : Finset ι) (ht : t.Nonempty)
    (f : ι → X → ℝ) (hf : ∀ i ∈ t, ContinuousOn (f i) s) :
    ContinuousOn (fun x => t.sup' ht fun i => f i x) s := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton i =>
      simp only [Finset.sup'_singleton]
      exact hf i (by simp)
  | cons i t hi ht ih =>
      have hrw : ∀ x : X, (Finset.cons i t hi).sup' (ht.cons i) (fun j => f j x)
          = f i x ⊔ t.sup' ht (fun j => f j x) := by
        intro x
        exact Finset.sup'_cons ht
      simp only [hrw]
      exact ContinuousOn.sup' (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))
