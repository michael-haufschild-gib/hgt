import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Matrix Set

example (X : Type) [TopologicalSpace X] (n : ℕ) (s : Set X) (A : X → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, ContinuousOn (fun x => A x i j) s) : ContinuousOn (fun x => (A x).det) s := by
  simp only [Matrix.det_apply']
  refine continuousOn_finset_sum _ fun σ _ => ?_
  refine ContinuousOn.mul continuousOn_const ?_
  exact continuousOn_finset_prod _ fun i _ => h _ _

example (X ι : Type) [TopologicalSpace X] (s : Set X) (t : Finset ι) (ht : t.Nonempty)
    (f : ι → X → ℝ) (hf : ∀ i ∈ t, ContinuousOn (f i) s) :
    ContinuousOn (fun x => t.sup' ht fun i => f i x) s := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton i =>
      simp only [Finset.sup'_singleton]
      exact hf i (by simp)
  | cons i t hi ht ih =>
      simp only [Finset.sup'_cons]
      exact ContinuousOn.sup' (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))
