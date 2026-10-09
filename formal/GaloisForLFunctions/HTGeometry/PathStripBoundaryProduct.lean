import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Lifting

open scoped Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {X : Type*} [TopologicalSpace X]

/-- The bottom or top edge chain of the first i cells. -/
def pathRowPrefix (b : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1))) :
    ∀ i, Path (b 0) (b i)
  | 0 => Path.refl (b 0)
  | i + 1 => (pathRowPrefix b h i).trans (h i)

@[simp] theorem pathRowPrefix_zero (b : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1))) :
    pathRowPrefix b h 0 = Path.refl (b 0) := rfl

@[simp] theorem pathRowPrefix_succ (b : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1))) (i : ℕ) :
    pathRowPrefix b h (i + 1) = (pathRowPrefix b h i).trans (h i) := rfl

/-- Positive boundary of one strip cell, in bottom-right-top-left traversal order. -/
def pathStripCell (b t : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1)))
    (k : ∀ i, Path (t i) (t (i + 1))) (v : ∀ i, Path (b i) (t i)) (i : ℕ) :
    Path (b i) (b i) :=
  ((h i).trans (v (i + 1))).trans ((k i).symm.trans (v i).symm)

/-- Transport a cell boundary to the common lower-left basepoint. -/
def basedPathStripCell (b t : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1)))
    (k : ∀ i, Path (t i) (t (i + 1))) (v : ∀ i, Path (b i) (t i)) (i : ℕ) :
    Path (b 0) (b 0) :=
  ((pathRowPrefix b h i).trans (pathStripCell b t h k v i)).trans (pathRowPrefix b h i).symm

/-- Outer boundary of the first i cells. -/
def pathStripBoundary (b t : ℕ → X) (h : ∀ i, Path (b i) (b (i + 1)))
    (k : ∀ i, Path (t i) (t (i + 1))) (v : ∀ i, Path (b i) (t i)) (i : ℕ) :
    Path (b 0) (b 0) :=
  (((pathRowPrefix b h i).trans (v i)).trans (pathRowPrefix t k i).symm).trans (v 0).symm

/-- Shared boundary edges cancel with the exact fundamental-group multiplication order. -/
theorem pathStripBoundary_succ_class (b t : ℕ → X)
    (h : ∀ i, Path (b i) (b (i + 1))) (k : ∀ i, Path (t i) (t (i + 1)))
    (v : ∀ i, Path (b i) (t i)) (i : ℕ) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v (i + 1))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v i)) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedPathStripCell b t h k v i)) := by
  change Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v (i + 1)) =
    (Path.Homotopic.Quotient.mk (basedPathStripCell b t h k v i)).trans
      (Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v i))
  simp only [pathStripBoundary, basedPathStripCell, pathStripCell, pathRowPrefix_succ,
    Path.trans_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (pathRowPrefix b h i)).symm
    (Path.Homotopic.Quotient.mk (pathRowPrefix b h i)), Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (v i)).symm (Path.Homotopic.Quotient.mk (v i)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The empty strip has trivial boundary class. -/
theorem pathStripBoundary_zero_class (b t : ℕ → X)
    (h : ∀ i, Path (b i) (b (i + 1))) (k : ∀ i, Path (t i) (t (i + 1)))
    (v : ∀ i, Path (b i) (t i)) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v 0)) = 1 := by
  change Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v 0) =
    Path.Homotopic.Quotient.refl (b 0)
  simp only [pathStripBoundary, pathRowPrefix_zero, Path.refl_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm]

/-- A row's boundary class is the ascending product of its based cell classes. -/
theorem pathStripBoundary_class_eq_prod (b t : ℕ → X)
    (h : ∀ i, Path (b i) (b (i + 1))) (k : ∀ i, Path (t i) (t (i + 1)))
    (v : ∀ i, Path (b i) (t i)) (m : ℕ) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathStripBoundary b t h k v m)) =
      ((List.range m).map (fun i =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedPathStripCell b t h k v i)))).prod := by
  induction m with
  | zero => simpa only [List.range_zero, List.map_nil, List.prod_nil] using
      pathStripBoundary_zero_class b t h k v
  | succ m ih =>
      rw [pathStripBoundary_succ_class, ih, List.range_succ, List.map_append,
        List.prod_append, List.map_singleton, List.prod_singleton]

/-- The same ascending product is the actual covering monodromy of the outer boundary. -/
theorem monodromy_pathStripBoundary {E : Type*} [TopologicalSpace E] {p : E → X}
    (cov : IsCoveringMap p) (b t : ℕ → X)
    (h : ∀ i, Path (b i) (b (i + 1))) (k : ∀ i, Path (t i) (t (i + 1)))
    (v : ∀ i, Path (b i) (t i)) (m : ℕ) :
    cov.monodromyPerm (b 0)
      (FundamentalGroup.fromPath (.mk (pathStripBoundary b t h k v m))) =
      ((List.range m).map (fun i =>
        cov.monodromyPerm (b 0)
          (FundamentalGroup.fromPath (.mk (basedPathStripCell b t h k v i))))).prod := by
  induction m with
  | zero =>
      rw [pathStripBoundary_zero_class, map_one]
      simp only [List.range_zero, List.map_nil, List.prod_nil]
  | succ m ih =>
      rw [pathStripBoundary_succ_class, map_mul, ih, List.range_succ, List.map_append,
        List.prod_append, List.map_singleton, List.prod_singleton]

end
end GaloisForLFunctions.HTGeometry
