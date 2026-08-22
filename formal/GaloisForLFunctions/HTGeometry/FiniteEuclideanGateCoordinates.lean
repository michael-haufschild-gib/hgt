import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Flattened finite Euclidean gate coordinates

Finite families of finite Euclidean gate coordinates are reindexed to one
literal Euclidean space.  The maps below are continuous linear and explicitly
surjective, so analytic rank witnesses can be moved between the product-shaped
gate source and a `EuclideanSpace ℝ (Fin m)` source without any norm tuning.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unflatten one Euclidean coordinate vector into one finite Euclidean
coordinate block for every gate. -/
def finiteEuclideanGateUnflatten (R : ℕ) (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ (Fin R × ι) →L[ℝ]
      (Fin R → EuclideanSpace ℝ ι) :=
  ContinuousLinearMap.pi fun r =>
    (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin R × ι => ℝ) (r, i)).comp
          (EuclideanSpace.equiv (Fin R × ι) ℝ).toContinuousLinearMap)

/-- Flatten a finite family of Euclidean gate coordinates into one literal
Euclidean vector. -/
def finiteEuclideanGateFlatten (R : ℕ) (ι : Type*) [Fintype ι] :
    (Fin R → EuclideanSpace ℝ ι) →L[ℝ]
      EuclideanSpace ℝ (Fin R × ι) :=
  (EuclideanSpace.equiv (Fin R × ι) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ri =>
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ι => ℝ) ri.2).comp
        ((EuclideanSpace.equiv ι ℝ).toContinuousLinearMap.comp
          (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin R => EuclideanSpace ℝ ι) ri.1)))

/-- Flattening followed by unflattening is the identity on every finite gate
coordinate assignment. -/
theorem finiteEuclideanGateUnflatten_flatten
    (R : ℕ) (ι : Type*) [Fintype ι]
    (w : Fin R → EuclideanSpace ℝ ι) :
    finiteEuclideanGateUnflatten R ι (finiteEuclideanGateFlatten R ι w) = w := by
  funext r
  apply (EuclideanSpace.equiv ι ℝ).injective
  ext i
  simp [finiteEuclideanGateUnflatten, finiteEuclideanGateFlatten]

/-- Reindex an arbitrary finite Euclidean source by its cardinality. -/
def euclideanReindex (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ (Fin (Fintype.card ι)) →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (Fintype.card ι) => ℝ) (Fintype.equivFin ι i)).comp
        (EuclideanSpace.equiv (Fin (Fintype.card ι)) ℝ).toContinuousLinearMap)

/-- Finite Euclidean reindexing is surjective. -/
theorem euclideanReindex_surjective
    (ι : Type*) [Fintype ι] : Function.Surjective (euclideanReindex ι) := by
  intro y
  let x : EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    (EuclideanSpace.equiv (Fin (Fintype.card ι)) ℝ).symm
      (fun j => (EuclideanSpace.equiv ι ℝ y) ((Fintype.equivFin ι).symm j))
  refine ⟨x, ?_⟩
  apply (EuclideanSpace.equiv ι ℝ).injective
  ext i
  simp [x, euclideanReindex]

/-- Unflattening is surjective, with the displayed flattening as a section. -/
theorem finiteEuclideanGateUnflatten_surjective
    (R : ℕ) (ι : Type*) [Fintype ι] :
    Function.Surjective (finiteEuclideanGateUnflatten R ι) := by
  intro w
  exact ⟨finiteEuclideanGateFlatten R ι w,
    finiteEuclideanGateUnflatten_flatten R ι w⟩

end

end GaloisForLFunctions.HTGeometry
