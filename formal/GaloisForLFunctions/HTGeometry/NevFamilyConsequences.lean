import GaloisForLFunctions.HTGeometry.NevExtremalFamily

/-!
# Consequences for the constructed family

The interface's downstream theorems were proved for an arbitrary `ClassicalNevanlinnaExtremalFamily`.
Now that one exists for every indeterminate moment sequence, they become unconditional statements
about the sequence itself: the parameter of a leaf is recovered exactly as a projective coordinate on
its carrier, and the barycentres of the leaves against parameter laws form a closed embedded family of
representing measures.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Exact label recovery.**  Pushing a leaf forward along the projective label of the constructed
matrix returns the point mass at its own parameter. -/
theorem nevLeaf_map_projectiveLabel (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (t : OnePoint ℝ) :
    Measure.map (nevMatrixDataInf h h0b).projectiveLabel (nevLeaf h h0b h0 t : Measure ℝ)
      = Measure.dirac t :=
  (nevExtremalFamily h h0b h0).map_projectiveLabel_leaf t

/-- The barycentre of the constructed leaves against a law on the parameter space. -/
noncomputable def nevBarycenter (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (eta : ProbabilityMeasure (OnePoint ℝ)) : ProbabilityMeasure ℝ :=
  (nevExtremalFamily h h0b h0).toBoundaryFamily.barycenter eta

/-- **Every barycentre represents the moment sequence.**  So the constructed family generates a whole
family of solutions to the moment problem, one for each law on `ℝ ∪ {∞}`. -/
theorem nevBarycenter_hasHamburgerMoments (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (eta : ProbabilityMeasure (OnePoint ℝ)) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (nevBarycenter h h0b h0 eta : Measure ℝ) :=
  (nevExtremalFamily h h0b h0).toBoundaryFamily.barycenter_hasHamburgerMoments eta

/-- **The barycentre map is a closed embedding.**  The solutions obtained this way form a closed
copy of the space of parameter laws — the simplex structure, for a constructed family. -/
theorem nevBarycenter_isClosedEmbedding (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Topology.IsClosedEmbedding (nevBarycenter h h0b h0) :=
  (nevExtremalFamily h h0b h0).toBoundaryFamily.barycenter_isClosedEmbedding

/-- **The leaves are pairwise distinct.**  Distinct parameters give distinct leaves, since their
projective-label pushforwards are distinct point masses. -/
theorem nevLeaf_injective (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Function.Injective (nevLeaf h h0b h0) := by
  intro t₁ t₂ hEq
  have h1 := nevLeaf_map_projectiveLabel h h0b h0 t₁
  have h2 := nevLeaf_map_projectiveLabel h h0b h0 t₂
  rw [hEq, h2] at h1
  have := congrArg (fun μ => μ {t₁}) h1
  simp only [Measure.dirac_apply' _ (measurableSet_singleton t₁)] at this
  by_contra hne
  rw [Set.indicator_of_mem rfl, Set.indicator_of_notMem (fun hc => hne (by simpa using hc.symm))]
    at this
  simp at this

end HTGeometry
