import GaloisForLFunctions.HTGeometry.HaferkampBlockPauliTransport

/-!
# Compiling aligned edge-list gate words to finite architecture parameters

The BLC construction naturally returns a list of local gates.  This module
converts any aligned list to the `Fin edges.length → SU(4)` parameter family
used by `TwoQubitArchitecture`, preserving the exact reverse-chronological
contraction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- View an aligned list as a finite-indexed parameter family. -/
def edgeListGatesAsFn {α : Type*} (values : List α) (n : ℕ)
    (hvalues : values.length = n) : Fin n → α :=
  fun i => values.get (Fin.cast hvalues.symm i)

/-- Reifying an aligned gate list as a finite family and listing it again is
the identity operation. -/
theorem ofFn_edgeListGatesAsFn {α : Type*} (values : List α) (n : ℕ)
    (hvalues : values.length = n) :
    List.ofFn (edgeListGatesAsFn values n hvalues) = values := by
  apply List.ext_get
  · simpa using hvalues.symm
  · intro k hk₁ hk₂
    rw [List.get_ofFn]
    simp [edgeListGatesAsFn]

/-- Listing the pointwise interpretation of an aligned finite gate family is
the literal `zipWith` interpretation of its two source lists. -/
theorem ofFn_zipWith_edgeListGatesAsFn
    {α β γ : Type*} (lift : α → β → γ)
    (edges : List α) (values : List β)
    (hvalues : values.length = edges.length) :
    List.ofFn (fun r : Fin edges.length =>
      lift (edges.get r)
        (edgeListGatesAsFn values edges.length hvalues r)) =
      List.zipWith lift edges values := by
  apply List.ext_get
  · rw [List.length_ofFn, List.length_zipWith, hvalues, min_self]
  · intro k hk₁ hk₂
    rw [List.get_ofFn]
    change lift (edges.get _) (values.get _) =
      (List.zipWith lift edges values)[k]
    rw [List.getElem_zipWith]
    rfl

/-- The full edge-list gate word compiled to `TwoQubitArchitecture` parameters
has exactly the same contraction as its list-level BLC semantics. -/
theorem edgeListBlockContraction_eq_ofEdgeList_contraction
    {n : ℕ} (edges : List (Fin n × Fin n))
    (hdistinct : ∀ edge ∈ edges, edge.1 ≠ edge.2)
    (values : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ))
    (hvalues : values.length = edges.length) :
    edgeListBlockContraction edges values =
      (TwoQubitArchitecture.ofEdgeList edges hdistinct).contraction
        (edgeListGatesAsFn values edges.length hvalues) := by
  rw [TwoQubitArchitecture.ofEdgeList_contraction]
  unfold edgeListBlockContraction haferkampGateWordReverseProduct
  have htotalWord :
      List.ofFn (fun r : Fin edges.length =>
        totalTwoQubitLift (edges.get r)
          (edgeListGatesAsFn values edges.length hvalues r)) =
        List.zipWith totalTwoQubitLift edges values :=
    ofFn_zipWith_edgeListGatesAsFn totalTwoQubitLift edges values hvalues
  rw [← htotalWord]
  congr 1
  apply congrArg List.reverse
  apply List.ext_get
  · simp
  · intro k hk₁ hk₂
    rw [List.get_ofFn, List.get_ofFn]
    have hk : k < edges.length := by simpa using hk₁
    let i : Fin edges.length := ⟨k, hk⟩
    have hi := totalTwoQubitLift_eq_twoQubitLift (edges.get i)
      (hdistinct _ (List.get_mem _ _))
      (edgeListGatesAsFn values edges.length hvalues i)
    simpa [i] using hi

namespace BackwardsLightCone

/-- The list-level BLC transport compiles to the native finite-indexed
architecture contraction without changing its Pauli action. -/
theorem exists_architecture_gate_transport
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    (cone : BackwardsLightCone n edges root) (hn : 1 < n)
    (P : Fin n → Option (Fin 3)) (hP : ∃ q, P q ≠ none) :
    ∃ gates : Fin edges.length → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
      ∃ R : Fin n → Option (Fin 3), ∃ c : ℂ, c ≠ 0 ∧
        (((TwoQubitArchitecture.ofEdgeList edges cone.edge_distinct).contraction gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose
            ((TwoQubitArchitecture.ofEdgeList edges cone.edge_distinct).contraction gates :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          c • finitePauliMatrix R) ∧ R root = some 2 := by
  obtain ⟨values, hvalues, R, c, hc, htransport, hroot⟩ :=
    cone.exists_full_block_transport hn P hP
  let gates := edgeListGatesAsFn values edges.length hvalues
  refine ⟨gates, R, c, hc, ?_, hroot⟩
  rw [← edgeListBlockContraction_eq_ofEdgeList_contraction
    edges cone.edge_distinct values hvalues]
  exact htransport

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
