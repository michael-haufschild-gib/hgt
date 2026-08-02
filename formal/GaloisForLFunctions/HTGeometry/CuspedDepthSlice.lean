import GaloisForLFunctions.HTGeometry.CuspedHorizonHomotopy

/-!
# Slices of the all-depth horizon poset

A vertex of depth beyond the first is comparable to exactly the vertices carried by its own line, so
each fixed slice of positive depth is an antichain: its order complex is a set of points, with no
incidence simplices at all and no homology.  The depth-one slice, by contrast, is the whole building
and already carries the homology of the all-depth complex.

That is the phase law between slices and the whole: the topology sits in the depth-one incidence
skeleton, and the deeper slices are inert, however far the derivative tails run.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

namespace CuspedVertex

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-! ## The classification of the relations of a deep vertex -/

omit [FiniteDimensional K V] in
/-- **A deep vertex is comparable to exactly the vertices of its own cusp.**  Depth beyond the first
is carried by a line, and nothing outside that line is related to it in either direction. -/
theorem comparable_iff_space_eq {v w : CuspedVertex K V} (hv : v.depth ≠ 0) :
    (v ≤ w ∨ w ≤ v) ↔ w.space = v.space := by
  constructor
  · rintro (h | h)
    · exact space_eq_of_le_of_depth_ne_zero hv h
    · by_cases hw : w.depth = 0
      · have h1 : v.depth ≤ w.depth := h.1
        exact absurd (by omega : v.depth = 0) hv
      · exact (space_eq_of_le_of_depth_ne_zero hw h).symm
  · exact fun h => le_total_of_space_eq h.symm

omit [FiniteDimensional K V] in
/-- **Distinct horizons never meet below the first depth.**  Two vertices carried by different
subspaces, one of them deep, are incomparable. -/
theorem not_comparable_of_space_ne {v w : CuspedVertex K V} (hv : v.depth ≠ 0)
    (h : w.space ≠ v.space) : ¬ (v ≤ w ∨ w ≤ v) :=
  fun hc => h ((comparable_iff_space_eq hv).1 hc)

omit [FiniteDimensional K V] in
/-- **A deep vertex is unrelated to every depth-one vertex but its own line.**  In particular it is
unrelated to the vertex of any larger subspace containing that line. -/
theorem not_comparable_depthOne_of_space_ne {v w : CuspedVertex K V} (hv : v.depth ≠ 0)
    (_hw : w.depth = 0) (h : w.space ≠ v.space) : ¬ (v ≤ w ∨ w ≤ v) :=
  not_comparable_of_space_ne hv h

/-! ## Slices of positive depth -/

omit [FiniteDimensional K V] in
/-- **A slice of positive depth is an antichain.**  Comparable vertices of equal positive depth are
carried by the same line, hence equal. -/
theorem eq_of_le_of_depth_eq {d : ℕ} (hd : d ≠ 0) {v w : CuspedVertex K V}
    (hv : v.depth = d) (hw : w.depth = d) (h : v ≤ w) : v = w :=
  ext' (space_eq_of_le_of_depth_ne_zero (by rw [hv]; exact hd) h).symm (by rw [hv, hw])

omit [FiniteDimensional K V] in
/-- The same, as an antichain statement. -/
theorem isAntichain_depthSlice {d : ℕ} (hd : d ≠ 0) :
    IsAntichain (· ≤ ·) {v : CuspedVertex K V | v.depth = d} :=
  fun _ hv _ hw hne h => hne (eq_of_le_of_depth_eq hd hv hw h)

/-- **A slice of positive depth has no incidence simplices above dimension zero.**  Its order
complex is a discrete set of horizon jets. -/
theorem hasDimensionLT_nerve_depthSlice {d : ℕ} (hd : d ≠ 0) :
    SSet.HasDimensionLT
      (nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = d})) 1 := by
  refine hasDimensionLT_nerve_of_chain_bound 1 fun n f hf => ?_
  by_contra hcon
  have hn : (0 : ℕ) < n := by omega
  have hlt : f ⟨0, by omega⟩ < f ⟨1, by omega⟩ := hf (by simp [Fin.lt_def])
  have hle : ((f ⟨0, by omega⟩ : {v : CuspedVertex K V // v.depth = d}) : CuspedVertex K V)
      ≤ (f ⟨1, by omega⟩ : CuspedVertex K V) := le_of_lt hlt
  exact absurd (Subtype.ext (eq_of_le_of_depth_eq hd (f ⟨0, by omega⟩).2 (f ⟨1, by omega⟩).2 hle))
    (ne_of_lt hlt)

/-- **A slice of positive depth carries no homology.**  The derivative tails of one depth are
mutually invisible, so nothing above degree zero survives. -/
theorem isZero_homology_nerve_depthSlice {d : ℕ} (hd : d ≠ 0) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero
      ((nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = d})).homology R n) :=
  haveI := hasDimensionLT_nerve_depthSlice (K := K) (V := V) hd
  isZero_homology_of_hasDimensionLT _ 1 R n hn

/-! ## The depth-one slice -/

/-- **The depth-one slice is the building.**  A vertex of depth zero is a nonzero proper subspace and
nothing more, ordered by reverse inclusion. -/
def depthZeroSliceOrderIso :
    {v : CuspedVertex K V // v.depth = 0} ≃o ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ where
  toFun v := OrderDual.toDual ⟨v.1.space, v.1.ne_bot, v.1.ne_top⟩
  invFun S := ⟨⟨(OrderDual.ofDual S).1, 0, (OrderDual.ofDual S).2.1, (OrderDual.ofDual S).2.2,
    fun h => absurd rfl h⟩, rfl⟩
  left_inv v := Subtype.ext (ext' rfl v.2.symm)
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    constructor
    · intro h
      exact ⟨by rw [a.2, b.2], fun _ => h, fun hc => absurd a.2 hc⟩
    · intro h
      exact h.2.1 a.2

variable [DecidableEq (Submodule K V)]

/-- **The depth-one slice already carries the homology of the whole all-depth complex.**  The cusps
retract away, and what is left is exactly the slice of depth one. -/
noncomputable def depthZeroSliceHomologyIso {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) :
    (nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = 0})).homology R n
      ≅ (nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R n :=
  (SSet.homologyFunctor R n).mapIso (orderIsoNerveIso (depthZeroSliceOrderIso (K := K) (V := V)))
    ≪≫ (cuspBuildingHomologyIso K V R n).symm

/-- **The slice-versus-global phase law.**  In every positive degree the homology of a slice of
positive depth vanishes, while the depth-one slice reproduces the homology of the whole all-depth
complex: the topological information is concentrated in the depth-one incidence skeleton, and the
derivative tails contribute nothing of their own. -/
theorem slice_phase_law {d : ℕ} (hd : d ≠ 0) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero
        ((nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = d})).homology R n)
      ∧ Nonempty
        ((nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = 0})).homology R n
          ≅ (nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R n) :=
  ⟨isZero_homology_nerve_depthSlice hd R n hn, ⟨depthZeroSliceHomologyIso R n⟩⟩

end CuspedVertex

end GaloisForLFunctions.HTGeometry
