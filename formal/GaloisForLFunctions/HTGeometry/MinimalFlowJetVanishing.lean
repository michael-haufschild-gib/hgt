import Mathlib

/-!
# A minimal flow has no proper closed jet-vanishing set

The set on which a whole equivariant family of continuous functionals vanishes is closed and
invariant.  On a minimal flow — every orbit dense — a closed invariant set is empty or everything,
so if one point of the space fails one functional the vanishing set is empty.

This is the step that turns "the distinguished element is regular at some time" into "every element
of the hull is regular at some time", with no common regular time and no uniqueness assumption: the
functionals are the separant evaluated at the real times, translation permutes them by shifting the
time, and minimality of the hull flow does the rest.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {G X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] [Zero Y]

/-- The common vanishing set of a family of continuous functionals is closed. -/
theorem isClosed_setOf_forall_eq_zero {ι : Type*} (Φ : ι → X → Y)
    (hcont : ∀ i, Continuous (Φ i)) : IsClosed {x : X | ∀ i, Φ i x = 0} := by
  have hrw : {x : X | ∀ i, Φ i x = 0} = ⋂ i, Φ i ⁻¹' ({0} : Set Y) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hrw]
  exact isClosed_iInter fun i => (isClosed_singleton (x := (0 : Y))).preimage (hcont i)

section Action

variable [Monoid G] [MulAction G X]

omit [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] in
/-- An equivariant family of functionals has invariant common vanishing set. -/
theorem smul_mem_setOf_forall_eq_zero {ι : Type*} (Φ : ι → X → Y)
    (hequiv : ∀ (g : G) (i : ι), ∃ j, ∀ x, Φ i (g • x) = Φ j x)
    {x : X} (hx : ∀ i, Φ i x = 0) (g : G) : ∀ i, Φ i (g • x) = 0 := by
  intro i
  obtain ⟨j, hj⟩ := hequiv g i
  rw [hj x, hx j]

/-- **A minimal flow has no proper closed invariant set.** -/
theorem eq_empty_of_isClosed_of_invariant {Z : Set X}
    (hmin : ∀ x : X, Dense (Set.range fun g : G => g • x))
    (hZclosed : IsClosed Z) (hZinv : ∀ (g : G), ∀ x ∈ Z, g • x ∈ Z)
    {x₀ : X} (hx₀ : x₀ ∉ Z) : Z = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have horb : (Set.range fun g : G => g • z) ⊆ Z := by
    rintro _ ⟨g, rfl⟩
    exact hZinv g z hz
  have : (Set.univ : Set X) ⊆ Z := by
    have hd := hmin z
    rw [dense_iff_closure_eq] at hd
    rw [← hd]
    exact hZclosed.closure_subset_iff.mpr horb
  exact hx₀ (this (Set.mem_univ x₀))

/-- **The regularity law of a minimal flow.**  If every functional of an equivariant continuous
family vanishes on some point, then it vanishes on every point; contrapositively, a single point at
which one functional is nonzero forces every point to have one. -/
theorem exists_ne_zero_of_exists_ne_zero {ι : Type*} (Φ : ι → X → Y)
    (hcont : ∀ i, Continuous (Φ i))
    (hequiv : ∀ (g : G) (i : ι), ∃ j, ∀ x, Φ i (g • x) = Φ j x)
    (hmin : ∀ x : X, Dense (Set.range fun g : G => g • x))
    {x₀ : X} (hx₀ : ∃ i, Φ i x₀ ≠ 0) : ∀ x : X, ∃ i, Φ i x ≠ 0 := by
  have hempty : {x : X | ∀ i, Φ i x = 0} = ∅ := by
    refine eq_empty_of_isClosed_of_invariant (G := G) hmin
      (isClosed_setOf_forall_eq_zero Φ hcont) (fun g x hx => ?_) (x₀ := x₀) ?_
    · exact smul_mem_setOf_forall_eq_zero (G := G) Φ hequiv hx g
    · intro hcon
      obtain ⟨i, hi⟩ := hx₀
      exact hi (hcon i)
  intro x
  by_contra hcon
  have hx : x ∈ {x : X | ∀ i, Φ i x = 0} := by
    intro i
    by_contra hne
    exact hcon ⟨i, hne⟩
  rw [hempty] at hx
  exact hx

end Action


/-! ### Compactness produces a finite subordinate closed cover -/

/-- **A finite closed cover subordinate to an open cover.**  On a compact regular space every open
cover has a finite closed refinement, each piece inside one member of the cover. -/
theorem exists_finite_closed_cover_subordinate {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [RegularSpace X] {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x, ∃ i, x ∈ U i) :
    ∃ (M : ℕ) (idx : Fin M → ι) (F : Fin M → Set X),
      (∀ j, IsClosed (F j)) ∧ (∀ j, F j ⊆ U (idx j)) ∧ ∀ x, ∃ j, x ∈ F j := by
  classical
  choose i hi using hcov
  have hnhds : ∀ x : X, U (i x) ∈ nhds x := fun x => (hU (i x)).mem_nhds (hi x)
  choose K hKnhds hKclosed hKsub using fun x : X => exists_mem_nhds_isClosed_subset (hnhds x)
  have hopencov : ∀ x : X, x ∈ interior (K x) := fun x => mem_interior_iff_mem_nhds.mpr (hKnhds x)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => interior (K x))
    (fun x => isOpen_interior) (fun y _ => Set.mem_iUnion.mpr ⟨y, hopencov y⟩)
  set e : Fin T.card ≃ {y // y ∈ T} := (T.equivFin).symm with he
  refine ⟨T.card, fun j => i (e j).1, fun j => K (e j).1, fun j => hKclosed _,
    fun j => hKsub _, fun y => ?_⟩
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ y))
  obtain ⟨hxT, hyx⟩ := Set.mem_iUnion.mp hx
  refine ⟨e.symm ⟨x, hxT⟩, ?_⟩
  show y ∈ K (e (e.symm ⟨x, hxT⟩)).1
  rw [Equiv.apply_symm_apply]
  exact interior_subset hyx

/-- **The finite regular-chart cover.**  On a compact regular flow with dense orbits, an equivariant
continuous family of functionals that is somewhere nonzero produces a finite closed cover on each
piece of which one fixed functional never vanishes. -/
theorem exists_finite_closed_regular_cover {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [RegularSpace X] [TopologicalSpace Y] [T1Space Y] [Zero Y] {ι : Type*}
    (Φ : ι → X → Y) (hcont : ∀ i, Continuous (Φ i)) (hreg : ∀ x, ∃ i, Φ i x ≠ 0) :
    ∃ (M : ℕ) (idx : Fin M → ι) (F : Fin M → Set X),
      (∀ j, IsClosed (F j)) ∧ (∀ x, ∃ j, x ∈ F j) ∧ ∀ j, ∀ x ∈ F j, Φ (idx j) x ≠ 0 := by
  have hUopen : ∀ i : ι, IsOpen {x : X | Φ i x ≠ 0} := by
    intro i
    have hrw : {x : X | Φ i x ≠ 0} = Φ i ⁻¹' ({0} : Set Y)ᶜ := rfl
    rw [hrw]
    exact (isClosed_singleton (x := (0 : Y))).isOpen_compl.preimage (hcont i)
  obtain ⟨M, idx, F, hFclosed, hFsub, hFcov⟩ :=
    exists_finite_closed_cover_subordinate (fun i : ι => {x : X | Φ i x ≠ 0}) hUopen hreg
  exact ⟨M, idx, F, hFclosed, hFcov, fun j x hx => hFsub j hx⟩

end GaloisForLFunctions.HTGeometry
