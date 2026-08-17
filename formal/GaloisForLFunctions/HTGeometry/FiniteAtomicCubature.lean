import Mathlib

/-!
# Finite atomic cubature in `ℝ^N`

A limit of convex combinations of points of a **compact** `K ⊆ ℝ^N` is itself a convex combination
of at most `N + 1` points of `K` (`exists_atomic_of_mem_closure_convexHull`).  This is the finite
step that converts an infinite positive representation of a truncated moment block into an exact
finitely-atomic one, with the Carathéodory bound on the number of atoms.

The route avoids the general statement "the convex hull of a compact set in finite dimension is
compact", which mathlib does not have (it only has the finite-set case,
`Set.Finite.isCompact_convexHull`).  Instead:

* `atomicSpan n K` is the set of convex combinations of exactly `n` points of `K` — a *closed* set,
  because it is the image of the compact `stdSimplex ℝ (Fin n) ×ˢ Kⁿ` under a continuous map
  (`atomicSpan_eq_image`, `isCompact_atomicSpan`, `isClosed_atomicSpan`);
* `convexHull_subset_atomicSpan` is Carathéodory in coordinates: mathlib's
  `eq_pos_convex_span_of_mem_convexHull` produces an affinely independent family, whose cardinality
  is at most `N + 1` by `AffineIndependent.card_le_finrank_succ`, and the family is padded out to
  exactly `N + 1` atoms with zero weights via `Function.extend`.

Since `atomicSpan (N+1) K` is closed and contains `convexHull ℝ K`, it contains its closure.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry


variable {N : ℕ}

/-- The set of points of `ℝ^N` representable as a convex combination of at most `n` points of `K`. -/
def atomicSpan (n : ℕ) (K : Set (Fin N → ℝ)) : Set (Fin N → ℝ) :=
  {m | ∃ (w : Fin n → ℝ) (z : Fin n → (Fin N → ℝ)),
    w ∈ stdSimplex ℝ (Fin n) ∧ (∀ i, z i ∈ K) ∧ ∑ i, w i • z i = m}

theorem atomicSpan_eq_image (n : ℕ) (K : Set (Fin N → ℝ)) :
    atomicSpan n K =
      (fun p : (Fin n → ℝ) × (Fin n → (Fin N → ℝ)) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin n) ×ˢ (Set.univ.pi fun _ => K)) := by
  ext m
  constructor
  · rintro ⟨w, z, hw, hz, hsum⟩
    exact ⟨(w, z), ⟨hw, fun i _ => hz i⟩, hsum⟩
  · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, hsum⟩
    exact ⟨w, z, hw, fun i => hz i (Set.mem_univ i), hsum⟩

theorem isCompact_atomicSpan (n : ℕ) {K : Set (Fin N → ℝ)} (hK : IsCompact K) :
    IsCompact (atomicSpan n K) := by
  rw [atomicSpan_eq_image]
  refine IsCompact.image ?_ ?_
  · exact (isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hK)
  · fun_prop

theorem isClosed_atomicSpan (n : ℕ) {K : Set (Fin N → ℝ)} (hK : IsCompact K) :
    IsClosed (atomicSpan n K) := (isCompact_atomicSpan n hK).isClosed

theorem sum_extend_embedding {ι : Type} [Fintype ι] {n : ℕ} {M : Type*} [AddCommMonoid M]
    (e : ι ↪ Fin n) (f : Fin n → M) (hf : ∀ j, (¬ ∃ i, e i = j) → f j = 0) :
    ∑ j, f j = ∑ i : ι, f (e i) := by
  classical
  rw [← Finset.sum_image (f := f) (g := e) (s := (Finset.univ : Finset ι))
    (fun a _ b _ hab => e.injective hab)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro j _ hj
  refine hf j ?_
  intro hex
  exact hj (Finset.mem_image.mpr ⟨hex.choose, Finset.mem_univ _, hex.choose_spec⟩)

/-- **Carathéodory in coordinates.**  A point of the convex hull of `K ⊆ ℝ^N` is a convex
combination of at most `N + 1` points of `K`. -/
theorem convexHull_subset_atomicSpan {K : Set (Fin N → ℝ)} (hK : K.Nonempty) :
    convexHull ℝ K ⊆ atomicSpan (N + 1) K := by
  obtain ⟨k₀, hk₀⟩ := hK
  intro x hx
  obtain ⟨ι, hιfin, z, w, hzrange, hindep, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  classical
  have hcard : Fintype.card ι ≤ N + 1 := by
    have h1 := hindep.card_le_finrank_succ
    have h2 : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z)) ≤ N := by
      have := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      simpa [Module.finrank_fin_fun] using this
    omega
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin (N + 1)) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard
  classical
  set w' : Fin (N + 1) → ℝ := Function.extend e w (fun _ => 0) with hw'def
  set z' : Fin (N + 1) → (Fin N → ℝ) := Function.extend e z (fun _ => k₀) with hz'def
  have hw'e : ∀ i : ι, w' (e i) = w i := fun i => e.injective.extend_apply w (fun _ => 0) i
  have hz'e : ∀ i : ι, z' (e i) = z i := fun i => e.injective.extend_apply z (fun _ => k₀) i
  have hw'out : ∀ j : Fin (N + 1), (¬ ∃ i, e i = j) → w' j = 0 := by
    intro j hj
    rw [hw'def]
    exact Function.extend_apply' w (fun _ => 0) j hj
  have hz'out : ∀ j : Fin (N + 1), (¬ ∃ i, e i = j) → z' j = k₀ := by
    intro j hj
    rw [hz'def]
    exact Function.extend_apply' z (fun _ => k₀) j hj
  refine ⟨w', z', ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j
    by_cases hex : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hex
      rw [hw'e i]
      exact (hwpos i).le
    · rw [hw'out j hex]
  · rw [sum_extend_embedding e w' hw'out]
    rw [Finset.sum_congr rfl (fun i _ => hw'e i)]
    exact hwsum
  · intro j
    by_cases hex : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hex
      rw [hz'e i]
      exact hzrange ⟨i, rfl⟩
    · rw [hz'out j hex]
      exact hk₀
  · have hzero : ∀ j : Fin (N + 1), (¬ ∃ i, e i = j) → (fun j => w' j • z' j) j = 0 := by
      intro j hj
      simp only []
      rw [hw'out j hj, zero_smul]
    rw [sum_extend_embedding e (fun j => w' j • z' j) hzero]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hw'e i, hz'e i])]
    exact hwz

/-- **Finite atomic cubature.**  A limit of convex combinations of points of a compact
`K ⊆ ℝ^N` is itself a convex combination of at most `N + 1` points of `K`. -/
theorem exists_atomic_of_mem_closure_convexHull {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) {m : Fin N → ℝ} (hm : m ∈ closure (convexHull ℝ K)) :
    ∃ (w : Fin (N + 1) → ℝ) (z : Fin (N + 1) → (Fin N → ℝ)),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, z i ∈ K) ∧ ∑ i, w i • z i = m := by
  have hsub : closure (convexHull ℝ K) ⊆ atomicSpan (N + 1) K := by
    refine closure_minimal (convexHull_subset_atomicSpan hne) (isClosed_atomicSpan _ hK)
  obtain ⟨w, z, ⟨hw0, hw1⟩, hz, hsum⟩ := hsub hm
  exact ⟨w, z, hw0, hw1, hz, hsum⟩


end GaloisForLFunctions.HTGeometry

end
