import GaloisForLFunctions.HTGeometry.VertexIndependenceSphere
import GaloisForLFunctions.HTGeometry.PathIndependenceProbe
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicJoin

/-!
# The repeated cubic join is the independence complex of separated blocks

The corpus's `fusedCubicFaces n` is the face set of the `n`-fold join of the physical cubic sparse
unit complex `K_3 = Ind(P_5)`: a face is a set of block-labelled vertices whose fibre over every
block is a cubic face. Relabelling the block-labelled vertex `(i, q)` by the natural number
`6 i + q` identifies this face set with the faces of the independence complex of the induced
subgraph of the path on `joinVertsFrom 0 n`, that is, `n` blocks of five consecutive vertices
separated by one deleted vertex.

The relabelling is injective and cardinality preserving, so the occupation grading matches. The
reduced cohomology of the join is therefore one dimensional in occupation `2n` and zero in every
other occupation — topological degree `2n - 1`, the reduced cohomology of `S^(2n-1)`. This is the
cohomological content of the classical statement that the `n`-fold join of a circle is a
`(2n-1)`-sphere, and it is what the Euler-weighted heat trace of the fusion tower uses.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Finset

/-! ### Cubic faces are the faces of `P_5` -/

/-- **The cubic faces are exactly the faces of the path on five vertices.** -/
theorem mem_cubicFaces_iff_isPathFace_image (σ : Finset (Fin 5)) :
    σ ∈ ChronologicalTensor.cubicFaces ↔ IsPathFace 5 (σ.image Fin.val) := by
  set T : Finset ℕ := σ.image Fin.val with hT
  set g : ℕ → ℝ := fun v => if v ∈ T then 1 else 0 with hg
  have hgne : ∀ v : ℕ, g v ≠ 0 ↔ v ∈ T := by
    intro v
    by_cases hv : v ∈ T
    · rw [hg]
      simp only [if_pos hv]
      exact ⟨fun _ => hv, fun _ => one_ne_zero⟩
    · rw [hg]
      simp only [if_neg hv]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hv⟩
  have hmemT : ∀ q : Fin 5, (q : ℕ) ∈ T ↔ q ∈ σ := by
    intro q
    rw [hT, Finset.mem_image]
    exact ⟨fun ⟨p, hp, hpq⟩ => (Fin.val_injective hpq) ▸ hp, fun h => ⟨q, h, rfl⟩⟩
  have hsupp : ChronologicalTensor.cubicProbeSupport (fun q : Fin 5 => g (q : ℕ)) = σ := by
    ext q
    rw [ChronologicalTensor.cubicProbeSupport, Finset.mem_filter]
    exact ⟨fun h => (hmemT q).mp ((hgne _).mp h.2),
      fun h => ⟨Finset.mem_univ _, (hgne _).mpr ((hmemT q).mpr h)⟩⟩
  have hpath : pathProbeSupport 5 g = T := by
    ext v
    rw [mem_pathProbeSupport]
    constructor
    · exact fun h => (hgne v).mp h.2
    · intro hv
      refine ⟨?_, (hgne v).mpr hv⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp (hT ▸ hv)
      exact p.is_lt
  rw [← hsupp, mem_cubicFaces_iff_isPathFace g, hpath]

/-! ### The block relabelling -/

/-- The relabelling of block-labelled vertices by natural numbers. -/
def cubicJoinLabel {n : ℕ} (p : Fin n × Fin 5) : ℕ := 6 * (p.1 : ℕ) + (p.2 : ℕ)

theorem cubicJoinLabel_injective (n : ℕ) : Function.Injective (@cubicJoinLabel n) := by
  rintro ⟨i, q⟩ ⟨i', q'⟩ h
  have hval : 6 * (i : ℕ) + (q : ℕ) = 6 * (i' : ℕ) + (q' : ℕ) := h
  have hq : (q : ℕ) < 5 := q.is_lt
  have hq' : (q' : ℕ) < 5 := q'.is_lt
  have hi : (i : ℕ) = (i' : ℕ) := by omega
  have hqq : (q : ℕ) = (q' : ℕ) := by omega
  rw [Prod.mk.injEq]
  exact ⟨Fin.val_injective hi, Fin.val_injective hqq⟩

theorem mem_cubicJoinLabel_image {n : ℕ} {σ : Finset (Fin n × Fin 5)} {v : ℕ} :
    v ∈ σ.image cubicJoinLabel
      ↔ ∃ i : Fin n, ∃ q : Fin 5, (i, q) ∈ σ ∧ 6 * (i : ℕ) + (q : ℕ) = v := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨i, q⟩, hp, hv⟩
    exact ⟨i, q, hp, hv⟩
  · rintro ⟨i, q, hp, hv⟩
    exact ⟨(i, q), hp, hv⟩

theorem cubicJoinLabel_image_card {n : ℕ} (σ : Finset (Fin n × Fin 5)) :
    (σ.image cubicJoinLabel).card = σ.card :=
  Finset.card_image_of_injective σ (cubicJoinLabel_injective n)

theorem mem_cubicFaceFiber_image {n : ℕ} {σ : Finset (Fin n × Fin 5)} {i : Fin n} {v : ℕ} :
    v ∈ (ChronologicalTensor.cubicFaceFiber σ i).image Fin.val
      ↔ ∃ q : Fin 5, (q : ℕ) = v ∧ (i, q) ∈ σ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, rfl, (ChronologicalTensor.cubicFaceFiber_mem σ i q).mp hq⟩
  · rintro ⟨q, rfl, hq⟩
    exact ⟨q, (ChronologicalTensor.cubicFaceFiber_mem σ i q).mpr hq, rfl⟩

/-- **The join face condition is the block-separated path face condition.** -/
theorem isFace_cubicJoinLabel_image_iff {n : ℕ} (σ : Finset (Fin n × Fin 5)) :
    VertexIndependence.IsFace (VertexIndependence.joinVertsFrom 0 n)
        (σ.image cubicJoinLabel)
      ↔ ∀ i : Fin n, IsPathFace 5 ((ChronologicalTensor.cubicFaceFiber σ i).image Fin.val) := by
  constructor
  · intro h i
    refine ⟨fun v hv => ?_, fun v hv hv1 => ?_⟩
    · obtain ⟨q, rfl, -⟩ := mem_cubicFaceFiber_image.mp hv
      exact q.is_lt
    · obtain ⟨q, rfl, hq⟩ := mem_cubicFaceFiber_image.mp hv
      obtain ⟨q', hq', hq'2⟩ := mem_cubicFaceFiber_image.mp hv1
      exact h.2 (6 * (i : ℕ) + (q : ℕ))
        (mem_cubicJoinLabel_image.mpr ⟨i, q, hq, rfl⟩)
        (mem_cubicJoinLabel_image.mpr ⟨i, q', hq'2, by omega⟩)
  · intro h
    refine ⟨fun v hv => ?_, fun v hv hv1 => ?_⟩
    · obtain ⟨i, q, -, rfl⟩ := mem_cubicJoinLabel_image.mp hv
      exact VertexIndependence.mem_joinVertsFrom.mpr
        ⟨(i : ℕ), i.is_lt, (q : ℕ), q.is_lt, by omega⟩
    · obtain ⟨i, q, hiq, rfl⟩ := mem_cubicJoinLabel_image.mp hv
      obtain ⟨i', q', hiq', hv'⟩ := mem_cubicJoinLabel_image.mp hv1
      have h2 : (q : ℕ) < 5 := q.is_lt
      have h2' : (q' : ℕ) < 5 := q'.is_lt
      have hi : (i' : ℕ) = (i : ℕ) := by omega
      have hq : (q' : ℕ) = (q : ℕ) + 1 := by omega
      have hfst : i' = i := Fin.val_injective hi
      refine (h i).2 (q : ℕ) (mem_cubicFaceFiber_image.mpr ⟨q, rfl, hiq⟩) ?_
      refine mem_cubicFaceFiber_image.mpr ⟨q', hq, ?_⟩
      rw [← hfst]
      exact hiq'

/-- **The repeated cubic join is the independence complex of `n` separated five-vertex blocks.** -/
theorem mem_fusedCubicFaces_iff_isFace (n : ℕ) (σ : Finset (Fin n × Fin 5)) :
    σ ∈ ChronologicalTensor.fusedCubicFaces n
      ↔ VertexIndependence.IsFace (VertexIndependence.joinVertsFrom 0 n)
          (σ.image cubicJoinLabel) := by
  rw [ChronologicalTensor.fusedCubicFaces_mem, isFace_cubicJoinLabel_image_iff]
  exact ⟨fun h i => (mem_cubicFaces_iff_isPathFace_image _).mp (h i),
    fun h i => (mem_cubicFaces_iff_isPathFace_image _).mpr (h i)⟩

/-! ### The sphere cohomology of the repeated cubic join -/

/-- **The `n`-fold cubic join has the reduced cohomology of `S^(2n-1)`.** One class in occupation
`2n`, that is topological degree `2n - 1`, and none in any other occupation. This is the
cohomological content of the sphere-homotopy reading of the join powers; the reduced Euler
characteristic `-1` of `ChronologicalTensor.fusedCubicReducedEuler_eq` is its alternating sum. -/
theorem cubicJoin_cohomology_finrank (F : Type*) [Field F] (n j : ℕ) :
    Module.finrank F
        (VertexIndependence.cohomology F (VertexIndependence.joinVertsFrom 0 n) j)
      = if j = 2 * n then 1 else 0 :=
  VertexIndependence.joinCohomology_finrank F 0 n j

/-- The single class of the `n`-fold cubic join, in occupation `2n`. -/
theorem cubicJoin_cohomology_nonempty (F : Type*) [CommRing F] (n : ℕ) :
    Nonempty (VertexIndependence.cohomology F (VertexIndependence.joinVertsFrom 0 n) (2 * n)
      ≃ₗ[F] F) :=
  VertexIndependence.joinCohomology_nonempty_equiv F n 0

/-- Every other occupation of the `n`-fold cubic join vanishes. -/
theorem cubicJoin_cohomology_subsingleton (F : Type*) [CommRing F] (n j : ℕ) (hj : j ≠ 2 * n) :
    Subsingleton (VertexIndependence.cohomology F (VertexIndependence.joinVertsFrom 0 n) j) :=
  VertexIndependence.joinCohomology_subsingleton F n 0 j hj

end
end GaloisForLFunctions.HTGeometry
