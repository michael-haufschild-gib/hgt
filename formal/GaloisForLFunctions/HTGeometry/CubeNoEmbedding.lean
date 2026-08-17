import GaloisForLFunctions.HTGeometry.CubeSeparation
import GaloisForLFunctions.HTGeometry.CubeFaceDimensionBound

/-!
# The `m`-cube does not embed in `ℝ^k` for `k < m`

An injective continuous image of the cube carries the `m` pairs of opposite faces to `m` pairs of
disjoint compact sets, so the essential-face dimension bound applies and forces `m ≤ k`.

This is the Lebesgue dimension of Euclidean space in the form dimension theory uses: it forbids a
topological embedding of `[0,1]^m` into `ℝ^k` whenever `k < m`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- Two disjoint nonempty compact sets in a metric space are uniformly separated. -/
theorem exists_pos_lt_dist_of_disjoint_compact {X : Type*} [MetricSpace X] {A B : Set X}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hd : ∀ y ∈ A, y ∉ B) : ∃ ε > 0, ∀ y ∈ A, ∀ y' ∈ B, ε < dist y y' := by
  obtain ⟨y₀, hy₀A, hy₀min⟩ := hA.exists_isMinOn hAne (Metric.continuous_infDist_pt B).continuousOn
  have hpos : 0 < infDist y₀ B := by
    rw [← Metric.infDist_pos_iff_notMem_closure hBne, hB.isClosed.closure_eq]
    exact hd y₀ hy₀A
  refine ⟨infDist y₀ B / 2, by linarith, ?_⟩
  intro y hy y' hy'
  have h1 : infDist y₀ B ≤ infDist y B := isMinOn_iff.mp hy₀min y hy
  have h2 : infDist y B ≤ dist y y' := Metric.infDist_le_dist_of_mem hy'
  linarith

/-- **No continuous injection of the `m`-cube into a space of dimension below `m`.** -/
theorem not_injOn_unitCube {k m : ℕ} (hkm : k < m)
    (h : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (hc : ContinuousOn h (unitCube m)) : ¬ Set.InjOn h (unitCube m) := by
  classical
  intro hinj
  have hm : 0 < m := by omega
  set faceLo : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
    fun i => {x | x ∈ unitCube m ∧ x i = 0} with hfaceLo
  set faceHi : Fin m → Set (EuclideanSpace ℝ (Fin m)) :=
    fun i => {x | x ∈ unitCube m ∧ x i = 1} with hfaceHi
  have hfaceLoClosed : ∀ i, IsClosed (faceLo i) := by
    intro i
    have hrw : faceLo i = unitCube m ∩ (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' {0} := by
      ext x; simp [hfaceLo, Set.mem_inter_iff, and_comm]
    rw [hrw]
    exact (isClosed_unitCube m).inter
      (isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
  have hfaceHiClosed : ∀ i, IsClosed (faceHi i) := by
    intro i
    have hrw : faceHi i = unitCube m ∩ (fun x : EuclideanSpace ℝ (Fin m) => x i) ⁻¹' {1} := by
      ext x; simp [hfaceHi, Set.mem_inter_iff, and_comm]
    rw [hrw]
    exact (isClosed_unitCube m).inter
      (isClosed_singleton.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
  have hfaceLoSub : ∀ i, faceLo i ⊆ unitCube m := fun i x hx => hx.1
  have hfaceHiSub : ∀ i, faceHi i ⊆ unitCube m := fun i x hx => hx.1
  have hfaceLoCompact : ∀ i, IsCompact (faceLo i) := fun i =>
    (GaloisForLFunctions.isCompact_unitCube m).of_isClosed_subset (hfaceLoClosed i) (hfaceLoSub i)
  have hfaceHiCompact : ∀ i, IsCompact (faceHi i) := fun i =>
    (GaloisForLFunctions.isCompact_unitCube m).of_isClosed_subset (hfaceHiClosed i) (hfaceHiSub i)
  have hAcompact : ∀ i, IsCompact (h '' faceLo i) := fun i =>
    (hfaceLoCompact i).image_of_continuousOn (hc.mono (hfaceLoSub i))
  have hBcompact : ∀ i, IsCompact (h '' faceHi i) := fun i =>
    (hfaceHiCompact i).image_of_continuousOn (hc.mono (hfaceHiSub i))
  have hAne : ∀ i, (h '' faceLo i).Nonempty := fun i =>
    ⟨h 0, ⟨0, ⟨zero_mem_unitCube m, by simp⟩, rfl⟩⟩
  have hBne : ∀ i, (h '' faceHi i).Nonempty := fun i =>
    ⟨h (cubeOne m), ⟨cubeOne m, ⟨cubeOne_mem_unitCube m, by simp⟩, rfl⟩⟩
  have hdisj : ∀ i, Disjoint (h '' faceLo i) (h '' faceHi i) := by
    intro i
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
    have hEq := hinj hx'.1 hx.1 hxx
    subst hEq
    have h0 := hx.2
    have h1 := hx'.2
    rw [h0] at h1
    norm_num at h1
  have hbound := GaloisForLFunctions.le_finrank_of_cube_faces
    (E := EuclideanSpace ℝ (Fin k)) (A := fun i => h '' faceLo i) (B := fun i => h '' faceHi i)
    (S := Set.univ) hAcompact hAne hBcompact hBne hdisj hc (fun x _ => Set.mem_univ _)
    (fun x hx i hxi => ⟨x, ⟨hx, hxi⟩, rfl⟩) (fun x hx i hxi => ⟨x, ⟨hx, hxi⟩, rfl⟩)
  rw [finrank_euclideanSpace_fin] at hbound
  omega

end GaloisForLFunctions.HTGeometry
