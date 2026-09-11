import GaloisForLFunctions.HTGeometry.PathIndependenceCochain
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicFaces

/-!
# Path faces as supports of separated nonnegative probes

The faces of the independence complex of the path `P_n` are exactly the supports of the
nonnegative probes on `{0, …, n-1}` whose adjacent coordinates never activate together.
This identifies the abstract face condition `IsPathFace` with the physical separated-support
condition, and specialises to the cubic norming complex of `ChronologicalTensor.CubicFaces`,
whose four facets `{0,2,4}`, `{0,3}`, `{1,3}`, `{1,4}` are the maximal nonadjacent subsets
of `P_5`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Finset

/-- The support of a probe on the vertices of the path `P_n`. -/
def pathProbeSupport (n : ℕ) (g : ℕ → ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun v => g v ≠ 0)

theorem mem_pathProbeSupport {n : ℕ} {g : ℕ → ℝ} {v : ℕ} :
    v ∈ pathProbeSupport n g ↔ v < n ∧ g v ≠ 0 := by
  rw [pathProbeSupport, Finset.mem_filter, Finset.mem_range]

/-- **The face condition is the separated-support condition.** -/
theorem isPathFace_pathProbeSupport (n : ℕ) (g : ℕ → ℝ) :
    IsPathFace n (pathProbeSupport n g) ↔ ∀ v, v + 1 < n → (g v = 0 ∨ g (v + 1) = 0) := by
  constructor
  · intro h v hv
    by_cases h0 : g v = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      by_contra h1
      exact h.2 v (mem_pathProbeSupport.mpr ⟨by omega, h0⟩)
        (mem_pathProbeSupport.mpr ⟨hv, h1⟩)
  · intro h
    refine ⟨fun v hv => (mem_pathProbeSupport.mp hv).1, fun v hv hv1 => ?_⟩
    have h0 := (mem_pathProbeSupport.mp hv).2
    have h1 := mem_pathProbeSupport.mp hv1
    rcases h v h1.1 with hz | hz
    · exact h0 hz
    · exact h1.2 hz

/-- The nonnegative probe realising a given face. -/
def pathFaceProbe (σ : Finset ℕ) (v : ℕ) : ℝ := if v ∈ σ then 1 else 0

theorem pathFaceProbe_nonneg (σ : Finset ℕ) (v : ℕ) : 0 ≤ pathFaceProbe σ v := by
  rw [pathFaceProbe]
  split
  · norm_num
  · norm_num

theorem pathProbeSupport_pathFaceProbe {n : ℕ} {σ : Finset ℕ} (h : IsPathFace n σ) :
    pathProbeSupport n (pathFaceProbe σ) = σ := by
  ext v
  rw [mem_pathProbeSupport]
  constructor
  · rintro ⟨-, hne⟩
    by_contra hv
    rw [pathFaceProbe, if_neg hv] at hne
    exact hne rfl
  · intro hv
    refine ⟨h.1 v hv, ?_⟩
    rw [pathFaceProbe, if_pos hv]
    norm_num

/-- **Path faces are exactly the supports of separated nonnegative probes.** -/
theorem isPathFace_iff_exists_nonneg_probe {n : ℕ} {σ : Finset ℕ} :
    IsPathFace n σ ↔ ∃ g : ℕ → ℝ, (∀ v, 0 ≤ g v) ∧ pathProbeSupport n g = σ ∧
      ∀ v, v + 1 < n → (g v = 0 ∨ g (v + 1) = 0) := by
  constructor
  · intro h
    refine ⟨pathFaceProbe σ, pathFaceProbe_nonneg σ, pathProbeSupport_pathFaceProbe h, ?_⟩
    rw [← isPathFace_pathProbeSupport, pathProbeSupport_pathFaceProbe h]
    exact h
  · rintro ⟨g, -, hsupp, hsep⟩
    rw [← hsupp, isPathFace_pathProbeSupport]
    exact hsep

/-! ### The cubic norming complex is the path complex on five vertices -/

theorem isPathFace_pathProbeSupport_five (g : ℕ → ℝ) :
    IsPathFace 5 (pathProbeSupport 5 g) ↔
      (g 0 = 0 ∨ g 1 = 0) ∧ (g 1 = 0 ∨ g 2 = 0) ∧ (g 2 = 0 ∨ g 3 = 0) ∧
        (g 3 = 0 ∨ g 4 = 0) := by
  rw [isPathFace_pathProbeSupport]
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3⟩ v hv
    have hv4 : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hv4 with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem image_cubicProbeSupport_val (g : ℕ → ℝ) :
    (ChronologicalTensor.cubicProbeSupport (fun q : Fin 5 => g (q : ℕ))).image Fin.val
      = pathProbeSupport 5 g := by
  ext v
  simp only [Finset.mem_image, mem_pathProbeSupport, ChronologicalTensor.cubicProbeSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.is_lt, hq⟩
  · rintro ⟨hv, hne⟩
    exact ⟨⟨v, hv⟩, hne, rfl⟩

/-- **The cubic faces are the faces of `P_5`.** -/
theorem mem_cubicFaces_iff_isPathFace (g : ℕ → ℝ) :
    ChronologicalTensor.cubicProbeSupport (fun q : Fin 5 => g (q : ℕ))
        ∈ ChronologicalTensor.cubicFaces
      ↔ IsPathFace 5 (pathProbeSupport 5 g) := by
  rw [ChronologicalTensor.cubicProbeSupport_face, isPathFace_pathProbeSupport_five]
  norm_num

end
end GaloisForLFunctions.HTGeometry
