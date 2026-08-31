import GaloisForLFunctions.HTGeometry.HomogeneousEuclideanNoGo

/-!
# The homogeneous obstruction on a locally Euclidean target

The Euclidean no-go localizes: if a compact homogeneous space embeds in a space that is locally
Euclidean of dimension `p` along the image, and it receives a continuous injection from a nonempty
open subset of `ℝ^p`, then its image is open.  Being also compact it is clopen, so on a connected
target it is everything — which is the contradiction whenever the target is known to contain a point
outside the image.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The localized homogeneous obstruction.**  The image of a compact homogeneous space in a
target that is locally Euclidean of dimension `p` along that image, and which receives a continuous
injection from a nonempty open subset of `E`, is open. -/
theorem isOpen_range_of_compact_homogeneous_locally_euclidean
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {Y : Type*} [TopologicalSpace Y]
    (J : X → Y) (hJcont : Continuous J) (hJinj : Function.Injective J)
    (hhom : ∀ x y : X, ∃ h : X ≃ₜ X, h x = y)
    {U : Set E} (hUopen : IsOpen U) (hUne : U.Nonempty)
    {Φ : E → X} (hΦcont : ContinuousOn Φ U) (hΦinj : Set.InjOn Φ U)
    (hchart : ∀ y : X, ∃ (V : Set Y) (χ : Y → E), IsOpen V ∧ J y ∈ V ∧
      ContinuousOn χ V ∧ Set.InjOn χ V ∧ IsOpen (χ '' V) ∧
      ∀ W ⊆ V, IsOpen (χ '' W) → IsOpen W) :
    IsOpen (Set.range J) := by
  classical
  obtain ⟨u, hu⟩ := hUne
  set x₀ : X := Φ u with hx₀
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨y, rfl⟩
  obtain ⟨h, hh⟩ := hhom x₀ y
  obtain ⟨V, χ, hVopen, hyV, hχcont, hχinj, -, hχopen⟩ := hchart y
  set g : E → Y := fun e => J (h (Φ e)) with hg
  have hgcont : ContinuousOn g U := (hJcont.comp h.continuous).comp_continuousOn hΦcont
  have hginj : Set.InjOn g U := fun a ha b hb hab =>
    hΦinj ha hb (h.injective (hJinj hab))
  set U' : Set E := U ∩ g ⁻¹' V with hU'
  have hU'open : IsOpen U' := hgcont.isOpen_inter_preimage hUopen hVopen
  have hgu : g u = J y := by
    show J (h (Φ u)) = J y
    rw [← hx₀, hh]
  have huU' : u ∈ U' := ⟨hu, by show g u ∈ V; rw [hgu]; exact hyV⟩
  -- the chart composite is continuous and injective on `U'`
  have hcomp : ContinuousOn (fun e => χ (g e)) U' :=
    hχcont.comp (hgcont.mono inter_subset_left) fun e he => he.2
  have hcompinj : Set.InjOn (fun e => χ (g e)) U' := by
    intro a ha b hb hab
    exact hginj ha.1 hb.1 (hχinj ha.2 hb.2 hab)
  have hopenimg : IsOpen ((fun e => χ (g e)) '' U') :=
    invariance_of_domain_open_map (fun e => χ (g e)) U' hU'open hcomp hcompinj
  refine ⟨g '' U', ?_, ?_, ⟨u, huU', hgu⟩⟩
  · rintro _ ⟨e, he, rfl⟩
    exact ⟨h (Φ e), rfl⟩
  · refine hχopen (g '' U') (fun _ ⟨e, he, hey⟩ => hey ▸ he.2) ?_
    have himg : χ '' (g '' U') = (fun e => χ (g e)) '' U' := by
      rw [Set.image_image]
    rw [himg]
    exact hopenimg

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The proper-image contradiction.**  On a connected Hausdorff target that is locally Euclidean
along the image, a compact homogeneous space receiving a continuous injection from a nonempty open
subset of `E` cannot embed properly: its image would be clopen and hence everything. -/
theorem false_of_compact_homogeneous_locally_euclidean_proper
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y]
    (J : X → Y) (hJcont : Continuous J) (hJinj : Function.Injective J)
    (hhom : ∀ x y : X, ∃ h : X ≃ₜ X, h x = y)
    {U : Set E} (hUopen : IsOpen U) (hUne : U.Nonempty)
    {Φ : E → X} (hΦcont : ContinuousOn Φ U) (hΦinj : Set.InjOn Φ U)
    (hchart : ∀ y : X, ∃ (V : Set Y) (χ : Y → E), IsOpen V ∧ J y ∈ V ∧
      ContinuousOn χ V ∧ Set.InjOn χ V ∧ IsOpen (χ '' V) ∧
      ∀ W ⊆ V, IsOpen (χ '' W) → IsOpen W)
    (hproper : ∃ y : Y, y ∉ Set.range J) :
    False := by
  have hopen : IsOpen (Set.range J) :=
    isOpen_range_of_compact_homogeneous_locally_euclidean J hJcont hJinj hhom hUopen hUne
      hΦcont hΦinj hchart
  have hclosed : IsClosed (Set.range J) := (isCompact_range hJcont).isClosed
  have hne : (Set.range J).Nonempty := Set.range_nonempty J
  rcases (isClopen_iff (α := Y)).mp ⟨hclosed, hopen⟩ with h | h
  · exact absurd h hne.ne_empty
  · obtain ⟨y, hy⟩ := hproper
    exact hy (by rw [h]; trivial)

end GaloisForLFunctions.HTGeometry
