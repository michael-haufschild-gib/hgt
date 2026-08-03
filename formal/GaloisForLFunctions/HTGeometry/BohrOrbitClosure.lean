import GaloisForLFunctions.HTGeometry.BohrHullContinuity
import GaloisForLFunctions.HTGeometry.InfiniteTorusForwardDensity

/-!
# Boundary points are limits of the orbit

An orbit which is asymptotic to a continuous parametrised family along a flow with dense forward
tails accumulates on the whole family: to reach a prescribed parameter one waits until the orbit is
close to the family, and then uses density of the remaining tail to steer the flow near that
parameter.

For the hull of an exponential carrier this says that every boundary state is a limit of orbit
states, which is the inclusion `B ⊆ closure O` of the orbit closure decomposition.
-/

open Filter Topology Set

namespace GaloisForLFunctions

noncomputable section

/-- **Asymptotic orbits reach every parameter.**  If a family `α` is continuous, the flow `θ` has
dense forward tails, and the orbit `G` is asymptotic to `α ∘ θ`, then every value of `α` lies in the
closure of the orbit. -/
theorem mem_closure_range_of_dense_tails {T Y : Type*} [TopologicalSpace T] [UniformSpace Y]
    {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (htails : ∀ T₀ : ℝ, Dense {x : T | ∃ t : ℝ, T₀ ≤ t ∧ θ t = x})
    (hasym : ∀ V ∈ uniformity Y, ∀ᶠ t in atTop, (α (θ t), G t) ∈ V)
    (x : T) : α x ∈ closure (Set.range G) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨V, hV, hVN⟩ := UniformSpace.mem_nhds_iff.mp hN
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  have hpre : α ⁻¹' (UniformSpace.ball (α x) W) ∈ 𝓝 x :=
    hα.continuousAt (UniformSpace.ball_mem_nhds _ hW)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp (hasym W hW)
  set U : Set T := interior (α ⁻¹' UniformSpace.ball (α x) W) with hU
  have hUopen : IsOpen U := isOpen_interior
  have hxU : x ∈ U := mem_interior_iff_mem_nhds.mpr hpre
  obtain ⟨y, hyU, hyorbit⟩ :=
    (dense_iff_inter_open.mp (htails T₀)) U hUopen ⟨x, hxU⟩
  obtain ⟨t, htT₀, rfl⟩ := hyorbit
  rw [hU] at hyU
  have hmem : θ t ∈ α ⁻¹' UniformSpace.ball (α x) W := interior_subset hyU
  have hball : α (θ t) ∈ UniformSpace.ball (α x) W := hmem
  have hGt : (α x, G t) ∈ V := by
    refine hWV ?_
    exact ⟨α (θ t), hball, hT₀ t htT₀⟩
  refine ⟨G t, hVN hGt, ⟨t, rfl⟩⟩

/-- **Every boundary state of the hull is a limit of an asymptotic orbit.**  Specialised to the
phase hull of an exponential carrier: the phase flow has dense forward tails, so an orbit asymptotic
to the boundary family accumulates on the whole boundary. -/
theorem bohrHullMap_mem_closure_range_of_asymptotic {ι : Type*} [Countable ι] [DecidableEq ι]
    {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    {phase : ℝ → ι → Circle} {G : ℝ → C(ℂ, ℂ)}
    (hflow : ∀ T₀ : ℝ, Dense {x : ι → Circle | ∃ t : ℝ, T₀ ≤ t ∧ phase t = x})
    (hasym : ∀ V ∈ uniformity C(ℂ, ℂ), ∀ᶠ t in atTop,
      (bohrHullMap a omega h (phase t), G t) ∈ V)
    (lam : ι → Circle) :
    bohrHullMap a omega h lam ∈ closure (Set.range G) :=
  mem_closure_range_of_dense_tails (continuous_bohrHullMap h) hflow hasym lam


/-! ## Splitting the closure of an orbit -/

/-- **Bounded times contribute only orbit points.**  The image of a compact time window is closed,
so a limit of orbit points from a bounded window is itself an orbit point. -/
theorem mem_range_of_mem_closure_image_compact {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {G : ℝ → Y} (hG : Continuous G) {M : ℝ} {y : Y}
    (hy : y ∈ closure (G '' Set.Icc (-M) M)) : y ∈ Set.range G := by
  have hcompact : IsCompact (G '' Set.Icc (-M) M) := (isCompact_Icc).image hG
  have hclosed : IsClosed (G '' Set.Icc (-M) M) := hcompact.isClosed
  rw [hclosed.closure_eq] at hy
  obtain ⟨t, -, rfl⟩ := hy
  exact ⟨t, rfl⟩

/-- **The closure of an orbit splits.**  A limit of orbit points is either an orbit point or a
cluster point of the orbit at arbitrarily large times. -/
theorem closure_range_subset_union_clusterAtInfinity {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {G : ℝ → Y} (hG : Continuous G) :
    closure (Set.range G) ⊆ Set.range G ∪ ⋂ M : ℝ, closure (G '' {t : ℝ | M < |t|}) := by
  intro y hy
  by_cases hrange : y ∈ Set.range G
  · exact Or.inl hrange
  refine Or.inr (Set.mem_iInter.mpr fun M => ?_)
  have hsplit : Set.range G = G '' Set.Icc (-M) M ∪ G '' {t : ℝ | M < |t|} := by
    rw [← Set.image_union]
    have hcover : Set.Icc (-M) M ∪ {t : ℝ | M < |t|} = Set.univ := by
      ext t
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases le_or_gt |t| M with habs | habs
      · exact Or.inl ⟨by cases abs_le.mp habs with | intro h1 h2 => linarith,
          (abs_le.mp habs).2⟩
      · exact Or.inr habs
    rw [hcover, Set.image_univ]
  rw [hsplit, closure_union] at hy
  rcases hy with hy | hy
  · exact absurd (mem_range_of_mem_closure_image_compact hG hy) hrange
  · exact hy

end

end GaloisForLFunctions
