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


/-- **The cluster set at infinity is the boundary family.**  On a compact parameter space, an orbit
asymptotic to a continuous family has all its cluster points at infinity in the range of that
family: an ultrafilter refining the cocompact filter converges on the parameter space, and the
asymptotic comparison transports its limit. -/
theorem clusterAtInfinity_subset_range {T Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [UniformSpace Y] [T2Space Y] {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (hasym : Tendsto (fun t => (α (θ t), G t)) (Filter.cocompact ℝ) (uniformity Y))
    {y : Y} (hy : ∀ M : ℝ, y ∈ closure (G '' {t : ℝ | M < |t|})) :
    y ∈ Set.range α := by
  classical
  have hne : (Filter.comap G (nhds y) ⊓ Filter.cocompact ℝ).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s hs s' hs'
    obtain ⟨N, hN, hNs⟩ := Filter.mem_comap.mp hs
    obtain ⟨K, hK, hKs⟩ := Filter.hasBasis_cocompact.mem_iff.mp hs'
    obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    have hcompl : {t : ℝ | M < |t|} ⊆ Kᶜ := by
      intro t ht hcon
      have := hM hcon
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact absurd this (not_le.mpr ht)
    obtain ⟨w, hwN, hwimg⟩ := (mem_closure_iff_nhds.mp (hy M)) N hN
    obtain ⟨t, ht, rfl⟩ := hwimg
    exact ⟨t, hNs hwN, hKs (hcompl ht)⟩
  haveI : (Filter.comap G (nhds y) ⊓ Filter.cocompact ℝ).NeBot := hne
  set U : Ultrafilter ℝ := Ultrafilter.of (Filter.comap G (nhds y) ⊓ Filter.cocompact ℝ) with hU
  have hUF : (↑U : Filter ℝ) ≤ Filter.comap G (nhds y) ⊓ Filter.cocompact ℝ :=
    Ultrafilter.of_le _
  have hGy : Tendsto G (↑U : Filter ℝ) (nhds y) :=
    le_trans (Filter.map_mono (le_trans hUF inf_le_left)) Filter.map_comap_le
  have hcocompact : (↑U : Filter ℝ) ≤ Filter.cocompact ℝ := le_trans hUF inf_le_right
  obtain ⟨lam, -, hlam⟩ := isCompact_univ.ultrafilter_le_nhds (U.map θ) (by simp)
  have hθ : Tendsto θ (↑U : Filter ℝ) (nhds lam) := by
    rw [Ultrafilter.coe_map] at hlam
    exact hlam
  have hαθ : Tendsto (fun t => α (θ t)) (↑U : Filter ℝ) (nhds (α lam)) :=
    (hα.tendsto lam).comp hθ
  have hclose : Tendsto (fun t => (α (θ t), G t)) (↑U : Filter ℝ) (uniformity Y) :=
    hasym.mono_left hcocompact
  have hGlam : Tendsto G (↑U : Filter ℝ) (nhds (α lam)) := hαθ.congr_uniformity hclose
  exact ⟨lam, tendsto_nhds_unique hGlam hGy⟩

/-- **The closure of an asymptotic orbit is the orbit together with the boundary family.** -/
theorem closure_range_subset_union_range {T Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [UniformSpace Y] [T2Space Y] {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (hG : Continuous G)
    (hasym : Tendsto (fun t => (α (θ t), G t)) (Filter.cocompact ℝ) (uniformity Y)) :
    closure (Set.range G) ⊆ Set.range G ∪ Set.range α := by
  intro y hy
  rcases closure_range_subset_union_clusterAtInfinity hG hy with horbit | hcluster
  · exact Or.inl horbit
  · exact Or.inr (clusterAtInfinity_subset_range hα hasym (Set.mem_iInter.mp hcluster))


/-- **The orbit closure decomposition.**  An orbit asymptotic to a continuous family on a compact
parameter space, along a flow with dense forward tails, has closure exactly the orbit together with
the family. -/
theorem closure_range_eq_union_range {T Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [UniformSpace Y] [T2Space Y] {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (hG : Continuous G)
    (htails : ∀ T₀ : ℝ, Dense {x : T | ∃ t : ℝ, T₀ ≤ t ∧ θ t = x})
    (hasym : Tendsto (fun t => (α (θ t), G t)) (Filter.cocompact ℝ) (uniformity Y)) :
    closure (Set.range G) = Set.range G ∪ Set.range α := by
  refine Set.Subset.antisymm (closure_range_subset_union_range hα hG hasym) ?_
  have hatTop : (Filter.atTop : Filter ℝ) ≤ Filter.cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  have hasymTop : ∀ V ∈ uniformity Y, ∀ᶠ t in Filter.atTop, (α (θ t), G t) ∈ V := by
    intro V hV
    exact hatTop (hasym hV)
  refine Set.union_subset subset_closure ?_
  rintro - ⟨x, rfl⟩
  exact mem_closure_range_of_dense_tails hα htails hasymTop x


/-- The phase flow read in the circle group of each coordinate. -/
def circlePhaseFlow {ι : Type*} (omega : ι → ℝ) (t : ℝ) : ι → Circle :=
  fun i => AddCircle.homeomorphCircle (one_ne_zero) (HTGeometry.clockPhasePoint omega t i)

/-- Coordinatewise the unit torus is the product of circles. -/
def unitTorusHomeomorphCircles (ι : Type*) : UnitAddTorus ι ≃ₜ (ι → Circle) :=
  Homeomorph.piCongrRight fun _ => AddCircle.homeomorphCircle one_ne_zero

theorem circlePhaseFlow_eq {ι : Type*} (omega : ι → ℝ) (t : ℝ) :
    circlePhaseFlow omega t
      = unitTorusHomeomorphCircles ι (HTGeometry.clockPhasePoint omega t) := rfl

/-- **Forward tails of the circle phase flow are dense.** -/
theorem dense_forwardOrbit_circlePhaseFlow {ι : Type*} [Countable ι] [DecidableEq ι]
    {omega : ι → ℝ} (hindep : HTGeometry.RationallyIndependentSequence omega) (T₀ : ℝ) :
    Dense {x : ι → Circle | ∃ t : ℝ, T₀ ≤ t ∧ circlePhaseFlow omega t = x} := by
  have hbase := HTGeometry.dense_forwardOrbit hindep T₀
  have himage : (unitTorusHomeomorphCircles ι) ''
      {x : UnitAddTorus ι | ∃ t : ℝ, T₀ ≤ t ∧ HTGeometry.clockPhasePoint omega t = x}
      ⊆ {x : ι → Circle | ∃ t : ℝ, T₀ ≤ t ∧ circlePhaseFlow omega t = x} := by
    rintro - ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, (circlePhaseFlow_eq omega t)⟩
  refine Dense.mono himage ?_
  exact (unitTorusHomeomorphCircles ι).surjective.denseRange.dense_image
    (unitTorusHomeomorphCircles ι).continuous hbase

/-- **The orbit closure of an asymptotic Bohr orbit.**  For an exponential carrier with summable
weights and rationally independent frequencies, an orbit asymptotic to the phase hull along the
phase flow has closure exactly the orbit together with the whole hull, a homeomorphic copy of the
phase torus. -/
theorem bohrHull_closure_range_eq {ι : Type*} [Countable ι] [DecidableEq ι]
    {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (hindep : HTGeometry.RationallyIndependentSequence omega)
    {G : ℝ → C(ℂ, ℂ)} (hG : Continuous G)
    (hasym : Tendsto (fun t => (bohrHullMap a omega h (circlePhaseFlow omega t), G t))
      (Filter.cocompact ℝ) (uniformity C(ℂ, ℂ))) :
    closure (Set.range G) = Set.range G ∪ Set.range (bohrHullMap a omega h) :=
  closure_range_eq_union_range (continuous_bohrHullMap h) hG
    (dense_forwardOrbit_circlePhaseFlow hindep) hasym

end

end GaloisForLFunctions
