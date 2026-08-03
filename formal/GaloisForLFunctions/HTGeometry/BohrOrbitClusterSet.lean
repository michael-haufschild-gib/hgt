import GaloisForLFunctions.HTGeometry.OuterCauchyOrbitBoundary

/-!
# The boundary is exactly the cluster set at infinity

Every tail of a flow with dense forward tails is still dense, so an orbit asymptotic to a continuous
family accumulates on the whole family arbitrarily late.  Together with the converse inclusion this
identifies the boundary family with the set of cluster points of the orbit at infinity.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- **Asymptotic orbits reach every parameter arbitrarily late.**  The parameter is approached by
orbit points with times beyond any prescribed bound. -/
theorem mem_closure_image_tail_of_dense_tails {T Y : Type*} [TopologicalSpace T] [UniformSpace Y]
    {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (htails : ∀ T₀ : ℝ, Dense {x : T | ∃ t : ℝ, T₀ ≤ t ∧ θ t = x})
    (hasym : ∀ V ∈ uniformity Y, ∀ᶠ t in atTop, (α (θ t), G t) ∈ V)
    (T₁ : ℝ) (x : T) : α x ∈ closure (G '' {t : ℝ | T₁ ≤ t}) := by
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
    (dense_iff_inter_open.mp (htails (max T₀ T₁))) U hUopen ⟨x, hxU⟩
  obtain ⟨t, htT, rfl⟩ := hyorbit
  rw [hU] at hyU
  have hmem : θ t ∈ α ⁻¹' UniformSpace.ball (α x) W := interior_subset hyU
  have hGt : (α x, G t) ∈ V :=
    hWV ⟨α (θ t), hmem, hT₀ t (le_trans (le_max_left _ _) htT)⟩
  exact ⟨G t, hVN hGt, ⟨t, le_trans (le_max_right _ _) htT, rfl⟩⟩

/-- **Every boundary point is a cluster point at infinity.** -/
theorem range_subset_clusterAtInfinity {T Y : Type*} [TopologicalSpace T] [UniformSpace Y]
    {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (htails : ∀ T₀ : ℝ, Dense {x : T | ∃ t : ℝ, T₀ ≤ t ∧ θ t = x})
    (hasym : ∀ V ∈ uniformity Y, ∀ᶠ t in atTop, (α (θ t), G t) ∈ V) :
    Set.range α ⊆ ⋂ M : ℝ, closure (G '' {t : ℝ | M < |t|}) := by
  rintro - ⟨x, rfl⟩
  refine Set.mem_iInter.mpr fun M => ?_
  refine closure_mono (Set.image_mono ?_)
    (mem_closure_image_tail_of_dense_tails hα htails hasym (M + 1) x)
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  calc M < t := by linarith
    _ ≤ |t| := le_abs_self t

/-- **The cluster set at infinity is exactly the boundary family.**  This is claim (5). -/
theorem clusterAtInfinity_eq_range {T Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [UniformSpace Y] [T2Space Y] {α : T → Y} {θ : ℝ → T} {G : ℝ → Y} (hα : Continuous α)
    (htails : ∀ T₀ : ℝ, Dense {x : T | ∃ t : ℝ, T₀ ≤ t ∧ θ t = x})
    (hasym : Tendsto (fun t => (α (θ t), G t)) (Filter.cocompact ℝ) (uniformity Y)) :
    (⋂ M : ℝ, closure (G '' {t : ℝ | M < |t|})) = Set.range α := by
  have hatTop : (Filter.atTop : Filter ℝ) ≤ Filter.cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  refine Set.Subset.antisymm
    (fun y hy => clusterAtInfinity_subset_range hα hasym (Set.mem_iInter.mp hy)) ?_
  exact range_subset_clusterAtInfinity hα htails fun V hV => hatTop (hasym hV)

/-- **The cluster set of a perturbed orbit is its boundary family.** -/
theorem clusterAtInfinity_perturbedOrbit_eq {a : ι → ℂ} {omega : ι → ℝ}
    [Countable ι] [DecidableEq ι] (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) {c eps : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K) :
    (⋂ M : ℝ, closure ((perturbedOrbit h S hS eps) '' {t : ℝ | M < |t|}))
      = Set.range (perturbedBoundary h c eps) :=
  clusterAtInfinity_eq_range (continuous_perturbedBoundary h c eps)
    (dense_forwardOrbit_circlePhaseFlow hindep)
    (tendsto_uniformity_perturbedOrbit h hS hcollapse)

/-- **Claim (5) for the card's own orbit.** -/
theorem clusterAtInfinity_outerCauchyOrbit_eq [Countable ι] [DecidableEq ι] (ν : Measure ℝ)
    [IsFiniteMeasure ν] {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) (eps : ℂ) :
    (⋂ M : ℝ, closure ((perturbedOrbit h (outerBackground ν)
        (continuousOn_outerBackground ν) eps) '' {t : ℝ | M < |t|}))
      = Set.range (perturbedBoundary h (Complex.exp (-1)) eps) :=
  clusterAtInfinity_perturbedOrbit_eq h hindep (continuousOn_outerBackground ν)
    fun _ hK hKH => tendstoUniformlyOn_outerBackground_translate ν hK hKH

end

end GaloisForLFunctions
