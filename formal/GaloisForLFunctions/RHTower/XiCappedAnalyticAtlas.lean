import GaloisForLFunctions.RHTower.XiSimplyConnectedCappedFactorization
import GaloisForLFunctions.HTGeometry.ComplexPowerAtlas

open Topology Set Function Filter
open scoped UpperHalfPlane Manifold ContDiff

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

noncomputable section

variable (H : Subgroup (coveringDeckGroup markedUniversalCover))

/-- The old covering projection, viewed in the ambient complex plane, is locally a homeomorphism. -/
theorem markedImageComplexProjection_isLocalHomeomorph :
    IsLocalHomeomorph (fun y : MarkedImageCover H => (markedImageProjection H y : ℂ)) :=
  isOpen_target.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
    (isCoveringMap_markedImageProjection H).isLocalHomeomorph

private def oldEmbeddingChart : OpenPartialHomeomorph (MarkedImageCover H) (CappedMarkedCover H) :=
  (finitePeripheralCapData H).isOpenEmbedding_old.toOpenPartialHomeomorph
    (finitePeripheralCapData H).old

private def capEmbeddingChart (i : FinitePeripheralIndex H) :
    OpenPartialHomeomorph UnitCapDisk (CappedMarkedCover H) :=
  ((finitePeripheralCapData H).isOpenEmbedding_cap i).toOpenPartialHomeomorph
    ((finitePeripheralCapData H).cap i)

private def diskEmbeddingChart : OpenPartialHomeomorph UnitCapDisk ℂ :=
  (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    Subtype.val

/-- An old sheet has degree-one power coordinate equal to the completed projection. -/
def cappedOldPowerChart (y : MarkedImageCover H) : ComplexPowerChart (cappedMarkedProjection H) where
  chart := (oldEmbeddingChart H).symm.trans
    ((markedImageComplexProjection_isLocalHomeomorph H).localInverseAt y).symm
  degree := 1
  positive := by norm_num
  offset := 0
  scale := 1
  scale_ne_zero := one_ne_zero
  projection x hx := by
    have hr := (oldEmbeddingChart H).right_inv hx.1
    change (finitePeripheralCapData H).old ((oldEmbeddingChart H).symm x) = x at hr
    have he := congrArg (cappedMarkedProjection H) hr
    simpa only [OpenPartialHomeomorph.trans_apply,
      IsLocalHomeomorph.localInverseAt_symm, cappedMarkedProjection_old,
      pow_one, one_mul, zero_add] using he.symm

/-- Each attached disk is a power coordinate for its exact ramified projection. -/
def cappedCapPowerChart (i : FinitePeripheralIndex H) : ComplexPowerChart (cappedMarkedProjection H) where
  chart := (capEmbeddingChart H i).symm.trans diskEmbeddingChart
  degree := (chosenPeripheralPowerChart H i).degree
  positive := (chosenPeripheralPowerChart H i).positive
  offset := peripheralCenter i.val.1
  scale := 1 / 4
  scale_ne_zero := by norm_num
  projection x hx := by
    have hr := (capEmbeddingChart H i).right_inv hx.1
    change (finitePeripheralCapData H).cap i ((capEmbeddingChart H i).symm x) = x at hr
    have he := congrArg (cappedMarkedProjection H) hr
    rw [cappedMarkedProjection_cap] at he
    change cappedMarkedProjection H x = peripheralCenter i.val.1 +
      (1 / 4 : ℂ) * (((capEmbeddingChart H i).symm x : UnitCapDisk) : ℂ) ^
        (chosenPeripheralPowerChart H i).degree
    rw [← he]
    ring

def cappedPowerCharts : MarkedImageCover H ⊕ FinitePeripheralIndex H →
    ComplexPowerChart (cappedMarkedProjection H) :=
  Sum.elim (cappedOldPowerChart H) (cappedCapPowerChart H)

/-- The actual power-coordinate domains cover every point of the completion. -/
theorem cappedPowerCharts_cover (x : CappedMarkedCover H) :
    ∃ i, x ∈ (cappedPowerCharts H i).chart.source := by
  rcases x with y | i
  · refine ⟨Sum.inl y, ?_⟩
    change (finitePeripheralCapData H).old y ∈
      ((oldEmbeddingChart H).symm.trans
        ((markedImageComplexProjection_isLocalHomeomorph H).localInverseAt y).symm).source
    refine ⟨(oldEmbeddingChart H).map_source (mem_univ y), ?_⟩
    have he := (finitePeripheralCapData H).isOpenEmbedding_old.toOpenPartialHomeomorph_left_inv
      (finitePeripheralCapData H).old (x := y)
    change (oldEmbeddingChart H).symm ((finitePeripheralCapData H).old y) = y at he
    change (oldEmbeddingChart H).symm ((finitePeripheralCapData H).old y) ∈
      ((markedImageComplexProjection_isLocalHomeomorph H).localInverseAt y).target
    rw [he]
    exact (markedImageComplexProjection_isLocalHomeomorph H).self_mem_localInverseAt_target
  · refine ⟨Sum.inr i, ?_⟩
    change (finitePeripheralCapData H).point i ∈
      ((capEmbeddingChart H i).symm.trans diskEmbeddingChart).source
    refine ⟨?_, mem_univ _⟩
    change (finitePeripheralCapData H).point i ∈ (capEmbeddingChart H i).target
    rw [← (finitePeripheralCapData H).cap_center i]
    exact (capEmbeddingChart H i).map_source (mem_univ _)

/-- The analytic atlas is built on the previously constructed Hausdorff topology. -/
instance cappedMarkedCoverChartedSpace : ChartedSpace ℂ (CappedMarkedCover H) :=
  ComplexPowerChart.chartedSpace (cappedPowerCharts H) (cappedPowerCharts_cover H)

/-- Every completed marked image cover is a complex analytic one-manifold. -/
instance cappedMarkedCoverIsManifold : IsManifold 𝓘(ℂ, ℂ) ω (CappedMarkedCover H) :=
  ComplexPowerChart.isManifold (cappedPowerCharts H) (cappedPowerCharts_cover H)

/-- The completed covering projection is an analytic map in its constructed atlas. -/
theorem contMDiff_cappedMarkedProjection :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (cappedMarkedProjection H) :=
  ComplexPowerChart.contMDiff_projection (cappedPowerCharts H) (cappedPowerCharts_cover H)
    (continuous_cappedMarkedProjection H)

/-- Every continuous actual Xi lift into the completion is analytic. -/
theorem contMDiff_cappedXiLift (G : C(ℂ, CappedMarkedCover H))
    (hG : ∀ z, cappedMarkedProjection H (G z) = xi z) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G := by
  apply ComplexPowerChart.contMDiff_lift (cappedPowerCharts H) (cappedPowerCharts_cover H)
    G.continuous
  have he : cappedMarkedProjection H ∘ G = xi := funext hG
  intro z
  rw [he]
  exact xi_differentiable.analyticAt z

/-- The completed cover is noncompact because its projection contains the unbounded old target. -/
instance cappedMarkedCoverNoncompactSpace : NoncompactSpace (CappedMarkedCover H) where
  noncompact_univ := by
    intro hc
    obtain ⟨R, hRp, hR⟩ := (hc.image (continuous_cappedMarkedProjection H)).isBounded.exists_pos_norm_le
    let z : Target := ⟨((R + 1 : ℝ) : ℂ), by
      constructor
      · exact_mod_cast (ne_of_gt (by linarith : 0 < R + 1))
      · exact_mod_cast (by linarith : R + 1 ≠ -1)⟩
    obtain ⟨w, hw⟩ := markedUniversalCover_surjective z
    let y : MarkedImageCover H := Quotient.mk (MulAction.orbitRel H ℍ) w
    have hp : cappedMarkedProjection H ((finitePeripheralCapData H).old y) = ((R + 1 : ℝ) : ℂ) :=
      congrArg Subtype.val hw
    have hb := hR _ ⟨(finitePeripheralCapData H).old y, mem_univ _, rfl⟩
    rw [hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)] at hb
    linarith

/-- Actual Xi has an analytic factorization through its simply connected completed image cover.
Both analytic maps, the complex atlas and simple connectedness are constructed unconditionally. -/
theorem xi_analytic_simplyConnected_capped_factorization :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      SimplyConnectedSpace (CappedMarkedCover H) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (cappedMarkedProjection H) ∧
      ∃ G : C(ℂ, CappedMarkedCover H),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G ∧
        ∀ z, cappedMarkedProjection H (G z) = xi z := by
  obtain ⟨H, hs, G, hG⟩ := xi_simplyConnected_capped_factorization
  exact ⟨H, hs, contMDiff_cappedMarkedProjection H, G, contMDiff_cappedXiLift H G hG, hG⟩

end
end RHTower.XiMarkedMonodromy
