import GaloisForLFunctions.HTGeometry.ContinuousAnalyticRoot
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Topology Set Function Filter
open scoped Manifold ContDiff

namespace GaloisForLFunctions.HTGeometry

/-- An open complex coordinate in which a projection is an affine positive power. -/
structure ComplexPowerChart {M : Type*} [TopologicalSpace M] (p : M → ℂ) where
  chart : OpenPartialHomeomorph M ℂ
  degree : ℕ
  positive : 0 < degree
  offset : ℂ
  scale : ℂ
  scale_ne_zero : scale ≠ 0
  projection : ∀ x ∈ chart.source, p x = offset + scale * (chart x) ^ degree

namespace ComplexPowerChart

variable {M : Type*} [TopologicalSpace M] {p : M → ℂ}

/-- All overlaps of power coordinates are analytic, including overlaps containing zeros. -/
theorem analyticOnNhd_transition (c d : ComplexPowerChart p) :
    AnalyticOnNhd ℂ (c.chart.symm.trans d.chart) (c.chart.symm.trans d.chart).source := by
  let f : ℂ → ℂ := fun z => (c.offset + c.scale * z ^ c.degree - d.offset) / d.scale
  have hf : AnalyticOnNhd ℂ f (c.chart.symm.trans d.chart).source := fun z _ =>
    ((analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow c.degree))).sub
      analyticAt_const).div analyticAt_const d.scale_ne_zero
  apply analyticOnNhd_of_continuousOn_pow_eq_allowing_zeros
    (c.chart.symm.trans d.chart).open_source d.positive hf
    (c.chart.symm.trans d.chart).continuousOn
  intro z hz
  have hc := c.projection (c.chart.symm z) (c.chart.map_target hz.1)
  rw [c.chart.right_inv hz.1] at hc
  have hd := d.projection (c.chart.symm z) hz.2
  rw [hc] at hd
  change (d.chart (c.chart.symm z)) ^ d.degree = _
  apply (eq_div_iff d.scale_ne_zero).mpr
  linear_combination -hd

/-- A covering family of power coordinates defines a charted space on its existing topology. -/
noncomputable abbrev chartedSpace {ι : Type*} (c : ι → ComplexPowerChart p)
    (hcover : ∀ x, ∃ i, x ∈ (c i).chart.source) : ChartedSpace ℂ M where
  atlas := range (fun i => (c i).chart)
  chartAt x := (c (Classical.choose (hcover x))).chart
  mem_chart_source x := Classical.choose_spec (hcover x)
  chart_mem_atlas _x := mem_range_self _

/-- The power-coordinate atlas is a complex analytic one-manifold. -/
theorem isManifold {ι : Type*} (c : ι → ComplexPowerChart p)
    (hcover : ∀ x, ∃ i, x ∈ (c i).chart.source) :
    letI := chartedSpace c hcover
    IsManifold 𝓘(ℂ, ℂ) ω M := by
  letI := chartedSpace c hcover
  apply isManifold_of_contDiffOn 𝓘(ℂ, ℂ) ω M
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [mfld_simps] using ((c i).analyticOnNhd_transition (c j)).contDiffOn
    ((c i).chart.symm.trans (c j).chart).open_source.uniqueDiffOn (n := ω)

/-- A continuous lift is analytic in every power coordinate when its projection is analytic. -/
theorem analyticAt_coordinate_of_continuous_lift (c : ComplexPowerChart p)
    {g : ℂ → M} {a : ℂ} (hg : Continuous g) (hga : g a ∈ c.chart.source)
    (hf : AnalyticAt ℂ (p ∘ g) a) : AnalyticAt ℂ (c.chart ∘ g) a := by
  have hn : ∀ᶠ z in 𝓝 a, g z ∈ c.chart.source :=
    hg.continuousAt.eventually_mem (c.chart.open_source.mem_nhds hga)
  apply analyticAt_of_eventually_continuousAt_pow_eq c.positive
    ((hf.sub analyticAt_const).div analyticAt_const c.scale_ne_zero)
  · filter_upwards [hn] with z hz
    exact (c.chart.continuousOn.continuousAt (c.chart.open_source.mem_nhds hz)).comp
      hg.continuousAt
  · filter_upwards [hn] with z hz
    change c.chart (g z) ^ c.degree = (p (g z) - c.offset) / c.scale
    apply (eq_div_iff c.scale_ne_zero).mpr
    have he := c.projection (g z) hz
    linear_combination -he

/-- The projection is analytic when read in any power coordinate. -/
theorem analyticOnNhd_projection (c : ComplexPowerChart p) :
    AnalyticOnNhd ℂ (p ∘ c.chart.symm) c.chart.target := by
  intro z hz
  apply (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow c.degree))).congr
  filter_upwards [c.chart.open_target.mem_nhds hz] with w hw
  have he := c.projection (c.chart.symm w) (c.chart.map_target hw)
  rw [c.chart.right_inv hw] at he
  exact he.symm

/-- A continuous power projection is an analytic map of the resulting complex manifold. -/
theorem contMDiff_projection {ι : Type*} (c : ι → ComplexPowerChart p)
    (hcover : ∀ x, ∃ i, x ∈ (c i).chart.source) (hp : Continuous p) :
    letI := chartedSpace c hcover
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p := by
  letI := chartedSpace c hcover
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨hp.continuousAt, ?_⟩
  let i := Classical.choose (hcover x)
  have hx : x ∈ (c i).chart.source := Classical.choose_spec (hcover x)
  have ha := (c i).analyticOnNhd_projection ((c i).chart x) ((c i).chart.map_source hx)
  simp only [extChartAt, OpenPartialHomeomorph.extend, mfld_simps]
  change ContDiffWithinAt ℂ ω (p ∘ (c i).chart.symm) univ ((c i).chart x)
  exact ha.contDiffAt.contDiffWithinAt

/-- Analyticity of the projection upgrades any continuous complex lift to an analytic map. -/
theorem contMDiff_lift {ι : Type*} (c : ι → ComplexPowerChart p)
    (hcover : ∀ x, ∃ i, x ∈ (c i).chart.source)
    {g : ℂ → M} (hg : Continuous g) (hf : ∀ z, AnalyticAt ℂ (p ∘ g) z) :
    letI := chartedSpace c hcover
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g := by
  letI := chartedSpace c hcover
  intro a
  apply contMDiffAt_iff.mpr
  refine ⟨hg.continuousAt, ?_⟩
  let i := Classical.choose (hcover (g a))
  have ha := (c i).analyticAt_coordinate_of_continuous_lift hg
    (Classical.choose_spec (hcover (g a))) (hf a)
  simp only [extChartAt, OpenPartialHomeomorph.extend, mfld_simps]
  change ContDiffWithinAt ℂ ω ((c i).chart ∘ g) univ a
  exact ha.contDiffAt.contDiffWithinAt

end ComplexPowerChart
end GaloisForLFunctions.HTGeometry
