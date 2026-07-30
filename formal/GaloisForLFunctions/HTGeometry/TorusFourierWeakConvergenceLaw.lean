import Mathlib

/-!
# Weak convergence from all finite-torus characters

On a finite-dimensional compact torus, convergence of every Fourier
character integral forces weak convergence of the complete probability
measure.  No candidate limit measure must be supplied: compactness produces
a cluster measure, Fourier density makes that cluster measure unique, and a
unique cluster point forces convergence.
-/

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Integration of a complex continuous function depends continuously on
a probability measure over a compact space. -/
theorem continuous_integral_complex_continuousMap
    (f : C(X, ℂ)) :
    Continuous
      (fun μ : ProbabilityMeasure X =>
        ∫ x, f x ∂(μ : Measure X)) := by
  rw [continuous_iff_continuousAt]
  intro μ
  have hid :
      Tendsto (fun ν : ProbabilityMeasure X => ν) (𝓝 μ) (𝓝 μ) :=
    tendsto_id
  have hall :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
      hid
  let fb : X →ᵇ ℂ :=
    ContinuousMap.equivBoundedOfCompact X ℂ f
  change
    Tendsto
      (fun ν : ProbabilityMeasure X =>
        ∫ x, f x ∂(ν : Measure X))
      (𝓝 μ)
      (𝓝 (∫ x, f x ∂(μ : Measure X)))
  simpa [fb] using hall fb

/-- A convergent map and one of its map-cluster points have the same
Hausdorff limit. -/
theorem eq_of_mapClusterPt_of_tendsto
    {α Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {l : Filter α} {u : α → Y} {x y : Y}
    (hx : MapClusterPt x l u)
    (hy : Tendsto u l (𝓝 y)) :
    x = y := by
  by_contra hxy
  have hd : Disjoint (𝓝 x) (𝓝 y) :=
    disjoint_nhds_nhds.mpr hxy
  have hle :
      𝓝 x ⊓ map u l ≤ 𝓝 x ⊓ 𝓝 y :=
    inf_le_inf_left _ hy
  have hne : (𝓝 x ⊓ map u l).NeBot := hx
  have hne' : (𝓝 x ⊓ 𝓝 y).NeBot :=
    hne.mono hle
  exact hne'.ne hd.eq_bot

private def integralDifferenceLinearMap
    (μ ν : ProbabilityMeasure X) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    (∫ x, f x ∂(μ : Measure X)) -
      ∫ x, f x ∂(ν : Measure X)
  map_add' f g := by
    have hfμ : Integrable (fun x => f x) (μ : Measure X) :=
      f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgμ : Integrable (fun x => g x) (μ : Measure X) :=
      g.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hfν : Integrable (fun x => f x) (ν : Measure X) :=
      f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgν : Integrable (fun x => g x) (ν : Measure X) :=
      g.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [ContinuousMap.add_apply]
    rw [integral_add hfμ hgμ, integral_add hfν hgν]
    ring
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply]
    rw [integral_smul, integral_smul]
    simp only [RingHom.id_apply]
    ring

private theorem norm_integralDifferenceLinearMap_le
    (μ ν : ProbabilityMeasure X) (f : C(X, ℂ)) :
    ‖integralDifferenceLinearMap μ ν f‖ ≤ 2 * ‖f‖ := by
  have hμ :
      ‖∫ x, f x ∂(μ : Measure X)‖ ≤ ‖f‖ := by
    have h :=
      norm_integral_le_of_norm_le_const
        (μ := (μ : Measure X))
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    simpa using h
  have hν :
      ‖∫ x, f x ∂(ν : Measure X)‖ ≤ ‖f‖ := by
    have h :=
      norm_integral_le_of_norm_le_const
        (μ := (ν : Measure X))
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
    simpa using h
  change
    ‖(∫ x, f x ∂(μ : Measure X)) -
        ∫ x, f x ∂(ν : Measure X)‖ ≤ 2 * ‖f‖
  calc
    ‖(∫ x, f x ∂(μ : Measure X)) -
        ∫ x, f x ∂(ν : Measure X)‖
        ≤ ‖∫ x, f x ∂(μ : Measure X)‖ +
          ‖∫ x, f x ∂(ν : Measure X)‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add hμ hν
    _ = 2 * ‖f‖ := by ring

private def integralDifference
    (μ ν : ProbabilityMeasure X) : C(X, ℂ) →L[ℂ] ℂ :=
  (integralDifferenceLinearMap μ ν).mkContinuous 2
    (norm_integralDifferenceLinearMap_le μ ν)

/-- Probability measures on a finite torus are determined by all Fourier
character integrals. -/
theorem probabilityMeasure_ext_of_mFourier_integral_eq
    {d : Type*} [Fintype d]
    (μ ν : ProbabilityMeasure (UnitAddTorus d))
    (h : ∀ n : d → ℤ,
      (∫ x, UnitAddTorus.mFourier n x
        ∂(μ : Measure (UnitAddTorus d))) =
      ∫ x, UnitAddTorus.mFourier n x
        ∂(ν : Measure (UnitAddTorus d))) :
    μ = ν := by
  let L := integralDifference μ ν
  have hspan :
      Submodule.span ℂ (Set.range UnitAddTorus.mFourier) ≤
        L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    change
      (∫ x, UnitAddTorus.mFourier n x
          ∂(μ : Measure (UnitAddTorus d))) -
        ∫ x, UnitAddTorus.mFourier n x
          ∂(ν : Measure (UnitAddTorus d)) = 0
    rw [h n, sub_self]
  have hclosure :
      (Submodule.span ℂ
          (Set.range (UnitAddTorus.mFourier :
            (d → ℤ) → C(UnitAddTorus d, ℂ)))).topologicalClosure ≤
        L.toLinearMap.ker :=
    Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [UnitAddTorus.span_mFourier_closure_eq_top] at hclosure
  have hzero (f : C(UnitAddTorus d, ℂ)) : L f = 0 := by
    exact hclosure Submodule.mem_top
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(UnitAddTorus d, ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hz := hzero fc
  have hfcμ :
      Integrable (fun x => (f x : ℂ))
        (μ : Measure (UnitAddTorus d)) :=
    fc.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfcν :
      Integrable (fun x => (f x : ℂ))
        (ν : Measure (UnitAddTorus d)) :=
    fc.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change
    (∫ x, (f x : ℂ) ∂(μ : Measure (UnitAddTorus d))) -
      ∫ x, (f x : ℂ) ∂(ν : Measure (UnitAddTorus d)) = 0 at hz
  have hre := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.zero_re] at hre
  have hμ :
      (∫ x, (f x : ℂ)
        ∂(μ : Measure (UnitAddTorus d))).re =
          ∫ x, f x ∂(μ : Measure (UnitAddTorus d)) := by
    simpa using (integral_re hfcμ).symm
  have hν :
      (∫ x, (f x : ℂ)
        ∂(ν : Measure (UnitAddTorus d))).re =
          ∫ x, f x ∂(ν : Measure (UnitAddTorus d)) := by
    simpa using (integral_re hfcν).symm
  rw [hμ, hν] at hre
  exact sub_eq_zero.mp hre

/-- Convergence of all finite-torus Fourier integrals to those of a stated
measure forces weak convergence to that measure. -/
theorem probabilityMeasure_tendsto_of_mFourier_integral_tendsto
    {α d : Type*} [Fintype d]
    {l : Filter α}
    (μs : α → ProbabilityMeasure (UnitAddTorus d))
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (h : ∀ n : d → ℤ,
      Tendsto
        (fun a =>
          ∫ x, UnitAddTorus.mFourier n x
            ∂(μs a : Measure (UnitAddTorus d)))
        l
        (𝓝 (∫ x, UnitAddTorus.mFourier n x
          ∂(μ : Measure (UnitAddTorus d))))) :
    Tendsto μs l (𝓝 μ) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  apply probabilityMeasure_ext_of_mFourier_integral_eq
  intro n
  let F :
      ProbabilityMeasure (UnitAddTorus d) → ℂ :=
    fun ρ =>
      ∫ x, UnitAddTorus.mFourier n x
        ∂(ρ : Measure (UnitAddTorus d))
  have hcluster :
      MapClusterPt (F ν) l (F ∘ μs) :=
    hν.continuousAt_comp
      (continuous_integral_complex_continuousMap
        (UnitAddTorus.mFourier n)).continuousAt
  have ht :
      Tendsto (F ∘ μs) l (𝓝 (F μ)) := by
    simpa [F, Function.comp_def] using h n
  exact eq_of_mapClusterPt_of_tendsto hcluster ht

/-- **Complete Fourier-to-ensemble lift.** If every finite-torus Fourier
coefficient of a family of probability measures converges, then there is
one and only one probability measure with those coefficients, and the
whole family converges weakly to it. -/
theorem existsUnique_probabilityMeasure_tendsto_of_mFourier_limit
    {α d : Type*} [Fintype d]
    {l : Filter α} [l.NeBot]
    (μs : α → ProbabilityMeasure (UnitAddTorus d))
    (limit : (d → ℤ) → ℂ)
    (h : ∀ n : d → ℤ,
      Tendsto
        (fun a =>
          ∫ x, UnitAddTorus.mFourier n x
            ∂(μs a : Measure (UnitAddTorus d)))
        l (𝓝 (limit n))) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus d),
      Tendsto μs l (𝓝 μ) ∧
        ∀ n : d → ℤ,
          (∫ x, UnitAddTorus.mFourier n x
            ∂(μ : Measure (UnitAddTorus d))) = limit n := by
  obtain ⟨μ, hμcluster⟩ :=
    exists_clusterPt_of_compactSpace (map μs l)
  have hμmap : MapClusterPt μ l μs := hμcluster
  have hcoeff :
      ∀ n : d → ℤ,
        (∫ x, UnitAddTorus.mFourier n x
          ∂(μ : Measure (UnitAddTorus d))) = limit n := by
    intro n
    let F :
        ProbabilityMeasure (UnitAddTorus d) → ℂ :=
      fun ρ =>
        ∫ x, UnitAddTorus.mFourier n x
          ∂(ρ : Measure (UnitAddTorus d))
    have hcluster :
        MapClusterPt (F μ) l (F ∘ μs) :=
      hμmap.continuousAt_comp
        (continuous_integral_complex_continuousMap
          (UnitAddTorus.mFourier n)).continuousAt
    have ht :
        Tendsto (F ∘ μs) l (𝓝 (limit n)) := by
      simpa [F, Function.comp_def] using h n
    exact eq_of_mapClusterPt_of_tendsto hcluster ht
  have hconv : Tendsto μs l (𝓝 μ) := by
    apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto μs μ
    intro n
    simpa [hcoeff n] using h n
  refine ⟨μ, ⟨hconv, hcoeff⟩, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν.1 hconv

end

end GaloisForLFunctions.HTGeometry
