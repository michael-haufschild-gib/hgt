import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

private def integralDifferenceLinearMap
    (μ ν : ProbabilityMeasure X) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f :=
    (∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X)
  map_add' f g := by
    have hfμ : Integrable (fun x => f x) (μ : Measure X) :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hgμ : Integrable (fun x => g x) (μ : Measure X) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfν : Integrable (fun x => f x) (ν : Measure X) :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hgν : Integrable (fun x => g x) (ν : Measure X) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
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
  have hμ : ‖∫ x, f x ∂(μ : Measure X)‖ ≤ ‖f‖ := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := (μ : Measure X))
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
  have hν : ‖∫ x, f x ∂(ν : Measure X)‖ ≤ ‖f‖ := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := (ν : Measure X))
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
  change ‖(∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X)‖ ≤ 2 * ‖f‖
  calc
    _ ≤ ‖∫ x, f x ∂(μ : Measure X)‖ + ‖∫ x, f x ∂(ν : Measure X)‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add hμ hν
    _ = 2 * ‖f‖ := by ring

private def integralDifference
    (μ ν : ProbabilityMeasure X) : C(X, ℂ) →L[ℂ] ℂ :=
  (integralDifferenceLinearMap μ ν).mkContinuous 2
    (norm_integralDifferenceLinearMap_le μ ν)

theorem probabilityMeasure_ext_of_denseSpan_integral_eq
    (F : Set C(X, ℂ))
    (hF : (Submodule.span ℂ F).topologicalClosure = ⊤)
    (μ ν : ProbabilityMeasure X)
    (h : ∀ f ∈ F,
      (∫ x, f x ∂(μ : Measure X)) = ∫ x, f x ∂(ν : Measure X)) :
    μ = ν := by
  let L := integralDifference μ ν
  have hspan : Submodule.span ℂ F ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    intro f hf
    change (∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X) = 0
    rw [h f hf, sub_self]
  have hclosure : (Submodule.span ℂ F).topologicalClosure ≤ L.toLinearMap.ker :=
    Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [hF] at hclosure
  have hzero (f : C(X, ℂ)) : L f = 0 := hclosure Submodule.mem_top
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(X, ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hz := hzero fc
  have hfcμ : Integrable (fun x => (f x : ℂ)) (μ : Measure X) :=
    fc.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfcν : Integrable (fun x => (f x : ℂ)) (ν : Measure X) :=
    fc.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, (f x : ℂ) ∂(μ : Measure X)) - ∫ x, (f x : ℂ) ∂(ν : Measure X) = 0 at hz
  have hre := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.zero_re] at hre
  have hμ : (∫ x, (f x : ℂ) ∂(μ : Measure X)).re = ∫ x, f x ∂(μ : Measure X) := by
    simpa using (integral_re hfcμ).symm
  have hν : (∫ x, (f x : ℂ) ∂(ν : Measure X)).re = ∫ x, f x ∂(ν : Measure X) := by
    simpa using (integral_re hfcν).symm
  rw [hμ, hν] at hre
  exact sub_eq_zero.mp hre

theorem probabilityMeasure_tendsto_of_denseSpan_integral_tendsto
    {α : Type*}
    {l : Filter α}
    (F : Set C(X, ℂ))
    (hF : (Submodule.span ℂ F).topologicalClosure = ⊤)
    (μs : α → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (h : ∀ f ∈ F,
      Tendsto (fun a => ∫ x, f x ∂(μs a : Measure X)) l
        (𝓝 (∫ x, f x ∂(μ : Measure X)))) :
    Tendsto μs l (𝓝 μ) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  apply probabilityMeasure_ext_of_denseSpan_integral_eq F hF
  intro f hf
  let J : ProbabilityMeasure X → ℂ := fun ρ => ∫ x, f x ∂(ρ : Measure X)
  have hcluster : MapClusterPt (J ν) l (J ∘ μs) :=
    hν.continuousAt_comp
      (continuous_integral_complex_continuousMap_infinite f).continuousAt
  have ht : Tendsto (J ∘ μs) l (𝓝 (J μ)) := by
    simpa [J, Function.comp_def] using h f hf
  exact eq_of_mapClusterPt_of_tendsto_infinite hcluster ht

end

end GaloisForLFunctions.HTGeometry
