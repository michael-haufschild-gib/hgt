import GaloisForLFunctions.HTGeometry.BochnerL2HilbertTensor
import GaloisForLFunctions.HTGeometry.HilbertCompactJetApproximation
import GaloisForLFunctions.HTGeometry.CompactUniformL2Convergence

/-! Hilbert projections retain finite tensor structure and converge in the actual L² norm. -/
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {α E ι : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def liftL2Operator : (E →L[ℂ] E) →L[ℂ] Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (ContinuousLinearMap.id ℂ (E →L[ℂ] E)).compLpL₂ 2 μ

/-- A rank-one Hilbert projection becomes the actual scalar-vector L² tensor. -/
theorem rankOne_compLp (v : E) (f : Lp E 2 μ) :
    ((innerSL ℂ v).smulRight v).compLp f =
      bochnerL2Product ((innerSL ℂ v).compLp f) v := by
  apply Lp.ext
  filter_upwards [((innerSL ℂ v).smulRight v).coeFn_compLp f,
    (innerSL ℂ v).coeFn_compLp f,
    bochnerL2Product_ae ((innerSL ℂ v).compLp f) v] with t h0 h1 h2
  rw [h0,h2,h1]
  rfl

theorem hilbertFiniteProjection_compLp (b : HilbertBasis ι ℂ E) (s : Finset ι) (f : Lp E 2 μ) :
    (hilbertFiniteProjection b s).compLp f =
      ∑ i ∈ s, bochnerL2Product ((innerSL ℂ (b i)).compLp f) (b i) := by
  change liftL2Operator (hilbertFiniteProjection b s) f = _
  rw [hilbertFiniteProjection,map_sum]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact rankOne_compLp (b i) f

/-- The actual L² image of a continuous compactly supported Hilbert-valued family is recovered
in norm by finite Hilbert projections. -/
theorem hilbertFiniteProjection_compLp_tendsto [TopologicalSpace α] [BorelSpace α]
    [IsFiniteMeasureOnCompacts μ] (b : HilbertBasis ι ℂ E)
    (F : α → E) (hF : Continuous F) (hK : HasCompactSupport F) :
    Tendsto (fun s : Finset ι => (hilbertFiniteProjection b s).compLp
      ((hF.memLp_of_hasCompactSupport (p := 2) (μ := μ) hK).toLp F)) atTop
      (𝓝 ((hF.memLp_of_hasCompactSupport (p := 2) (μ := μ) hK).toLp F)) := by
  let hf := hF.memLp_of_hasCompactSupport (p := 2) (μ := μ) hK
  have hP (s : Finset ι) : MemLp (fun x => hilbertFiniteProjection b s (F x)) 2 μ :=
    (hilbertFiniteProjection b s).comp_memLp' hf
  have he (s : Finset ι) : (hilbertFiniteProjection b s).compLp (hf.toLp F) =
      (hP s).toLp (fun x => hilbertFiniteProjection b s (F x)) := by
    apply Lp.ext
    filter_upwards [(hilbertFiniteProjection b s).coeFn_compLp (hf.toLp F),hf.coeFn_toLp,
      (hP s).coeFn_toLp] with x h0 h1 h2
    rw [h0,h1,h2]
  change Tendsto (fun s => (hilbertFiniteProjection b s).compLp (hf.toLp F)) _ _
  simp_rw [he]
  apply toLp_tendsto_of_uniform_finite_support hP hf (isClosed_closure : IsClosed (tsupport F)).measurableSet hK.measure_lt_top.ne
  · intro s x hx
    rw [image_eq_zero_of_notMem_tsupport hx,map_zero]
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  · rw [← tendstoUniformlyOn_univ]
    apply ((hilbertFiniteProjection_uniformOn_compact b (range F) (hK.isCompact_range hF)).comp F).mono
    intro x _
    exact ⟨x,rfl⟩

end
end GaloisForLFunctions.HTGeometry
