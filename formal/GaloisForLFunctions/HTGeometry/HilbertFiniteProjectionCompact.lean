import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! Finite Hilbert-basis projections converge uniformly on compact sets. -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (b : HilbertBasis ι ℂ E)

def hilbertFiniteProjection (s : Finset ι) : E →L[ℂ] E :=
  ∑ i ∈ s, (innerSL ℂ (b i)).smulRight (b i)

theorem hilbertFiniteProjection_apply (s : Finset ι) (x : E) :
    hilbertFiniteProjection b s x = ∑ i ∈ s, inner ℂ (b i) x • b i := by
  simp [hilbertFiniteProjection]

theorem hilbertFiniteProjection_norm_le (s : Finset ι) (x : E) :
    ‖hilbertFiniteProjection b s x‖ ≤ ‖x‖ := by
  have he : inner ℂ (hilbertFiniteProjection b s x) (hilbertFiniteProjection b s x) =
      inner ℂ (hilbertFiniteProjection b s x) x := by
    simp only [hilbertFiniteProjection_apply,sum_inner,inner_smul_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [b.orthonormal.inner_right_sum _ hi]
  have hh := re_inner_le_norm (𝕜 := ℂ) (hilbertFiniteProjection b s x) x
  rw [← he,inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (hilbertFiniteProjection b s x),norm_nonneg x]

theorem hilbertFiniteProjection_tendsto (x : E) :
    Tendsto (fun s : Finset ι => hilbertFiniteProjection b s x) atTop (𝓝 x) := by
  simpa only [HasSum,hilbertFiniteProjection_apply,b.repr_apply_apply,
    SummationFilter.unconditional] using b.hasSum_repr x

theorem hilbertFiniteProjection_uniformEquicontinuous :
    UniformEquicontinuous (fun s : Finset ι => fun x => hilbertFiniteProjection b s x) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  refine ⟨ε,hε,?_⟩
  intro x y hxy s
  simp only [dist_eq_norm,← map_sub] at hxy ⊢
  exact (hilbertFiniteProjection_norm_le b s (x-y)).trans_lt hxy

theorem hilbertFiniteProjection_uniformOn_compact (K : Set E) (hK : IsCompact K) :
    TendstoUniformlyOn (fun s : Finset ι => fun x => hilbertFiniteProjection b s x)
      (fun x => x) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : UniformEquicontinuous (fun s : Finset ι => fun x : K =>
      hilbertFiniteProjection b s (x:E)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε,hε,?_⟩
    intro x y hxy s
    rw [dist_eq_norm,← map_sub]
    change dist (x:E) (y:E) < ε at hxy
    rw [dist_eq_norm] at hxy
    exact (hilbertFiniteProjection_norm_le b s ((x:E)-(y:E))).trans_lt hxy
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (he.equicontinuous.tendsto_uniformFun_iff_pi atTop (fun x : K => (x:E))).mpr
  exact tendsto_pi_nhds.mpr (fun x => hilbertFiniteProjection_tendsto b x)

end
end GaloisForLFunctions.HTGeometry
