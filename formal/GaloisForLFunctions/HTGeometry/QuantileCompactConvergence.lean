import GaloisForLFunctions.HTGeometry.QuantileCoupling

/-! Compact convergence of quantiles from pointwise CDF convergence and a strictly increasing
limit CDF. Finite open brackets handle discontinuous atomic quantiles. -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem quantile_mem_Ioc_of_cdf_bracket (μ : Measure ℝ) {p a b : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : cdf μ a < p) (hb : p ≤ cdf μ b) :
    quantile μ p ∈ Ioc a b := by
  refine ⟨?_, (quantile_le_iff hp.1 hp.2).mpr hb⟩
  by_contra h
  exact (not_le.mpr ha) ((quantile_le_iff hp.1 hp.2).mp (not_lt.mp h))

theorem tendstoUniformlyOn_quantile_of_tendsto_cdf {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (hcdf : ∀ x : ℝ, Tendsto (fun i => cdf (μ i) x) l (𝓝 (cdf ν x)))
    (hstrict : StrictMono (cdf ν)) {K : Set ℝ} (hK : IsCompact K)
    (hinterior : K ⊆ Ioo (0 : ℝ) 1) :
    TendstoUniformlyOn (fun i p => quantile (μ i) p) (quantile ν) l K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let lower (p : K) := quantile ν p.val - ε / 4
  let upper (p : K) := quantile ν p.val + ε / 4
  have hlo (p : K) : cdf ν (lower p) < p.val := by
    by_contra h
    have hq := (quantile_le_iff (hinterior p.property).1
      (hinterior p.property).2).mpr (le_of_not_gt h)
    dsimp [lower] at hq
    linarith
  have hhi (p : K) : p.val < cdf ν (upper p) := by
    exact (le_cdf_quantile (hinterior p.property).1 (hinterior p.property).2).trans_lt
      (hstrict (by dsimp [upper]; linarith))
  let left (p : K) := (cdf ν (lower p) + p.val) / 2
  let right (p : K) := (p.val + cdf ν (upper p)) / 2
  let U (p : K) := Ioo (left p) (right p)
  have hleft (p : K) : cdf ν (lower p) < left p ∧ left p < p.val := by
    dsimp [left]
    constructor <;> linarith [hlo p]
  have hright (p : K) : p.val < right p ∧ right p < cdf ν (upper p) := by
    dsimp [right]
    constructor <;> linarith [hhi p]
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => isOpen_Ioo) (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, (hleft ⟨p, hp⟩).2, (hright ⟨p, hp⟩).1⟩)
  have hevent (p : K) : ∀ᶠ i in l,
      cdf (μ i) (lower p) < left p ∧ right p < cdf (μ i) (upper p) := by
    filter_upwards [(hcdf (lower p)).eventually (eventually_lt_nhds (hleft p).1),
      (hcdf (upper p)).eventually (eventually_gt_nhds (hright p).2)] with i hi hj
    exact ⟨hi, hj⟩
  have hall : ∀ᶠ i in l, ∀ p ∈ s,
      cdf (μ i) (lower p) < left p ∧ right p < cdf (μ i) (upper p) :=
    (Finset.eventually_all s).mpr fun p _ => hevent p
  filter_upwards [hall] with i hi p hp
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hs hp)
  obtain ⟨hcs, hpc⟩ := mem_iUnion.mp hc
  have hμ := quantile_mem_Ioc_of_cdf_bracket (μ i) (hinterior hp)
    ((hi c hcs).1.trans hpc.1) (hpc.2.trans (hi c hcs).2).le
  have hν := quantile_mem_Ioc_of_cdf_bracket ν (hinterior hp)
    ((hleft c).1.trans hpc.1) (hpc.2.trans (hright c).2).le
  dsimp [lower, upper] at hμ hν
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hμ.1, hμ.2, hν.1, hν.2]

end

end GaloisForLFunctions.HTGeometry
