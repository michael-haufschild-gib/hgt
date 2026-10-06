import GaloisForLFunctions.HTGeometry.ManifoldTopFormIntegral
import GaloisForLFunctions.HTGeometry.EuclideanCompactStokes

/-!
# Stokes' theorem on a closed oriented manifold

For a compact manifold `M` without boundary, oriented by `o`, and any `k`-form `α`,

`∫_M dα = 0`   (`topFormIntegral_exteriorDerivative_eq_zero`).

The proof is the standard reduction to Euclidean space.

* In a chart, `d` is the Euclidean exterior derivative of the chart representative
  (`formChartValue_exteriorDerivative`), so a form vanishing near a point has `dα = 0` there
  (`exteriorDerivative_apply_eq_zero`).
* Decompose `α = Σ_p ρ_p α` over a chart partition of unity; then `dα = Σ_p d(ρ_p α)`, and each
  `d(ρ_p α)` vanishes outside the support of `ρ_p`, so by locality its integral is a chart
  integral.
* In the chart the integrand is `sign · (dR)(b)` with the orientation sign locally constant on
  the chart target, hence it is `(dG)(b)` for the compactly supported smooth form
  `G = 1_T · sign · R`, whose integral vanishes by Euclidean Stokes
  (`chartIntegral_exteriorDerivative_eq_zero`).
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- In a chart, the exterior derivative is the Euclidean exterior derivative of the chart
representative. -/
theorem formChartValue_exteriorDerivative [I.Boundaryless] {k : ℕ}
    (β : DifferentialGeometry.DifferentialForm I M k) {p z : M}
    (hz : z ∈ (extChartAt I p).source) :
    formChartValue p (DifferentialGeometry.DifferentialForm.exteriorDerivative β) z =
      extDeriv (fun y => formChartValue p β ((extChartAt I p).symm y)) ((extChartAt I p) z) :=
  DifferentialGeometry.DifferentialForm.exteriorDerivative_localRepresentation β hz
    (BoundarylessManifold.isInteriorPoint (I := I) (M := M))

/-- A form is determined by any one of its chart values. -/
theorem eq_zero_of_formChartValue_eq_zero {k : ℕ}
    (β : DifferentialGeometry.DifferentialForm I M k) {p z : M}
    (hz : z ∈ (extChartAt I p).source) (h : formChartValue p β z = 0) : β z = 0 := by
  have hb := mem_baseSet_of_mem_extChartAt_source hz
  rw [formChartValue_eq] at h
  ext v
  have h1 := congrArg (fun L : E [⋀^Fin k]→L[ℝ] ℝ =>
    L (fun i => (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z (v i))) h
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h1
  have hv : (⇑((trivializationAt E (TangentSpace I) p).symmL ℝ z) ∘ fun i =>
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ z (v i)) = v := by
    funext i
    exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt hb (v i)
  rw [hv] at h1
  simpa using h1

/-- **Locality of `d`**: a form vanishing near `z` has exterior derivative zero at `z`. -/
theorem exteriorDerivative_apply_eq_zero [I.Boundaryless] {k : ℕ}
    (β : DifferentialGeometry.DifferentialForm I M k) {z : M} {U : Set M} (hU : IsOpen U)
    (hzU : z ∈ U) (hβ : ∀ w ∈ U, β w = 0) :
    DifferentialGeometry.DifferentialForm.exteriorDerivative β z = 0 := by
  have hz : z ∈ (extChartAt I z).source := mem_extChartAt_source z
  apply eq_zero_of_formChartValue_eq_zero _ hz
  rw [formChartValue_exteriorDerivative β hz]
  have hev : (fun y => formChartValue z β ((extChartAt I z).symm y)) =ᶠ[𝓝 ((extChartAt I z) z)]
      fun _ => 0 := by
    have hcont : ContinuousAt (extChartAt I z).symm ((extChartAt I z) z) :=
      (continuousOn_extChartAt_symm z).continuousAt
        ((isOpen_extChartAt_target z).mem_nhds ((extChartAt I z).map_source hz))
    have hmem : (extChartAt I z).symm ⁻¹' U ∈ 𝓝 ((extChartAt I z) z) := by
      apply hcont.preimage_mem_nhds
      rw [(extChartAt I z).left_inv hz]
      exact hU.mem_nhds hzU
    filter_upwards [hmem] with y hy
    exact formChartValue_eq_zero z β (hβ _ hy)
  rw [hev.extDeriv_eq]
  have h0 : (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) = 0 := rfl
  rw [h0, show (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) = (0 : ℝ) • (0 : E → E [⋀^Fin k]→L[ℝ] ℝ) by simp,
    extDeriv_smul, zero_smul]

variable {n : ℕ}

/-- In chart coordinates the orientation sign is locally constant on the chart target. -/
theorem chartSign_symm_eventuallyEq [FiniteDimensional ℝ E] [I.Boundaryless]
    (o : DifferentialGeometry.ManifoldOrientation I M n) (e : Orientation ℝ E (Fin n))
    {p : M} {y : E} (hy : y ∈ (extChartAt I p).target) :
    (fun y' => chartSign o e p ((extChartAt I p).symm y')) =ᶠ[𝓝 y]
      fun _ => chartSign o e p ((extChartAt I p).symm y) := by
  have hcont : ContinuousAt (extChartAt I p).symm y :=
    (continuousOn_extChartAt_symm p).continuousAt ((isOpen_extChartAt_target p).mem_nhds hy)
  exact hcont.eventually (chartSign_eventuallyEq o e ((extChartAt I p).map_target hy))

variable [MeasurableSpace E] [BorelSpace E]

/-- **Chart Stokes**: the chart integral of an exact top form `dβ`, with `β` vanishing outside a
compact subset of the chart domain, is zero. -/
theorem chartIntegral_exteriorDerivative_eq_zero [FiniteDimensional ℝ E] [I.Boundaryless]
    {k : ℕ} (μ : Measure E) [μ.IsAddHaarMeasure]
    (o : DifferentialGeometry.ManifoldOrientation I M (k + 1))
    (e : Orientation ℝ E (Fin (k + 1))) (b : Fin (k + 1) → E) {p : M}
    (β : DifferentialGeometry.DifferentialForm I M k) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (extChartAt I p).source) (hβ : ∀ z, β z ≠ 0 → z ∈ K) :
    chartIntegral μ o e b p (DifferentialGeometry.DifferentialForm.exteriorDerivative β) = 0 := by
  set φ := extChartAt I p
  set T := φ.target
  let R : E → E [⋀^Fin k]→L[ℝ] ℝ := fun y => formChartValue p β (φ.symm y)
  let sgn : E → ℝ := fun y => chartSign o e p (φ.symm y)
  let G : E → E [⋀^Fin k]→L[ℝ] ℝ := T.indicator fun y => sgn y • R y
  have hTo : IsOpen T := isOpen_extChartAt_target p
  have hKc : IsCompact (φ '' K) := hK.image_of_continuousOn ((continuousOn_extChartAt p).mono hKs)
  have hKT : φ '' K ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    exact φ.map_source (hKs hz)
  have hRcont : ContDiffOn ℝ ∞ R T :=
    DifferentialGeometry.DifferentialForm.localRep_contDiffOn β p
  -- `G` vanishes off the compact image of `K`
  have hG0 : ∀ y, y ∉ φ '' K → G y = 0 := by
    intro y hy
    by_cases hyT : y ∈ T
    · have hz : β (φ.symm y) = 0 := by
        by_contra hne
        exact hy ⟨_, hβ _ hne, φ.right_inv hyT⟩
      simp only [G, Set.indicator_of_mem hyT, R, formChartValue_eq_zero p β hz, smul_zero]
    · exact Set.indicator_of_notMem hyT _
  -- near points of the chart target, `G` is a constant multiple of `R`
  have hGloc : ∀ y ∈ T, G =ᶠ[𝓝 y] fun y' => sgn y • R y' := by
    intro y hy
    filter_upwards [hTo.mem_nhds hy, chartSign_symm_eventuallyEq o e hy] with y' hy' hs
    simp only [G, Set.indicator_of_mem hy', sgn]
    rw [hs]
  have hGout : ∀ y ∉ T, G =ᶠ[𝓝 y] fun _ => 0 := by
    intro y hy
    have hy' : y ∉ φ '' K := fun h => hy (hKT h)
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hy'] with y' hy''
    exact hG0 y' hy''
  have hGsmooth : ContDiff ℝ 1 G := by
    refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ T
    · have hR : ContDiffAt ℝ 1 R y :=
        (hRcont.contDiffAt (hTo.mem_nhds hy)).of_le (by exact_mod_cast le_top)
      exact (hR.const_smul (sgn y)).congr_of_eventuallyEq (hGloc y hy)
    · exact contDiffAt_const.congr_of_eventuallyEq (hGout y hy)
  have hGsupp : HasCompactSupport G := HasCompactSupport.intro hKc hG0
  have hdens : ∀ y ∈ T, chartDensity o e b p
      (DifferentialGeometry.DifferentialForm.exteriorDerivative β) y = extDeriv G y b := by
    intro y hy
    unfold chartDensity
    rw [formChartValue_exteriorDerivative β (φ.map_target hy), φ.right_inv hy,
      (hGloc y hy).extDeriv_eq]
    change sgn y * extDeriv R y b = extDeriv (sgn y • R) y b
    rw [extDeriv_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hout : ∀ y ∉ T, extDeriv G y b = 0 := by
    intro y hy
    rw [(hGout y hy).extDeriv_eq]
    have h0 : (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) =
        (0 : ℝ) • (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) := (zero_smul ℝ _).symm
    rw [h0, extDeriv_smul, zero_smul]
    rfl
  unfold chartIntegral
  rw [setIntegral_congr_fun hTo.measurableSet hdens,
    setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  exact integral_extDeriv_apply_eq_zero μ hGsmooth hGsupp b

omit [MeasurableSpace E] [BorelSpace E] in
/-- The weighted pieces of a form over the chart partition sum to the form. -/
theorem sum_weightedForm_chartPartition [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    {k : ℕ} (α : DifferentialGeometry.DifferentialForm I M k) :
    ∑ p ∈ (finite_chartPartition_support (I := I) (M := M)).toFinset,
      weightedForm (chartPartition I M p) α = α := by
  apply ContMDiffSection.ext
  intro z
  have happly : ∀ (s : Finset M) (f : M → DifferentialGeometry.DifferentialForm I M k),
      (∑ p ∈ s, f p) z = ∑ p ∈ s, f p z := by
    intro s f
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        DifferentialGeometry.DifferentialForm.add_apply, ih]
  rw [happly]
  simp only [weightedForm_apply]
  rw [← Finset.sum_smul]
  have hone : ∑ p ∈ (finite_chartPartition_support (I := I) (M := M)).toFinset,
      chartPartition I M p z = 1 := by
    rw [← (chartPartition I M).sum_eq_one (mem_univ z)]
    refine (finsum_eq_sum_of_support_subset _ fun p hp => ?_).symm
    exact (finite_chartPartition_support (I := I) (M := M)).mem_toFinset.mpr ⟨_, hp⟩
  rw [hone, one_smul]

/-- **Stokes' theorem on a closed oriented manifold**: `∫_M dα = 0`. -/
theorem topFormIntegral_exteriorDerivative_eq_zero [FiniteDimensional ℝ E] [T2Space M]
    [CompactSpace M] [I.Boundaryless] {k : ℕ} (μ : Measure E) [μ.IsAddHaarMeasure]
    (o : DifferentialGeometry.ManifoldOrientation I M (k + 1))
    (e : Orientation ℝ E (Fin (k + 1))) (b : Fin (k + 1) → E)
    (α : DifferentialGeometry.DifferentialForm I M k) :
    topFormIntegral μ o e b (DifferentialGeometry.DifferentialForm.exteriorDerivative α) = 0 := by
  set S := (finite_chartPartition_support (I := I) (M := M)).toFinset
  have hd : DifferentialGeometry.DifferentialForm.exteriorDerivative α =
      ∑ p ∈ S, DifferentialGeometry.DifferentialForm.exteriorDerivative
        (weightedForm (chartPartition I M p) α) := by
    conv_lhs => rw [← sum_weightedForm_chartPartition α]
    exact map_sum (DifferentialGeometry.DifferentialForm.exteriorDerivativeLinearMap k) _ S
  rw [hd, topFormIntegral_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hK : IsClosed (tsupport (chartPartition I M p)) := isClosed_tsupport _
  have hsupp : ∀ z, DifferentialGeometry.DifferentialForm.exteriorDerivative
      (weightedForm (chartPartition I M p) α) z ≠ 0 → z ∈ tsupport (chartPartition I M p) := by
    intro z hz
    by_contra hzn
    apply hz
    refine exteriorDerivative_apply_eq_zero _ hK.isOpen_compl hzn fun w hw => ?_
    rw [weightedForm_apply, image_eq_zero_of_notMem_tsupport hw, zero_smul]
  rw [topFormIntegral_eq_chartIntegral μ o e b _ hK (tsupport_chartPartition_subset p) hsupp]
  exact chartIntegral_exteriorDerivative_eq_zero μ o e b _ hK.isCompact
    (tsupport_chartPartition_subset p) (weightedForm_ne_zero_mem α p)

end GaloisForLFunctions.HTGeometry
