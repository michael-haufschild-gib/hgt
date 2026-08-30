import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLogCovering

/-!
# Full rank of the number-field unit place-log lattice

Uniform unit-log covering implies that the real span of unit log profiles is the entire weighted
zero-sum archimedean hyperplane.  The proof uses only the closedness of finite-dimensional
subspaces and dilation, so no rank formula or selected family of fundamental units is assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Real span of logarithmic place profiles of number-ring units. -/
def numberFieldUnitPlaceLogRealSpan : Submodule ℝ (InfinitePlace K → ℝ) :=
  Submodule.span ℝ (Set.range (numberFieldUnitPlaceLogEmbeddings (K := K)))

/-- Dirichlet full rank, derived from unconditional covering rather than assumed. -/
theorem numberFieldUnitPlaceLogRealSpan_eq_hyperplane :
    numberFieldUnitPlaceLogRealSpan (K := K) =
      numberFieldUnitPlaceLogHyperplane (K := K) := by
  apply le_antisymm
  · rw [numberFieldUnitPlaceLogRealSpan, Submodule.span_le]
    rintro x ⟨u, rfl⟩
    exact sum_mult_numberFieldUnitPlaceLogEmbeddings u
  · intro y hy
    obtain ⟨R, hR, hcover⟩ :=
      exists_numberFieldUnitPlaceLog_coveringRadius (K := K)
    have hclosed : IsClosed (numberFieldUnitPlaceLogRealSpan (K := K) :
        Set (InfinitePlace K → ℝ)) :=
      Submodule.closed_of_finiteDimensional _
    apply hclosed.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε hR)
    let q : ℝ := (n : ℝ) + 1
    have hq : 0 < q := by dsimp [q]; positivity
    have hqy : q • y ∈ numberFieldUnitPlaceLogHyperplane (K := K) :=
      (numberFieldUnitPlaceLogHyperplane (K := K)).smul_mem q hy
    obtain ⟨u, hu⟩ := hcover (q • y) hqy
    let z : InfinitePlace K → ℝ := q⁻¹ • numberFieldUnitPlaceLogEmbeddings u
    have hz : z ∈ numberFieldUnitPlaceLogRealSpan (K := K) := by
      apply (numberFieldUnitPlaceLogRealSpan (K := K)).smul_mem
      exact Submodule.subset_span (Set.mem_range_self u)
    refine ⟨z, hz, ?_⟩
    have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
    have hdist : dist y z = q⁻¹ *
        ‖numberFieldUnitPlaceLogEmbeddings u - q • y‖ := by
      rw [dist_eq_norm]
      dsimp [z]
      calc
        ‖y - q⁻¹ • numberFieldUnitPlaceLogEmbeddings u‖ =
            ‖q⁻¹ • (q • y - numberFieldUnitPlaceLogEmbeddings u)‖ := by
              congr 1
              simp [smul_sub, ne_of_gt hq]
        _ = ‖q⁻¹‖ * ‖q • y - numberFieldUnitPlaceLogEmbeddings u‖ :=
          norm_smul _ _
        _ = q⁻¹ * ‖numberFieldUnitPlaceLogEmbeddings u - q • y‖ := by
          rw [Real.norm_eq_abs, abs_of_pos hqinv, norm_sub_rev]
    rw [hdist]
    calc
      q⁻¹ * ‖numberFieldUnitPlaceLogEmbeddings u - q • y‖ ≤ q⁻¹ * R :=
        mul_le_mul_of_nonneg_left hu (le_of_lt hqinv)
      _ < ε := by
        have hqform : q⁻¹ = 1 / ((n : ℝ) + 1) := by simp [q, one_div]
        rw [hqform]
        calc
          (1 / ((n : ℝ) + 1)) * R < (ε / R) * R :=
            mul_lt_mul_of_pos_right hn hR
          _ = ε := by field_simp

end

end GaloisForLFunctions.HTGeometry
