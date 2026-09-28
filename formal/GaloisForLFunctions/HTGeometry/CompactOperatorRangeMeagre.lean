import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Ranges of compact operators are meagre

In an infinite-dimensional normed space no compact set has interior (Riesz), so every compact
set is closed and nowhere dense.  The range of a compact linear map `T : E → H` out of any
topological vector space is covered by the countably many compact dilates `cⁿ • K` of one compact
set `K` whose preimage is a neighbourhood of zero.  Hence the union of the ranges of countably many
compact linear maps into an infinite-dimensional Banach space is meagre, its complement is
residual and dense, and no countable family of compact maps covers the space.

* `interior_eq_empty_of_isCompact_of_not_finiteDimensional` : **Riesz, interior form.**
* `range_subset_iUnion_isCompact_of_isCompactOperator` : **compact dilate exhaustion of a
  compact range.**
* `isMeagre_range_of_isCompactOperator` : **a compact range is meagre.**
* `compl_iUnion_range_mem_residual_of_isCompactOperator`,
  `dense_compl_iUnion_range_of_isCompactOperator`,
  `iUnion_range_ne_univ_of_isCompactOperator` : **countable compact atlases never cover.**
-/

open Filter Topology
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

section Riesz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable (𝕜) in
/-- **Riesz, interior form.**  In an infinite-dimensional normed space a compact set has empty
interior: a compact neighbourhood of one point would make the space locally compact. -/
theorem interior_eq_empty_of_isCompact_of_not_finiteDimensional
    (hH : ¬ FiniteDimensional 𝕜 H) {K : Set H} (hK : IsCompact K) : interior K = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  haveI : LocallyCompactSpace H :=
    hK.locallyCompactSpace_of_mem_nhds_of_addGroup (mem_interior_iff_mem_nhds.1 hx)
  exact hH (FiniteDimensional.of_locallyCompactSpace 𝕜)

variable (𝕜) in
/-- In an infinite-dimensional normed space every compact set is nowhere dense. -/
theorem isNowhereDense_of_isCompact_of_not_finiteDimensional
    (hH : ¬ FiniteDimensional 𝕜 H) {K : Set H} (hK : IsCompact K) : IsNowhereDense K := by
  rw [IsNowhereDense, hK.isClosed.closure_eq]
  exact interior_eq_empty_of_isCompact_of_not_finiteDimensional 𝕜 hH hK

end Riesz

section CompactRange

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/-- **Compact dilate exhaustion.**  The range of a compact linear map out of a topological vector
space lies in a countable union of compact sets: the dilates `cⁿ • K` of one compact set `K`
whose preimage is a neighbourhood of zero, for a fixed scalar `‖c‖ > 1`. -/
theorem range_subset_iUnion_isCompact_of_isCompactOperator
    {T : E →ₗ[𝕜] H} (hT : IsCompactOperator T) :
    ∃ K : ℕ → Set H, (∀ n, IsCompact (K n)) ∧ Set.range T ⊆ ⋃ n, K n := by
  obtain ⟨K, hK, hKnhds⟩ := hT
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : c ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hc)
  refine ⟨fun n => (c ^ n) • K, fun n => hK.image (continuous_const_smul _), ?_⟩
  rintro _ ⟨x, rfl⟩
  have hsmall : Tendsto (fun n : ℕ => (c⁻¹) ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hc
  have hsmul : Tendsto (fun n : ℕ => ((c⁻¹) ^ n) • x) atTop (𝓝 0) := by
    simpa using hsmall.smul_const x
  obtain ⟨n, hn⟩ := (hsmul.eventually hKnhds).exists
  refine Set.mem_iUnion.2 ⟨n, ⟨T (((c⁻¹) ^ n) • x), hn, ?_⟩⟩
  change c ^ n • T (((c⁻¹) ^ n) • x) = T x
  rw [map_smul, smul_smul, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, one_smul]

variable [CompleteSpace 𝕜]

/-- **A compact range is meagre** in an infinite-dimensional normed space. -/
theorem isMeagre_range_of_isCompactOperator
    (hH : ¬ FiniteDimensional 𝕜 H) {T : E →ₗ[𝕜] H} (hT : IsCompactOperator T) :
    IsMeagre (Set.range T) := by
  obtain ⟨K, hK, hsub⟩ := range_subset_iUnion_isCompact_of_isCompactOperator hT
  exact IsMeagre.mono hsub (isMeagre_iUnion fun n =>
    (isNowhereDense_of_isCompact_of_not_finiteDimensional 𝕜 hH (hK n)).isMeagre)

end CompactRange

section Atlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {ι : Type*} [Countable ι] {E : ι → Type*} [∀ m, AddCommGroup (E m)]
  [∀ m, Module 𝕜 (E m)] [∀ m, TopologicalSpace (E m)] [∀ m, ContinuousSMul 𝕜 (E m)]

/-- The union of the ranges of countably many compact linear maps into an infinite-dimensional
normed space is meagre. -/
theorem isMeagre_iUnion_range_of_isCompactOperator
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →ₗ[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    IsMeagre (⋃ m, Set.range (T m)) :=
  isMeagre_iUnion fun m => isMeagre_range_of_isCompactOperator hH (hT m)

/-- **Countable compact-route atlases leave a residual set.** -/
theorem compl_iUnion_range_mem_residual_of_isCompactOperator
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →ₗ[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    (⋃ m, Set.range (T m))ᶜ ∈ residual H :=
  isMeagre_iUnion_range_of_isCompactOperator hH T hT

/-- **Countable compact-route atlases leave a dense set** in an infinite-dimensional Banach
space. -/
theorem dense_compl_iUnion_range_of_isCompactOperator [CompleteSpace H]
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →ₗ[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    Dense (⋃ m, Set.range (T m))ᶜ :=
  dense_of_mem_residual (compl_iUnion_range_mem_residual_of_isCompactOperator hH T hT)

/-- **Countable compact-route atlases never cover** an infinite-dimensional Banach space. -/
theorem iUnion_range_ne_univ_of_isCompactOperator [CompleteSpace H]
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →ₗ[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    (⋃ m, Set.range (T m)) ≠ Set.univ := by
  intro hcover
  obtain ⟨y, hy⟩ := (dense_compl_iUnion_range_of_isCompactOperator hH T hT).nonempty
  exact hy (hcover ▸ Set.mem_univ y)

/-- **Theorem (countable compact-route atlases).**  For countably many compact linear maps
`T m : E m → H` out of arbitrary topological vector spaces into an infinite-dimensional Banach
space, the complement of the union of their ranges is residual and dense, and in particular
nonempty. -/
theorem compactRouteAtlas_residual_dense_escape [CompleteSpace H]
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →ₗ[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    (⋃ m, Set.range (T m))ᶜ ∈ residual H ∧ Dense (⋃ m, Set.range (T m))ᶜ ∧
      (⋃ m, Set.range (T m)) ≠ Set.univ :=
  ⟨compl_iUnion_range_mem_residual_of_isCompactOperator hH T hT,
    dense_compl_iUnion_range_of_isCompactOperator hH T hT,
    iUnion_range_ne_univ_of_isCompactOperator hH T hT⟩

end Atlas

section BanachAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*} [Countable ι] {E : ι → Type*} [∀ m, NormedAddCommGroup (E m)]
  [∀ m, NormedSpace 𝕜 (E m)]

/-- **Theorem (countable compact-route atlases, Banach form).**  For countably many compact
bounded operators `T m : E m →L H` between normed spaces, `H` an infinite-dimensional Banach
space, `H \ ⋃ m, T m (E m)` is residual and dense. -/
theorem compactRouteAtlas_residual_dense_escape_clm
    (hH : ¬ FiniteDimensional 𝕜 H) (T : ∀ m, E m →L[𝕜] H)
    (hT : ∀ m, IsCompactOperator (T m)) :
    (Set.univ \ ⋃ m, Set.range (T m)) ∈ residual H ∧
      Dense (Set.univ \ ⋃ m, Set.range (T m)) ∧
      (⋃ m, Set.range (T m)) ≠ Set.univ := by
  have h := compactRouteAtlas_residual_dense_escape hH (fun m => (T m : E m →ₗ[𝕜] H)) hT
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← Set.compl_eq_univ_sdiff]
  exact h

end BanachAtlas

end GaloisForLFunctions.HTGeometry
