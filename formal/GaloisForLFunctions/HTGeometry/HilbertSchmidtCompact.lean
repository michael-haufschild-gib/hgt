/-
# Compactness of Hilbert–Schmidt operators

A Hilbert–Schmidt operator `T : E →L[𝕜] F` is the operator-norm limit of its finite-rank
truncations `x ↦ ∑_{i ∈ s} ⟨eᵢ, x⟩ • T eᵢ` along a Hilbert basis: the error is controlled by a tail
of the summable series `∑ᵢ ‖T eᵢ‖²` through the series Cauchy–Schwarz inequality, and tails of a
summable series are arbitrarily small.  Since the compact operators are closed in operator norm,
every Hilbert–Schmidt operator is compact.  The same tail bound at the empty truncation gives the
fundamental norm comparison `‖T‖ ≤ ‖T‖_HS`.

Proved here:
* `hsTruncation`, `hsTruncation_apply`, `hasSum_inner_smul`, `sub_hsTruncation_apply` — the
  finite-rank truncation of `T` along a finite subfamily of a Hilbert basis, the basis expansion
  `T x = ∑ᵢ ⟨eᵢ, x⟩ • T eᵢ`, and the identification of `T − Tₛ` with the tail of the expansion.
* `norm_sub_hsTruncation_le` — the truncation error bound `‖T − Tₛ‖ ≤ √(∑_{i ∉ s} ‖T eᵢ‖²)`.
* `IsHilbertSchmidt.exists_tail_lt` — tails of the Hilbert–Schmidt series are arbitrarily small.
* `opNorm_le_hsNorm` — the operator norm is dominated by the Hilbert–Schmidt norm.
* `isCompactOperator_hsTruncation` — each truncation is compact (finite-dimensional range).
* `IsHilbertSchmidt.isCompactOperator` — **Hilbert–Schmidt operators are compact**.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open scoped BigOperators ComplexConjugate InnerProductSpace
open Metric Filter

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Hilbert-basis expansion of an operator value.**  `T x = ∑ᵢ ⟨b i, x⟩ • T (b i)`: apply the
continuous `T` to the basis expansion of `x`. -/
theorem hasSum_inner_smul {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) (x : E) :
    HasSum (fun i => (inner 𝕜 (b i) x) • T (b i)) (T x) := by
  have h := (b.hasSum_repr x).mapL T
  simp only [map_smul, HilbertBasis.repr_apply_apply] at h
  exact h

/-- The finite-rank truncation of `T` along a finite subfamily of a Hilbert basis:
`x ↦ ∑_{i ∈ s} ⟨b i, x⟩ • T (b i)`. -/
noncomputable def hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (s : Finset ι) : E →L[𝕜] F :=
  ∑ i ∈ s, (innerSL 𝕜 (b i)).smulRight (T (b i))

omit [CompleteSpace E] [CompleteSpace F] in
theorem hsTruncation_apply {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F) (s : Finset ι)
    (x : E) : hsTruncation b T s x = ∑ i ∈ s, (inner 𝕜 (b i) x) • T (b i) := by
  rw [hsTruncation, sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [smulRight_apply, innerSL_apply_apply]

omit [CompleteSpace E] in
/-- The defect of the truncation is the tail of the basis expansion:
`T x − Tₛ x = ∑_{i ∉ s} ⟨b i, x⟩ • T (b i)`. -/
theorem sub_hsTruncation_apply {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (s : Finset ι) (x : E) :
    T x - hsTruncation b T s x = ∑' i : {i // i ∉ s}, (inner 𝕜 (b i) x) • T (b i) := by
  have h := (hasSum_inner_smul b T x).summable.sum_add_tsum_subtype_compl s
  rw [(hasSum_inner_smul b T x).tsum_eq] at h
  rw [hsTruncation_apply, sub_eq_iff_eq_add']
  exact h.symm

/-- **The truncation error bound.**  `‖T − Tₛ‖ ≤ √(∑_{i ∉ s} ‖T (b i)‖²)`: the tail of the basis
expansion is estimated by the series Cauchy–Schwarz inequality against Parseval for `x`. -/
theorem norm_sub_hsTruncation_le {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) (s : Finset ι) :
    ‖T - hsTruncation b T s‖ ≤ Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) := by
  refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [sub_apply, sub_hsTruncation_apply]
  have hbT : Summable (fun i : {i // i ∉ s} => ‖T (b i)‖ ^ 2) := (hT.summable b).subtype _
  have hbx : Summable (fun i : {i // i ∉ s} => ‖inner 𝕜 (b i) x‖ ^ 2) :=
    (b.summable_norm_inner_sq x).subtype _
  have hprod : Summable (fun i : {i // i ∉ s} => ‖inner 𝕜 (b i) x‖ * ‖T (b i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hbx.mul_left (2⁻¹)).add (hbT.mul_left (2⁻¹)))
    nlinarith [sq_nonneg (‖inner 𝕜 (b i) x‖ - ‖T (b i)‖), norm_nonneg (inner 𝕜 (b i) x),
      norm_nonneg (T (b i))]
  have hnorm : Summable (fun i : {i // i ∉ s} => ‖(inner 𝕜 (b i) x) • T (b i)‖) :=
    hprod.congr fun i => (norm_smul _ _).symm
  calc ‖∑' i : {i // i ∉ s}, (inner 𝕜 (b i) x) • T (b i)‖
      ≤ ∑' i : {i // i ∉ s}, ‖(inner 𝕜 (b i) x) • T (b i)‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' i : {i // i ∉ s}, ‖inner 𝕜 (b i) x‖ * ‖T (b i)‖ :=
        tsum_congr fun i => norm_smul _ _
    _ ≤ Real.sqrt (∑' i : {i // i ∉ s}, ‖inner 𝕜 (b i) x‖ ^ 2)
          * Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) :=
        tsum_mul_le_sqrt_mul_sqrt hbx hbT
    _ ≤ ‖x‖ * Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) := by
        have hle : ∑' i : {i // i ∉ s}, ‖inner 𝕜 (b i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
          have h := (b.summable_norm_inner_sq x).sum_add_tsum_subtype_compl s
          rw [b.tsum_norm_inner_sq x] at h
          have hpart : 0 ≤ ∑ i ∈ s, ‖inner 𝕜 (b i) x‖ ^ 2 :=
            Finset.sum_nonneg fun i _ => by positivity
          linarith
        have hsqrt := Real.sqrt_le_sqrt hle
        rw [Real.sqrt_sq (norm_nonneg x)] at hsqrt
        exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2) * ‖x‖ := mul_comm _ _

/-- **Tails of the Hilbert–Schmidt series are arbitrarily small.**  For every `ε > 0` there is a
finite subfamily outside which `∑ ‖T (b i)‖² < ε`. -/
theorem IsHilbertSchmidt.exists_tail_lt {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι 𝕜 E) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ 2 < ε := by
  have hsum := hT.summable b
  have htend : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖T (b i)‖ ^ 2)
      Filter.atTop (nhds (∑' i, ‖T (b i)‖ ^ 2)) := hsum.hasSum
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp htend ε hε).exists
  refine ⟨s, ?_⟩
  have h := hsum.sum_add_tsum_subtype_compl s
  rw [Real.dist_eq, abs_lt] at hs
  linarith [hs.1]

/-- **The operator norm is dominated by the Hilbert–Schmidt norm.**  `‖T‖ ≤ ‖T‖_HS`: the empty
truncation of the error bound. -/
theorem opNorm_le_hsNorm {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T := by
  have h := norm_sub_hsTruncation_le hT (hsBasis 𝕜 E) (∅ : Finset _)
  have h0 : hsTruncation (hsBasis 𝕜 E) T ∅ = 0 := by
    rw [hsTruncation, Finset.sum_empty]
  rw [h0, sub_zero] at h
  refine h.trans (Real.sqrt_le_sqrt ?_)
  have hsum : Summable (fun i => ‖T (hsBasis 𝕜 E i)‖ ^ 2) := hT
  have h2 := hsum.sum_add_tsum_subtype_compl (∅ : Finset _)
  simp only [Finset.sum_empty, zero_add] at h2
  rw [h2]
  exact le_rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- An operator whose range lies in a finite-dimensional subspace is compact: the closed ball of
that subspace is compact and absorbs the image of the unit ball. -/
private theorem isCompactOperator_of_range_le {A : E →L[𝕜] F} (V : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 V] (hmem : ∀ x, A x ∈ V) : IsCompactOperator A := by
  refine ⟨Subtype.val '' Metric.closedBall (0 : V) (‖A‖ + 1),
    (isCompact_closedBall 0 _).image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_
  intro x hx
  refine ⟨⟨A x, hmem x⟩, ?_, rfl⟩
  rw [mem_closedBall_zero_iff]
  calc ‖(⟨A x, hmem x⟩ : V)‖ = ‖A x‖ := rfl
    _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ ≤ ‖A‖ * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_zero_iff.mp hx)) (norm_nonneg A)
    _ ≤ ‖A‖ + 1 := by rw [mul_one]; linarith [norm_nonneg A]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Each basis truncation is a compact operator: its range lies in the span of the finitely many
vectors `T (b i)`, `i ∈ s`. -/
theorem isCompactOperator_hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] F)
    (s : Finset ι) : IsCompactOperator (hsTruncation b T s) := by
  classical
  letI : FiniteDimensional 𝕜
      (Submodule.span 𝕜 ((s.image fun i => T (b i) : Finset F) : Set F)) :=
    FiniteDimensional.span_of_finite 𝕜 (Finset.finite_toSet _)
  refine isCompactOperator_of_range_le
    (Submodule.span 𝕜 ((s.image fun i => T (b i) : Finset F) : Set F)) fun x => ?_
  rw [hsTruncation_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)

/-- **Hilbert–Schmidt operators are compact.**  The finite-rank basis truncations converge to `T`
in operator norm — the error is a tail of the summable series `∑ᵢ ‖T eᵢ‖²` — and the compact
operators are closed in operator norm. -/
theorem IsHilbertSchmidt.isCompactOperator {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  have hcl : T ∈ closure {W : E →L[𝕜] F | IsCompactOperator W} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨s, hs⟩ := hT.exists_tail_lt (hsBasis 𝕜 E) (show (0 : ℝ) < δ ^ 2 by positivity)
    refine ⟨hsTruncation (hsBasis 𝕜 E) T s, isCompactOperator_hsTruncation _ _ _, ?_⟩
    rw [dist_eq_norm]
    exact (norm_sub_hsTruncation_le hT (hsBasis 𝕜 E) s).trans_lt ((Real.sqrt_lt' hδ).mpr hs)
  exact isClosed_setOf_isCompactOperator.closure_subset hcl

end ContinuousLinearMap
