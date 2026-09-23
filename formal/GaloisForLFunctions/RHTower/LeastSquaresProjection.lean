import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.MetricSpace.Infsep

/-!
# Least squares in an inner product space, from the normal equations

The distance from a vector to the span of a finite family is determined by two data: the Gram matrix of
the family and the vector of pairings with the target.  This file proves that, in the form the
quantitative theory uses, for an arbitrary inner product space over an arbitrary `RCLike` field.

Given `v : n → H`, a target `x`, and coefficients `c` solving the **normal equations**

`∀ i, ∑ j ⟪v i, v j⟫ · c j = ⟪v i, x⟫`,

the combination `y = ∑ c j • v j` is the orthogonal projection of `x` onto the span, and

`‖x − y‖² = ‖x‖² − re ∑ i conj(c i) · ⟪v i, x⟫`,  `dist(x, span v) = ‖x − y‖`.

No hypothesis of linear independence or invertibility is needed: the theorems are about *a* solution of
the normal equations, which is exactly what a least-squares computation produces.  When the family is
linearly independent, `Matrix.posDef_gram_iff_linearIndependent` says the Gram matrix is positive definite,
hence invertible, so a solution exists and is unique — but the identities below do not need that.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {n : Type*} [Fintype n]

/-- The residual of a solution of the normal equations is orthogonal to every member of the family. -/
theorem inner_residual_eq_zero (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x) (i : n) :
    inner 𝕜 (v i) (x - ∑ j, c j • v j) = 0 := by
  rw [inner_sub_right, inner_sum]
  have : ∑ j, inner 𝕜 (v i) (c j • v j) = ∑ j, inner 𝕜 (v i) (v j) * c j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    ring
  rw [this, hc i, sub_self]

/-- The residual is orthogonal to the whole span. -/
theorem inner_residual_span_eq_zero (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x)
    {z : H} (hz : z ∈ Submodule.span 𝕜 (Set.range v)) :
    inner 𝕜 (x - ∑ j, c j • v j) z = 0 := by
  have hker : Submodule.span 𝕜 (Set.range v)
      ≤ (innerSL 𝕜 (x - ∑ j, c j • v j)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h := inner_residual_eq_zero v x c hc i
    have h2 : inner 𝕜 (x - ∑ j, c j • v j) (v i) = 0 := by
      rw [← inner_conj_symm, h, map_zero]
    exact h2
  exact hker hz

/-- **The least-squares value.**  A solution of the normal equations realises the squared distance as
`‖x‖²` minus the pairing form. -/
theorem norm_sq_residual (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x) :
    ‖x - ∑ j, c j • v j‖ ^ (2 : ℕ)
      = ‖x‖ ^ (2 : ℕ) - RCLike.re (∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x) := by
  set y : H := ∑ j, c j • v j with hy
  have hortho : inner 𝕜 (x - y) y = 0 := by
    refine inner_residual_span_eq_zero v x c hc ?_
    rw [hy]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hxy : inner 𝕜 x y = inner 𝕜 y y := by
    have := hortho
    rw [inner_sub_left, sub_eq_zero] at this
    exact this
  have hyy : inner 𝕜 y y = ∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x := by
    rw [hy, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    congr 1
    rw [inner_sum]
    have : ∑ j, inner 𝕜 (v i) (c j • v j) = ∑ j, inner 𝕜 (v i) (v j) * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right]
      ring
    rw [this, hc i]
  have hnorm : ‖x - y‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) - 2 * RCLike.re (inner 𝕜 x y) + ‖y‖ ^ (2 : ℕ) :=
    norm_sub_sq (𝕜 := 𝕜) x y
  have hyre : (RCLike.re (inner 𝕜 y y) : ℝ) = ‖y‖ ^ (2 : ℕ) := inner_self_eq_norm_sq y
  rw [hnorm, hxy, hyy] at *
  rw [← hyre, hyy]
  ring

/-- **The explained mass.**  The squared norm of the projection is the pairing form. -/
theorem norm_sq_combination_of_normalEquations (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x) :
    ‖∑ j, c j • v j‖ ^ (2 : ℕ) = RCLike.re (∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x) := by
  set y : H := ∑ j, c j • v j with hy
  have hyy : inner 𝕜 y y = ∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x := by
    rw [hy, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    congr 1
    rw [inner_sum]
    have : ∑ j, inner 𝕜 (v i) (c j • v j) = ∑ j, inner 𝕜 (v i) (v j) * c j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right]
      ring
    rw [this, hc i]
  have := inner_self_eq_norm_sq (𝕜 := 𝕜) y
  rw [hyy] at this
  exact this.symm

/-- **The quadratic form of the least-squares problem.**  The squared distance to an arbitrary combination,
with no hypothesis on the coefficients: `‖x‖²` minus twice the pairing plus the Gram form. -/
theorem norm_sq_sub_combination (v : n → H) (x : H) (c : n → 𝕜) :
    ‖x - ∑ j, c j • v j‖ ^ (2 : ℕ)
      = ‖x‖ ^ (2 : ℕ) - 2 * RCLike.re (∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x)
        + RCLike.re (∑ i, ∑ j, (starRingEnd 𝕜) (c i) * c j * inner 𝕜 (v i) (v j)) := by
  set y : H := ∑ j, c j • v j with hy
  have hxy : RCLike.re (inner 𝕜 x y)
      = RCLike.re (∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x) := by
    have h1 : inner 𝕜 x y = ∑ j, c j * inner 𝕜 x (v j) := by
      rw [hy, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right]
    have h2 : (starRingEnd 𝕜) (∑ i, (starRingEnd 𝕜) (c i) * inner 𝕜 (v i) x)
        = ∑ j, c j * inner 𝕜 x (v j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, RingHomInvPair.comp_apply_eq, inner_conj_symm]
    rw [h1, ← h2, RCLike.conj_re]
  have hyy : ‖y‖ ^ (2 : ℕ)
      = RCLike.re (∑ i, ∑ j, (starRingEnd 𝕜) (c i) * c j * inner 𝕜 (v i) (v j)) := by
    have hinner : inner 𝕜 y y
        = ∑ i, ∑ j, (starRingEnd 𝕜) (c i) * c j * inner 𝕜 (v i) (v j) := by
      rw [hy, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right]
      ring
    have h := inner_self_eq_norm_sq (𝕜 := 𝕜) y
    rw [hinner] at h
    exact h.symm
  rw [norm_sub_sq (𝕜 := 𝕜), hxy, hyy]

/-- **The projection is the closest point.** -/
theorem norm_residual_le (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x)
    {z : H} (hz : z ∈ Submodule.span 𝕜 (Set.range v)) :
    ‖x - ∑ j, c j • v j‖ ≤ ‖x - z‖ := by
  set y : H := ∑ j, c j • v j with hy
  have hyspan : y ∈ Submodule.span 𝕜 (Set.range v) := by
    rw [hy]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hdiff : y - z ∈ Submodule.span 𝕜 (Set.range v) := Submodule.sub_mem _ hyspan hz
  have hortho : inner 𝕜 (x - y) (y - z) = 0 :=
    inner_residual_span_eq_zero v x c hc hdiff
  have hsplit : x - z = (x - y) + (y - z) := by abel
  have hsq : ‖x - z‖ ^ (2 : ℕ) = ‖x - y‖ ^ (2 : ℕ) + ‖y - z‖ ^ (2 : ℕ) := by
    rw [hsplit, norm_add_sq (𝕜 := 𝕜), hortho]
    simp
  nlinarith [norm_nonneg (x - y), norm_nonneg (x - z), norm_nonneg (y - z), hsq]

/-- The span of a finite family always has an orthogonal projection: it is finite dimensional. -/
theorem hasOrthogonalProjection_span (v : n → H) :
    (Submodule.span 𝕜 (Set.range v)).HasOrthogonalProjection := by
  haveI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range v)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  infer_instance

/-- **The bridge to mathlib's projector.**  A solution of the normal equations computes the orthogonal
projection onto the span, so any statement about `starProjection` on a finite span can be evaluated from the
Gram matrix and the pairing vector. -/
theorem starProjection_eq_of_normalEquations (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x) :
    haveI := hasOrthogonalProjection_span (𝕜 := 𝕜) v
    (Submodule.span 𝕜 (Set.range v)).starProjection x = ∑ j, c j • v j := by
  haveI := hasOrthogonalProjection_span (𝕜 := 𝕜) v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro w hw
    exact inner_residual_span_eq_zero v x c hc hw

/-- **The distance to the span, from the normal equations.** -/
theorem infDist_span_eq (v : n → H) (x : H) (c : n → 𝕜)
    (hc : ∀ i, ∑ j, inner 𝕜 (v i) (v j) * c j = inner 𝕜 (v i) x) :
    Metric.infDist x (Submodule.span 𝕜 (Set.range v) : Set H) = ‖x - ∑ j, c j • v j‖ := by
  have hyspan : (∑ j, c j • v j) ∈ Submodule.span 𝕜 (Set.range v) := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine le_antisymm ?_ ?_
  · have h := Metric.infDist_le_dist_of_mem (x := x) hyspan
    rwa [dist_eq_norm] at h
  · refine (Metric.le_infDist ⟨0, Submodule.zero_mem _⟩).mpr fun z hz => ?_
    rw [dist_eq_norm]
    exact norm_residual_le v x c hc hz

end RHTower

end
