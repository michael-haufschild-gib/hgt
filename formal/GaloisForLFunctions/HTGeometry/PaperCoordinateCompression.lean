import GaloisForLFunctions.HTGeometry.VectorSequenceShift
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-!
# Finite coordinate compression of vector histories

Coordinate prefixes are contractive orthogonal projections and recover every history in norm.
Compressing any bounded operator on both sides converges strongly together with its adjoint
and its positive Gram operator. For finite-dimensional fibres all compressions are compact,
so the compact-ideal Gram cost of every finite compression is zero.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped InnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Keep exactly the first `N` vector coordinates. -/
def paperCoordinateProjection (N : ℕ) : VecSeq E →L[ℂ] VecSeq E :=
  ∑ n ∈ Finset.range N,
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => E) 2 n) ∘L
      lp.evalCLM ℂ (fun _ : ℕ => E) 2 n

theorem paperCoordinateProjection_apply (N : ℕ) (x : VecSeq E) :
    paperCoordinateProjection N x = ∑ n ∈ Finset.range N, lp.single 2 n (x n) := by
  simp only [paperCoordinateProjection, sum_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

theorem paperCoordinateProjection_coordinate (N : ℕ) (x : VecSeq E) (n : ℕ) :
    paperCoordinateProjection N x n = if n < N then x n else 0 := by
  rw [paperCoordinateProjection_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single,
    Finset.mem_range]

/-- Prefix restriction never enlarges the history norm. -/
theorem norm_paperCoordinateProjection_apply_le (N : ℕ) (x : VecSeq E) :
    ‖paperCoordinateProjection N x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [paperCoordinateProjection_coordinate]
  split_ifs <;> simp

theorem norm_paperCoordinateProjection_le (N : ℕ) :
    ‖(paperCoordinateProjection N : VecSeq E →L[ℂ] VecSeq E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_paperCoordinateProjection_apply_le N x

theorem paperCoordinateProjection_idempotent (N : ℕ) :
    (paperCoordinateProjection N : VecSeq E →L[ℂ] VecSeq E) ∘L
      paperCoordinateProjection N = paperCoordinateProjection N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, paperCoordinateProjection_coordinate]
  split_ifs <;> rfl

/-- Finite prefixes recover each actual vector history. -/
theorem tendsto_paperCoordinateProjection (x : VecSeq E) :
    Tendsto (fun N => paperCoordinateProjection N x) atTop (𝓝 x) := by
  simpa only [paperCoordinateProjection_apply] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x).tendsto_sum_nat

/-- The literal two-sided finite coordinate compression. -/
def paperCoordinateCompression (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    VecSeq E →L[ℂ] VecSeq E :=
  paperCoordinateProjection N ∘L T ∘L paperCoordinateProjection N

theorem norm_paperCoordinateCompression_apply_le
    (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) (x : VecSeq E) :
    ‖paperCoordinateCompression T N x‖ ≤ ‖T‖ * ‖x‖ := by
  exact (norm_paperCoordinateProjection_apply_le N _).trans
    ((T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_paperCoordinateProjection_apply_le N x)
        (norm_nonneg T)))

theorem norm_paperCoordinateCompression_le (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    ‖paperCoordinateCompression T N‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    (norm_paperCoordinateCompression_apply_le T N)

private theorem tendsto_bounded_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℕ → H →L[ℂ] H) (B : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ n z, ‖A n z‖ ≤ C * ‖z‖)
    (hstrong : ∀ z, Tendsto (fun n => A n z) atTop (𝓝 (B z)))
    (x : ℕ → H) (y : H) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => A n (x n)) atTop (𝓝 (B y)) := by
  have hsmall : Tendsto (fun n => A n (x n - y)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => hbound n (x n - y))
    have hx0 : Tendsto (fun n => x n - y) atTop (𝓝 0) := by
      simpa using hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hx0.norm
  have h := hsmall.add (hstrong y)
  simpa only [map_sub, sub_add_cancel, zero_add] using h

/-- Two-sided compressions converge strongly for every bounded history operator. -/
theorem tendsto_paperCoordinateCompression
    (T : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => paperCoordinateCompression T N x) atTop (𝓝 (T x)) := by
  exact tendsto_bounded_apply paperCoordinateProjection (ContinuousLinearMap.id ℂ _) 1
    (fun N z => by simpa using norm_paperCoordinateProjection_apply_le N z)
    tendsto_paperCoordinateProjection (fun N => T (paperCoordinateProjection N x)) (T x)
    (T.continuous.tendsto x |>.comp (tendsto_paperCoordinateProjection x))

/-- The complete family of finite compressions determines the bounded operator uniquely. -/
theorem paperCoordinateCompression_injective :
    Function.Injective (fun T : VecSeq E →L[ℂ] VecSeq E => paperCoordinateCompression T) := by
  intro S T h
  change paperCoordinateCompression S = paperCoordinateCompression T at h
  apply ContinuousLinearMap.ext
  intro x
  have hS := tendsto_paperCoordinateCompression S x
  have hT := tendsto_paperCoordinateCompression T x
  rw [h] at hS
  exact tendsto_nhds_unique hS hT

variable [CompleteSpace E]

/-- Prefix projections are orthogonal projections, with their actual vector coordinates. -/
theorem adjoint_paperCoordinateProjection (N : ℕ) :
    ContinuousLinearMap.adjoint (paperCoordinateProjection N : VecSeq E →L[ℂ] VecSeq E) =
      paperCoordinateProjection N := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [paperCoordinateProjection_apply, sum_inner, inner_sum,
    lp.inner_single_left, lp.inner_single_right]

theorem adjoint_paperCoordinateCompression (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    ContinuousLinearMap.adjoint (paperCoordinateCompression T N) =
      paperCoordinateCompression (ContinuousLinearMap.adjoint T) N := by
  simp only [paperCoordinateCompression, ContinuousLinearMap.adjoint_comp,
    adjoint_paperCoordinateProjection, ContinuousLinearMap.comp_assoc]

/-- The same compression sequence also recovers the adjoint strongly. -/
theorem tendsto_adjoint_paperCoordinateCompression
    (T : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => ContinuousLinearMap.adjoint (paperCoordinateCompression T N) x)
      atTop (𝓝 (ContinuousLinearMap.adjoint T x)) := by
  simpa only [adjoint_paperCoordinateCompression] using
    tendsto_paperCoordinateCompression (ContinuousLinearMap.adjoint T) x

/-- The positive Gram operators converge strongly as well. -/
theorem tendsto_gram_paperCoordinateCompression
    (T : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => (ContinuousLinearMap.adjoint (paperCoordinateCompression T N) ∘L
        paperCoordinateCompression T N) x)
      atTop (𝓝 ((ContinuousLinearMap.adjoint T ∘L T) x)) := by
  simp only [adjoint_paperCoordinateCompression, ContinuousLinearMap.comp_apply]
  exact tendsto_bounded_apply (paperCoordinateCompression (ContinuousLinearMap.adjoint T))
    (ContinuousLinearMap.adjoint T) ‖ContinuousLinearMap.adjoint T‖
    (norm_paperCoordinateCompression_apply_le (ContinuousLinearMap.adjoint T))
    (tendsto_paperCoordinateCompression (ContinuousLinearMap.adjoint T))
    (fun N => paperCoordinateCompression T N x) (T x)
    (tendsto_paperCoordinateCompression T x)

variable [FiniteDimensional ℂ E]

/-- Finite prefixes have compact range whenever the fibre is finite-dimensional. -/
theorem isCompactOperator_paperCoordinateProjection (N : ℕ) :
    IsCompactOperator (paperCoordinateProjection N : VecSeq E →L[ℂ] VecSeq E) := by
  change paperCoordinateProjection N ∈ compactOperatorStarAlgebra (VecSeq E)
  apply (compactOperatorStarAlgebra (VecSeq E)).sum_mem
  intro n _
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (lp.evalCLM ℂ (fun _ : ℕ => E) 2 n)).clm_comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => E) 2 n)

theorem isCompactOperator_paperCoordinateCompression
    (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    IsCompactOperator (paperCoordinateCompression T N) :=
  (isCompactOperator_paperCoordinateProjection N).comp_clm
    (T ∘L paperCoordinateProjection N)

/-- The source paper's ideal weight vanishes on every finite coordinate compression. -/
theorem compactOperatorTraceCost_paperCoordinateCompression
    (T : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    compactOperatorTraceCost (VecSeq E) (paperCoordinateCompression T N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (isCompactOperator_paperCoordinateCompression T N)

end

end GaloisForLFunctions.HTGeometry
