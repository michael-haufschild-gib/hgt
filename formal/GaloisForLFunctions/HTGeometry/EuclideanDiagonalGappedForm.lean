import Mathlib

/-!
# Diagonal operators and the gapped quadratic form

A diagonal operator with a real symbol is self-adjoint, acts on each coordinate vector by its
symbol, and has quadratic form the symbol-weighted mass of the coordinates.  If one coordinate
strictly dominates the others by a fixed amount, the form obeys the gap inequality with that
coordinate as the distinguished direction.

This is the hypothesis a gapped-eigenline stability statement consumes.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal operator on Euclidean space with a real symbol. -/
def diagCLM (f : ι → ℝ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.diagonal fun i => ((f i : ℝ) : ℂ))

theorem diagCLM_apply (f : ι → ℝ) (x : EuclideanSpace ℂ ι) (i : ι) :
    ((diagCLM f) x).ofLp i = ((f i : ℝ) : ℂ) * x.ofLp i := by
  show (∑ j, (Matrix.diagonal fun j => ((f j : ℝ) : ℂ)) i j * x.ofLp j) = _
  rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]

theorem isSelfAdjoint_diagCLM (f : ι → ℝ) : IsSelfAdjoint (diagCLM f) := by
  have hherm : (Matrix.diagonal fun i => ((f i : ℝ) : ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  exact (Matrix.isHermitian_iff_isSelfAdjoint.mp hherm).map (Matrix.toEuclideanCLM (𝕜 := ℂ))

theorem diagCLM_single (f : ι → ℝ) (i₀ : ι) :
    diagCLM f (EuclideanSpace.single i₀ (1 : ℂ))
      = ((f i₀ : ℝ) : ℂ) • EuclideanSpace.single i₀ (1 : ℂ) := by
  ext i
  rw [diagCLM_apply]
  by_cases hi : i = i₀ <;> simp [hi]

omit [DecidableEq ι] in
theorem norm_sq_eq_sum (x : EuclideanSpace ℂ ι) : ‖x‖ ^ 2 = ∑ i, ‖x.ofLp i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem reApplyInnerSelf_diagCLM (f : ι → ℝ) (x : EuclideanSpace ℂ ι) :
    (diagCLM f).reApplyInnerSelf x = ∑ i, f i * ‖x.ofLp i‖ ^ 2 := by
  have hz : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    simpa using RCLike.mul_conj (K := ℂ) z
  set S : ℝ := ∑ i, f i * ‖x.ofLp i‖ ^ 2 with hS
  have h : (inner ℂ (diagCLM f x) x : ℂ) = (S : ℂ) := by
    rw [PiLp.inner_apply, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diagCLM_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    calc x.ofLp i * (((f i : ℝ) : ℂ) * (starRingEnd ℂ) (x.ofLp i))
        = ((f i : ℝ) : ℂ) * (x.ofLp i * (starRingEnd ℂ) (x.ofLp i)) := by ring
      _ = ((f i : ℝ) : ℂ) * ((‖x.ofLp i‖ ^ 2 : ℝ) : ℂ) := by rw [hz]
      _ = ((f i * ‖x.ofLp i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, h]
  simp

/-- **The gapped quadratic form of a diagonal operator.**  If one coordinate of the symbol exceeds
every other by `Δ`, the form is bounded by the top value minus `Δ` times the mass off that
coordinate. -/
theorem reApplyInnerSelf_diagCLM_le (f : ι → ℝ) (i₀ : ι) (Δ : ℝ)
    (h : ∀ i, i ≠ i₀ → f i ≤ f i₀ - Δ) (x : EuclideanSpace ℂ ι) :
    (diagCLM f).reApplyInnerSelf x
      ≤ f i₀ * ‖x‖ ^ 2
        - Δ * (‖x‖ ^ 2 - ‖(inner ℂ (EuclideanSpace.single i₀ (1 : ℂ)) x : ℂ)‖ ^ 2) := by
  classical
  set g : ι → ℝ := fun i => ‖x.ofLp i‖ ^ 2 with hg
  have hgnn : ∀ i, 0 ≤ g i := fun i => by positivity
  set T : ℝ := ∑ i ∈ Finset.univ.erase i₀, g i with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun i _ => hgnn i
  have hnormsq : ‖x‖ ^ 2 = g i₀ + T := by
    rw [norm_sq_eq_sum, ← Finset.add_sum_erase _ g (Finset.mem_univ i₀)]
  have hinner : ‖(inner ℂ (EuclideanSpace.single i₀ (1 : ℂ)) x : ℂ)‖ ^ 2 = g i₀ := by
    rw [EuclideanSpace.inner_single_left]
    simp [hg]
  have hsplit : (diagCLM f).reApplyInnerSelf x
      = f i₀ * g i₀ + ∑ i ∈ Finset.univ.erase i₀, f i * g i := by
    rw [reApplyInnerSelf_diagCLM, ← Finset.add_sum_erase _ (fun i => f i * g i) (Finset.mem_univ i₀)]
  have hbound : ∑ i ∈ Finset.univ.erase i₀, f i * g i ≤ (f i₀ - Δ) * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (h i (Finset.mem_erase.mp hi).1) (hgnn i)
  rw [hsplit, hnormsq, hinner]
  nlinarith [hbound]

end

end HTGeometry
