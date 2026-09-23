import GaloisForLFunctions.HTGeometry.ObserverDistance
import GaloisForLFunctions.HTGeometry.HermitianFlat

/-!
# A maximal flat is Euclidean

The directions diagonal in one frame carry the tangent norm as the Euclidean norm of their weights,
and the logarithm identifies the points of the flat with those directions.  So the distance between
two points of a flat, measured in the logarithmic chart, is the Euclidean distance of their weights:
a maximal flat is a Euclidean space, of dimension `N - 1` after the traceless normalization.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The tangent norm of a diagonal direction -/

/-- **The tangent norm of a diagonal direction is the Euclidean norm of its weights.** -/
theorem hsNorm_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap (diagOp b w))
      = Real.sqrt (∑ i, w i ^ (2 : ℕ)) := by
  rw [hsNorm_toCLM_diagonal b (diagOp_apply_basis b w)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem diagOp_sub (b : OrthonormalBasis (Fin n) ℂ E) (w w' : Fin n → ℝ) :
    diagOp b w - diagOp b w' = diagOp b (w - w') := by
  have h := (diagOpₗ b).map_sub w w'
  simp only [diagOpₗ_apply] at h
  exact h.symm

/-- **The tangent distance of two diagonal directions is the Euclidean distance of their
weights.** -/
theorem hsNorm_diagOp_sub (b : OrthonormalBasis (Fin n) ℂ E) (w w' : Fin n → ℝ) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap (diagOp b w - diagOp b w'))
      = Real.sqrt (∑ i, (w i - w' i) ^ (2 : ℕ)) := by
  rw [diagOp_sub b w w', hsNorm_diagOp b (w - w')]
  congr 1

/-! ## The flat in the logarithmic chart -/

/-- **The logarithm of a point of a flat is its direction.** -/
theorem logOp_metricRay_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    (w : Fin n → ℝ) :
    logOp (isSymmetric_metricRay (isSymmetric_diagOp b w) hn 1) hn = diagOp b w :=
  logOp_metricRay (isSymmetric_diagOp b w) hn

/-- **A maximal flat is Euclidean.**  The distance between two points of a flat, measured by the
tangent norm of the difference of their logarithms, is the Euclidean distance of their weights.  So
in the logarithmic chart a flat is a Euclidean space — of dimension `N - 1` once the directions are
normalized to be traceless. -/
theorem flat_dist_eq (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    (w w' : Fin n → ℝ) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap
        (logOp (isSymmetric_metricRay (isSymmetric_diagOp b w) hn 1) hn
          - logOp (isSymmetric_metricRay (isSymmetric_diagOp b w') hn 1) hn))
      = Real.sqrt (∑ i, (w i - w' i) ^ (2 : ℕ)) := by
  rw [logOp_metricRay_diagOp b hn w, logOp_metricRay_diagOp b hn w', hsNorm_diagOp_sub b w w']

/-- **Distinct weights give distinct points of the flat.**  The exponential parametrizes a flat by
its weight space faithfully. -/
theorem metricRay_diagOp_injective (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {w w' : Fin n → ℝ}
    (h : ((metricRay (diagOp b w) 1 : E →ₗ[ℂ] E)) = ((metricRay (diagOp b w') 1 : E →ₗ[ℂ] E))) :
    w = w' := by
  have hlog : diagOp b w = diagOp b w' := by
    rw [← logOp_metricRay_diagOp b hn w, ← logOp_metricRay_diagOp b hn w']
    congr 1
  exact diagOpₗ_injective b hlog

/-- **The distance in a flat vanishes only on the diagonal.** -/
theorem flat_dist_eq_zero_iff (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    (w w' : Fin n → ℝ) :
    ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap
        (logOp (isSymmetric_metricRay (isSymmetric_diagOp b w) hn 1) hn
          - logOp (isSymmetric_metricRay (isSymmetric_diagOp b w') hn 1) hn)) = 0 ↔ w = w' := by
  rw [flat_dist_eq b hn w w']
  constructor
  · intro h
    have hnn : 0 ≤ ∑ i, (w i - w' i) ^ (2 : ℕ) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, (w i - w' i) ^ (2 : ℕ) = 0 := (Real.sqrt_eq_zero hnn).1 h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (w i - w' i)).1 hsum i
      (Finset.mem_univ i)
    have := pow_eq_zero_iff two_ne_zero |>.1 hi
    linarith [this]
  · rintro rfl
    simp

end GaloisForLFunctions.HTGeometry
