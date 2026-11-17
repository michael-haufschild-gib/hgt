import GaloisForLFunctions.HTGeometry.HardyDiskSpace
import GaloisForLFunctions.HTGeometry.PaperRecurrentDiagonal
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Compact cancellation for arbitrary finite rotation sums

The finite-combination question of arXiv:2610.35415 has an exact answer
for disk rotations on the Hardy space. Repeated rotations combine by
adding their coefficients; compactness forces every resulting coefficient
to vanish. Cesàro mean-square rigidity removes any root-of-unity or
rational-angle restriction.
-/

open Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Dynamics
open HTGeometry _root_.RHTower
noncomputable section

private theorem rotation_bound (z : Circle) (k : ℕ) : ‖(z : ℂ) ^ k‖ ≤ 1 := by
  rw [norm_pow, Circle.norm_coe, one_pow]

/-- Composition with an arbitrary disk rotation in actual Hardy coordinates. -/
def phaseRotation (z : Circle) : HardyDisk →L[ℂ] HardyDisk :=
  lpDiagonalCLM (fun k => (z : ℂ) ^ k) (by norm_num) (rotation_bound z)

theorem phaseRotation_hardyFun (z : Circle) (f : HardyDisk) (w : ℂ) :
    hardyFun (phaseRotation z f) w = hardyFun f ((z : ℂ) * w) := by
  unfold hardyFun
  apply tsum_congr
  intro k
  change (z : ℂ) ^ k * f k * w ^ k = f k * ((z : ℂ) * w) ^ k
  rw [mul_pow]
  ring

theorem phaseRotation_unitary (z : Circle) :
    phaseRotation z ∈ unitary (HardyDisk →L[ℂ] HardyDisk) := by
  apply paperBoundedDiagonal_unitary _ (by norm_num) (rotation_bound z)
  intro k
  rw [norm_pow, Circle.norm_coe, one_pow]

/-- Full exponential multiplier, allowing equal rotations and arbitrary complex coefficients. -/
def phaseRotationSymbol {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) (k : ℕ) : ℂ :=
  finiteExponentialPencil Finset.univ c (fun i => (z i : ℂ)) k

theorem phaseRotationSymbol_bound {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) (k : ℕ) :
    ‖phaseRotationSymbol z c k‖ ≤ ∑ i, ‖c i‖ := by
  unfold phaseRotationSymbol finiteExponentialPencil
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one]

/-- A finite sum of genuine rotation-composition operators. -/
def phaseRotationSum {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) : HardyDisk →L[ℂ] HardyDisk :=
  lpDiagonalCLM (phaseRotationSymbol z c) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (phaseRotationSymbol_bound z c)

theorem phaseRotationSum_eq_sum {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    phaseRotationSum z c = ∑ i, c i • phaseRotation (z i) := by
  ext f k
  simp only [phaseRotationSum, phaseRotationSymbol, finiteExponentialPencil,
    phaseRotation, lpDiagonalCLM_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact coefficient attached to one geometric rotation, with repetitions aggregated. -/
def rotationFiber {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) (u : ℂ) : ℂ :=
  finiteExponentialFiberCoefficient Finset.univ c (fun i => (z i : ℂ)) u

private theorem phaseRotationSum_zero_of_fibers {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ)
    (h : ∀ u ∈ Finset.univ.image (fun i => (z i : ℂ)), rotationFiber z c u = 0) :
    phaseRotationSum z c = 0 := by
  have hs (k : ℕ) : phaseRotationSymbol z c k = 0 := by
    rw [phaseRotationSymbol, ← finiteExponentialPencil_image_eq]
    unfold finiteExponentialPencil
    apply Finset.sum_eq_zero
    intro u hu
    change rotationFiber z c u * u ^ k = 0
    rw [h u hu, zero_mul]
  ext f k
  change phaseRotationSymbol z c k * f k = 0
  rw [hs, zero_mul]

/-- Compactness is equivalent to exact cancellation in every rotation fiber. -/
theorem phaseRotationSum_compact_iff {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    IsCompactOperator (phaseRotationSum z c) ↔
      ∀ u ∈ Finset.univ.image (fun i => (z i : ℂ)), rotationFiber z c u = 0 := by
  constructor
  · intro h u hu
    by_contra hc
    have hn := tendsto_norm_of_isCompactOperator_lpDiagonalCLM _
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (phaseRotationSymbol_bound z c) h
    have hz : Tendsto (phaseRotationSymbol z c) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hn
    exact not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient
      Finset.univ c (fun i => (z i : ℂ)) (fun i _ => Circle.norm_coe _)
      ⟨u, hu, hc⟩ hz
  · intro h
    rw [phaseRotationSum_zero_of_fibers z c h]
    exact isCompactOperator_zero

/-- No nonzero finite rotation-composition sum can become compact. -/
theorem phaseRotationSum_compact_iff_zero {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    IsCompactOperator (phaseRotationSum z c) ↔ phaseRotationSum z c = 0 := by
  constructor
  · intro h
    exact phaseRotationSum_zero_of_fibers z c ((phaseRotationSum_compact_iff z c).mp h)
  · intro h
    rw [h]
    exact isCompactOperator_zero

#print axioms phaseRotation_hardyFun
#print axioms phaseRotation_unitary
#print axioms phaseRotationSum_eq_sum
#print axioms phaseRotationSum_compact_iff
#print axioms phaseRotationSum_compact_iff_zero
end
end GaloisForLFunctions.HilbertMetric.Dynamics
