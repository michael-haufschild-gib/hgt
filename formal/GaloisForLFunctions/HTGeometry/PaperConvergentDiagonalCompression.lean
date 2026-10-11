import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression
import GaloisForLFunctions.HTGeometry.SourceCompleteTransience

/-!
# Finite observations of a convergent depth diagonal

Every finite compression has zero compact-ideal cost and converges strongly to the full
history. Operator-norm convergence holds exactly when its limiting character vanishes.
The existing source-head compact-tail theorem supplies the positive direction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Classical
open scoped ENNReal Topology

/-- The coordinate prefix and the native source-head projection are the same operator. -/
theorem paperCoordinateProjection_succ_eq_headProjection (N : ℕ) :
    (paperCoordinateProjection (N + 1) : VecSeq ℂ →L[ℂ] VecSeq ℂ) = headProjection N := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  rw [paperCoordinateProjection_coordinate, headProjection_apply, headWeight]
  by_cases hn : n ≤ N
  · simp [hn]
  · simp [hn]

/-- The two-sided compression of a depth diagonal is its literal finite prefix. -/
theorem paperConvergentDiagonal_compression_apply (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (N : ℕ) (f : VecSeq ℂ) (n : ℕ) :
    paperCoordinateCompression (paperConvergentDiagonal v hv) N f n =
      if n < N then v n * f n else 0 := by
  simp only [paperCoordinateCompression, ContinuousLinearMap.comp_apply,
    paperCoordinateProjection_coordinate, paperConvergentDiagonal_apply]
  split_ifs <;> simp_all

/-- The remainder of a diagonal prefix is exactly the native source-head tail. -/
theorem paperConvergentDiagonal_sub_compression (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (N : ℕ) :
    paperConvergentDiagonal v hv -
      paperCoordinateCompression (paperConvergentDiagonal v hv) (N + 1) =
    paperConvergentDiagonal v hv ∘L
      (ContinuousLinearMap.id ℂ (VecSeq ℂ) - headProjection N) := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperConvergentDiagonal_compression_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, paperConvergentDiagonal_apply, headProjection_apply,
    headWeight]
  by_cases hn : n ≤ N <;> simp [hn]

/-- No finite prefix can close the gap determined by the limiting character. -/
theorem paperConvergentDiagonal_compression_gap (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) (N : ℕ) :
    ‖L‖ ≤ ‖paperConvergentDiagonal v hv -
      paperCoordinateCompression (paperConvergentDiagonal v hv) N‖ :=
  paperConvergentDiagonal_limit_le_norm_sub_compact v hv
    ⟨_, isCompactOperator_paperCoordinateCompression _ N⟩

/-- Prefixes converge in norm exactly when the complete history is compact. -/
theorem paperConvergentDiagonal_norm_compression_tendsto_iff (v : ℕ → ℂ) {L : ℂ}
    (hv : Tendsto v atTop (𝓝 L)) :
    Tendsto (fun N => ‖paperConvergentDiagonal v hv -
      paperCoordinateCompression (paperConvergentDiagonal v hv) (N + 1)‖)
      atTop (𝓝 0) ↔ L = 0 := by
  constructor
  · intro h
    have hle : ‖L‖ ≤ 0 := ge_of_tendsto' h
      (fun N => paperConvergentDiagonal_compression_gap v hv (N + 1))
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  · intro h
    simp_rw [paperConvergentDiagonal_sub_compression]
    exact tendsto_norm_comp_sub_headProjection _
      ((paperConvergentDiagonal_compact_iff v hv).mpr h)

end
end GaloisForLFunctions.HTGeometry
