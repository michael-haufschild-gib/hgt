import GaloisForLFunctions.HTGeometry.PaperRotationNormRate
import GaloisForLFunctions.HTGeometry.UniversalSpectralSemigroupWallCrossingLaw

/-! # The complex first-order phase defect retains its orientation -/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

theorem paperRotationPhase_sub_norm_le (s t : ℝ) :
    ‖paperRotationPhase s - paperRotationPhase t‖ ≤ |s - t| := by
  have he : paperRotationPhase s - paperRotationPhase t =
      (paperRotationPhase (s - t) - 1) * paperRotationPhase t := by
    rw [sub_mul, one_mul, ← paperRotationPhase_add, sub_add_cancel]
  rw [he, norm_mul, paperRotationPhase_norm, mul_one]
  exact paperRotationPhase_norm_le _

theorem paperRotationPhase_lipschitz : LipschitzWith 1 paperRotationPhase := by
  apply LipschitzWith.mk_one
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs] using paperRotationPhase_sub_norm_le s t

theorem paperRotationPhase_scaled_eq_kernel (t : ℝ) (n : ℕ) :
    (((n : ℝ) + 1 : ℝ) : ℂ) * (paperRotationPhase (t / ((n : ℝ) + 1)) - 1) =
      (t : ℂ) * Complex.I *
        forwardWindowKernel (((t / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) := by
  by_cases ht : t = 0
  · simp [ht]
  · have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [forwardWindowKernel_of_ne
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero ht hn)) Complex.I_ne_zero)]
    change _ * (Complex.exp _ - 1) = _
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht]

theorem paperRotationPhase_scaled_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) *
      (paperRotationPhase (t / ((n : ℝ) + 1)) - 1))
      atTop (𝓝 ((t : ℂ) * Complex.I)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hz : Tendsto (fun n : ℕ => (((t / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    simpa using ((Complex.continuous_ofReal.tendsto 0).comp ht).mul_const Complex.I
  have h := ((continuous_forwardWindowKernel.tendsto 0).comp hz).const_mul
    ((t : ℂ) * Complex.I)
  simpa only [Function.comp_def, forwardWindowKernel_zero, mul_one,
    ← paperRotationPhase_scaled_eq_kernel] using h

end
end GaloisForLFunctions.HTGeometry
