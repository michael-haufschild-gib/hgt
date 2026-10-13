import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression
import Mathlib.MeasureTheory.Function.L2Space

/-! # Exact energy split across disjoint source coordinates

Discrete prefixes and physical support cuts partition squared response norm.
The retained energy grows and the discarded energy decreases with depth.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory
variable {I E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace α] {μ : Measure α}

theorem lp_norm_sq_add_of_disjoint (x y : lp (fun _ : I => E) 2)
    (h : ∀ i, x i = 0 ∨ y i = 0) : ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + y‖ ^ 2 := by
  have hi : inner ℂ x y = 0 := by
    rw [lp.inner_eq_tsum]
    have he : (fun i => inner ℂ (x i) (y i)) = fun _ => 0 := by
      funext i
      rcases h i with hi | hi <;> simp [hi]
    rw [he]
    simp
  simpa only [pow_two] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hi).symm

theorem l2_norm_sq_add_of_ae_disjoint (x y : Lp E 2 μ)
    (h : ∀ᵐ t ∂μ, x t = 0 ∨ y t = 0) : ‖x‖ ^ 2 + ‖y‖ ^ 2 = ‖x + y‖ ^ 2 := by
  have hi : inner ℂ x y = 0 := by
    rw [L2.inner_def]
    have he : (fun t => inner ℂ (x t) (y t)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [h] with t ht
      rcases ht with ht | ht <;> simp [ht]
    rw [integral_congr_ae he]
    simp
  simpa only [pow_two] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hi).symm

theorem paperCoordinateProjection_energy_split (N : ℕ) (x : VecSeq E) :
    ‖paperCoordinateProjection N x‖ ^ 2 + ‖x - paperCoordinateProjection N x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := lp_norm_sq_add_of_disjoint (paperCoordinateProjection N x)
    (x - paperCoordinateProjection N x) (fun n => by
      simp only [paperCoordinateProjection_coordinate, lp.coeFn_sub, Pi.sub_apply]
      split_ifs <;> simp)
  have he : paperCoordinateProjection N x + (x - paperCoordinateProjection N x) = x := by abel
  simpa only [he] using h

theorem norm_paperCoordinateProjection_monotone (x : VecSeq E) :
    Monotone (fun N => ‖paperCoordinateProjection N x‖) := by
  intro M N hMN
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  simp only [paperCoordinateProjection_coordinate]
  by_cases hn : n < M
  · simp only [if_pos hn, if_pos (lt_of_lt_of_le hn hMN), le_refl]
  · simp only [if_neg hn, norm_zero, norm_nonneg]

theorem norm_paperCoordinateTail_antitone (x : VecSeq E) :
    Antitone (fun N => ‖x - paperCoordinateProjection N x‖) := by
  intro M N hMN
  have h := norm_paperCoordinateProjection_monotone x hMN
  have hM := paperCoordinateProjection_energy_split M x
  have hN := paperCoordinateProjection_energy_split N x
  have hPM := norm_nonneg (paperCoordinateProjection M x)
  have hPN := norm_nonneg (paperCoordinateProjection N x)
  have htM := norm_nonneg (x - paperCoordinateProjection M x)
  have htN := norm_nonneg (x - paperCoordinateProjection N x)
  nlinarith

end
end GaloisForLFunctions.HTGeometry
