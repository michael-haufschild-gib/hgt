import GaloisForLFunctions.HTGeometry.WuExponentialEnergy

/-!
# Two characteristic directions

The integration mechanism of Wu, arXiv:2609.08421, Lemma 2.3, on arbitrary
bounded continuous Hilbert or Banach-valued fields. The finite rectangle
constant factors exactly into the masses of the two null directions.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Energy along any continuous observation curve is controlled by the ambient sup norm. -/
theorem energy_comp_le {X : Type*} [TopologicalSpace X]
    (d t : ℝ) (f : BoundedContinuousFunction X E) (p : C(ℝ, X)) :
    energy d t (fun s => f (p s)) ≤ mass d t * ‖f‖ ^ (2 : ℕ) := by
  calc energy d t (fun s => f (p s)) ≤ mass d t * ‖f.compContinuous p‖ ^ (2 : ℕ) :=
      energy_le_mass d t (f.compContinuous p)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (f.norm_compContinuous_le p))
      (mass_nonneg d t)

/-- Energy on a rectangle, integrating both characteristic directions. -/
def rectangleEnergy (d u v : ℝ) (f : ℝ × ℝ → E) : ℝ :=
  ∫ s in (0 : ℝ)..|u|, weight d u s * energy d v (fun r => f (s, r))

theorem rectangleEnergy_nonneg (d u v : ℝ) (f : ℝ × ℝ → E) :
    0 ≤ rectangleEnergy d u v f := by
  exact intervalIntegral.integral_nonneg (abs_nonneg u)
    (fun s _ => mul_nonneg (weight_pos d u s).le (energy_nonneg _ _ _))

theorem continuous_slice_energy (d v : ℝ) (f : BoundedContinuousFunction (ℝ × ℝ) E) :
    Continuous (fun s => energy d v (fun r => f (s, r))) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((continuous_weight d v).comp continuous_snd).mul (f.continuous.norm.pow 2)

/-- Exact finite-rectangle version of the repeated integration estimate. -/
theorem rectangleEnergy_le_mass (d u v : ℝ) (f : BoundedContinuousFunction (ℝ × ℝ) E) :
    rectangleEnergy d u v f ≤ mass d u * mass d v * ‖f‖ ^ (2 : ℕ) := by
  calc rectangleEnergy d u v f ≤
      ∫ s in (0 : ℝ)..|u|, weight d u s * (mass d v * ‖f‖ ^ (2 : ℕ)) := by
        apply intervalIntegral.integral_mono_on (abs_nonneg u)
          (((continuous_weight d u).mul (continuous_slice_energy d v f)).intervalIntegrable 0 |u|)
          (((continuous_weight d u).mul continuous_const).intervalIntegrable 0 |u|)
        intro s _
        exact mul_le_mul_of_nonneg_left
          (energy_comp_le d v f ⟨fun r => (s, r), continuous_const.prodMk continuous_id⟩)
          (weight_pos d u s).le
    _ = _ := by rw [intervalIntegral.integral_mul_const, integral_weight]; ring

/-- Two integrations gain two powers of the positive damping rate in squared energy. -/
theorem rectangleEnergy_le (d u v : ℝ) (f : BoundedContinuousFunction (ℝ × ℝ) E) :
    rectangleEnergy d u v f ≤ ‖f‖ ^ (2 : ℕ) / (2 * Real.exp d) ^ (2 : ℕ) := by
  calc rectangleEnergy d u v f ≤ mass d u * mass d v * ‖f‖ ^ (2 : ℕ) :=
      rectangleEnergy_le_mass d u v f
    _ ≤ (1 / (2 * Real.exp d)) * (1 / (2 * Real.exp d)) * ‖f‖ ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (mass_le d u) (mass_le d v) (mass_nonneg d v) (by positivity)
    _ = _ := by ring

/-- The full rectangle gains one inverse damping rate in the L² norm. -/
theorem sqrt_rectangleEnergy_le (d u v : ℝ) (f : BoundedContinuousFunction (ℝ × ℝ) E) :
    Real.sqrt (rectangleEnergy d u v f) ≤ ‖f‖ / (2 * Real.exp d) := by
  calc Real.sqrt (rectangleEnergy d u v f) ≤
      Real.sqrt (‖f‖ ^ (2 : ℕ) / (2 * Real.exp d) ^ (2 : ℕ)) := Real.sqrt_le_sqrt (rectangleEnergy_le d u v f)
    _ = _ := by rw [Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)]

/-- The two outgoing edge norms share the square-root damping gain. -/
theorem edge_energy_sum_le (d u v : ℝ) (f : BoundedContinuousFunction (ℝ × ℝ) E) :
    Real.sqrt (energy d u (fun s => f (s, |v|))) +
      Real.sqrt (energy d v (fun r => f (|u|, r))) ≤
        2 * ‖f‖ / Real.sqrt (2 * Real.exp d) := by
  have h (t : ℝ) (p : C(ℝ, ℝ × ℝ)) :
      Real.sqrt (energy d t (fun s => f (p s))) ≤ ‖f‖ / Real.sqrt (2 * Real.exp d) := by
    calc Real.sqrt (energy d t (fun s => f (p s))) ≤
        ‖f.compContinuous p‖ / Real.sqrt (2 * Real.exp d) := sqrt_energy_le d t (f.compContinuous p)
      _ ≤ _ := div_le_div_of_nonneg_right (f.norm_compContinuous_le p) (Real.sqrt_nonneg _)
  have hu := h u ⟨fun s => (s, |v|), continuous_id.prodMk continuous_const⟩
  have hv := h v ⟨fun r => (|u|, r), continuous_const.prodMk continuous_id⟩
  calc _ ≤ ‖f‖ / Real.sqrt (2 * Real.exp d) + ‖f‖ / Real.sqrt (2 * Real.exp d) :=
      add_le_add hu hv
    _ = _ := by ring

/-- Constant fields attain the exact product of finite-interval masses. -/
theorem rectangleEnergy_const (d u v : ℝ) (x : E) :
    rectangleEnergy d u v (fun _ => x) = mass d u * mass d v * ‖x‖ ^ (2 : ℕ) := by
  simp only [rectangleEnergy, energy_const, intervalIntegral.integral_mul_const, integral_weight]
  ring

end
end GaloisForLFunctions.HTGeometry.Wu
