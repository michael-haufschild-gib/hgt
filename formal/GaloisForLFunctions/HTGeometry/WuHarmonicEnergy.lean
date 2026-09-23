import GaloisForLFunctions.HTGeometry.WuDoubleNullEnergy
import GaloisForLFunctions.HTGeometry.BoundedMultiplierCalculus
import GaloisForLFunctions.HTGeometry.BohrAPWitnesses

/-!
# Exponential energy for harmonic evolution and Bohr phases

Wu's integration estimate applies to the existing multiplication evolution
on an arbitrary spectral measure. Unbounded continuous dispersion functions
are admitted: multiplication by their phases remains unitary. Bohr phase
modulation preserves the weighted energy exactly, so the estimate alone
cannot detect oscillatory cancellation.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory
noncomputable section

section Multiplier
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  (μ : Measure α)

/-- Exact energy for arbitrary continuous real dispersion and arbitrary spectral measure. -/
theorem multiplier_energy (ω : C(α, ℝ)) (x : Lp ℂ 2 μ) (d t : ℝ) :
    energy d t (fun s => freeGroup ω ω.continuous.measurable s x) = mass d t * ‖x‖ ^ (2 : ℕ) := by
  unfold energy
  simp_rw [norm_freeGroup_apply]
  rw [intervalIntegral.integral_mul_const, integral_weight]

/-- Initial-state errors retain the same exact weighted energy identity. -/
theorem multiplier_difference_energy (ω : C(α, ℝ)) (x y : Lp ℂ 2 μ) (d t : ℝ) :
    energy d t (fun s => freeGroup ω ω.continuous.measurable s x -
      freeGroup ω ω.continuous.measurable s y) = mass d t * ‖x - y‖ ^ (2 : ℕ) := by
  simp_rw [← map_sub]
  exact multiplier_energy μ ω (x - y) d t

/-- Two independent dispersion directions saturate the rectangle constant. -/
theorem multiplier_rectangle_energy (ω ν : C(α, ℝ)) (x : Lp ℂ 2 μ) (d u v : ℝ) :
    rectangleEnergy d u v (fun p => freeGroup ω ω.continuous.measurable p.1
      (freeGroup ν ν.continuous.measurable p.2 x)) = mass d u * mass d v * ‖x‖ ^ (2 : ℕ) := by
  unfold rectangleEnergy energy
  simp_rw [norm_freeGroup_apply]
  rw [intervalIntegral.integral_mul_const, integral_weight,
    intervalIntegral.integral_mul_const, integral_weight]
  ring
end Multiplier

/-- A Bohr phase has the same weighted energy as a constant unit signal. -/
theorem bohr_character_energy (lam d t : ℝ) : energy d t (bcfChar lam) = mass d t := by
  unfold energy
  simp_rw [norm_bcfChar_apply, one_pow, mul_one]
  exact integral_weight d t

/-- Frequency modulation leaves the complete weighted energy unchanged. -/
theorem bohr_modulation_energy (f : ℝ → ℂ) (lam d t : ℝ) :
    energy d t (fun s => bcfChar lam s * f s) = energy d t f := by
  unfold energy
  simp_rw [norm_mul, norm_bcfChar_apply, one_mul]

/-- Finite harmonic synthesis has a rate-dependent bound uniform in all frequencies and collisions. -/
theorem finite_bohr_energy_le {ι : Type*} (S : Finset ι) (c : ι → ℂ) (lam : ι → ℝ) (d t : ℝ) :
    energy d t (fun s => ∑ i ∈ S, c i * bcfChar (lam i) s) ≤
      (∑ i ∈ S, ‖c i‖) ^ (2 : ℕ) / (2 * Real.exp d) := by
  let f : BoundedContinuousFunction ℝ ℂ := ∑ i ∈ S, c i • bcfChar (lam i)
  have he (s : ℝ) : f s = ∑ i ∈ S, c i * bcfChar (lam i) s := by simp [f]
  have hb : ‖f‖ ≤ ∑ i ∈ S, ‖c i‖ := by
    apply (BoundedContinuousFunction.norm_le (Finset.sum_nonneg (fun i _ => norm_nonneg (c i)))).mpr
    intro s
    rw [he]
    calc ‖∑ i ∈ S, c i * bcfChar (lam i) s‖ ≤ ∑ i ∈ S, ‖c i * bcfChar (lam i) s‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_bcfChar_apply, mul_one]
  have hh := (energy_le d t f).trans (div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg (c i)))).mpr hb)
    (by positivity))
  simpa only [energy, he] using hh

end
end GaloisForLFunctions.HTGeometry.Wu
