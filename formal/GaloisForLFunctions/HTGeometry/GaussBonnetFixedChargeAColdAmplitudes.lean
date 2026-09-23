import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdCancellation
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdHeat

/-!
# Universal cold thermodynamic amplitude products

Combine independently proved radius scales to eliminate the diverging
radius. Products involving latent heat, actual heat capacity, entropy,
volume, temperature and pressure have exact universal limits independent
of the conserved charge/coupling fraction and entropy reference length.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeA_latent_heat_temperature_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALatentHeat w φ τ) * (egbFixedChargeATemperature w φ τ)) atTop (𝓝 (1 / Real.pi)) := by
  have h := (egbFixedChargeALatentHeat_radius_cold_limit w φ).mul (egbFixedChargeATemperature_radius_cold_limit w φ)
  have he : (1 : ℝ) * (1 / Real.pi) = 1 / Real.pi := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => (egbFixedChargeALatentHeat w φ τ / (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeATemperature w φ τ * (egbFixedChargeALargeRadius w φ τ))) = (fun τ => (egbFixedChargeALatentHeat w φ τ) * (egbFixedChargeATemperature w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_entropy_jump_temperature_square_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAEntropyJump w φ τ) * ((egbFixedChargeATemperature w φ τ) ^ (2 : ℕ))) atTop (𝓝 (1 / Real.pi)) := by
  have h := (egbFixedChargeAEntropyJump_radius_square_cold_limit w φ).mul ((egbFixedChargeATemperature_radius_cold_limit w φ).pow 2)
  have he : Real.pi * (1 / Real.pi) ^ (2 : ℕ) = 1 / Real.pi := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => (egbFixedChargeAEntropyJump w φ τ / (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ)) * (egbFixedChargeATemperature w φ τ * (egbFixedChargeALargeRadius w φ τ)) ^ (2 : ℕ)) = (fun τ => (egbFixedChargeAEntropyJump w φ τ) * ((egbFixedChargeATemperature w φ τ) ^ (2 : ℕ))) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_volume_jump_temperature_cube_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAVolumeJump w φ τ) * ((egbFixedChargeATemperature w φ τ) ^ (3 : ℕ))) atTop (𝓝 (4 / (3 * Real.pi ^ (2 : ℕ)))) := by
  have h := (egbFixedChargeAVolumeJump_radius_cube_cold_limit w φ).mul ((egbFixedChargeATemperature_radius_cold_limit w φ).pow 3)
  have he : (4 * Real.pi / 3) * (1 / Real.pi) ^ (3 : ℕ) = 4 / (3 * Real.pi ^ (2 : ℕ)) := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => (egbFixedChargeAVolumeJump w φ τ / (egbFixedChargeALargeRadius w φ τ) ^ (3 : ℕ)) * (egbFixedChargeATemperature w φ τ * (egbFixedChargeALargeRadius w φ τ)) ^ (3 : ℕ)) = (fun τ => (egbFixedChargeAVolumeJump w φ τ) * ((egbFixedChargeATemperature w φ τ) ^ (3 : ℕ))) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_large_heat_capacity_temperature_square_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) * ((egbFixedChargeATemperature w φ τ) ^ (2 : ℕ))) atTop (𝓝 (4 / Real.pi)) := by
  have h := (egbFixedChargeA_large_heat_capacity_radius_square_cold_limit w φ l).mul ((egbFixedChargeATemperature_radius_cold_limit w φ).pow 2)
  have he : (4 * Real.pi) * (1 / Real.pi) ^ (2 : ℕ) = 4 / Real.pi := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => ((egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) / (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ)) * (egbFixedChargeATemperature w φ τ * (egbFixedChargeALargeRadius w φ τ)) ^ (2 : ℕ)) = (fun τ => (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) * ((egbFixedChargeATemperature w φ τ) ^ (2 : ℕ))) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_large_heat_capacity_pressure_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeAPressure w φ τ)) atTop (𝓝 ((3 : ℝ) / 2)) := by
  have h := (egbFixedChargeA_large_heat_capacity_radius_square_cold_limit w φ l).mul (egbFixedChargeAPressure_radius_cold_limit w φ)
  have he : (4 * Real.pi) * (3 / (8 * Real.pi)) = (3 : ℝ) / 2 := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => ((egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) / (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ)) * (egbFixedChargeAPressure w φ τ * (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ))) = (fun τ => (egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeAPressure w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_entropy_jump_pressure_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAEntropyJump w φ τ) * (egbFixedChargeAPressure w φ τ)) atTop (𝓝 ((3 : ℝ) / 8)) := by
  have h := (egbFixedChargeAEntropyJump_radius_square_cold_limit w φ).mul (egbFixedChargeAPressure_radius_cold_limit w φ)
  have he : Real.pi * (3 / (8 * Real.pi)) = (3 : ℝ) / 8 := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => (egbFixedChargeAEntropyJump w φ τ / (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ)) * (egbFixedChargeAPressure w φ τ * (egbFixedChargeALargeRadius w φ τ) ^ (2 : ℕ))) = (fun τ => (egbFixedChargeAEntropyJump w φ τ) * (egbFixedChargeAPressure w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_large_mass_temperature_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeATemperature w φ τ)) atTop (𝓝 (1 / Real.pi)) := by
  have h := (egbFixedChargeA_large_mass_radius_cold_limit w φ).mul (egbFixedChargeATemperature_radius_cold_limit w φ)
  have he : (1 : ℝ) * (1 / Real.pi) = 1 / Real.pi := by field_simp <;> ring
  rw [he] at h
  have hf : (fun τ => ((egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) / (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeATemperature w φ τ * (egbFixedChargeALargeRadius w φ τ))) = (fun τ => (egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)) * (egbFixedChargeATemperature w φ τ)) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp <;> ring
  rwa [hf] at h

theorem egbFixedChargeA_large_gibbs_temperature_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeALargeGibbs w φ l τ * egbFixedChargeATemperature w φ τ) atTop (𝓝 0) := by
  simpa only [mul_zero] using (egbFixedChargeALargeGibbs_cold_limit w φ l).mul (egbFixedChargeATemperature_cold_limit w φ)

end GaloisForLFunctions.HTGeometry
