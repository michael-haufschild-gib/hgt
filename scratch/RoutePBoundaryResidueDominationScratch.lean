import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

open Complex MeasureTheory Filter Topology

namespace RHTower

private noncomputable def positiveLaplace (ν : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) ∂ν

theorem positiveLaplace_boundary_residue_norm_le_real_mass
    (ν : Measure ℝ) (γ B : ℝ) (c : ℂ)
    (hreal : Tendsto
      (fun σ : ℝ => σ * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-σ * u) ∂ν)
      (𝓝[>] (0 : ℝ)) (𝓝 B))
    (himag : Tendsto
      (fun σ : ℝ => (σ : ℂ) * positiveLaplace ν ((σ : ℂ) + γ * I))
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ‖c‖ ≤ B := by
  have hle : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ),
      ‖(σ : ℂ) * positiveLaplace ν ((σ : ℂ) + γ * I)‖ ≤
        σ * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-σ * u) ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
    have hbound := GaloisForLFunctions.RHTower.norm_complexLaplace_le ν
      ((σ : ℂ) + γ * I)
    have hre : (((σ : ℂ) + γ * I)).re = σ := by simp
    rw [hre] at hbound
    exact mul_le_mul_of_nonneg_left hbound hσ.le
  have hnorm : Tendsto
      (fun σ : ℝ => ‖(σ : ℂ) * positiveLaplace ν ((σ : ℂ) + γ * I)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖c‖) := himag.norm
  exact le_of_tendsto_of_tendsto hnorm hreal hle

end RHTower
