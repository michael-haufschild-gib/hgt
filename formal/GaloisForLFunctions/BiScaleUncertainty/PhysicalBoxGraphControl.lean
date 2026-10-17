import GaloisForLFunctions.BiScaleUncertainty.PhysicalBoxAffineRegularity
import GaloisForLFunctions.BiScaleUncertainty.CompactSourceGraphAdmission

/-!
# Affine box producers in compact source graphs

Logarithmic Dirichlet mass is bounded by the actual full physical energy.
The constructed affine producer consequently controls diffuse and nodal
multiplicative jump energy with an explicit finite gap-to-width factor.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported Topology
namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

theorem sourceDirichletMass_le_norm_sq (ψ : C_c(ℝ, ℝ)) (q : Velocity) :
    sourceDirichletMass ψ q ≤ ENNReal.ofReal (‖q‖^2) := by
  have hr : -multiplierSourceRadius ψ ≤ multiplierSourceRadius ψ := by
    linarith only [multiplierSourceRadius_pos ψ]
  have hi : IntegrableOn (velocityDensity q)
      (Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      (intervalIntegrable_velocityDensity q _ _).1
  calc
    _ = ENNReal.ofReal (∫ y in Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ),
        velocityDensity q y) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (velocityDensity_nonneg q))).symm
    _ = ENNReal.ofReal (energy q (Real.exp (-multiplierSourceRadius ψ))
        (Real.exp (multiplierSourceRadius ψ))) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
        integral_velocityDensity]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [energy, intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hr), norm_sq_velocity]
      exact setIntegral_le_integral (integrable_velocity_sq q)
        (Eventually.of_forall (fun t => sq_nonneg (q t)))

theorem compact_jumpEnergy_le_norm_sq (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    jumpEnergy (compactMixture ψ weights) q ≤ resistanceMass ψ weights * ENNReal.ofReal (‖q‖^2) := by
  calc
    _ ≤ congestionEnergy (compactMixture ψ weights) q := by
      rw [congestionEnergy_eq_jump_add_slack]
      exact le_add_of_nonneg_right zero_le
    _ ≤ resistanceMass ψ weights * sourceDirichletMass ψ q := compact_congestionEnergy_le ψ weights q
    _ ≤ _ := mul_le_mul_right (sourceDirichletMass_le_norm_sq ψ q) _

theorem compact_boxAverage_affine_jump_le (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (a b s : ℝ) (q : Velocity) :
    jumpEnergy (compactMixture ψ weights) (physicalAffineCommutator a b (physicalBoxAverage s q)) ≤
      resistanceMass ψ weights * ENNReal.ofReal
        (4*|a| *(min 1 (|b*(a-1)|/Real.exp s))^2*‖q‖^2) := by
  exact (compact_jumpEnergy_le_norm_sq ψ weights _).trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (physicalBoxAverage_affine_energy_le a b s q)) _)

theorem compact_boxAverage_affine_bound_ne_top (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (a b s : ℝ) (q : Velocity) :
    resistanceMass ψ weights * ENNReal.ofReal
      (4*|a| *(min 1 (|b*(a-1)|/Real.exp s))^2*‖q‖^2) ≠ ⊤ :=
  ENNReal.mul_ne_top (resistanceMass_ne_top ψ weights) ENNReal.ofReal_ne_top

theorem compact_boxAverage_approximation_tendsto (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0)
    (q : Velocity) :
    Tendsto (fun s : ℝ => jumpEnergy (compactMixture ψ weights) (physicalBoxAverage s q-q))
      atBot (𝓝 0) := by
  have hc : Tendsto (fun _ : ℝ => q) atBot (𝓝 q) := tendsto_const_nhds
  have he : Tendsto (fun s : ℝ => ‖physicalBoxAverage s q-q‖^2) atBot (𝓝 0) := by
    simpa using ((physicalBoxAverage_tendsto q).sub hc).norm.pow 2
  have hr : Tendsto (fun s : ℝ => (resistanceMass ψ weights).toReal *
      ‖physicalBoxAverage s q-q‖^2) atBot (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul (resistanceMass ψ weights).toReal
  have hb (s : ℝ) : jumpEnergy (compactMixture ψ weights) (physicalBoxAverage s q-q) ≤
      ENNReal.ofReal ((resistanceMass ψ weights).toReal * ‖physicalBoxAverage s q-q‖^2) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (resistanceMass_ne_top ψ weights)]
    exact compact_jumpEnergy_le_norm_sq ψ weights _
  have ht : Tendsto (fun s : ℝ => ENNReal.ofReal ((resistanceMass ψ weights).toReal *
      ‖physicalBoxAverage s q-q‖^2)) atBot (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) hb

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
