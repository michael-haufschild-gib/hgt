import GaloisForLFunctions.RHTower.CausalMobiusThetaLargestPrime
import GaloisForLFunctions.RHTower.CausalMobiusThetaPhysicalSource
import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauBounds
import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauSecondOrder
import GaloisForLFunctions.RHTower.ConstrainedWeilPolarDerivativeTest
import GaloisForLFunctions.RHTower.ConstrainedWeilWeightedRayBounds
import GaloisForLFunctions.RHTower.DualDiagonalContour
import GaloisForLFunctions.RHTower.EvenWeilRHCriterion
import GaloisForLFunctions.RHTower.GammaDampedNearField

/-!
# Uniform constants discharged in `RHTower` (A)

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower

open Complex Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry MeasureTheory Metric Polynomial Set Topology Zeta23 intervalIntegral
open scoped Real

/-- `abs_thetaIncrement_le_of_inv_cube` with its constants supplied by
`RHTower.exists_abs_thetaCuspSeed_le_inv_cube`. -/
theorem abs_thetaIncrement_le_of_inv_cube_uniform :
    ∃ (Cg : ℝ), ∀ (N : ℕ) (r : ℕ), 1 ≤ N → 1 ≤ r →
      |thetaIncrement N r| ≤ 2 * Cg * (N : ℝ) ^ 3 / (r : ℝ) ^ 3 := by
  obtain ⟨Cg, h_0_0, h_0_1⟩ := RHTower.exists_abs_thetaCuspSeed_le_inv_cube
  refine ⟨Cg, ?_⟩
  intro N r hN hr
  apply abs_thetaIncrement_le_of_inv_cube <;> assumption

/-- `abs_thetaCuspSeed_natCast_div_le` with its constants supplied by
`RHTower.exists_abs_thetaCuspSeed_le_inv_cube`. -/
theorem abs_thetaCuspSeed_natCast_div_le_uniform :
    ∃ (Cg : ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (r : ℕ),
      |thetaCuspSeed (r / N)| ≤ Cg * N ^ 3 * ((r : ℝ) ^ 3)⁻¹ := by
  obtain ⟨Cg, h_0_0, h_0_1⟩ := RHTower.exists_abs_thetaCuspSeed_le_inv_cube
  refine ⟨Cg, ?_⟩
  intro N hN r
  apply abs_thetaCuspSeed_natCast_div_le <;> assumption

/-- `norm_integral_edgeDeriv_cexp_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_bound`. -/
theorem norm_integral_edgeDeriv_cexp_le_uniform :
    ∃ (M₀ : ℝ), ∀ (c : ℂ),
      ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((deriv plateauEdge s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖ ≤ M₀ * Real.exp (|c.re| / 4) / 4 := by
  obtain ⟨M₀, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_bound
  refine ⟨M₀, ?_⟩
  intro c
  apply norm_integral_edgeDeriv_cexp_le <;> assumption

/-- `norm_integral_edgeDerivDeriv_cexp_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_deriv_bound`. -/
theorem norm_integral_edgeDerivDeriv_cexp_le_uniform :
    ∃ (M₀ : ℝ), ∀ (c : ℂ),
      ‖∫ s in (0 : ℝ)..(1 / 4 : ℝ), ((deriv (deriv plateauEdge) s : ℝ) : ℂ) * Complex.exp (c * (s : ℂ))‖ ≤ M₀ * Real.exp (|c.re| / 4) / 4 := by
  obtain ⟨M₀, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_deriv_bound
  refine ⟨M₀, ?_⟩
  intro c
  apply norm_integral_edgeDerivDeriv_cexp_le <;> assumption

/-- `abs_deriv_plateauBump_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_global_bound`. -/
theorem abs_deriv_plateauBump_le_uniform :
    ∃ (K : ℝ), ∀ (a : ℝ) (u : ℝ),
      |deriv plateauEdge u * plateauEdge (a - u) - plateauEdge u * deriv plateauEdge (a - u)| ≤ 2 * K := by
  obtain ⟨K, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_global_bound
  refine ⟨K, ?_⟩
  intro a u
  apply abs_deriv_plateauBump_le <;> assumption

/-- `abs_plateauProfileDeriv_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_global_bound`. -/
theorem abs_plateauProfileDeriv_le_uniform :
    ∃ (K : ℝ), ∀ (a : ℝ) (u : ℝ),
      |plateauProfileDeriv a u| ≤ 4 * K := by
  obtain ⟨K, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_global_bound
  refine ⟨K, ?_⟩
  intro a u
  apply abs_plateauProfileDeriv_le <;> assumption

/-- `norm_deriv_twistedOddTest_plateau_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_global_bound`. -/
theorem norm_deriv_twistedOddTest_plateau_le_uniform :
    ∃ (K : ℝ), ∀ (a : ℝ) (ha0 : 0 ≤ a) (γ : ℝ) (x : ℝ),
      ‖deriv (twistedOddTest (plateauProfile a ha0) γ : ℝ → ℂ) x‖ ≤ |γ| + 4 * K := by
  obtain ⟨K, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_global_bound
  refine ⟨K, ?_⟩
  intro a ha0 γ x
  apply norm_deriv_twistedOddTest_plateau_le <;> assumption

/-- `norm_sq_twistedPlateau_polarDerivativeSource_le` with its constants supplied by
`RHTower.exists_plateauEdge_deriv_global_bound`. -/
theorem norm_sq_twistedPlateau_polarDerivativeSource_le_uniform :
    ∃ (K : ℝ), ∀ (a : ℝ) (ha0 : 0 ≤ a) (γ : ℝ) (A : SuzukiPositiveAperture) (hA : a < A.1),
      ‖ccmArchimedeanFormToAperture A ((twistedOddTest (plateauProfile a ha0) γ).polarDerivativeSource A hA).toCCMFormVector‖ ^ 2 ≤ 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 := by
  obtain ⟨K, h_0_0, h_0_1⟩ := RHTower.exists_plateauEdge_deriv_global_bound
  refine ⟨K, ?_⟩
  intro a ha0 γ A hA
  apply norm_sq_twistedPlateau_polarDerivativeSource_le <;> assumption

/-- `norm_twistedMoment_plateau_le₂` with its constants supplied by
`RHTower.exists_plateau_coeff_bound₂`. -/
theorem norm_twistedMoment_plateau_le₂_uniform :
    ∃ (M : ℝ), ∀ (Θ : ℝ), 0 ≤ Θ → ∀ (a : ℝ), 1 / 2 ≤ a → ∀ (ha0 : 0 ≤ a) (b : ℝ) (μ : ℝ), |b| ≤ Θ →
      ‖twistedMoment (plateauProfile a ha0) b μ‖ ≤ 4 * M * Real.exp (Θ / 4) * Real.exp (a * Θ) * (if (b : ℂ) + I * (μ : ℂ) = 0 then 0 else 1 / ‖(b : ℂ) + I * (μ : ℂ)‖ ^ (2 : ℕ)) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_plateau_coeff_bound₂
  refine ⟨M, ?_⟩
  intro Θ hΘ a ha ha0 b μ hb
  apply norm_twistedMoment_plateau_le₂ <;> assumption

/-- `norm_dualDiagonalIntegrand_left_le` with its constants supplied by
`RHTower.exists_norm_zetaChi_le_rightStrip`, `RHTower.exists_norm_riemannZeta_le_leftStrip`. -/
theorem norm_dualDiagonalIntegrand_left_le_uniform :
    ∃ (Cχ : ℝ) (Cζ : ℝ), ∀ (d : ℝ) (c : ℝ) (x : ℝ) (τ : ℝ), 0 < d → d ≤ 1 / 8 → 0 < c → 0 < x → ∀ (v : ℝ),
      ‖dualDiagonalIntegrand d c x τ (((-(1 / 4) : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
  obtain ⟨Cχ, h_0_0, h_0_1⟩ := RHTower.exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζ, h_1_0, h_1_1⟩ := RHTower.exists_norm_riemannZeta_le_leftStrip
  refine ⟨Cχ, Cζ, ?_⟩
  intro d c x τ hd hd8 hc hx v
  apply norm_dualDiagonalIntegrand_left_le <;> assumption

/-- `integral_cutSourceDeriv_le` with its constants supplied by
`RHTower.exists_bound_deriv_unitCutoff`. -/
theorem integral_cutSourceDeriv_le_uniform :
    ∃ (C₁ : ℝ), ∀ (g : ℝ → ℝ) (g' : ℝ → ℝ), Integrable (fun x => |g x| * Real.exp (|x| / 2)) → Integrable (fun x => |g' x| * Real.exp (|x| / 2)) → ∀ (c : ℝ) (R : ℝ), 1 ≤ R →
      ∫ x, |cutSourceDeriv g g' c R x| * Real.exp (|x| / 2) ≤ C₁ * (∫ x, |g x| * Real.exp (|x| / 2)) + (∫ x, |g' x| * Real.exp (|x| / 2)) + |c| * ∫ x, |deriv (unitCutoff : ℝ → ℝ) x| * Real.exp (|x| / 2) := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_bound_deriv_unitCutoff
  refine ⟨C₁, ?_⟩
  intro g g' hI0 hI1 c R hR
  apply integral_cutSourceDeriv_le <;> assumption

/-- `tendsto_scaled_regPart` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_scaled_regPart_uniform :
    ∀ (v : ℝ),
      Tendsto (fun ε : ℝ => ((ε : ℂ)) ^ 2 * gammaDampedRegPart (1 + ε) (ε * v)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  intro v
  apply tendsto_scaled_regPart <;> assumption

/-- `tendsto_scaledPolePart` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_scaledPolePart_uniform :
    ∀ (v : ℝ),
      Tendsto (fun ε : ℝ => scaledPolePart ε v) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((1 / riemannZeta 2) * ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹))) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  intro v
  apply tendsto_scaledPolePart <;> assumption

/-- `tendsto_scaledPoleIntegrand` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_scaledPoleIntegrand_uniform :
    ∀ (v : ℝ),
      Tendsto (fun ε : ℝ => scaledPoleIntegrand ε v) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((((1 / riemannZeta 2) * ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 * HTGeometry.gammaCyclicDensity 0)) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  intro v
  apply tendsto_scaledPoleIntegrand <;> assumption

/-- `tendsto_integral_scaledPoleIntegrand` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_integral_scaledPoleIntegrand_uniform :
    Tendsto (fun ε : ℝ => ∫ v : ℝ, scaledPoleIntegrand ε v) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ v : ℝ, (((1 / riemannZeta 2) * ((criticalDirection v)⁻¹ ^ 2 - (criticalDirection v)⁻¹)).im) ^ 2 * HTGeometry.gammaCyclicDensity 0)) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  apply tendsto_integral_scaledPoleIntegrand <;> assumption

/-- `tendsto_nearPoleEnergy` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_nearPoleEnergy_uniform :
    Tendsto nearPoleEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((1 / (2 * Real.pi)) * (HTGeometry.gammaCyclicDensity 0 * ((6 / Real.pi ^ 2) ^ 2 * Real.pi)))) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  apply tendsto_nearPoleEnergy <;> assumption

end RHTower
