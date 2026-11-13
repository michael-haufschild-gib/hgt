import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy
import GaloisForLFunctions.HTGeometry.QuadraticTangentRemainder

/-!
# The derivative of the actual ground energy

The transverse gap gives a quadratic remainder in the confinement
coefficient. Its reciprocal parameter dependence determines the tangent.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory WindowTowerOfSpecZ

/-- The confinement coefficient varies reciprocally with the ratio. -/
theorem hasDerivAt_criticalAliasCoefficient {R : ℝ} (hR : 0 < R) :
    HasDerivAt criticalAliasCoefficient (-(criticalAliasCoefficient R) / R) R := by
  have heq (r : ℝ) : criticalAliasCoefficient r = criticalAliasCoefficient 1 / r := by
    simp only [criticalAliasCoefficient, mul_one, div_div]
  have h := (hasDerivAt_const R (criticalAliasCoefficient 1)).div (hasDerivAt_id R) hR.ne'
  change HasDerivAt ((fun _ : ℝ => criticalAliasCoefficient 1) / id)
    ((0 * R - criticalAliasCoefficient 1 * 1) / R ^ 2) R at h
  have hf : ((fun _ : ℝ => criticalAliasCoefficient 1) / id) =
      criticalAliasCoefficient := by
    funext r
    exact (heq r).symm
  rw [hf] at h
  have hc : (0 * R - criticalAliasCoefficient 1 * 1) / R ^ 2 =
      -(criticalAliasCoefficient R) / R := by
    rw [heq R]
    ring
  simpa only [hc] using h

/-- The variational floor vanishes at the finite global threshold. -/
theorem criticalHalfLineGroundEnergy_eq_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    criticalHalfLineGroundEnergy W₀ = 0 := by
  obtain ⟨δ, C, hδ, _, hbound⟩ := criticalHalfLineGroundEnergy_quadratic_tangent hW ht hF
  have h := hbound W₀ hW (by simpa only [sub_self, abs_zero] using hδ.le)
  have habs : |criticalHalfLineGroundEnergy W₀| ≤ 0 := by
    simpa only [sub_self, zero_mul, sub_zero, zero_pow two_ne_zero, mul_zero] using h
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

/-- The ground-energy derivative is the confinement derivative times the critical exponential mass. -/
theorem hasDerivAt_criticalHalfLineGroundEnergy
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    HasDerivAt criticalHalfLineGroundEnergy
      (-(criticalAliasCoefficient W₀) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / W₀) W₀ := by
  obtain ⟨δ, C, hδ, _, hbound⟩ := criticalHalfLineGroundEnergy_quadratic_tangent hW ht hF
  have ha := hasDerivAt_criticalAliasCoefficient hW
  have hlim : Tendsto
      (fun R => |criticalAliasCoefficient R - criticalAliasCoefficient W₀|) (𝓝 W₀) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (ha.continuousAt.tendsto.sub_const (criticalAliasCoefficient W₀)).abs
  have hnear : ∀ᶠ R in 𝓝 W₀, |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ :=
    (hlim.eventually (gt_mem_nhds hδ)).mono fun _ h => h.le
  have hquadratic : ∀ᶠ R in 𝓝 W₀,
      ‖criticalHalfLineGroundEnergy R - criticalHalfLineGroundEnergy W₀ -
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          (criticalAliasCoefficient R - criticalAliasCoefficient W₀)‖ ≤
      C * ‖criticalAliasCoefficient R - criticalAliasCoefficient W₀‖ ^ 2 := by
    filter_upwards [hnear, (lt_mem_nhds hW : ∀ᶠ R in 𝓝 W₀, 0 < R)] with R hη hR
    simpa only [criticalHalfLineGroundEnergy_eq_zero hW ht hF, sub_zero,
      Real.norm_eq_abs, sq_abs, mul_comm] using hbound R hR hη
  have h := HTGeometry.hasDerivAt_of_quadratic_comparison ha hquadratic
  convert h using 1; ring

#print axioms hasDerivAt_criticalHalfLineGroundEnergy

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
