import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeDenseCutoffEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeSmallCutoffEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeIntermediateEnergy

/-!
# Complete physical energy vanishes for independently growing horizons and cutoffs

The dense-cutoff, logarithmic-cutoff and intermediate estimates cover every
pair of scales. Thus no polynomial relation between cutoff and horizon is
needed for vanishing of the literal complete physical energy.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

private theorem tendsto_of_partition {α β : Type*} [TopologicalSpace β]
    {f : α → β} {l : Filter α} {b : β} (s : Set α)
    (hs : Tendsto f (l ⊓ principal s) (𝓝 b))
    (hc : Tendsto f (l ⊓ principal sᶜ) (𝓝 b)) : Tendsto f l (𝓝 b) := by
  rw [Filter.tendsto_def] at hs hc ⊢
  intro U hU
  have hs' := eventually_inf_principal.mp (hs U hU)
  have hc' := eventually_inf_principal.mp (hc U hU)
  filter_upwards [hs', hc'] with x hx hy
  by_cases h : x ∈ s
  · exact hx h
  · exact hy h

/-- Every independently growing prime cutoff and horizon has vanishing complete physical energy. -/
theorem tendsto_harmonicPrimeCharge_physical_energy_uniform {ι : Type*} {l : Filter ι}
    {Q N : ι → ℕ} (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun i => completeWeilEnergy φ (2 * K * Real.log (N i) ^ (1 / 8 : ℝ))
      (N i) (harmonicPrimeChargeVector (Q i) (N i) t)) l (𝓝 0) := by
  let dense : Set ι := {i | N i ≤ Q i ^ 64}
  apply tendsto_of_partition dense
  · apply tendsto_harmonicPrimeCharge_energy_dense_cutoff
      (hQ.mono_left inf_le_left) (hN.mono_left inf_le_left) _ hφ hφ0 hsupp hM hK t
    rw [eventually_inf_principal]
    exact Eventually.of_forall fun _ hi => hi
  · let lf := l ⊓ principal denseᶜ
    have hQf : Tendsto Q lf atTop := hQ.mono_left inf_le_left
    have hNf : Tendsto N lf atTop := hN.mono_left inf_le_left
    have hfar : ∀ᶠ i in lf, Q i ^ 64 ≤ N i := by
      rw [eventually_inf_principal]
      apply Eventually.of_forall
      intro i hi
      change ¬N i ≤ Q i ^ 64 at hi
      omega
    let small : Set ι := {i | (Q i : ℝ) ^ 32 ≤ Real.log (N i)}
    apply tendsto_of_partition small
    · apply tendsto_harmonicPrimeCharge_energy_small_cutoff
        (hQf.mono_left inf_le_left) (hNf.mono_left inf_le_left)
        (hfar.filter_mono inf_le_left) _ hφ hsupp hM hK t
      rw [eventually_inf_principal]
      exact Eventually.of_forall fun _ hi => hi
    · apply tendsto_harmonicPrimeCharge_energy_intermediate
        (hQf.mono_left inf_le_left) (hNf.mono_left inf_le_left)
        (hfar.filter_mono inf_le_left) _ hφ hsupp hM hK t
      rw [eventually_inf_principal]
      apply Eventually.of_forall
      intro i hi
      change ¬(Q i : ℝ) ^ 32 ≤ Real.log (N i) at hi
      exact (lt_of_not_ge hi).le

/-- The concrete tilted spline has the same uniform vanishing law at every positive critical multiple. -/
theorem tendsto_tilted_harmonicPrimeCharge_physical_energy_uniform
    {ι : Type*} {l : Filter ι} {Q N : ι → ℕ}
    (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop) {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun i => completeWeilEnergy tiltedUnitSpline
      (2 * K * Real.log (N i) ^ (1 / 8 : ℝ)) (N i)
        (harmonicPrimeChargeVector (Q i) (N i) t)) l (𝓝 0) := by
  apply tendsto_harmonicPrimeCharge_physical_energy_uniform hQ hN contDiff_tiltedUnitSpline
    _ tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK t
  intro u
  unfold tiltedUnitSpline atomDilate
  exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _

#print axioms tendsto_harmonicPrimeCharge_physical_energy_uniform
#print axioms tendsto_tilted_harmonicPrimeCharge_physical_energy_uniform

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
