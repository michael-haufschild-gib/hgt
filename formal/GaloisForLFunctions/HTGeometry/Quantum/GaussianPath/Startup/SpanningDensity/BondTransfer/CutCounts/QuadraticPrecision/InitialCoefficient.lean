import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.InitialSpeed
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondMass

/-! # Quadratic contact of the optimal physical distance above one sweep -/
open Filter Set MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- Throughout a positive-density range of above-sweep budgets, the actual
quadratic coefficient exists and is at least 1/64, uniformly in prefix
and budget. The time limit is two-sided at each fixed prefix. -/
theorem gaussian_sweep_quadratic_coefficient :
    ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let u := pathPauliDisorderShell ω n
      let H := (⟨_,isSelfAdjoint_pathHamiltonian u⟩ :
        selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
      ∀ k : ℕ, n+1≤k → (k:ℝ)≤(1+b)*((n+1:ℕ):ℝ) →
        ∃ v∈Icc (1/64:ℝ) (84*‖u‖^2),
          Tendsto (fun t => orbitCircuitDistance H k t/t^2) (𝓝[≠] 0) (𝓝 v) := by
  obtain ⟨b,hb,hw⟩ := gaussian_quadratic_precision_excess
  refine ⟨b,hb,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro u H k hlow hhigh
  have hratio : ∀ᶠ t in 𝓝[<] (0:ℝ), orbitCircuitDistance H k t/(-t)^2∈Icc (1/64:ℝ) (84*‖u‖^2) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (-1:ℝ)<0))] with t ht hneg
    have hp : 0< -t := neg_pos.mpr (show t<0 from ht)
    have ht₁ : -t≤1 := by linarith only [hneg]
    let f := orbitCircuitDistance H k (-t)
    have lower : (-t)^2/64<f := by
      by_contra! h
      exact hhigh.not_gt (hn (-t) ⟨hp,ht₁⟩ k ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h))
    obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error u (-t) hp.le 1 one_pos
    have hcount : C.gateCount≤n+1 := by simpa only [one_mul] using hC.le
    have upper : f≤(-t)^2*(84*‖u‖^2) :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp
        ⟨z,hz,C,hcount.trans hlow,by simpa only [Nat.cast_one,div_one] using he⟩
    change _≤orbitCircuitDistance H k t/(-t)^2 ∧ _≤_
    rw [←orbitCircuitDistance_neg_time H k t]
    refine ⟨(le_div_iff₀ (sq_pos_of_pos hp)).mpr ?_,(div_le_iff₀ (sq_pos_of_pos hp)).mpr ?_⟩
    · change _≤f
      linarith only [lower]
    · change f≤_
      linarith only [upper]
  obtain ⟨v,hv,ht⟩ := initial_power_in_interval H 2 hratio
  exact ⟨v,hv,by simpa only [sq_abs] using ht⟩

#print axioms gaussian_sweep_quadratic_coefficient
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
