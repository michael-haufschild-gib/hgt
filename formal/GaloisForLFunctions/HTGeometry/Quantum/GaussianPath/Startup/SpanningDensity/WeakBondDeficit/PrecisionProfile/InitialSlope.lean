import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.InitialSpeed
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.PhysicalSpeed

/-! # Initial distance speed below one physical bond sweep -/

open Set Filter Topology Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- On every long typical prefix the actual initial speed is of order
(K⁻¹ d¹⁰)^(1/9), simultaneously in the mesoscopic-to-extensive range
of missing gate counts d. The limit takes time to zero at fixed prefix. -/
theorem gaussian_initial_deficit_slope :
    ∃ γ>0, ∃ Q>0, ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ (d : ℕ) (h : ℝ), d≤n+1 → (d:ℝ)=K*h^9 → 0<h → h≤γ → Q≤K*h^20 →
        ∃ v∈Icc (c*(K*h^10)) (C*(K*h^10)),
          Tendsto (fun t => orbitCircuitDistance H (n+1-d) t/|t|) (𝓝[≠] 0) (𝓝 v) := by
  obtain ⟨γ,hγ,Q,hQ,c,hc,C,hC,hw⟩ := gaussian_deficit_distance_speed
  refine ⟨γ,hγ,Q,hQ,c,hc,C,hC,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro K H d h hdn hd hh hγd hscale
  let V := K*h^10
  have hK : 0<K := by dsimp only [K]; positivity
  have hV : 0<V := mul_pos hK (pow_pos hh _)
  apply initial_speed_in_interval
  have he : ∀ᶠ t : ℝ in 𝓝[<] 0, -(1/V)<t := nhdsWithin_le_nhds (lt_mem_nhds (neg_lt_zero.mpr (one_div_pos.mpr hV)))
  filter_upwards [self_mem_nhdsWithin,he] with t ht hlo
  have hab := abs_of_neg (show t<0 from ht)
  have htime : |t| * V≤1 := (le_div_iff₀ hV).mp (by rw [hab]; linarith only [hlo])
  obtain ⟨hl,hu⟩ := hn d h hdn hd hh hγd hscale t htime
  change c*(|t| * V)≤orbitCircuitDistance H (n+1-d) t at hl
  change orbitCircuitDistance H (n+1-d) t≤C*(|t| * V) at hu
  rw [hab] at hl hu
  refine ⟨(le_div_iff₀ (neg_pos.mpr ht)).mpr ?_,(div_le_iff₀ (neg_pos.mpr ht)).mpr ?_⟩ <;>
    linarith only [hl,hu]

#print axioms gaussian_initial_deficit_slope
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
