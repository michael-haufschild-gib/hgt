import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.BudgetDistance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder.LeftLimits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.DistanceGap

/-! # Exact initial speed of the distance to a physical gate budget -/

open Set Filter Topology Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
open PhaseBoundary.FiniteCertificates PhaseBoundary.FiniteCertificates.BudgetComparisons
open PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The ratio of budget distance to any integral power of absolute time has a unique
limit at identity whenever it is bounded on a punctured interval.
Algebraicity of the distance over analytic coefficients selects a limit
from the interval of possible slopes. Circuit inversion gives both signs. -/
theorem initial_power_in_interval {N j : ℕ} (H : selfAdjoint (Reg N)) (p : ℕ) {a b : ℝ}
    (hb : ∀ᶠ t in 𝓝[<] (0:ℝ), orbitCircuitDistance H j t/(-t)^p∈Icc a b) :
    ∃ v∈Icc a b, Tendsto (fun t => orbitCircuitDistance H j t/|t|^p) (𝓝[≠] 0) (𝓝 v) := by
  let g : coefficients := ⟨fun t => (-t)^p,analyticOnNhd_id.neg.pow p⟩
  have hg : IsAlgebraic coefficients (fun t : ℝ => (-t)^p) := isAlgebraic_algebraMap g
  have hlt : ∀ᶠ t in 𝓝[<] (0:ℝ), t<0 := self_mem_nhdsWithin
  obtain ⟨v,hv,hlim⟩ := algebraic_ratio_limit (orbitCircuitDistance_lipschitz H j).continuous
    (algebraic_distance H j) (continuous_id.neg.pow p) hg 0
    (hlt.mono fun _ ht => pow_pos (neg_pos.mpr ht) p) hb.frequently
  have he : Tendsto (fun t : ℝ => -|t|) (𝓝[≠] 0) (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hne : ∀ᶠ t in 𝓝[≠] (0:ℝ), t≠0 := self_mem_nhdsWithin
    refine ⟨?_,hne.mono fun t ht => neg_lt_zero.mpr (abs_pos.mpr ht)⟩
    let f : ℝ→ℝ := fun t => -|t|
    have hcont : Continuous f := by dsimp only [f]; fun_prop
    have hzero : f 0=0 := by simp [f]
    change Tendsto f _ (𝓝 0)
    have hlim₀ : Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 (f 0)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [hzero] at hlim₀
  refine ⟨v,hv,(hlim.comp he).congr ?_⟩
  intro t
  change orbitCircuitDistance H j (-|t|)/(- -|t|)^p=_
  rw [neg_neg,orbitCircuitDistance_neg_time]
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,orbitCircuitDistance_neg_time]

/-- A bounded linear distance ratio gives a two-sided initial speed. -/
theorem initial_speed_in_interval {N j : ℕ} (H : selfAdjoint (Reg N)) {a b : ℝ}
    (hb : ∀ᶠ t in 𝓝[<] (0:ℝ), orbitCircuitDistance H j t/(-t)∈Icc a b) :
    ∃ v∈Icc a b, Tendsto (fun t => orbitCircuitDistance H j t/|t|) (𝓝[≠] 0) (𝓝 v) := by
  simpa only [pow_one] using initial_power_in_interval (j:=j) H 1 (a:=a) (b:=b) (by simpa only [pow_one] using hb)

/-- Every Hermitian generator and every physical gate budget have a
well-defined initial distance speed between zero and the generator norm. -/
theorem circuit_initial_speed {N : ℕ} (H : selfAdjoint (Reg N)) (j : ℕ) :
    ∃ v∈Icc 0 ‖H.val‖, Tendsto (fun t => orbitCircuitDistance H j t/|t|) (𝓝[≠] 0) (𝓝 v) := by
  have hzero : orbitCircuitDistance H j 0=0 := by
    apply le_antisymm _ Metric.infDist_nonneg
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one N,Nat.zero_le _,?_⟩
    simp [unitaryEvolution,TwoQubitCircuit.one_eval]
  apply initial_speed_in_interval
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp : 0< -t := neg_pos.mpr ht
  have hn : 0≤orbitCircuitDistance H j t := Metric.infDist_nonneg
  have h := (orbitCircuitDistance_lipschitz H j).dist_le_mul t 0
  rw [Real.dist_eq,hzero,sub_zero,abs_of_nonneg hn,Real.dist_eq,sub_zero,abs_of_neg ht] at h
  exact ⟨div_nonneg hn hp.le,(div_le_iff₀ hp).mpr h⟩

#print axioms circuit_initial_speed
end
end GaloisForLFunctions.HTGeometry
