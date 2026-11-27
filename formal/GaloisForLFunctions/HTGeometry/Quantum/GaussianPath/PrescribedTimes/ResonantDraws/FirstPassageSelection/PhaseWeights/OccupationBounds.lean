import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.BudgetLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Uniform Haar bounds before any selection on the couplings -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation
noncomputable section

/-- The size cutoff precedes the selection of the draw. This permits
arbitrarily rare conditioning events in the physical snapshot law. -/
theorem subcritical_phase_mass (s : ℕ→ℕ) (hs : subcriticalBudget s)
    {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) (Real.sqrt 2)) {l b : ℝ}
    (hl : 0≤l) (hlx : l<physicalArc ε) (hxb : physicalArc ε<b) :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := k+3
      let D := 2^N
      ∀ j ≤ s N, l^D ≤ affordablePhaseMass k j ε ω ∧ affordablePhaseMass k j ε ω ≤ b^D := by
  let x := physicalArc ε
  obtain ⟨hx,htol⟩ := physicalArc_spec hε.1 hε.2
  change x ∈ Ioo (0:ℝ) (1/2) at hx
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hxb hx.2)
  have hyb := hy.trans_le (min_le_left ..)
  have hyhalf := hy.trans_le (min_le_right ..)
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0<δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx.1.le,hx.2.le⟩ ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  have hh := enlarged_arc_eventually_lt hs (36+128/δ) y b (hx.1.trans hxy) hyb
  filter_upwards [(tendsto_add_atTop_nat 3).eventually (hh.and (budget_le_dimension_eventually hs))] with k hk
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,
    PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hr hlim
  intro N D j hj
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  have hD : 0<D := Nat.two_pow_pos N
  have hu := finite_budget_eventually_lt H (hr k) (s N) hx.1.le hxy hyhalf 0 (b^D) (by
    have hp : 0 ≤ zeroGateArcDensity (2^N) y :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx.1.trans hxy).le _)
    apply (mul_le_mul_of_nonneg_right (net_envelope_le_exp N (s N) δ hδ hk.2) hp).trans_lt
    simpa only [zeroGateArcDensity,Nat.cast_pow,Nat.cast_ofNat] using hk.1)
  have hlow : l^D ≤ zeroGateArcDensity D x := calc
    _ ≤ x^D := pow_le_pow_left₀ hl hlx.le D
    _ = x*x^(D-1) := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ D)]
    _ ≤ (D:ℝ)*x^(D-1) := mul_le_mul_of_nonneg_right
      ((hx.2.le.trans (by norm_num : (1/2:ℝ)≤1)).trans (by exact_mod_cast (show 1≤D from hD)))
      (pow_nonneg hx.1.le _)
  have hz := zero_visitFraction_tendsto H (hr k) ⟨x,hx.1.le,hx.2.le⟩ 0
  have hz' : zeroGateArcTolerance x=ε := htol
  rw [hz'] at hu
  change Tendsto (fun T => visitFraction H 0 (zeroGateArcTolerance x) 0 T) atTop (𝓝 (zeroGateArcDensity D x)) at hz
  rw [hz'] at hz
  have hjlim := hlim k j ε (fun _ => 0)
  simp only [zero_add] at hjlim
  constructor
  · apply hlow.trans (le_of_tendsto_of_tendsto hz hjlim ?_)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact visitFraction_mono H (Nat.zero_le j) ε 0 T hT
  · apply le_of_tendsto hjlim
    filter_upwards [hu,eventually_ge_atTop (0:ℝ)] with T hb hT
    exact (visitFraction_mono H hj ε 0 T hT).trans hb.le

#print axioms subcritical_phase_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
