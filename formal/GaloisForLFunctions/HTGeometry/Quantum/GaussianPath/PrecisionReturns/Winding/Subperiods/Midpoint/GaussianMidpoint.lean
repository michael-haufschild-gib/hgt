import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.PhysicalWidth

/-! # Halfway to the first fine scalar return on a frozen Gaussian prefix -/

open Filter MeasureTheory Set Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- At half the absolute date of the first empty return, the physical
empty-circuit error tends to the semicircle chord as return precision increases.
The observation origin can depend on the entire draw. -/
theorem gaussian_first_return_midpoint :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a > (0:ℝ), Tendsto (fun ε => orbitCircuitDistance H 0 (firstVisit H a 0 ε/2))
        (𝓝[>] (0:ℝ)) (𝓝 (sqrt 2)) := by
  filter_upwards [gaussian_first_winding_primitive] with ω hω k
  intro N H a ha
  let f (ε : ℝ) := turnWidth H (firstVisit H a 0 ε/2)
  have ha₀ : Continuous physicalArc := by unfold physicalArc; fun_prop
  have hr : Tendsto physicalArc (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [physicalArc,zero_div,arcsin_zero,mul_zero] using
      (ha₀.continuousAt (x:=(0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hbox : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      f ε ∈ Icc ((1-physicalArc ε)/2) ((1+physicalArc ε)/2) := by
    filter_upwards [hω k a ha,Ioo_mem_nhdsGT (sqrt_pos.mpr zero_lt_two)] with ε hv hε
    obtain ⟨⟨b,z,hz⟩,hp⟩ := hv
    have h := (physicalArc_spec hε.1 hε.2).1
    have hh := width_at_division H ⟨h.1.le,h.2.le.trans (by norm_num)⟩ (d:=2) (by decide) hz
      (hp b z hz 2 (by decide))
    simpa only [Nat.cast_ofNat,show (2:ℝ)-1=1 by norm_num] using hh
  have hl := ((tendsto_const_nhds (x:=(1:ℝ))).sub hr).div_const 2
  have hu := ((tendsto_const_nhds (x:=(1:ℝ))).add hr).div_const 2
  have hw : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (1/2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [sub_zero] using hl)
      (by simpa only [add_zero] using hu) (hbox.mono fun _ h => h.1) (hbox.mono fun _ h => h.2)
  have hc : Continuous zeroGateArcTolerance := by unfold zeroGateArcTolerance; fun_prop
  have hhalf : zeroGateArcTolerance (1/2)=sqrt 2 := by
    unfold zeroGateArcTolerance
    rw [show π*(1/2)/2=π/4 by ring,sin_pi_div_four]
    ring
  simp_rw [scalar_distance_eq_chord]
  rw [← hhalf]
  exact hc.continuousAt.tendsto.comp hw

#print axioms gaussian_first_return_midpoint
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
