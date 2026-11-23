import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.FirstTravel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass

/-! # Almost-sure travel width at the largest Gaussian coupling -/
open Set Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes ShortWindows
noncomputable section

/-- On one frozen draw the onset and every first return through half
its gate budget eventually require at least the local travel width
multiplied by the number of sites divided by a square root of a logarithm. -/
theorem gaussian_joint_frozen_travel_width :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let B := (N:ℝ)*localCrossingWidth N/sqrt (log (C*N))
      let x := prefixPoint k ω
      B < crossingOrigin (k+1) P (9/80) x ∧ ∀ s ≤ P/2, B < crossingWait (k+1) P s x := by
  obtain ⟨C,hC,hmass⟩ := FirstAscent.gaussian_subset_mass
  obtain ⟨k₀,hk₀⟩ := eventually_atTop.mp gaussian_capped_first_passage
  obtain ⟨j,hj⟩ := exists_nat_gt (1/C)
  have hall := ae_all_iff.mpr (fun k : ℕ => ae_all_iff.mpr (fun h : k₀ ≤ k => hk₀ k h))
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass,hall] with ω hm hh
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hm,eventually_ge_atTop k₀,eventually_ge_atTop j] with k hk hk' hj'
  intro N P B x
  have hCN : 1 < C*(N:ℝ) := by
    rw [mul_comm]
    apply (div_lt_iff₀ hC).mp
    exact hj.trans_le (by exact_mod_cast (show j ≤ N by dsimp [N]; omega))
  have hlog := log_pos hCN
  let L := sqrt (log (C*(N:ℝ)))
  have hL : 0 < L := sqrt_pos.mpr hlog
  have hcap (i : PrefixIndex (k+1)) : |x i| ≤ 2*L := by
    let l := pathCoeffEquiv (k+1) i
    have h := hk {l} (Finset.singleton_nonempty l)
    simp only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,one_pow,mul_one,div_one] at h
    change |pathPauliDisorderShell ω (k+1) l|^2 ≤ 4*log (C*(N:ℝ)) at h
    have he : L^2 = log (C*(N:ℝ)) := sq_sqrt hlog.le
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*L)).mp
    change |pathPauliDisorderShell ω (k+1) l|^2 ≤ _
    nlinarith only [h,he]
  have hw := hh k hk' (2*L) (by positivity) hcap
  have hB : travelProduct N/(2*L)=B := by
    change (2*(N:ℝ)*localCrossingWidth N)/(2*L)=(N:ℝ)*localCrossingWidth N/L
    field_simp [hL.ne']
  rw [hB,lt_min_iff] at hw
  exact ⟨hw.1,fun s hs => hw.2.trans_le (crossingWait_antitone hs _)⟩

#print axioms gaussian_joint_frozen_travel_width
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
