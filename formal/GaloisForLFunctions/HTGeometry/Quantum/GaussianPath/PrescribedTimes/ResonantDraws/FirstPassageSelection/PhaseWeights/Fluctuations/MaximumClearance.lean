import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.MaximumWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ReplayDensity

/-! # Quantitative lower mass of the actual maximum from its predecessor clearance -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open JointSpeeds SharpOccupation AccuracyScales.MaximumIntervals
open private complement_density from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.MaximumWindows
open private translated_fraction from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateBudgetDistribution
noncomputable section

/-- For a positive true maximum the predecessor budget misses the prescribed
error by a strictly positive amount somewhere on the orbit. -/
theorem predecessor_clearance {K m : ℕ} {H : selfAdjoint (Register K)} {ε : ℝ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H ε m) (hm₀ : m≠0) :
    ε < criticalHeight H (m-1) := by
  obtain ⟨v,hv⟩ := required_at_some_date hm
  have hmiss : ε < orbitCircuitDistance H (m-1) v := lt_of_not_ge fun h =>
    (by omega : ¬m ≤ m-1) (hv _ ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h))
  apply hmiss.trans_le (le_csSup _ (mem_range_self v))
  refine ⟨2,?_⟩
  rintro _ ⟨t,rfl⟩
  apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
  refine ⟨1,norm_one,TwoQubitCircuit.one K,Nat.zero_le _,?_⟩
  rw [one_smul,TwoQubitCircuit.one_eval]
  have h := norm_sub_le (unitaryEvolution H.val t) (1:Register K)
  rw [CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 t),norm_one] at h
  exact h.trans_eq (by norm_num)

/-- A full translated scalar neighborhood lies inside the maximizers.
Its measure gives a lower bound at every radius below the actual clearance
of the predecessor, including at the prescribed physical error 1/10. -/
theorem maximum_atom_of_clearance (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let x := fun i => u (pathCoeffEquiv (k+1) i)
      let m := prefixMaximum (k+1) ε x
      (m=0 ∧ maximumAtom k ε x=1) ∨
        (0 < criticalHeight H (m-1)-ε ∧ ∀ η ∈ Ioo (0:ℝ) (min (sqrt 2) (criticalHeight H (m-1)-ε)),
          ((2^K:ℕ):ℝ)*(physicalArc η)^(2^K-1:ℕ) ≤ maximumAtom k ε x) := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction,gaussian_path_all_prefixes_maximally_projective,
    ae_all_iff.mpr (fun j => prefixFraction_eq k j ε)] with ω htime hspec hF
  intro K u H x m
  by_cases hm₀ : m=0
  · exact Or.inl ⟨hm₀,if_pos hm₀⟩
  obtain ⟨l,hl⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [K]; omega : 2 ≤ K) H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  have hml : m=l := prefixMaximum_eq u ε hl
  have hm : IsRecurrentOrbitCircuitMaximumAt H ε m := hml.symm ▸ hl
  refine Or.inr ⟨sub_pos.mpr (predecessor_clearance hm hm₀),?_⟩
  intro η hη
  let s := m-1
  have hg := hη.2.trans_le (min_le_right ..)
  obtain ⟨_,⟨v,rfl⟩,hv⟩ := exists_lt_of_lt_csSup (range_nonempty (orbitCircuitDistance H s))
    (show ε+η < criticalHeight H s by linarith only [hg])
  let S := (fun z : ℝ => z-v) ⁻¹' visitSet H 0 η
  have hS := (TrajectoryProfiles.translated_scalar_fraction H (hspec k) hη.1
    (hη.2.trans_le (min_le_left ..)) v).2 0
  simp only [sub_zero] at hS
  let A := visitSet H s ε
  have hex : S ⊆ Aᶜ := by
    intro z hz hfit
    have hback := (show HasProjectiveCircuitApproximation K η 0 (unitaryEvolution H.val (z-v)) from hz).neg_time H
    have he := affordable_add_time H (show HasProjectiveCircuitApproximation K ε s (unitaryEvolution H.val z) from hfit) hback
    rw [show z+ -(z-v)=v by ring,Nat.add_zero] at he
    exact hv.not_ge ((hasProjectiveCircuitApproximation_iff_infDist ..).mp he)
  have hh := translated_fraction H s ε 0 (affordablePhaseMass k s ε ω) (htime k s ε (fun _ => 0))
  simp only [add_zero] at hh
  have ht := complement_density (show MeasurableSet A from hh.1) hh.2
  rw [show maximumAtom k ε x=1-prefixFraction k s ε x from if_neg hm₀,hF s]
  apply le_of_tendsto_of_tendsto hS ht
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact div_le_div_of_nonneg_right (measureReal_mono (inter_subset_inter hex Subset.rfl)
    (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))) hT.le

#print axioms maximum_atom_of_clearance
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
