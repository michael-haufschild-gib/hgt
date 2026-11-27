import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.MaximumAtom
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.TimeTranslation

/-! # Recurrence frequency of maximum-cost windows on a frozen orbit -/
open Set Filter MeasureTheory ProbabilityTheory Topology Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open JointSpeeds SharpOccupation
open private translated_fraction from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateBudgetDistribution
noncomputable section

private theorem complement_density {A : Set ℝ} (hA : MeasurableSet A) {p : ℝ}
    (h : Tendsto (fun T : ℝ => volume.real (A∩Icc 0 T)/T) atTop (𝓝 p)) :
    Tendsto (fun T : ℝ => volume.real (Aᶜ∩Icc 0 T)/T) atTop (𝓝 (1-p)) := by
  apply (h.const_sub 1).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  have he : Aᶜ∩Icc 0 T=Icc 0 T \ (A∩Icc 0 T) := by ext; simp only [mem_inter_iff,mem_compl_iff,Set.mem_sdiff]; tauto
  rw [he,measureReal_sdiff inter_subset_right (hA.inter measurableSet_Icc) measure_Icc_lt_top.ne,
    Real.volume_real_Icc_of_le hT.le,sub_zero,sub_div,div_self hT.ne']

/-- Repeated occupied intervals give a lower bound on their limiting
time fraction, including when the gaps and the intervals overlap. -/
private theorem density_of_windows {F : Set ℝ} {G w p : ℝ} (hG : 0 < G) (hw : 0 < w)
    (hrec : ∀ a : ℝ, ∃ v∈Icc a (a+G), Icc v (v+w)⊆F)
    (hlim : Tendsto (fun T : ℝ => volume.real (F∩Icc 0 T)/T) atTop (𝓝 p)) : w/(w+G) ≤ p := by
  by_contra! h
  obtain ⟨c,hpc,hc⟩ := exists_between h
  have hocc : ∀ᶠ T : ℝ in atTop, volume.real (F∩Icc 0 T) ≤ c*T := by
    filter_upwards [hlim.eventually_lt_const hpc,eventually_gt_atTop (0:ℝ)] with T hT hT₀
    exact (div_le_iff₀ hT₀).mp hT.le
  have htrans : ∀ a : ℝ, ∃ v∈Icc a (a+G), ∀ t∈Icc 0 w, t+v∈F := by
    intro a
    obtain ⟨v,hv,hS⟩ := hrec a
    exact ⟨v,hv,fun t ht => hS ⟨by linarith only [ht.1],by linarith only [ht.2]⟩⟩
  have hbound := occupation_from_periods (Icc 0 w) F measurableSet_Icc hG htrans hocc 0 w hw.le
  rw [zero_add,inter_self,Real.volume_real_Icc_of_le hw.le,sub_zero] at hbound
  exact ((lt_div_iff₀ (add_pos hw hG)).mp hc).not_ge hbound

/-- For every choice of valid recurrent maximum windows, their width
relative to width plus gap is at most the top Haar atom. In particular
the same-error mean-to-maximum gap bounds every such recurrence rate. -/
theorem maximum_recurrence_frequency (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let K := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let x := fun i => u (pathCoeffEquiv (k+1) i)
      let m := prefixMaximum (k+1) ε x
      let M := prefixMean k ε x
      IsRecurrentOrbitCircuitMaximumAt H ε m ∧ ∀ G> (0:ℝ), ∀ w> (0:ℝ),
        (∀ a : ℝ, ∃ v∈Icc a (a+G), ∀ t∈Icc v (v+w), ∀ s < m, t∉visitSet H s ε) →
        w/(w+G) ≤ maximumAtom k ε x ∧ maximumAtom k ε x ≤
          exp (-(max 0 ((m:ℝ)-M))^2/(2*(((2^K-1:ℕ):ℝ)*(((35*2^K:ℕ):ℝ)/2)^2))) := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction,maximum_atom_bounds k hε,
    ae_all_iff.mpr (fun j => prefixFraction_eq k j ε)] with ω htime hbound hF
  intro K u H x m M
  obtain ⟨j,hj⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [K]; omega : 2 ≤ K) H
    (hasPauliWeightAtMost_pathHamiltonian u _) ε hε
  have hm : m=j := prefixMaximum_eq u ε hj
  refine ⟨hm.symm ▸ hj,?_⟩
  intro G hG w hw hrec
  refine ⟨?_,hbound.2⟩
  by_cases h₀ : m=0
  · rw [show maximumAtom k ε x=1 from if_pos h₀]
    exact (div_le_one (add_pos hw hG)).mpr (le_add_of_nonneg_right hG.le)
  let s := m-1
  have hs : s < m := by dsimp only [s]; omega
  let A := visitSet H s ε
  have hh := translated_fraction H s ε 0 (affordablePhaseMass k s ε ω) (htime k s ε (fun _ => 0))
  simp only [add_zero] at hh
  have hA : MeasurableSet A := hh.1
  have hl : Tendsto (fun T : ℝ => volume.real (A∩Icc 0 T)/T) atTop (𝓝 (affordablePhaseMass k s ε ω)) := hh.2
  rw [show maximumAtom k ε x=1-prefixFraction k s ε x from if_neg h₀,hF s]
  apply density_of_windows hG hw _ (complement_density hA hl)
  intro a
  obtain ⟨v,hv,h⟩ := hrec a
  exact ⟨v,hv,fun t ht => h t ht s hs⟩

#print axioms maximum_recurrence_frequency
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
