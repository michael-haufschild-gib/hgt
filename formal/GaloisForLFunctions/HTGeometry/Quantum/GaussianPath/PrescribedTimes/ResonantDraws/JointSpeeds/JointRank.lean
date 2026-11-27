import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.RealRelations
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.UniformWindows

/-! # Independent phase clocks on one frozen Gaussian prefix -/
open MeasureTheory Filter Set Topology Finset
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
noncomputable section

/-- The anchor cancels the sum of the coefficients at the remaining
levels, converting a relative-frequency test to a balanced real mode. -/
private def balancedLift {d : ℕ} (v : Fin d→ℝ) : Fin (d+1)→ℝ :=
  Fin.cases (∑ j, v j) (fun j => -v j)

private theorem balancedLift_sum {d : ℕ} (v : Fin d→ℝ) : ∑ j, balancedLift v j=0 := by
  rw [Fin.sum_univ_succ]
  simp [balancedLift]

private theorem balancedLift_action {d : ℕ} (v : Fin d→ℝ) (E : Fin (d+1)→ℝ) :
    ∑ i, balancedLift v i*E i = ∑ j, v j*RHTower.zeroProjectiveFrequency E j := by
  rw [Fin.sum_univ_succ]
  simp only [balancedLift,Fin.cases_zero,Fin.cases_succ,RHTower.zeroProjectiveFrequency,
    sum_mul,neg_mul,sum_neg_distrib,mul_sub,sum_sub_distrib]
  rw [sub_eq_add_neg]

/-- Almost surely no prescribed countable family of nonzero real tests
annihilates the relative frequencies, in any labeling of the spectrum. -/
theorem countable_gap_avoidance (k : ℕ) {M : Type*} [Countable M]
    (v : M→Fin (2^(k+3)-1)→ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let u := pathPauliDisorderShell ω (k+1)
      let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
      ∀ m, v m≠0 → ∀ e : Fin ((2^(k+3)-1)+1) ≃ (Fin (k+3)→Bool),
        ∑ j, v m j*RHTower.zeroProjectiveFrequency (E ∘ e) j ≠ 0 := by
  classical
  apply ae_all_iff.mpr
  intro m
  by_cases hv : v m=0
  · exact ae_of_all _ fun _ hn => (hn hv).elim
  let a := prefixPhaseEnergyEquiv k
  let c := balancedLift (v m) ∘ a
  have hs : ∑ j, c j=0 := (a.sum_comp _).trans (balancedLift_sum _)
  have hn : c≠0 := by
    intro hz
    apply hv
    funext i
    have h := congrFun hz (a.symm i.succ)
    simpa only [c,Function.comp_apply,Equiv.apply_symm_apply,balancedLift,Fin.cases_succ,Pi.zero_apply,neg_eq_zero] using h
  filter_upwards [real_mode_avoidance k c hs hn] with ω hw
  intro _ e hz
  let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
  apply hw (a.trans e)
  change (∑ j, (fun i => balancedLift (v m) i * (E ∘ e) i) (a j)) = 0
  exact (a.sum_comp (fun i => balancedLift (v m) i * (E ∘ e) i)).trans
    ((balancedLift_action (v m) (E ∘ e)).trans hz)

/-- Every finite family of incommensurate observation speeds has full
joint torus rank along almost every frozen chain, at every prefix size. -/
theorem gaussian_joint_phase_rank {I : Type} [Fintype I] (c : I→ℝ)
    (hc : RationallyIndependentFrequency c) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
      let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
      RationallyIndependentFrequency (fun p : I×Fin (2^N-1) =>
        c p.1*RHTower.zeroProjectiveFrequency (E ∘ e.symm) p.2) := by
  classical
  apply ae_all_iff.mpr
  intro k
  let d := 2^(k+3)-1
  let v (m : I×Fin d→ℤ) (j : Fin d) := finiteTorusCharacterDetuning (fun i => m (i,j)) c
  filter_upwards [countable_gap_avoidance k v] with ω hw
  intro N u E e m hm
  by_contra hn
  have hv : v m≠0 := by
    intro hz
    apply hn
    funext p
    exact congrFun (hc (fun i => m (i,p.2)) (congrFun hz p.2)) p.1
  apply hw m hv e.symm
  unfold finiteTorusCharacterDetuning at hm
  rw [Fintype.sum_prod_type,sum_comm] at hm
  simpa only [v,finiteTorusCharacterDetuning,sum_mul,mul_assoc] using hm

#print axioms countable_gap_avoidance
#print axioms gaussian_joint_phase_rank
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
