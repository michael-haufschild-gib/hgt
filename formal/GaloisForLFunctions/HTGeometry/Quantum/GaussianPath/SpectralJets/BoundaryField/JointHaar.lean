import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointFrequencies
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity

/-! # Joint Haar phase law under a change of a single boundary field -/
open Filter Topology MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section

private def liftPacket {I : Type*} [Fintype I] [DecidableEq I] (r : I) (m : {i : I // i≠r}→ℤ) (i : I) : ℤ :=
  if h : i=r then -(∑ j, m j) else m ⟨i,h⟩

private theorem lift_at_anchor {I : Type*} [Fintype I] [DecidableEq I] (r : I)
    (m : {i : I // i≠r}→ℤ) : liftPacket r m r = -(∑ j, m j) := by simp [liftPacket]

private theorem lift_off_anchor {I : Type*} [Fintype I] [DecidableEq I] (r : I)
    (m : {i : I // i≠r}→ℤ) (j : {i : I // i≠r}) : liftPacket r m j.val = m j := by
  simp only [liftPacket,dif_neg j.property]

private theorem lift_sum {I : Type*} [Fintype I] [DecidableEq I] (r : I) (m : {i : I // i≠r}→ℤ) :
    ∑ i, liftPacket r m i=0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r]
  simp only [lift_at_anchor,lift_off_anchor,neg_add_cancel]

private theorem lift_energy {I : Type*} [Fintype I] [DecidableEq I] (r : I) (m : {i : I // i≠r}→ℤ) (E : I→ℝ) :
    (∑ i, (liftPacket r m i:ℝ)*E i)=finiteTorusCharacterDetuning m (projectiveFrequency E r) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r]
  simp only [lift_at_anchor,lift_off_anchor,finiteTorusCharacterDetuning,projectiveFrequency,
    mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,Int.cast_neg,Int.cast_sum]
  ring

/-- Joint resonance of the anchored frequencies would lift to a resonance
balanced in both registers separately. -/
theorem independent_joined_gaps {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (E : I→ℝ) (F : J→ℝ) (r : I) (s : J)
    (h : ∀ (p : I→ℤ) (q : J→ℤ), (∑ i, p i)=0 → (∑ j, q j)=0 →
      (∑ i, (p i:ℝ)*E i)+(∑ j, (q j:ℝ)*F j)=0 → p=0 ∧ q=0) :
    RationallyIndependentFrequency (Sum.elim (projectiveFrequency E r) (projectiveFrequency F s)) := by
  intro m hm
  let p (i : {i : I // i≠r}) := m (.inl i)
  let q (i : {j : J // j≠s}) := m (.inr i)
  have he : (∑ i, (liftPacket r p i:ℝ)*E i)+(∑ j, (liftPacket s q j:ℝ)*F j)=0 := by
    rw [lift_energy,lift_energy]
    simpa only [finiteTorusCharacterDetuning,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,p,q] using hm
  obtain ⟨hp,hq⟩ := h _ _ (lift_sum r p) (lift_sum s q) he
  funext j
  cases j with
  | inl j => simpa only [liftPacket,dif_neg j.property,Pi.zero_apply,p] using congrFun hp j.val
  | inr j => simpa only [liftPacket,dif_neg j.property,Pi.zero_apply,q] using congrFun hq j.val

/-- One Gaussian chain, each prefix of at least three spins, and all but a
countable set of changes of its last Z field have a joint Haar phase law
on the two projective tori at the same laboratory time. -/
theorem gaussian_boundary_joint_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ t ∉ B,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      let F := (boundaryHermitian ω k t).eigenvalues
      ∀ r s, let f := Sum.elim (projectiveFrequency (fun i => -E i) r) (projectiveFrequency (fun j => -F j) s)
             Tendsto (clockPhaseWindowLaw f) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  filter_upwards [gaussian_boundary_joint_nonresonance] with ω hω
  intro k
  obtain ⟨B,hB,hs⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro t ht E F r s
  apply clockPhaseWindowLaw_tendsto_haar
  apply independent_joined_gaps
  intro p q hp hq he
  apply hs t ht p q hp hq
  simp only [mul_neg,Finset.sum_neg_distrib] at he
  linarith only [he]

#print axioms gaussian_boundary_joint_haar
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
