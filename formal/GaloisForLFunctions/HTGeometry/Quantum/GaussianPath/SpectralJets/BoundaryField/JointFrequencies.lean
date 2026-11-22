import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FrequencyAvoidance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Joint projective nonresonance of an orbit and its boundary perturbation -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Basis (k : ℕ) := Fin (k+3)→Bool

/-- Outside a countable set of terminal increments, the two spectra have
no joint integer resonance balanced separately in each register. All other
couplings agree exactly. -/
theorem gaussian_boundary_joint_nonresonance :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ t ∉ B,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      let F := (boundaryHermitian ω k t).eigenvalues
      ∀ (p : Basis k→ℤ) (q : Basis k→ℤ), (∑ i, p i)=0 → (∑ j, q j)=0 →
        (∑ i, (p i:ℝ)*E i)+(∑ j, (q j:ℝ)*F j)=0 → p=0 ∧ q=0 := by
  filter_upwards [gaussian_boundary_frequency_avoidance,gaussian_path_all_prefixes_maximally_projective] with ω ha hr
  intro k
  let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
  let Γ := range (fun p : Basis k→ℤ => -(∑ i, (p i:ℝ)*E i))
  obtain ⟨B,hB,h⟩ := ha k Γ (countable_range _)
  refine ⟨B,hB,?_⟩
  intro t ht _ F p q hp hq he
  have hz : q=0 := by
    by_contra hn
    exact h t ht q hn hq ⟨p,by linarith only [he]⟩
  subst q
  simp only [Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,add_zero] at he
  exact ⟨hr k p hp he,rfl⟩

#print axioms gaussian_boundary_joint_nonresonance
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
