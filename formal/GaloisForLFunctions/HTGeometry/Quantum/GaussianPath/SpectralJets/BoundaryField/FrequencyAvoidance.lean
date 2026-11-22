import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.GaussianActions

/-! # Changing one boundary field separates the projective frequency groups -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Basis (k : ℕ) := Fin (k+3)→Bool

/-- A single typical background works for every countable set of reference
frequencies, even one selected using that same background. Only countably
many terminal field increments can place any nonzero balanced action in it. -/
theorem gaussian_boundary_frequency_avoidance :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ Γ : Set ℝ, Γ.Countable →
      ∃ B : Set ℝ, B.Countable ∧ ∀ t ∉ B, ∀ m : Basis k→ℤ, m≠0 → (∑ i, m i)=0 →
        (∑ i, (m i:ℝ)*(boundaryHermitian ω k t).eigenvalues i)∉Γ := by
  filter_upwards [gaussian_integer_action_levels] with ω hω
  intro k Γ hΓ
  haveI : Countable Γ := hΓ.to_subtype
  let M := {m : Basis k→ℤ // m≠0 ∧ (∑ i, m i)=0}
  let action (m : M) (t : ℝ) := ∑ i, (m.val i:ℝ)*(boundaryHermitian ω k t).eigenvalues i
  let S (m : M) (v : Γ) := {t : ℝ | action m t=v.val}
  have hs (m : M) (v : Γ) : (S m v).Finite :=
    (hω k m.val m.property.1 m.property.2 v.val).subset fun _ ht => Or.inr ⟨Equiv.refl _,ht⟩
  refine ⟨⋃ m : M, ⋃ v : Γ, S m v,countable_iUnion fun m => countable_iUnion fun v => (hs m v).countable,?_⟩
  intro t ht m hm hb hΓm
  let p : M := ⟨m,hm,hb⟩
  exact ht (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨⟨action p t,hΓm⟩,rfl⟩⟩)

#print axioms gaussian_boundary_frequency_avoidance
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
