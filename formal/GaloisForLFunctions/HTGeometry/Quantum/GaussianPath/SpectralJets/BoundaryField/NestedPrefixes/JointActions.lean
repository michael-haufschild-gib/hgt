import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalLaw

/-! # Joint projective independence for nested prefixes of a single Gaussian chain -/

open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrefixCouplings
noncomputable section

/-- A shorter prefix uses none of the terminal field of a longer one. -/
theorem shell_before {j k : ℕ} (hj : j<k) (ω : PathPauliDisorder) :
    pathPauliDisorderShell (eraseTerminal k ω) (j+1)=pathPauliDisorderShell ω (j+1) := by
  unfold pathPauliDisorderShell
  congr 1
  funext l
  rcases l with ⟨t,a⟩ | ⟨t,a⟩
  · apply Function.update_of_ne
    intro h
    have ht : t.val=k+2 := congrArg Prod.fst h
    omega
  · apply Function.update_of_ne
    intro h
    exact nomatch congrArg Prod.snd h

theorem energy_before {j k : ℕ} (hj : j<k) (ω : PathPauliDisorder) :
    orderedBoundaryEnergy (eraseTerminal k ω) j 0=orderedBoundaryEnergy ω j 0 :=
  ordered_congr (by rw [boundaryHamiltonian,boundaryHamiltonian,shell_before hj])

def action (k : ℕ) (m : Config k → ℤ) (ω : PathPauliDisorder) :=
  ∑ i, (m i:ℝ)*orderedBoundaryEnergy ω k 0 i

theorem continuous_action (k : ℕ) (m : Config k → ℤ) : Continuous (action k m) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_frozen_energy k i)

/-- The largest prefix with a nonzero balanced weight cannot cancel any
integer combination of the strictly smaller prefixes on the same draw. -/
theorem gaussian_last_action :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (k : ℕ) (p : (j : Fin k) → Config j.val → ℤ)
      (m : Config k → ℤ), (∑ i, m i)=0 →
      (∑ j, action j.val (p j) ω)+action k m ω=0 → m=0 := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro p
  let g (ω : PathPauliDisorder) := -(∑ j, action j.val (p j) ω)
  have hg : Continuous g := (continuous_finsetSum _ fun j _ => continuous_action j.val (p j)).neg
  filter_upwards [gaussian_predictable_actions k g hg.measurable] with ω hω
  intro m hb he
  by_contra hn
  apply hω m hn hb
  have hf (j : Fin k) : action j.val (p j) (eraseTerminal k ω)=action j.val (p j) ω := by
    simp only [action,energy_before j.isLt]
  change action k m ω = -(∑ j, action j.val (p j) (eraseTerminal k ω))
  simp only [hf]
  linarith only [he]

/-- Every finite collection of distinct prefixes has jointly independent
balanced spectra. The prefixes share all their overlapping couplings. -/
theorem gaussian_nested_actions :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (m : (j : Fin n) → Config j.val → ℤ),
      (∀ j, (∑ i, m j i)=0) → (∑ j, action j.val (m j) ω)=0 → ∀ j, m j=0 := by
  filter_upwards [gaussian_last_action] with ω hω
  intro n
  induction n with
  | zero => intro _ _ _ j; exact Fin.elim0 j
  | succ k ih =>
    intro m hb he
    rw [Fin.sum_univ_castSucc] at he
    let p (j : Fin k) := m j.castSucc
    have hlast := hω k p (m (Fin.last k)) (hb (Fin.last k)) he
    have hz : action k (m (Fin.last k)) ω=0 := by simp only [hlast,action,Pi.zero_apply,
      Int.cast_zero,zero_mul,Finset.sum_const_zero]
    have hrest : (∑ j, action j.val (p j) ω)=0 := by
      change (∑ j, action j.val (p j) ω)+action k (m (Fin.last k)) ω=0 at he
      rwa [hz,add_zero] at he
    exact Fin.lastCases hlast (ih p (fun j => hb j.castSucc) hrest)

#print axioms gaussian_nested_actions
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
