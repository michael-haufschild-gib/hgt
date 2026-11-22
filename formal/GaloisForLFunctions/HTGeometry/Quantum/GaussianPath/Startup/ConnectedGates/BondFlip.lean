import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.StateMinor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels

/-! # Every physical bond has a nonzero double-flip amplitude -/
open Matrix MeasureTheory MvPolynomial
namespace GaloisForLFunctions.HTGeometry.ConnectedGates
noncomputable section

/-- On the all-zero input, XX on the specified edge flips precisely its
two bits with amplitude one. -/
private theorem xx_entry {n : ℕ} (e : Fin (n+1)) :
    finitePauliMatrix (couplingWord e (0,0)) (corner e.castSucc e.succ true true)
      (fun _ => false)=1 := by
  apply Finset.prod_eq_one
  intro i _
  by_cases h : i=e.castSucc
  · simp only [couplingWord,corner,if_pos h,boolPauliOptionEntry_x]
    simp
  · by_cases h' : i=e.succ
    · simp [couplingWord,corner,h',boolPauliOptionEntry_x]
    · simp [couplingWord,corner,h,h',boolPauliOptionEntry_none]

private theorem bond_flip_ae (n : ℕ) (e : Fin (n+1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, pathHamiltonian (pathPauliDisorderShell ω n)
      (corner e.castSucc e.succ true true) (fun _ => false)≠0 := by
  classical
  let d := Fintype.card (ChainLabel (n+2))
  let f := pathCoeffEquiv n
  let l : PathLabel n := .inr (e,0,0)
  let j := f.symm l
  let x := corner e.castSucc e.succ true true
  let y : Bits (n+2) := fun _ => false
  let a (i : Fin d) := finitePauliMatrix (pathWord (f i)) x y
  have ha : a j=1 := by
    dsimp only [a,j]; rw [Equiv.apply_symm_apply]; exact xx_entry e
  let P : MvPolynomial (Fin d) ℂ := ∑ i, X i*C (a i)
  have hP (z : Fin d→ℝ) : eval₂Hom (RingHom.id ℂ) (fun i => (z i:ℂ)) P=∑ i, (z i:ℂ)*a i := by
    simp [P]
  have hw : ∃ z : Fin d→ℝ, eval₂Hom (RingHom.id ℂ) (fun i => (z i:ℂ)) P≠0 := by
    refine ⟨fun i => if i=j then 1 else 0,?_⟩
    rw [hP]
    rw [Finset.sum_eq_single j]
    · simp [ha]
    · intro i _ hi; simp [hi]
    · exact fun h => (h (Finset.mem_univ j)).elim
  have hg := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae
    (SpectralJets.gaussian_ae_of_real_witness (RingHom.id ℂ) P (v:=1) one_ne_zero hw)
  filter_upwards [hg] with ω hω
  rw [hP] at hω
  let u := pathPauliDisorderShell ω n
  have he : pathHamiltonian u x y=∑ i, (u (f i):ℂ)*a i := by
    rw [pathHamiltonian_eq_sum,Matrix.sum_apply]
    exact (f.sum_comp (fun l => (u l:ℂ)*finitePauliMatrix (pathWord l) x y)).symm
  exact he ▸ hω

/-- One Gaussian draw has a nonzero two-spin flip on every edge of
every finite prefix. A single real XX coefficient witnesses each test. -/
theorem gaussian_bond_flip :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n, ∀ e : Fin (n+1),
      pathHamiltonian (pathPauliDisorderShell ω n) (corner e.castSucc e.succ true true) (fun _ => false)≠0 :=
  ae_all_iff.mpr fun n => ae_all_iff.mpr (bond_flip_ae n)

#print axioms gaussian_bond_flip
end
end GaloisForLFunctions.HTGeometry.ConnectedGates
