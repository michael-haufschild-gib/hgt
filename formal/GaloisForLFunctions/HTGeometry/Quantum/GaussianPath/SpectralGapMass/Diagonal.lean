import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpinMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.OppositeConfigurations
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.Multiplicity

/-! # Longitudinal fields force spectral mass away from zero -/
open Matrix Real
open RiemannGaussian.HermitianRankTrace
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass
noncomputable section

/-- The diagonal is a doubly stochastic average of the spectrum. -/
theorem diagonal_absolute_le {I : Type*} [Fintype I] [DecidableEq I] {M : Matrix I I ℂ}
    (h : M.IsHermitian) : (∑ i, |(M i i).re|)≤∑ j, |h.eigenvalues j| := by
  let w := normSqMatrix (h.eigenvectorUnitary : Matrix I I ℂ)
  have hw := normSqMatrix_mem_doublyStochastic_of_unitary h.eigenvectorUnitary.2
  rw [mem_doublyStochastic_iff_sum] at hw
  obtain ⟨hn,_,hc⟩ := hw
  calc
    _ ≤ ∑ i, ∑ j, w i j*|h.eigenvalues j| := by
      apply Finset.sum_le_sum
      intro i _
      change |RCLike.re (M i i)|≤_
      rw [Multiplicity.re_diag_eq_sum_normSq_eigenvalues h i]
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
      rw [abs_mul,abs_of_nonneg (hn i j)]
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [←Finset.sum_mul,show (∑ i, w i j)=1 from hc j,one_mul]

/-- Global reversal cancels every diagonal bond, leaving the onsite
Rademacher sum. Its absolute mass transfers to the true eigenvalues. -/
theorem longitudinal_absolute_lower {n : ℕ} (u : PathShell n) :
    (2:ℝ)^(n+2)*sqrt (∑ i : Fin (n+2), (u (.inl (i,2)))^2) ≤
      8*∑ j, |(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j| := by
  let a := fun i : Fin (n+2) => u (.inl (i,2))
  let f := pathDiagEnergy u
  let flip : (Fin (n+2) → Bool) ≃ (Fin (n+2) → Bool) :=
    ⟨fun s i => !(s i),fun s i => !(s i),fun s => funext fun _ => Bool.not_not _,fun s => funext fun _ => Bool.not_not _⟩
  have hp (s : Fin (n+2) → Bool) : 2*|linearEnergy a s|≤|f s|+|f (flip s)| := by
    have h := abs_sub (f s) (f (flip s))
    change |pathDiagEnergy u s-pathDiagEnergy u (fun i => !(s i))|≤_ at h
    rwa [ReturnSpacing.PhysicalComponents.opposite_energy,abs_mul,abs_of_pos zero_lt_two] at h
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun s _ => hp s
  rw [←Finset.mul_sum,Finset.sum_add_distrib,flip.sum_comp (fun s => |f s|)] at hh
  have hD := diagonal_absolute_le (isSelfAdjoint_pathHamiltonian u).isHermitian
  simp only [pathHamiltonian_diagonal_entry,Complex.ofReal_re] at hD
  exact (spin_absolute_lower _ a).trans (mul_le_mul_of_nonneg_left
    ((show (∑ s, |linearEnergy a s|)≤∑ s, |f s| by linarith only [hh]).trans hD) (by norm_num))

end
end GaloisForLFunctions.HTGeometry.SpectralGapMass
