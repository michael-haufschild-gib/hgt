import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # A physical time witnessing the norm of an energy difference -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
open private norm_scalarCenteredHamiltonian from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- At time π divided by the norm of a nonzero self-adjoint generator,
an extremal eigenline has phase −1. -/
theorem spectral_peak {n : ℕ} (H : selfAdjoint (Reg n)) (h : 0<‖H.val‖) :
    2≤‖unitaryEvolution H.val (π/‖H.val‖)-1‖ := by
  classical
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => |E i|) Finset.univ_nonempty
  have hnorm : ‖H.val‖=‖fun i => (E i:ℂ)‖ := by
    simpa only [scalarCenteredHamiltonian,Complex.ofReal_zero,zero_smul,sub_zero,E] using
      norm_scalarCenteredHamiltonian H 0
  have hmax : |E i|=‖H.val‖ := by
    rw [hnorm]
    apply le_antisymm
    · simpa only [Complex.norm_real,Real.norm_eq_abs] using
        (norm_le_pi_norm (fun j => (E j:ℂ)) i)
    · exact (pi_norm_le_iff_of_nonempty _).mpr fun j => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using hi j (Finset.mem_univ j)
  let s := π/‖H.val‖
  have signed : s*E i=π ∨ s*E i= -π := by
    rcases le_or_gt 0 (E i) with hp|hn
    · left
      rw [abs_of_nonneg hp] at hmax
      dsimp only [s]
      rw [hmax,div_mul_cancel₀ _ h.ne']
    · right
      rw [abs_of_neg hn] at hmax
      have he : E i= -‖H.val‖ := by linarith only [hmax]
      dsimp only [s]
      rw [he,mul_neg,div_mul_cancel₀ _ h.ne']
  have hp : anchorPhase E i s= -1 := by
    change Complex.exp (-(Complex.I*((s:ℂ)*(E i:ℂ))))= -1
    rw [←Complex.ofReal_mul]
    rcases signed with hp|hp
    · rw [hp,mul_comm,Complex.exp_neg,Complex.exp_pi_mul_I]
      norm_num
    · rw [hp,Complex.ofReal_neg,mul_neg,neg_neg,mul_comm,Complex.exp_pi_mul_I]
  have hd := norm_evolution_sub_scalar H s 1
  rw [one_smul] at hd
  rw [hd]
  have hi' := norm_le_pi_norm (fun j => anchorPhase E j s-1) i
  rw [hp] at hi'
  norm_num at hi' ⊢
  exact hi'

#print axioms spectral_peak
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
