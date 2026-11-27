import GaloisForLFunctions.HTGeometry.ReplicaAmplitudeMoments

/-! # Exact maximum of a Gaussian replica moment over spectral twists -/
open Real Finset Set
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every pair of occupations contributes a positive Gaussian weight
when the target phases agree at the center of the record. -/
def alignedMoment (w E : I → ℝ) (q : ℕ) (T : ℝ) :=
  ∑ p ∈ univ.piAntidiag q, ∑ z ∈ univ.piAntidiag q, fidelityReplicaMultiplicityWeight w p z*
    exp (-(T*(replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E z))^2/2)

private theorem kernel_real (x : ℝ) :
    gaussianObserverActionKernel x=(exp (-x^2/2):ℂ) := by
  rw [gaussianObserverActionKernel,Complex.ofReal_exp]
  push_cast <;> rfl

theorem identity_gaussian_moment (w E : I → ℝ) (q : ℕ) (T : ℝ) :
    twistedGaussianSpectralFidelityMean w E (fun _ => 1) q T=(alignedMoment w E q T:ℂ) := by
  rw [twistedGaussianSpectralFidelityMean_eq_actionKernel]
  simp [alignedMoment,kernel_real,replicaMultiplicityTwist]

private theorem replica_twist_le {v : I → ℂ} (hv : ∀ i, ‖v i‖ ≤ 1) (p z : I → ℕ) :
    ‖replicaMultiplicityTwist v p z‖ ≤ 1 := by
  rw [replicaMultiplicityTwist,norm_mul,norm_prod,norm_prod]
  apply mul_le_one₀
  · apply prod_le_one (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hv i)
  · positivity
  · apply prod_le_one (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow,show ‖(starRingEnd ℂ) (v i)‖=‖v i‖ from norm_star _]
    exact pow_le_one₀ (norm_nonneg _) (hv i)

/-- The identity twist attains the worst moment even when the other
targets may have arbitrary complex diagonal entries in the closed disk. -/
theorem greatest_gaussian_moment {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) (E : I → ℝ) (q : ℕ) (T : ℝ) :
    IsGreatest {x : ℝ | ∃ v : I → ℂ, (∀ i, ‖v i‖ ≤ 1) ∧
      x=‖twistedGaussianSpectralFidelityMean w E v q T‖} (alignedMoment w E q T) := by
  classical
  have hnn : 0 ≤ alignedMoment w E q T := sum_nonneg fun p _ => sum_nonneg fun z _ =>
    mul_nonneg (fidelityReplicaMultiplicityWeight_nonneg hw p z) (exp_pos _).le
  constructor
  · exact ⟨fun _ => 1,fun _ => norm_one.le,by
      rw [identity_gaussian_moment,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnn]⟩
  · rintro _ ⟨v,hv,rfl⟩
    rw [twistedGaussianSpectralFidelityMean_eq_actionKernel]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro p _
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro z _
    rw [norm_mul,norm_mul,norm_gaussianObserverActionKernel,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hw p z)]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right
      (fidelityReplicaMultiplicityWeight_nonneg hw p z) (replica_twist_le hv p z)) (exp_pos _).le

#print axioms greatest_gaussian_moment
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
