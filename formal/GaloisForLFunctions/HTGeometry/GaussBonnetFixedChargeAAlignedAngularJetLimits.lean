import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAAlignedAngularPeriodicity

/-!
# Uniform limits at every angular derivative order

Joint jet continuity gives uniform convergence on a full compact
angular period. Periodicity then extends the estimate to every real
angle. Every derivative of the critical correction is zero.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAAlignedAngularCorrection_jet_family_uniform_limit (w φ : ℝ) (n : ℕ) :
    TendstoUniformly
      (fun s (ψ : Icc (0 : ℝ) (2 * Real.pi)) => iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ s) ψ)
      (fun ψ => iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceCriticalState w φ)) ψ)
      (𝓝 (egbFixedChargeAAlignedForceCriticalState w φ)) := by
  have hc : ContinuousOn (fun p : EGBAlignedForceState × Icc (0 : ℝ) (2 * Real.pi) =>
      iteratedDeriv n (egbFixedChargeAAlignedAngularCorrection w φ p.1) p.2)
      (egbFixedChargeAAlignedSmoothDomain ×ˢ univ) := by
    apply (egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_continuousOn w φ n).comp
      (f := fun p : EGBAlignedForceState × Icc (0 : ℝ) (2 * Real.pi) => (p.1, (p.2 : ℝ)))
    · fun_prop
    · intro p hp
      exact ⟨hp.1, mem_univ _⟩
  exact hc.tendstoUniformly (egbFixedChargeAAlignedSmoothDomain_isOpen.mem_nhds
    (egbFixedChargeAAlignedForceCriticalState_mem_smoothDomain w φ))

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_uniform_zero_limit (w φ l : ℝ) (n : ℕ) :
    TendstoUniformly (fun τ ψ => iteratedDeriv n
      (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l)) ψ)
      (fun _ => (0 : ℝ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAAlignedAngularCorrection_jet_family_uniform_limit w φ n)) ε hε
  filter_upwards [(egbFixedChargeAAlignedForceState_critical_limit w φ l).eventually he] with τ hτ
  intro ψ
  obtain ⟨θ, hθ, hval⟩ :=
    (egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_periodic w φ (egbFixedChargeAAlignedForceState w φ τ l) n).exists_mem_Ico₀
      Real.two_pi_pos ψ
  have h := hτ ⟨θ, ⟨hθ.1, hθ.2.le⟩⟩
  rw [egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_critical] at h
  rw [hval]
  exact h

theorem egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_moving_zero_limit (w φ l : ℝ) (n : ℕ) (ψ : ℝ → ℝ) :
    Tendsto (fun τ => iteratedDeriv n
      (egbFixedChargeAAlignedAngularCorrection w φ (egbFixedChargeAAlignedForceState w φ τ l)) (ψ τ))
      atBot (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp
    (egbFixedChargeAAlignedAngularCorrection_iteratedDeriv_uniform_zero_limit w φ l n)) ε hε
  filter_upwards [h] with τ hτ
  simpa only [dist_comm] using hτ (ψ τ)

end GaloisForLFunctions.HTGeometry
