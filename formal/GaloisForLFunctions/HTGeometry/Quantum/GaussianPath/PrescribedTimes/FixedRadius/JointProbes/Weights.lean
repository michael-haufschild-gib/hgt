import GaloisForLFunctions.HTGeometry.AngularPhaseLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-! # The spectral weight of simultaneous phase readings -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
noncomputable section

/-- Each probe contributes its own anchored integer character. Physical
delays multiply these integer weights by the real probe slopes. -/
def probeWeight {I : Type*} [Fintype I] {D : ℕ} (i₀ : Fin D) (λ' : I → ℝ)
    (m : I × phaseIndex i₀ → ℤ) (j : Fin D) : ℝ :=
  ∑ i, λ' i * zeroSumWeight i₀ (fun l => m (i,l)) j

theorem probeWeight_balanced {I : Type*} [Fintype I] {D : ℕ} (i₀ : Fin D) (λ' : I → ℝ)
    (m : I × phaseIndex i₀ → ℤ) : ∑ j, probeWeight i₀ λ' m j=0 := by
  simp only [probeWeight]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,sum_zeroSumWeight,mul_zero,Finset.sum_const_zero]

theorem probeWeight_ne_zero {I : Type*} [Fintype I] {D : ℕ} (i₀ : Fin D) {λ' : I → ℝ}
    (hλ : RationallyIndependentFrequency λ') {m : I × phaseIndex i₀ → ℤ} (hm : m≠0) :
    probeWeight i₀ λ' m≠0 := by
  intro h
  apply hm
  funext p
  have hz := congrFun h p.2.val
  simp only [probeWeight,zeroSumWeight_of_ne i₀ _ p.2,Pi.zero_apply] at hz
  have hd : finiteTorusCharacterDetuning (fun i => m (i,p.2)) λ'=0 := by
    simpa only [finiteTorusCharacterDetuning,mul_comm] using hz
  exact congrFun (hλ _ hd) p.1

/-- Summing the frequencies of the relative-phase probes yields the
ordinary balanced spectral action, with no assumption on the eigenbasis. -/
theorem probe_detuning {I : Type*} [Fintype I] {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a,(P a).IsHermitian) (i₀ : Fin D) (m : I × phaseIndex i₀ → ℤ)
    (λ' : I → ℝ) (θ : Fin N → ℝ) :
    finiteTorusCharacterDetuning m (fun p => λ' p.1*projectivePhase hP i₀ θ p.2) =
      sortedSpectralAction hP (probeWeight i₀ λ' m) θ := by
  classical
  change (∑ p, (m p:ℝ)*(λ' p.1*projectivePhase hP i₀ θ p.2))=_
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, λ' i*sortedSpectralAction hP (zeroSumWeight i₀ (fun l => m (i,l))) θ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [←sum_weight_mul_projectivePhase,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      unfold sortedSpectralAction probeWeight
      simp only [Finset.mul_sum,Finset.sum_mul,←mul_assoc]
      rw [Finset.sum_comm]

#print axioms probe_detuning
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.FixedRadius
