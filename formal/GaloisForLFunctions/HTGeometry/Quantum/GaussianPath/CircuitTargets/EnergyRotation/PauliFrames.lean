import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.GaussianWords
import GaloisForLFunctions.HTGeometry.PauliLabelSupport

/-! # Pauli corrections of the same circuit visited at different dates -/
open Matrix Finset Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A visit to A and a visit to P A force a visit to P at their signed
time difference. A can depend on both dates and on the Hamiltonian. -/
theorem pauli_lag {n : ℕ} (H : selfAdjoint (Reg n)) (P : Fin n → Option (Fin 3))
    (A : Reg n) (s t : ℝ) (z w : ℂ) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    ∃ v : ℂ, ‖v‖=1 ∧ ‖unitaryEvolution H.val (t-s)-v • finitePauliMatrix P‖ ≤ 
      ‖unitaryEvolution H.val s-z • A‖+
        ‖unitaryEvolution H.val t-w • (finitePauliMatrix P*A)‖ := by
  let v := w/z
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne one_ne_zero)
  have hv : ‖v‖=1 := by simp only [v,norm_div,hw,hz,div_one]
  have hphase : v*z=w := div_mul_cancel₀ _ hz0
  let B := finitePauliMatrix P
  let U := unitaryEvolution H.val
  have hu := unitaryEvolution_mem_unitary H.2 s
  have h := unitaryEvolution_sub_mul H t s
  change U (t-s)*U s=U t at h
  have hex : (U (t-s)-v • B)*U s=
      (U t-w • (B*A))+(v • B)*(z • A-U s) := by
    rw [sub_mul,h,mul_sub,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hphase]
    abel
  have hb : ‖v • B‖=1 := by rw [norm_smul,hv,norm_finitePauliMatrix,one_mul]
  refine ⟨v,hv,?_⟩
  rw [←CStarRing.norm_mul_mem_unitary (U (t-s)-v • B) hu,hex]
  apply (norm_add_le ..).trans
  rw [add_comm ‖U s-z • A‖]
  apply add_le_add_left
  exact (norm_mul_le ..).trans_eq (by rw [hb,one_mul,norm_sub_rev])

/-- On one typical chain, two visited left Pauli corrections of an
arbitrary common unitary can differ on only a vanishing fraction of sites.
Both visits use projective error one tenth and unrestricted physical dates. -/
theorem gaussian_pauli_frame_diameter :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ X : unitaryGroup (Fin (n+2) → Bool) ℂ, ∀ P Q : Fin (n+2) → Option (Fin 3),
      ∀ s t : ℝ, ∀ z w : ℂ, ‖z‖=1 → ‖w‖=1 →
      ‖unitaryEvolution H s-z • (finitePauliMatrix P*X.val)‖ ≤ 1/10 →
      ‖unitaryEvolution H t-w • (finitePauliMatrix Q*X.val)‖ ≤ 1/10 →
      ((univ.filter fun i => P i ≠ Q i).card:ℝ) ≤ η*(n+2:ℕ) := by
  filter_upwards [gaussian_all_time_pauli_support] with ω hω
  intro η hη
  filter_upwards [hω η hη] with n hn
  intro H X P Q s t z w hz hw hp hq
  let R := optMulLabel Q P
  let a := optPhaseProd Q P
  let A := finitePauliMatrix P*X.val
  have hpq : finitePauliMatrix Q*finitePauliMatrix P=a • finitePauliMatrix R :=
    finitePauliMatrix_mul' Q P
  have hU := mul_mem (finitePauliMatrix_mem_unitary Q) (finitePauliMatrix_mem_unitary P)
  have ha := CStarRing.norm_of_mem_unitary hU
  rw [hpq,norm_smul,norm_finitePauliMatrix,mul_one] at ha
  have hright : a • (finitePauliMatrix R*A)=finitePauliMatrix Q*X.val := by
    rw [←Matrix.smul_mul,←hpq]
    dsimp only [A]
    rw [mul_assoc,←mul_assoc (finitePauliMatrix P),finitePauliMatrix_mul_self,one_mul]
  have hwa : ‖w*a‖=1 := by rw [norm_mul,hw,ha,one_mul]
  have hfit : ‖unitaryEvolution H t-(w*a) • (finitePauliMatrix R*A)‖ ≤ 1/10 := by
    rwa [←smul_smul,hright]
  obtain ⟨v,hv,hvfit⟩ := pauli_lag (⟨H,isSelfAdjoint_pathHamiltonian _⟩) R A s t z (w*a) hz hwa
  have hr := hn R (t-s) v hv (hvfit.trans (by linarith only [hp,hfit]))
  have hs : labelSupport R=univ.filter fun i => P i ≠ Q i := by
    ext i
    simp only [mem_labelSupport,R,optMulLabel,ne_eq,optMul_eq_none_iff,mem_filter,mem_univ,true_and,eq_comm]
  rwa [hs] at hr

#print axioms gaussian_pauli_frame_diameter
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
