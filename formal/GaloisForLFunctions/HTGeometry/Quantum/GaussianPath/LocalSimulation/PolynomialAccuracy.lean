import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Moments
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PathCircuit

/-! # Inverse-size simulation accuracy on growing time intervals -/
open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- N sixth-order steps suffice at error 1/N for every signed duration
satisfying |t|⁷≤N. Their total gate count is a deterministic multiple of N². -/
theorem gaussian_inverse_size_compiler :
    ∃ J : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t : ℝ, |t|^7≤N → HasProjectiveCircuitApproximation N (1/(N:ℝ)) (J*N^2) (unitaryEvolution H t) := by
  let L := (8:ℝ)^7*(1+7*21)
  have hL : 0≤L := by dsimp [L]; positivity
  obtain ⟨B,hB,hω⟩ := gaussian_prefix_local_moment 7
  obtain ⟨m,hm⟩ := exists_nat_gt (14*L^7*B)
  refine ⟨patchGateCost 6 21,?_⟩
  filter_upwards [hω] with ω hw
  filter_upwards [hw,eventually_ge_atTop m] with n hn hm'
  intro N H t ht
  obtain ⟨R,hR,hcap,hmom⟩ := hn
  let K := patchScale 6 (21*R)
  have hR' : 0≤R := zero_le_one.trans hR
  have hN : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by dsimp [N]; omega)
  have hN' := zero_lt_one.trans_le hN
  have hB' : 14*L^7*B≤N := hm.le.trans (by exact_mod_cast (show m≤N by dsimp [N]; omega))
  have hK : K≤L*R := by
    dsimp only [K,L,patchScale]
    norm_num
    linarith only [hR]
  have hK' : 0≤K := by dsimp [K,patchScale]; positivity
  have herr : 14*(N:ℝ)*(K*|t|)^7≤(1/(N:ℝ))*(N:ℝ)^6 := by
    calc
      _ ≤ 14*(N:ℝ)*((L*R)*|t|)^7 := by gcongr
      _ = (14*L^7*(N:ℝ))*R^7*|t|^7 := by ring
      _ ≤ (14*L^7*(N:ℝ))*(B*N)*N := by gcongr
      _ = (14*L^7*B)*(N:ℝ)^3 := by ring
      _ ≤ (N:ℝ)*(N:ℝ)^3 := mul_le_mul_of_nonneg_right hB' (by positivity)
      _ ≤ (N:ℝ)^5 := by
        rw [show (N:ℝ)*(N:ℝ)^3=(N:ℝ)^4 by ring]
        exact pow_le_pow_right₀ hN (by decide)
      _ = _ := by field_simp
  have he : 14*(N:ℝ)*(K*|t|)*(K*|t|/(N:ℝ))^6≤1/(N:ℝ) := by
    rw [div_pow,←mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hN' 6)).mpr
    calc _ = 14*(N:ℝ)*(K*|t|)^7 := by ring
         _ ≤ _ := herr
  have h := approx_enlarge (path_patch_circuit_abs (pathPauliDisorderShell ω n) R hR' hcap 6 N
    (by dsimp [N]; omega) t) he (le_refl _)
  change HasProjectiveCircuitApproximation N (1/(N:ℝ)) (N*(N*patchGateCost 6 21)) (unitaryEvolution H t) at h
  rwa [show N*(N*patchGateCost 6 21)=patchGateCost 6 21*N^2 by ring] at h

#print axioms gaussian_inverse_size_compiler
end
end GaloisForLFunctions.HTGeometry.LocalPatches
