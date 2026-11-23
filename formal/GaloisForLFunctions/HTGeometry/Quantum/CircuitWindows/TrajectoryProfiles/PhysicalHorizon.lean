import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.CoveringNumber
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # Lower bound on the length of a full trajectory observation -/
open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TrajectoryProfiles
open SharpOccupation
noncomputable section

/-- At precision 2⁻ᴰ, any interval that represents every translated
gate-distance profile has length at least (2^(D(D−2))−1)/(D(1+CN)).
The bound applies to every observation origin on the same Gaussian draw. -/
theorem gaussian_full_profile_observation_lower :
    ∃ C > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a G : ℝ, 0 ≤ G →
        (∀ v : ℝ, ∃ z ∈ Icc a (a+G), ∀ t : ℝ, ∀ s : ℕ,
          |orbitCircuitDistance H s (v+t)-orbitCircuitDistance H s (z+t)| ≤ 1/(2:ℝ)^D) →
          ((2:ℝ)^(D*(D-2))-1)/((D:ℝ)*(1+C*N)) ≤ G := by
  obtain ⟨C,hC,hbound⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,gaussian_path_all_prefixes_maximally_projective] with ω hb hi
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hb] with k hk
  intro N D H a G hG hcover
  let B := (2:ℝ)^D
  let η := 1/B
  have hD : 2 ≤ D := by
    change 2^1 ≤ 2^(k+3)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hDp : 0 < (D:ℝ) := by exact_mod_cast (by omega : 0<D)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hη : 0 < η := one_div_pos.mpr hB
  have hB₂ : (2:ℝ) ≤ B := by
    change (2:ℝ)^1 ≤ (2:ℝ)^D
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hsmall : η+η < sqrt 2 := by
    apply lt_of_le_of_lt _ ((lt_sqrt zero_le_one).mpr (by norm_num) : (1:ℝ)<sqrt 2)
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hB₂
    change 1/B+1/B ≤ 1
    linarith only [h]
  have hac := (ShortTimeProducts.physical_arc_bounds (add_pos hη hη) hsmall).2
  have harc : physicalArc (η+η) ≤ η := by linarith only [hac]
  have h := duration_of_cover H (hi k) a hG hη.le hη hsmall hcover
  have hK : ‖H.val‖ ≤ C*(N:ℝ) := hk
  have hcap : 1 ≤ (1+G*(1+C*N)*B)*((D:ℝ)*(1/B)^(D-1)) := by
    apply h.trans
    apply mul_le_mul
    · change 1+G*(1+‖H.val‖)/(1/B) ≤ 1+G*(1+C*N)*B
      rw [div_one_div]
      exact add_le_add_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hK 1) hG) hB.le) 1
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (physicalArc_spec (add_pos hη hη) hsmall).1.1.le harc _) hDp.le
    · apply mul_nonneg hDp.le
      exact pow_nonneg (physicalArc_spec (add_pos hη hη) hsmall).1.1.le _
    · positivity
  have hpow : B^(D-1) ≤ (1+G*(1+C*N)*B)*(D:ℝ) := by
    rw [one_div_pow,←mul_assoc,mul_one_div] at hcap
    simpa only [one_mul] using (le_div_iff₀ (pow_pos hB _)).mp hcap
  have hDb : (D:ℝ) ≤ B := by exact_mod_cast (Nat.lt_two_pow_self (n:=D)).le
  have hnext : D-2+1=D-1 := by omega
  have hbound' : B^(D-2) ≤ 1+(D:ℝ)*(1+C*N)*G := by
    apply (mul_le_mul_iff_left₀ hB).mp
    rw [←pow_succ,hnext]
    exact hpow.trans (by linarith only [hDb])
  apply (div_le_iff₀ (mul_pos hDp (by positivity))).mpr
  rw [pow_mul]
  change B^(D-2)-1 ≤ G*((D:ℝ)*(1+C*N))
  linarith only [hbound']

#print axioms gaussian_full_profile_observation_lower
end
end GaloisForLFunctions.HTGeometry.TrajectoryProfiles
