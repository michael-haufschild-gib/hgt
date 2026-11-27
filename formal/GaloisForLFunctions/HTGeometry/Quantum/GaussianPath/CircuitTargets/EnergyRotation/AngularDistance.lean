import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.GaussianWords
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.AngularEcho

/-! # Distance from extensive Pauli words to the whole physical orbit -/
open Matrix Finset Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section

private theorem angle_for_error {d : ℝ} (hd : 0 ≤ d) (he : d ≤ √2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ 2*θ ≤ π/2 ∧ d=2*sin θ ∧ (√2-d)^2 ≤ 4*(1-sin (2*θ)) := by
  let θ := arcsin (d/2)
  have ht : 0 ≤ θ := arcsin_nonneg.mpr (half_nonneg hd)
  have hπ := Real.pi_pos
  have hsqrt := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hco : θ ≤ π/4 := by
    have h := arcsin_le_arcsin (show d/2 ≤ sin (π/4) by rw [sin_pi_div_four]; linarith only [he])
    rwa [arcsin_sin (by linarith only [hπ]) (by linarith only [hπ])] at h
  have hs : sin θ=d/2 := sin_arcsin (by linarith only [hd]) (by nlinarith only [he,hd,hsqrt])
  have hc := cos_le_cos_of_nonneg_of_le_pi ht (by linarith only [hπ] : π/4 ≤ π) hco
  rw [cos_pi_div_four] at hc
  refine ⟨θ,ht,by linarith only [hco],by linarith only [hs],?_⟩
  have hdiff : √2-d ≤ 2*(cos θ-sin θ) := by linarith only [hs,hc]
  have h := pow_le_pow_left₀ (sub_nonneg.mpr he) hdiff 2
  rw [sin_two_mul]
  nlinarith only [h,sin_sq_add_cos_sq θ]

/-- At any fixed positive support density, the deficit below √2 is
at most C/√K, uniformly over every physical date, global phase, and
Pauli word chosen on the observed prefix. -/
theorem gaussian_extensive_pauli_angular_distance {η : ℝ} (hη : 0 < η) :
    ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ Q : Fin (n+2) → Option (Fin 3), η*(n+2:ℕ) ≤ ((labelSupport Q).card:ℝ) →
        ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 →
          (max (√2-‖unitaryEvolution H t-z • finitePauliMatrix Q‖) 0)^2*(n+2:ℕ) ≤ C := by
  obtain ⟨c,hc,hfield⟩ := extensive_field_mass hη
  obtain ⟨_,b,_,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨21*π^2*b/c^2,by positivity,?_⟩
  filter_upwards [hfield,hm] with ω hf hm
  filter_upwards [hf,hm] with n hf hm
  intro H Q hQ t z hz
  let d := ‖unitaryEvolution H t-z • finitePauliMatrix Q‖
  let K : ℝ := (n+2:ℕ)
  have hK : 0 < K := by dsimp only [K]; positivity
  change (max (√2-d) 0)^2*K ≤ _
  by_cases hhigh : √2 ≤ d
  · rw [max_eq_right (sub_nonpos.mpr hhigh),zero_pow (by decide),zero_mul]
    positivity
  have hd := (lt_of_not_ge hhigh).le
  rw [max_eq_left (sub_nonneg.mpr hd)]
  obtain ⟨θ,hθ,ht,he,hgap⟩ := angle_for_error (norm_nonneg _) hd
  let u := pathPauliDisorderShell ω n
  let V : unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨finitePauliMatrix Q,finitePauliMatrix_mem_unitary Q⟩
  obtain ⟨S,j,ha,hs⟩ := hf Q hQ
  have hp := transverse_of_rotation u Q S j ha
    (angular_energy_rotation ⟨H,isSelfAdjoint_pathHamiltonian u⟩ V t z hz hθ ht he.le)
  have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hK.le) hs 2
  have h := (mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 16)
    (sub_nonneg.mpr (sin_le_one _)))).trans hp
  have hlast := h.trans (mul_le_mul_of_nonneg_left hm.2 (by positivity))
  change 16*(1-sin (2*θ))*(c*K)^2 ≤ 84*π^2*(b*K) at hlast
  have hscaled := mul_le_mul_of_nonneg_right hgap (sq_nonneg (c*K))
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  apply (mul_le_mul_iff_left₀ hK).mp
  linarith only [hlast,hscaled]

#print axioms gaussian_extensive_pauli_angular_distance
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
