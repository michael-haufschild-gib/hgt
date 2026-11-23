import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.MomentFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.PhysicalWindow

/-! # A basis-independent gate floor on the Gaussian startup window -/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section

/-- The identity displacement is uniformly larger than 1/4 from an
inverse-size onset through every bounded horizon. -/
theorem gaussian_scalar_departure :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ |t| *(n+1:ℕ) → |t| ≤ T →
      (1/4:ℝ) < ‖1-unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t‖ := by
  obtain ⟨A,hA,hf⟩ := SpanningDensity.FixedHorizon.gaussian_all_bounded_horizons (by norm_num : (0:ℝ) < 1/2)
  refine ⟨A,hA,?_⟩
  filter_upwards [hf] with ω hf
  intro T
  filter_upwards [hf T] with n hf
  intro t ht hT
  let u := pathPauliDisorderShell ω n
  let U := unitaryEvolution (pathHamiltonian u) t
  change (1/4:ℝ) < ‖1-U‖
  by_contra! h
  have hcheap : HasProjectiveCircuitApproximation (n+2) (1/4) 0 U := by
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    rw [one_smul,TwoQubitCircuit.one_eval,norm_sub_rev]
    exact h
  have hneg := hf t ht hT 0 hcheap
  have hp : 0 ≤ (1-1/2:ℝ)*(n+1:ℕ) := by positivity
  exact hneg.not_ge (by simpa only [Nat.cast_zero] using hp)

/-- Through every bounded horizon, a fitting circuit in any basis must
satisfy B·4^s·N·t² ≥ 1 once the physical path has left its initial
inverse-size window. In particular its budget diverges whenever Nt² tends
to zero along these dates. -/
theorem gaussian_spectator_variance_floor :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, A ≤ |t| *(n+1:ℕ) → |t| ≤ T →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
      HasProjectiveCircuitApproximation (n+2) (1/10) s
        (W.val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t*star W.val) →
      1 ≤ B*(4:ℝ)^s*t^2*(n+2:ℕ) := by
  obtain ⟨A,hA,hf⟩ := gaussian_scalar_departure
  obtain ⟨_,b,_,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨A,400*b,hA,by positivity,?_⟩
  filter_upwards [hf,hm] with ω hf hm
  intro T
  filter_upwards [hf T,hm] with n hf hm
  intro t ht hT W s hfit
  have hw := variance_gate_floor _ t W (hf t ht hT) hfit
  have hpos : 0 ≤ 400*(4:ℝ)^s*t^2 := by positivity
  exact hw.trans ((mul_le_mul_of_nonneg_left hm.2 hpos).trans_eq (by ring))

/-- At a deterministic inverse-size date even the best choice of basis
needs a diverging budget. The bound holds simultaneously for every basis. -/
theorem gaussian_inverse_size_spectral_floor :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ᶠ n : ℕ in atTop, ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
      HasProjectiveCircuitApproximation (n+2) (1/10) s
        (W.val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (A/(n+1:ℕ))*star W.val) →
      ((n+1:ℕ):ℝ) ≤ K*(4:ℝ)^s := by
  obtain ⟨A,B,hA,hB,hw⟩ := gaussian_spectator_variance_floor
  refine ⟨A,2*B*A^2,hA,by positivity,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω A] with n hn
  intro W s hfit
  let m := ((n+1:ℕ):ℝ)
  have hm : 0 < m := by dsimp only [m]; positivity
  have hm₁ : 1 ≤ m := by dsimp only [m]; exact_mod_cast (show 1 ≤ n+1 by omega)
  have ht : |A/m|=A/m := abs_of_pos (div_pos hA hm)
  have h := hn (A/m) (by rw [ht]; exact (div_mul_cancel₀ A hm.ne').ge)
    (by rw [ht]; exact div_le_self hA.le hm₁) W s hfit
  have hn₂ : ((n+2:ℕ):ℝ) ≤ 2*m := by dsimp only [m]; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  change 1 ≤ B*4^s*(A/m)^2*((n+2:ℕ):ℝ) at h
  rw [div_pow] at h
  field_simp [hm.ne'] at h
  have hh := mul_le_mul_of_nonneg_left hn₂ (show 0 ≤ B*(4:ℝ)^s*A^2 by positivity)
  apply (mul_le_mul_iff_left₀ hm).mp
  nlinarith only [h,hh]

#print axioms gaussian_inverse_size_spectral_floor
#print axioms gaussian_spectator_variance_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
