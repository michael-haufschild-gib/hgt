import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMeanReturns

/-! # Physical duration of the excluded circuit window -/
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The spectral-sign packing pays both for a quadratic speed and for a
waiting interval of length 2^⌊D/2048⌋. -/
theorem double_exponential_excursion_width {n : ℕ} (hn : 64 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) (hcap : v ≤ (n:ℝ)^2) :
    (2:ℝ)^(2^n/2048) ≤ translatedExcursionWidth n v := by
  have grow (k : ℕ) (hk : 64 ≤ k) : 4096*(k+1)^2 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      calc
        _ ≤ 2*(4096*(k+1)^2) := by obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk; ring_nf; omega
        _ ≤ _ := by rw [pow_succ 2 k]; omega
  let A := 2^(2^n/2048)
  let M := (excursionGateBudget n+1)^(excursionGateBudget n)
  have hnD : n ≤ 2^n/2048 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2048)).mpr
    apply le_trans _ (grow n hn)
    nlinarith only [Nat.zero_le (n^2)]
  have price : 40*((n:ℝ)^2+1)+1 ≤ (A:ℝ) := by
    have h₁ : 40*(n^2+1)+1 ≤ 4096*(n+1)^2 := by nlinarith only [Nat.zero_le n,Nat.zero_le (n^2)]
    exact_mod_cast (h₁.trans ((grow n hn).trans (Nat.pow_le_pow_right (by decide : 0 < 2) hnD)))
  have square : A*A ≤ M := by
    apply le_trans _ (circuit_return_spacing_factor_bounds hn).1
    change 2^(2^n/2048)*2^(2^n/2048) ≤ 2^(2^n/1024)
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hM : 1 ≤ M := by dsimp [M]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsq : (A:ℝ)*A ≤ M := by exact_mod_cast square
  have hA' : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hp : 40*(v+1)+1 ≤ (A:ℝ) := by linarith only [hcap,price]
  have hcast : (A:ℝ) = (2:ℝ)^(2^n/2048) := by simp [A]
  rw [← hcast]
  change (A:ℝ) ≤ ((M-1:ℕ):ℝ)*(1/(40*(v+1)))
  rw [mul_one_div,le_div_iff₀ (by positivity),Nat.cast_sub hM,Nat.cast_one]
  linarith only [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) A),hA',hsq]

/-- The bound holds on every sufficiently long prefix of the same disorder. -/
theorem gaussian_path_eventual_double_exponential_width :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      (2:ℝ)^(2^(k+3)/2048) ≤ translatedExcursionWidth (k+3) ‖pathHamiltonian (pathPauliDisorderShell ω (k+1))‖ := by
  obtain ⟨_,b,_,_,hm⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hm] with ω hω
  obtain ⟨m,hm⟩ := exists_nat_gt (12+b)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,eventually_ge_atTop m,eventually_ge_atTop 64] with k hmass hk hlarge
  let N := k+3
  let u := pathPauliDisorderShell ω (k+1)
  have hnorm : ‖pathHamiltonian u‖ ≤ ∑ l, |u l| := by
    rw [pathHamiltonian_eq_sum]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun l _ => by
      rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one])
  have hN : 12+b ≤ (N:ℝ) := hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  apply double_exponential_excursion_width (by omega) (norm_nonneg _)
  exact hnorm.trans ((path_pauli_coefficient_mass_le u b hmass.2).trans (by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg N)))

#print axioms gaussian_path_eventual_double_exponential_width
end
end GaloisForLFunctions.HTGeometry.SpectralJets
