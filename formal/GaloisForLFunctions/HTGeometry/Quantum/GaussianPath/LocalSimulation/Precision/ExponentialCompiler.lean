import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.BinaryCompiler
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.Scale

/-! # Exponential simulation accuracy on an exponential physical interval -/
open Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- At every duration up to 2^(γN), any prescribed linear number of
accuracy bits costs at most 2^(αN) gates for γ < α ≤ 1. All choices
share one frozen Gaussian chain. -/
theorem gaussian_exponential_precision_compiler :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (c : ℕ) (γ α : ℝ), 0 ≤ γ → γ < α → α ≤ 1 →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let u := pathPauliDisorderShell ω (k+1)
        ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) →
          HasProjectiveCircuitApproximation N (1/(2:ℝ)^(c*N)) ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
            (unitaryEvolution (pathHamiltonian u) t) := by
  filter_upwards [gaussian_binary_precision_compiler] with ω hw
  intro c γ α hγ hγα hα
  let C : ℕ := c+1
  have hC : 0 < (C:ℝ) := by dsimp [C]; positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp (binary_compiler_envelope
    (div_nonneg hγ hC.le) ((div_lt_div_iff_of_pos_right hC).mpr hγα))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,eventually_ge_atTop M] with k hk hk'
  intro N u t ht
  let d := C*N
  have hd : N ≤ d := by dsimp [d,C]; rw [Nat.add_mul,one_mul]; omega
  have hd' : M ≤ d := (hk'.trans (by dsimp [N]; omega)).trans hd
  have htimes (v : ℝ) : v/(C:ℝ)*(d:ℝ) = v*(N:ℝ) := by
    dsimp only [d]; push_cast; field_simp [hC.ne']
  have hh := hM d hd'
  rw [htimes,htimes] at hh
  let F := (2:ℝ)^(5*d.sqrt+17)
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num)
  have hp : (N:ℝ)*(1+|t|)*F ≤ (2:ℝ)^(α*(N:ℝ)) := by
    apply le_trans _ hh
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by exact_mod_cast hd)
      (add_le_add_right ht 1) (by positivity) (Nat.cast_nonneg d)) (zero_le_one.trans hF)
  have hvol : (N:ℝ)*(1+|t|) ≤ (2:ℝ)^N := by
    apply (le_mul_of_one_le_right (by positivity) hF).trans (hp.trans _)
    have hh' := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α:=ℝ) N))
    simpa only [one_mul,rpow_natCast] using hh'
  have hscaled : (2:ℝ)^(c*N)*((N:ℝ)*(1+|t|)) ≤ (2:ℝ)^d := by
    exact (mul_le_mul_of_nonneg_left hvol (by positivity)).trans_eq (by
      rw [←pow_add]; congr 1; dsimp [d,C]; rw [Nat.add_mul,one_mul])
  obtain ⟨s,hfit,hs⟩ := hk t (c*N) d hd hscaled
  exact approx_enlarge hfit le_rfl (Nat.le_floor (hs.trans hp))

#print axioms gaussian_exponential_precision_compiler
end
end GaloisForLFunctions.HTGeometry.LocalPatches
