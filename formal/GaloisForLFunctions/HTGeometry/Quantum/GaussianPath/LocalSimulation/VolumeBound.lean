import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.BinaryScale
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Moments

/-! # Near-spacetime-linear circuit cost on one fixed Gaussian chain -/
open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- At binary spacetime scale d the overhead above N(1+|t|) is at most
2^(5 floor(sqrt d)+17), uniformly over every duration and admissible scale. -/
theorem gaussian_path_spacetime_upper :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      ∀ (t : ℝ), ∀ d : ℕ, (N:ℝ)*(1+|t|) ≤ (2:ℝ)^d →
        ∃ s : ℕ, HasProjectiveCircuitApproximation N (1/100:ℝ) s
          (unitaryEvolution (pathHamiltonian u) t) ∧
          (s:ℝ) ≤ (N:ℝ)*(1+|t|)*2^(5*d.sqrt+17) := by
  obtain ⟨B,_,hdraw⟩ := gaussian_prefix_local_exponential
  obtain ⟨b,hb⟩ := exists_nat_gt B
  let d₀ : ℕ := 128*128
  filter_upwards [hdraw] with ω hω
  filter_upwards [hω,eventually_ge_atTop b,eventually_ge_atTop ((2:ℕ)^d₀)] with n hh hn hlarge
  intro N u t d hvol
  have ht := abs_nonneg t
  obtain ⟨R,hR,hcap,hexp⟩ := hh
  have hN : (N:ℝ) ≤ (2:ℝ)^d :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith only [ht])).trans hvol
  have hN' : N ≤ (2:ℕ)^d := by exact_mod_cast hN
  have hD : d₀ ≤ d := by
    apply le_of_not_gt
    intro h
    have hbad := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h
    exact hbad.not_ge (hlarge.trans ((Nat.le_add_right n 2).trans hN'))
  have hB : B ≤ (N:ℝ) := hb.le.trans (by exact_mod_cast (show b ≤ N by dsimp [N]; omega))
  have htwo : (2:ℝ)^d ≤ Real.exp (d:ℝ) := by
    have h := Real.add_one_le_exp (1:ℝ)
    have h' : (2:ℝ) ≤ Real.exp 1 := by linarith only [h]
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h' d
  have hRd : R ≤ 2*(d:ℝ) := Real.exp_le_exp.mp (calc
    _ ≤ B*(N:ℝ) := hexp
    _ ≤ Real.exp (d:ℝ)*Real.exp (d:ℝ) := mul_le_mul ((hB.trans hN).trans htwo)
      (hN.trans htwo) (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add,two_mul])
  obtain ⟨p,r,hr,he,hcount⟩ := binary_patch_schedule N d |t| R ht hvol (Nat.le_sqrt.mpr hD)
    (zero_le_one.trans hR) hRd
  exact ⟨_,approx_enlarge (path_patch_circuit_abs u R (zero_le_one.trans hR) hcap p r hr t) he le_rfl,hcount⟩

#print axioms gaussian_path_spacetime_upper
end
end GaloisForLFunctions.HTGeometry.LocalPatches
