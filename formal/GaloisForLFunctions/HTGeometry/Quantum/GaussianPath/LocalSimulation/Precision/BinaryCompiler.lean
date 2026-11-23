import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Moments
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.BinaryScale

/-! # Local simulation with a prescribed number of accuracy bits -/
open Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- The error of the patch schedule is linear in the site count. Choosing
its order for an enlarged volume pays for accuracy while the actual circuit
still acts on the original register. -/
theorem gaussian_binary_precision_compiler :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      ∀ (t : ℝ) (b d : ℕ), N ≤ d → (2:ℝ)^b*((N:ℝ)*(1+|t|)) ≤ (2:ℝ)^d →
        ∃ s : ℕ, HasProjectiveCircuitApproximation N (1/(2:ℝ)^b) s
          (unitaryEvolution (pathHamiltonian u) t) ∧
          (s:ℝ) ≤ (N:ℝ)*(1+|t|)*2^(5*d.sqrt+17) := by
  obtain ⟨B,_,hdraw⟩ := gaussian_prefix_local_moment 2
  obtain ⟨a,ha⟩ := exists_nat_gt B
  filter_upwards [hdraw] with ω hω
  filter_upwards [hω,eventually_ge_atTop a,eventually_ge_atTop (128*128)] with n hn hna hroot
  intro N u t b d hNd hv
  obtain ⟨R,hR,hcap,hR₂⟩ := hn
  have hB : B ≤ (N:ℝ) := ha.le.trans (by exact_mod_cast (show a ≤ N by dsimp [N]; omega))
  have hNR : R ≤ (N:ℝ) := by
    apply (sq_le_sq₀ (zero_le_one.trans hR) (Nat.cast_nonneg _)).mp
    exact hR₂.trans (by rw [sq]; exact mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg _))
  have hd' : (N:ℝ) ≤ d := by exact_mod_cast hNd
  have hd : 128 ≤ d.sqrt := Nat.le_sqrt.mpr (by dsimp [N] at hNd; omega)
  have hV : (((2^b*N:ℕ):ℝ))*(1+|t|) ≤ (2:ℝ)^d := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hv
  obtain ⟨p,r,hr,he,hg⟩ := binary_patch_schedule (2^b*N) d |t| R (abs_nonneg t) hV hd
    (zero_le_one.trans hR) (by linarith only [hNR,hd',Nat.cast_nonneg (α:=ℝ) d])
  let K := patchScale p (21*R)
  have hscale : 0 < (2:ℝ)^b := by positivity
  have herr : 14*(N:ℝ)*(K*|t|)*(K*|t|/r)^p ≤ 1/(2:ℝ)^b := by
    apply (le_div_iff₀ hscale).mpr
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at he
    calc
      _ = 14*((2:ℝ)^b*N)*(K*|t|)*(K*|t|/r)^p := by ring
      _ ≤ 1/100 := he
      _ ≤ 1 := by norm_num
  refine ⟨_,approx_enlarge (path_patch_circuit_abs u R (zero_le_one.trans hR) hcap p r hr t) herr le_rfl,?_⟩
  change ((r*(N*patchGateCost p 21):ℕ):ℝ) ≤ (N:ℝ)*(1+|t|)*2^(5*d.sqrt+17)
  apply (mul_le_mul_iff_right₀ hscale).mp
  push_cast at hg ⊢
  calc
    _ = (r:ℝ)*((2^b*N)*(patchGateCost p 21:ℝ)) := by ring
    _ ≤ _ := hg
    _ = _ := by ring

#print axioms gaussian_binary_precision_compiler
end
end GaloisForLFunctions.HTGeometry.LocalPatches
