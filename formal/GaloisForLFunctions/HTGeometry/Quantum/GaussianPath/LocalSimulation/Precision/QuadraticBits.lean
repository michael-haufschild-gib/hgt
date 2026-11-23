import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.BinaryCompiler
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.Scale

/-! # Quadratically many accuracy bits at sub-Hilbert gate count -/
open Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- An exponent gap between duration and gate count pays for quadratically
many accuracy bits. The integer m depends only on the two exponents. -/
theorem gaussian_quadratic_precision_compiler (γ α : ℝ) (hγ : 0 ≤ γ) (hγα : γ < α) (hα : α ≤ 1) :
    ∃ m > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) →
        HasProjectiveCircuitApproximation N (1/(2:ℝ)^((N/m)^2)) ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
          (unitaryEvolution (pathHamiltonian u) t) := by
  let β := (γ+α)/2
  have hγβ : γ < β := by dsimp only [β]; linarith only [hγα]
  have hβα : β < α := by dsimp only [β]; linarith only [hγα]
  obtain ⟨m,hm⟩ := exists_nat_gt (10/(α-β))
  have hem : 0 < (m:ℝ) := (div_pos (by norm_num) (sub_pos.mpr hβα)).trans hm
  have hmp : 0 < m := by exact_mod_cast hem
  have hgap := (div_lt_iff₀ (sub_pos.mpr hβα)).mp hm
  refine ⟨m,hmp,?_⟩
  filter_upwards [gaussian_binary_precision_compiler] with ω hcompile
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hcompile,
    (tendsto_add_atTop_nat 3).eventually (binary_compiler_envelope hγ hγβ),
    eventually_ge_atTop m] with k hs henv hkm
  intro N u t ht
  let q := N/m
  let d := (q+N.sqrt+1)^2
  have hNd : N ≤ (N.sqrt+1)^2 := by rw [pow_two]; exact (Nat.lt_succ_sqrt N).le
  have hsum : q^2+N ≤ d := by
    have hq := Nat.zero_le (q*(N.sqrt+1))
    dsimp only [d]
    nlinarith only [hNd,hq]
  have hd : N ≤ d := (Nat.le_add_left N (q^2)).trans hsum
  let F := (2:ℝ)^(5*N.sqrt+17)
  have hNF : (N:ℝ)*(1+|t|)*F ≤ (2:ℝ)^(β*(N:ℝ)) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right ht 1) (Nat.cast_nonneg N))
      (show 0≤F by dsimp only [F]; positivity)).trans henv
  have hvol : (N:ℝ)*(1+|t|) ≤ (2:ℝ)^N := by
    apply (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans (hNF.trans _)
    rw [←rpow_natCast]
    exact rpow_le_rpow_of_exponent_le (by norm_num) (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hβα.le.trans hα) (Nat.cast_nonneg (α:=ℝ) N))
  have hbudget : (2:ℝ)^(q^2)*((N:ℝ)*(1+|t|)) ≤ (2:ℝ)^d :=
    (mul_le_mul_of_nonneg_left hvol (by positivity)).trans (by
      rw [←pow_add]; exact pow_le_pow_right₀ (by norm_num) hsum)
  obtain ⟨j,hfit,hj⟩ := hs t (q^2) d hd hbudget
  have hqN : (q:ℝ)*(m:ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
  have hmN : (m:ℝ) ≤ N := by exact_mod_cast (hkm.trans (by dsimp only [N]; omega))
  have hbits : ((5*(q+1):ℕ):ℝ) ≤ (α-β)*(N:ℝ) := by
    apply (mul_le_mul_iff_left₀ hem).mp
    push_cast
    linarith only [hqN,hmN,mul_le_mul_of_nonneg_right hgap.le (Nat.cast_nonneg (α:=ℝ) N)]
  have hcost : (j:ℝ) ≤ (2:ℝ)^(α*(N:ℝ)) := by
    apply hj.trans
    rw [show d.sqrt=q+N.sqrt+1 from Nat.sqrt_eq' _,show 5*(q+N.sqrt+1)+17=5*N.sqrt+17+5*(q+1) by omega,pow_add,
      ←mul_assoc]
    apply (mul_le_mul_of_nonneg_right hNF (by positivity)).trans
    rw [←rpow_natCast,←rpow_add (by norm_num : (0:ℝ)<2)]
    exact rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hbits])
  exact approx_enlarge hfit le_rfl (Nat.le_floor hcost)

#print axioms gaussian_quadratic_precision_compiler
end
end GaloisForLFunctions.HTGeometry.LocalPatches
