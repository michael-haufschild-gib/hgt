import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.Characteristic
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.DisjointLayers
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor
import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePrimeFieldIsGaussian

/-! # Gaussian comparison for a physical path split into disjoint packets -/
open Matrix Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- Normalized trace of the physical time evolution. -/
def shellTrace {n : ℕ} (u : PathShell n) (t : ℝ) :=
  ((Fintype.card (Fin (n+2)→Bool):ℂ))⁻¹*(unitaryEvolution (pathHamiltonian u) t).trace

/-- Spectral variance in the normalized trace state. -/
def shellVariance {n : ℕ} (u : PathShell n) : ℝ := ∑ l : PathLabel n, (u l)^2

private theorem trace_characteristic {n : ℕ} (u : PathShell n) (t : ℝ) :
    shellTrace u t=energyCharacteristic (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues (-t) := by
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  rw [shellTrace,unitaryEvolution_spectral hH,Matrix.trace_mul_cycle,hH.eigenvectorUnitary.property.1,
    Matrix.one_mul,Matrix.trace_diagonal]
  unfold energyCharacteristic
  congr 1
  apply sum_congr rfl
  intro i _
  congr 1
  push_cast
  ring

theorem norm_shellTrace_le {n : ℕ} (u : PathShell n) (t : ℝ) : ‖shellTrace u t‖≤1 := by
  rw [trace_characteristic,energyCharacteristic,norm_mul,norm_inv,Complex.norm_natCast]
  have hd : (0:ℝ)<Fintype.card (Fin (n+2)→Bool) := Nat.cast_pos.mpr Fintype.card_pos
  rw [←div_eq_inv_mul,div_le_one hd]
  exact (norm_sum_le _ _).trans_eq (by simp [Complex.norm_exp])

theorem shell_gaussian_error {n : ℕ} (u : PathShell n) (t : ℝ) :
    ‖shellTrace u t-(exp (-(t^2*shellVariance u/2)):ℂ)‖ ≤
      3* |t|^3*‖pathHamiltonian u‖*shellVariance u := by
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  obtain ⟨h₁,h₂⟩ := FluxOccupation.path_spectral_moments u
  have he : (∑ i, (hH.eigenvalues i)^2)=(Fintype.card (Fin (n+2)→Bool):ℝ)*shellVariance u := by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,shellVariance] using h₂
  rw [trace_characteristic]
  simpa only [neg_sq,abs_neg] using packet_gaussian_error hH.eigenvalues
    (sum_nonneg fun _ _ => sq_nonneg _) (norm_nonneg _) h₁ he
    (abs_eigenvalue_le_l2_opNorm hH) (-t)

/-- Independent site packets contribute multiplicatively to the exact
trace and additively to the error in its Gaussian approximation. -/
theorem disjoint_shell_comparison {n : ℕ} {ι : Type*} [Fintype ι]
    (S : ι→Finset (Fin (n+2))) (u : ι→PathShell n)
    (hd : ∀ i j, i≠j → Disjoint (S i) (S j))
    (hs : ∀ i, IsSiteSupported (S i) (pathHamiltonian (u i))) (t : ℝ) :
    ‖shellTrace (∑ i, u i) t-(exp (-(t^2*(∑ i, shellVariance (u i))/2)):ℂ)‖ ≤
      3* |t|^3*(∑ i, ‖pathHamiltonian (u i)‖*shellVariance (u i)) := by
  classical
  let D : ℂ := Fintype.card (Fin (n+2)→Bool)
  have hD : D≠0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hf := SpectatorCost.disjoint_trace_factors univ S
    (fun i => t • ((-Complex.I) • pathHamiltonian (u i))) (fun i => shellTrace (u i) t)
    (fun i _ j _ => hd i j) (fun i _ => (IsSiteSupported.complex_smul _ (hs i)).smul t) (fun i _ => by
      change _=(D⁻¹*_)*D
      rw [mul_comm _ D,←mul_assoc,mul_inv_cancel₀ hD,one_mul]
      rfl)
  have hsum : pathHamiltonian (∑ i, u i)=∑ i, pathHamiltonian (u i) := (pathHamiltonianLM n).map_sum ..
  have htrace : shellTrace (∑ i, u i) t=∏ i, shellTrace (u i) t := by
    simp only [shellTrace,hsum,unitaryEvolution,smul_sum]
    change D⁻¹*_=_
    rw [hf,←mul_assoc,inv_mul_cancel₀ hD,one_mul]
  let g (i : ι) := exp (-(t^2*shellVariance (u i)/2))
  have hg (i : ι) : g i≤1 := exp_le_one_iff.mpr (neg_nonpos.mpr
    (div_nonneg (mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)) (by norm_num)))
  have heq : (exp (-(t^2*(∑ i, shellVariance (u i))/2)):ℂ)=∏ i, (g i:ℂ) := by
    rw [←Complex.ofReal_prod]
    apply congrArg Complex.ofReal
    dsimp only [g]
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sum,sum_div,sum_neg_distrib]
  rw [htrace,heq]
  have h := GaloisForLFunctions.MultiscaleMollifiedZetaField.norm_prod_sub_prod_le_sum univ
    (fun i _ => norm_shellTrace_le (u i) t) (fun i _ => by simpa only [Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (exp_pos _)] using hg i)
  apply h.trans
  rw [mul_sum]
  exact sum_le_sum fun i _ => (shell_gaussian_error (u i) t).trans_eq (mul_assoc ..)

#print axioms disjoint_shell_comparison
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
