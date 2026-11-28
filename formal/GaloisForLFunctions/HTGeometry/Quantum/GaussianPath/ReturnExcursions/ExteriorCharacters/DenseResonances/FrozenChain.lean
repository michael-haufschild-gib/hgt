import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.AbsoluteWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Band
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Unsigned macroscopic detunings on the original Gaussian horizon -/

open Filter MeasureTheory Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
open PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- Even the empty circuit has an absolute macroscopic sinc sum larger
than every fixed multiple of the target signed scale. Every retained
same-bin pair has broad support and detuning at most the inverse width. -/
theorem gaussian_dense_resonances :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ M : ℝ, 0≤M → ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let H := generator (pathPauliDisorderShell ω (k+1))
      let w := (11/10:ℝ)^D+ElapsedWindow.clearanceTime H
      let F := (univ : Finset (Fin K → Bool)).powersetCard (D/2)
      let x (S : Finset (Fin K → Bool)) := ∑ i ∈ S, H.2.isHermitian.eigenvalues i
      let B : ℝ := D.choose (D/2)
      M*B^2*(9/10)^D < (pairCount F (D/4) (fun S T => |w*(x S-x T)|≤1):ℝ)/2 ∧
        M*B^2*(9/10)^D < absoluteWindow F x (D/4) w := by
  obtain ⟨C,hC,hω⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  filter_upwards [hω] with ω hw
  intro M hM
  obtain ⟨N,hN⟩ := eventually_atTop.mp (band_resonances C (2*M) (mul_nonneg (by norm_num) hM))
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hw
  filter_upwards [eventually_ge_atTop J,eventually_ge_atTop N] with k hk hN'
  intro K D H w F x B
  let n := 2^(k+1)
  have hkn : k+1≤n := Nat.lt_two_pow_self.le
  have hd : D=4*n := by dsimp only [D,K,n]; rw [show k+3=(k+1)+2 by omega,pow_add]; ring
  have hq : D/2=2*n := by omega
  have hr : D/4=n := by omega
  have hdim : Fintype.card (Fin K → Bool)=4*n := by
    simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hd
  have hH := hJ (k+1) (by omega)
  change ‖H.val‖≤C*(K:ℝ) at hH
  have hK : (K:ℝ)≤4*(n:ℝ) := by exact_mod_cast (show K≤4*n by dsimp only [K]; omega)
  have hδ : ElapsedWindow.clearanceTime H≤1 := by
    unfold ElapsedWindow.clearanceTime
    apply (div_le_one (by positivity)).mpr
    linarith only [norm_nonneg H.val]
  have hL : 1≤(11/10:ℝ)^D := one_le_pow₀ (by norm_num)
  have hw₀ : 0≤w := by dsimp [w,ElapsedWindow.clearanceTime]; positivity
  have hw₁ : w≤2*(11/10:ℝ)^(4*n) := by dsimp only [w]; rw [←hd]; linarith only [hδ,hL]
  have hh := hN n (by omega) (I:=Fin K → Bool) hdim H.2.isHermitian.eigenvalues ‖H.val‖ w (norm_nonneg _)
    (hH.trans (mul_le_mul_of_nonneg_left hK hC.le)) (abs_eigenvalue_le_l2_opNorm H.2.isHermitian) hw₀ hw₁
  have hh' : (2*M)*B^2*(9/10)^D < (pairCount F (D/4) (fun S T => |w*(x S-x T)|≤1):ℝ) := by
    dsimp only [F,x,B]
    rw [hq,hr,hd]
    exact hh
  have ht : M*B^2*(9/10)^D < (pairCount F (D/4) (fun S T => |w*(x S-x T)|≤1):ℝ)/2 := by
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc
      _ = (2*M)*B^2*(9/10)^D := by ring
      _ < _ := hh'
  exact ⟨ht,ht.trans_le (count_le_absolute F x (D/4) w)⟩

#print axioms gaussian_dense_resonances
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
