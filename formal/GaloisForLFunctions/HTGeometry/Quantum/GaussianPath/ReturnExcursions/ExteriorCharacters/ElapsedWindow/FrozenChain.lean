import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.DoublyExponentialScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # A positive signed obstruction at the doubly exponential horizon -/

open Matrix Finset MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
open AngularWindings.PhysicalTubes PrecisionReturns PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- At the prescribed doubly exponential horizon, an earlier first dip
forces its actual implementing circuit to have normalized signed window
sum at least $(9/10)^D$ using only differences supported on more than
$D/4$ energies. The window starts at the original crossing. -/
theorem gaussian_first_wait_or_dense_coherence :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let L := (11/10:ℝ)^D
      let H := generator (pathPauliDisorderShell ω (k+1))
      let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
      let B : ℝ := D.choose (D/2)
      ∀ s : ℕ, let v := firstVisit H σ s (1/10)
        L<v-σ ∨ ∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10) ∧
          B^2*(9/10)^D ≤ windowSum (univ.powersetCard (D/2)) (circuitMinor H C.eval)
            H.2.isHermitian.eigenvalues (D/4) σ (L+clearanceTime H) := by
  obtain ⟨C,hC,hω⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp (positive_window_price C)
  filter_upwards [hω] with ω hw
  obtain ⟨M,hM⟩ := eventually_atTop.mp hw
  filter_upwards [eventually_ge_atTop M,eventually_ge_atTop N] with k hk hk'
  intro K D L H σ B s v
  let n := 2^(k+1)
  have hkn : k+1≤n := Nat.lt_two_pow_self.le
  have hd : D=4*n := by dsimp only [D,K,n]; rw [show k+3=(k+1)+2 by omega,pow_add]; ring
  have hwidth := hM (k+1) (by omega)
  change ‖H.val‖≤C*(K:ℝ) at hwidth
  have hK : (K:ℝ)≤4*(n:ℝ) := by
    exact_mod_cast (show K≤4*n by dsimp only [K]; omega)
  have hprice := hN n (by omega) ‖H.val‖ (norm_nonneg _) (hwidth.trans
    (mul_le_mul_of_nonneg_left hK hC.le))
  rcases first_wait_or_window_sum k ω L s with h | ⟨W,hW,hv,hh⟩
  · exact Or.inl h
  refine Or.inr ⟨W,hW,hv,le_trans ?_ hh⟩
  have hq : D/2=2*n := by omega
  have hr : D/4=n := by omega
  have hm : min (D/2) (D-D/2)=2*n := by omega
  change B^2*(9/10)^D ≤ clearanceTime H/(L+clearanceTime H)*
    (B*(1-(9/80:ℝ)^2/2)^min (D/2) (D-D/2))^2-B*(2^(D/4)*(3/2)^D)
  dsimp only [B,L]
  rw [hm,hr,hq,hd]
  exact hprice

#print axioms gaussian_first_wait_or_dense_coherence
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.ElapsedWindow
